// SPDX-License-Identifier: GPL-2.0
/*
 * SELinux hide —— inline hook 版
 *
 * 隐藏逻辑移植自 KPM 版 selinux_hook.c：
 *
 *   1) 不再改写 selinuxfs 的 write_op[] 函数指针表，sel_write_access() /
 *      sel_write_context() 仍然是内核自己的函数：copy_from_user 处理、
 *      avc 权限检查、输出格式全部是原生路径，旧实现里“在内核里重新解析
 *      page 缓冲区”的那一整套路径整体移除。
 *
 *   2) 隐藏方式改为 per-task 作用域 + policydb 替换：应用进程进入
 *      /sys/fs/selinux 查询路径时给 current 打标，内核自己的
 *      string_to_context_struct() / context_struct_compute_av() 改用
 *      backup_sepolicy->policydb，于是 Magisk 相关的 type/context 表现为
 *      “策略里根本没有这个类型”（-EINVAL），与干净策略设备一致。
 *
 *   3) /sys/fs/selinux/status 不再 patch sel_handle_status_ops->open，
 *      改为 hook selinux_kernel_status_page()，把伪造页直接交给
 *      sel_open_handle_status()，read / mmap 两条路径一起覆盖。
 */

#include "selinux_hide.h"
#include "infra/symbol_resolver.h"
#include "linux/jump_label.h"
#include "linux/rcupdate.h"
#include "selinux/sepolicy.h"
#include "ss/policydb.h"
#include <linux/cred.h>
#include <linux/cpu.h>
#include <linux/memory.h>
#include <linux/uaccess.h>
#include <linux/init.h>
#include <linux/printk.h>
#include <linux/string.h>
#include <linux/fs.h>
#include <linux/mm.h>
#include <linux/spinlock.h>
#include <linux/sched.h>
#include <linux/atomic.h>
#include <linux/mutex.h>
#include <asm-generic/errno-base.h>
#include <net/genetlink.h>
#include <linux/moduleparam.h>
// security/selinux/include/security.h
#include <security.h>
#include <ss/context.h>
#include <ss/services.h>
#include <ss/mls.h>
#include <ss/conditional.h>
#include "avc.h"
#include "klog.h" // IWYU pragma: keep
#include "linux/kallsyms.h"
#include "objsec.h"
#include "hook/patch_memory.h"
#include "ksu.h"
#include "policy/feature.h"
#include "hook/lsm_hook.h"

/* ==========================================================================
 * inline hook 适配层
 *
 * 本文件只依赖两个原语：
 *
 *     int  ksu_inline_hook(void *target, void *replace, void **origin);
 *     void ksu_inline_unhook(void *target);
 *
 * 目标树里若是 kpatch_install/kpatch_remove 或 KernelPatch 的 hook_wrap()，
 * 只改下面两个包装即可，其它代码不用动。
 * ========================================================================== */
extern int ksu_inline_hook(void *target, void *replace, void **origin);
extern void ksu_inline_unhook(void *target);

static inline int sel_hide_inline_hook(void *target, void *replace, void **origin)
{
	return ksu_inline_hook(target, replace, origin);
}

static inline void sel_hide_inline_unhook(void *target)
{
	ksu_inline_unhook(target);
}

/*
 * string_to_context_struct() 的参数数量在历史版本里变过一次：
 *   4.x  : (pol, sidtabp, scontext, scontext_len, ctx, def_sid)   6 个
 *   5.x+ : (pol, sidtabp, scontext, ctx, def_sid)                 5 个
 * 传错会导致原函数拿 ctx 当 scontext_len 用，直接崩。特殊回溯树如果对不上，
 * 把 SEL_HIDE_STCS_TAKES_LEN 显式定义成 1 或 0 即可。
 */
#ifndef SEL_HIDE_STCS_TAKES_LEN
#if LINUX_VERSION_CODE < KERNEL_VERSION(5, 0, 0)
#define SEL_HIDE_STCS_TAKES_LEN 1
#else
#define SEL_HIDE_STCS_TAKES_LEN 0
#endif
#endif

#ifndef SIMPLE_TRANSACTION_LIMIT
#define SIMPLE_TRANSACTION_LIMIT (PAGE_SIZE - 1)
#endif

#define CLEAN_EVAL_SCOPE_SLOTS 8
#define SEL_HIDE_MAX_HOOKS 8
#define SEL_HIDE_ACCESS_RESP_MAX 128

static DEFINE_MUTEX(selinux_hide_mutex);
static bool ksu_selinux_hide_enabled __read_mostly = false;
static bool ksu_selinux_hide_running __read_mostly = false;

static void *sel_hide_hook_targets[SEL_HIDE_MAX_HOOKS];
static int sel_hide_hook_count;

/* ==========================================================================
 * clean-eval 作用域（per-task）
 * ========================================================================== */

struct clean_eval_scope {
	struct task_struct *task;
	u32 depth;
};

static struct clean_eval_scope clean_eval_scopes[CLEAN_EVAL_SCOPE_SLOTS];
static DEFINE_RAW_SPINLOCK(clean_eval_lock);
static atomic_t clean_eval_active = ATOMIC_INIT(0);

/* 干净（备份）策略库；Magisk 注入的 type/rule 不在里面 */
static struct policydb *clean_policydb_get(void)
{
	struct selinux_policy *policy = READ_ONCE(backup_sepolicy);

	return policy ? &policy->policydb : NULL;
}

static bool enter_clean_eval_scope(void)
{
	struct task_struct *task = current;
	bool entered = false;
	int empty = -1;
	int i;

	if (!clean_policydb_get())
		return false;

	raw_spin_lock(&clean_eval_lock);
	for (i = 0; i < CLEAN_EVAL_SCOPE_SLOTS; i++) {
		if (clean_eval_scopes[i].task == task) {
			clean_eval_scopes[i].depth++;
			entered = true;
			break;
		}
		if (empty < 0 && !clean_eval_scopes[i].task)
			empty = i;
	}
	if (!entered) {
		if (empty < 0) {
			raw_spin_unlock(&clean_eval_lock);
			pr_warn("selinux_hide: clean eval scope slots exhausted pid=%d comm=%s\n",
				task_pid_nr(task), task->comm);
			return false;
		}
		clean_eval_scopes[empty].task = task;
		clean_eval_scopes[empty].depth = 1;
		entered = true;
	}
	atomic_inc(&clean_eval_active);
	raw_spin_unlock(&clean_eval_lock);

	return entered;
}

static void leave_clean_eval_scope(void)
{
	struct task_struct *task = current;
	int i;

	raw_spin_lock(&clean_eval_lock);
	for (i = 0; i < CLEAN_EVAL_SCOPE_SLOTS; i++) {
		if (clean_eval_scopes[i].task != task)
			continue;

		if (--clean_eval_scopes[i].depth == 0)
			clean_eval_scopes[i].task = NULL;
		atomic_dec(&clean_eval_active);
		break;
	}
	raw_spin_unlock(&clean_eval_lock);
}

static bool current_in_clean_eval_scope(void)
{
	struct task_struct *task = current;
	bool found = false;
	int i;

	/* 热路径（avc 每次判定都会进来）先走一次无锁判断 */
	if (!atomic_read(&clean_eval_active))
		return false;

	raw_spin_lock(&clean_eval_lock);
	for (i = 0; i < CLEAN_EVAL_SCOPE_SLOTS; i++) {
		if (clean_eval_scopes[i].task == task && clean_eval_scopes[i].depth) {
			found = true;
			break;
		}
	}
	raw_spin_unlock(&clean_eval_lock);

	return found;
}

/* ==========================================================================
 * 伪造的 /sys/fs/selinux/status 页
 * ========================================================================== */

static DEFINE_STATIC_KEY_FALSE(fake_status_initialize_key);
static struct page *fake_status = NULL;

static void initialize_fake_status(void)
{
	struct selinux_kernel_status *new_status;
	struct selinux_kernel_status *status;
	struct page *new_page;

	mutex_lock(&selinux_state.status_lock);
	if (fake_status)
		goto out;
	if (!selinux_state.status_page) {
		pr_warn("initialize_fake_status: status_page not exist\n");
		goto out;
	}

	status = page_address(selinux_state.status_page);
	if (!status->enforcing && !ksu_late_loaded) {
		pr_warn("initialize_fake_status: skip not enforcing\n");
		goto out;
	}

	new_page = alloc_page(GFP_KERNEL | __GFP_ZERO);
	if (!new_page) {
		pr_err("initialize_fake_status: failed to allocate page\n");
		goto out;
	}

	new_status = page_address(new_page);
	memcpy(new_status, status, sizeof(*status));
	if (ksu_late_loaded) {
		// In late_load mode the loader may have reloaded sepolicy before us,
		// so the captured page is not stock. Serve what a stock boot ends
		// with instead: creation sentinel below 6.10, one load plus one
		// setenforce above.
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 10, 0)
		new_status->sequence = 4;
		new_status->policyload = 1;
#else
		new_status->sequence = 0;
		new_status->policyload = 0;
#endif
		if (!new_status->enforcing) {
			new_status->enforcing = 1;
		}
	}

	fake_status = new_page;
	pr_info("initialize_fake_status initialized: sequence=%d, policyload=%d, enforcing=%d\n",
		new_status->sequence, new_status->policyload, new_status->enforcing);

out:
	mutex_unlock(&selinux_state.status_lock);
}

/* 把伪造页的 policyload 当作 access 响应里应回的 seqno */
static u32 clean_status_policyload(void)
{
	struct selinux_kernel_status *status;
	u32 policyload = 1;

	mutex_lock(&selinux_state.status_lock);
	if (fake_status) {
		status = page_address(fake_status);
		policyload = status->policyload;
	}
	mutex_unlock(&selinux_state.status_lock);

	return policyload;
}

/* ==========================================================================
 * hook: selinux_kernel_status_page()
 *
 * sel_open_handle_status() 把工厂函数的返回值存进 filp->private_data，
 * read/mmap 都从这里取页，所以在工厂函数这一层替换即可，不再碰
 * sel_handle_status_ops（const file_operations，位于 rodata）。
 * ========================================================================== */

typedef struct page *(*selinux_kernel_status_page_fn)(void *state);
static selinux_kernel_status_page_fn orig_selinux_kernel_status_page;

static struct page *__nocfi my_selinux_kernel_status_page(void *state)
{
	struct page *page;
	struct page *ret;

	if (likely(current_uid().val >= 10000) &&
	    READ_ONCE(ksu_selinux_hide_enabled)) {
		mutex_lock(&selinux_state.status_lock);
		ret = fake_status;
		mutex_unlock(&selinux_state.status_lock);
		if (ret)
			return ret;
	}

	page = orig_selinux_kernel_status_page(state);

	if (static_branch_unlikely(&fake_status_initialize_key) && page) {
		mutex_lock(&selinux_state.status_lock);
		ret = fake_status;
		mutex_unlock(&selinux_state.status_lock);
		if (!ret)
			initialize_fake_status();
	}

	return page;
}

/* ==========================================================================
 * hook: context_struct_compute_av() / string_to_context_struct()
 *
 * 只替换第一个参数 policydb，其余参数、sidtab、调用约定全部保持原样，
 * 并且只在被打了作用域标记的 current 上生效。
 * ========================================================================== */

typedef void (*context_struct_compute_av_fn)(struct policydb *policydb,
					     struct context *scontext,
					     struct context *tcontext,
					     u16 tclass,
					     struct av_decision *avd,
					     struct extended_perms *xperms);
static context_struct_compute_av_fn orig_context_struct_compute_av;

static void __nocfi my_context_struct_compute_av(struct policydb *policydb,
						 struct context *scontext,
						 struct context *tcontext,
						 u16 tclass,
						 struct av_decision *avd,
						 struct extended_perms *xperms)
{
	struct policydb *clean = NULL;

	if (unlikely(current_in_clean_eval_scope()))
		clean = clean_policydb_get();
	if (clean)
		policydb = clean;

	orig_context_struct_compute_av(policydb, scontext, tcontext, tclass,
				       avd, xperms);
}

#if SEL_HIDE_STCS_TAKES_LEN
typedef int (*string_to_context_struct_fn)(struct policydb *pol,
					   struct sidtab *sidtabp,
					   char *scontext, u32 scontext_len,
					   struct context *ctx, u32 def_sid);
#else
typedef int (*string_to_context_struct_fn)(struct policydb *pol,
					   struct sidtab *sidtabp,
					   char *scontext,
					   struct context *ctx, u32 def_sid);
#endif
static string_to_context_struct_fn orig_string_to_context_struct;

static int __nocfi my_string_to_context_struct(struct policydb *pol,
					       struct sidtab *sidtabp,
					       char *scontext, u32 scontext_len,
					       struct context *ctx, u32 def_sid)
{
	struct policydb *clean = NULL;

	if (unlikely(current_in_clean_eval_scope()))
		clean = clean_policydb_get();
	if (clean)
		pol = clean;

#if SEL_HIDE_STCS_TAKES_LEN
	return orig_string_to_context_struct(pol, sidtabp, scontext,
					     scontext_len, ctx, def_sid);
#else
	return orig_string_to_context_struct(pol, sidtabp, scontext, ctx, def_sid);
#endif
}

/* ==========================================================================
 * hook: sel_write_access() / sel_write_context()
 *
 * 内核原生实现在 sel_write() 里拿到的是 memdup_user() 出来的内核缓冲区，
 * 这里只负责“进作用域 -> 跑原函数 -> 出作用域”，输入输出的解析、
 * avc 检查、错误码全部由内核自己产生。
 * ========================================================================== */

typedef ssize_t (*sel_write_op_fn)(struct file *file, char *buf, size_t size);
static sel_write_op_fn orig_sel_write_access;
static sel_write_op_fn orig_sel_write_context;

/* arm64：内核地址位于 TTBR1 上半区，bit63 恒为 1 */
static inline bool sel_hide_is_kernel_addr(const void *addr)
{
	return ((unsigned long)addr >> 63) != 0;
}

/*
 * 响应格式 "%x %x %x %x %u %x"，第 5 个字段是 seqno。
 * 把它改成伪造 status 页的 policyload，避免 /status 与 /access 自相矛盾。
 */
static ssize_t sel_hide_patch_seqno_field(char *buf, ssize_t len, size_t cap,
					  u32 seqno)
{
	char newstr[12];
	char *p = buf;
	char *end = buf + len;
	char *tok;
	size_t oldlen;
	size_t new_total;
	int newlen;
	int i;

	if (len <= 0)
		return len;

	for (i = 0; i < 4; i++) {
		while (p < end && *p == ' ')
			p++;
		while (p < end && *p != ' ')
			p++;
	}
	while (p < end && *p == ' ')
		p++;

	tok = p;
	while (p < end && *p >= '0' && *p <= '9')
		p++;
	oldlen = (size_t)(p - tok);
	if (!oldlen)
		return len;

	newlen = snprintf(newstr, sizeof(newstr), "%u", seqno);
	if (newlen <= 0)
		return len;

	if ((size_t)newlen != oldlen) {
		new_total = (size_t)len + (size_t)newlen - oldlen;
		if (new_total > cap)
			return len;
		memmove(tok + newlen, tok + oldlen,
			(size_t)(end - (tok + oldlen)));
		len = (ssize_t)new_total;
	}

	memcpy(tok, newstr, (size_t)newlen);
	return len;
}

static ssize_t sel_hide_patch_access_seqno(char *buf, size_t size, ssize_t ret)
{
	char tmp[SEL_HIDE_ACCESS_RESP_MAX];
	size_t cap;
	ssize_t len;

	if (!buf || ret <= 0 || (size_t)ret > size)
		return ret;
	if (!sel_hide_is_kernel_addr(buf))
		return ret;
	if ((size_t)ret >= sizeof(tmp))
		return ret;

	memcpy(tmp, buf, (size_t)ret);
	cap = min_t(size_t, size, sizeof(tmp));

	len = sel_hide_patch_seqno_field(tmp, ret, cap, clean_status_policyload());
	if (len == ret)
		return ret;

	memcpy(buf, tmp, (size_t)len);
	return len;
}

static ssize_t __nocfi my_sel_write_access(struct file *file, char *buf,
					   size_t size)
{
	bool scoped = false;
	ssize_t ret;

	if (likely(current_uid().val < 10000))
		return orig_sel_write_access(file, buf, size);

	if (enter_clean_eval_scope())
		scoped = true;

	ret = orig_sel_write_access(file, buf, size);

	if (scoped)
		leave_clean_eval_scope();

	if (ret > 0)
		ret = sel_hide_patch_access_seqno(buf, size, ret);

	return ret;
}

static ssize_t __nocfi my_sel_write_context(struct file *file, char *buf,
					    size_t size)
{
	bool scoped = false;
	ssize_t ret;

	if (likely(current_uid().val < 10000))
		return orig_sel_write_context(file, buf, size);

	if (enter_clean_eval_scope())
		scoped = true;

	ret = orig_sel_write_context(file, buf, size);

	if (scoped)
		leave_clean_eval_scope();

	return ret;
}

/* ==========================================================================
 * LSM hook: selinux_setprocattr()
 *
 * 只负责开作用域，/proc/self/attr/current 的解析、转换检查、commit_creds
 * 全部走内核原生实现；Magisk context 在 string_to_context_struct() 里
 * 因为干净策略查不到 type 而返回 -EINVAL。
 * ========================================================================== */

typedef int (*setprocattr_fn)(const char *name, void *value, size_t size);
static int my_setprocattr(const char *name, void *value, size_t size);
struct ksu_lsm_hook selinux_setprocattr_hook =
	KSU_LSM_HOOK_INIT(setprocattr, "selinux_setprocattr", my_setprocattr, 0);

static int __nocfi my_setprocattr(const char *name, void *value, size_t size)
{
	setprocattr_fn orig = (setprocattr_fn)selinux_setprocattr_hook.original;
	bool scoped = false;
	int ret;

	if (likely(current_uid().val < 10000) || strcmp(name, "current"))
		return orig(name, value, size);

	if (enter_clean_eval_scope())
		scoped = true;

	ret = orig(name, value, size);

	if (scoped)
		leave_clean_eval_scope();

	return ret;
}

/* ==========================================================================
 * hook 安装 / 卸载
 * ========================================================================== */

static int sel_hide_install_hook(const char *name, void *replace, void **origin)
{
	void *target;
	int ret;

	if (sel_hide_hook_count >= SEL_HIDE_MAX_HOOKS) {
		pr_err("selinux_hide: hook table full\n");
		return -ENOSPC;
	}

	target = find_kernel_symbol_exact(name);
	if (!target) {
		pr_warn("selinux_hide: symbol %s not found\n", name);
		return -ENOENT;
	}

	ret = sel_hide_inline_hook(target, replace, origin);
	if (ret) {
		pr_err("selinux_hide: hook %s failed: %d\n", name, ret);
		return ret;
	}

	sel_hide_hook_targets[sel_hide_hook_count++] = target;
	pr_info("selinux_hide: hook %s @ 0x%lx -> %px\n", name,
		(unsigned long)target, replace);

	return 0;
}

static void sel_hide_remove_hooks(void)
{
	int i;

	for (i = sel_hide_hook_count - 1; i >= 0; i--) {
		if (sel_hide_hook_targets[i])
			sel_hide_inline_unhook(sel_hide_hook_targets[i]);
		sel_hide_hook_targets[i] = NULL;
	}
	sel_hide_hook_count = 0;
}

static int ksu_selinux_hide_enable(void)
{
	int ret;

	pr_info("selinux_hide: init selinux hide (inline hook mode)\n");

	if (!backup_sepolicy) {
		pr_err("no backup sepolicy available, please save feature and reboot to retry!\n");
		return -EAGAIN;
	}

	sel_hide_hook_count = 0;

	ret = sel_hide_install_hook("selinux_kernel_status_page",
				    my_selinux_kernel_status_page,
				    (void **)&orig_selinux_kernel_status_page);
	if (ret)
		goto out;

	ret = sel_hide_install_hook("sel_write_access", my_sel_write_access,
				    (void **)&orig_sel_write_access);
	if (ret)
		goto out;

	ret = sel_hide_install_hook("sel_write_context", my_sel_write_context,
				    (void **)&orig_sel_write_context);
	if (ret)
		goto out;

	ret = sel_hide_install_hook("context_struct_compute_av",
				    my_context_struct_compute_av,
				    (void **)&orig_context_struct_compute_av);
	if (ret)
		goto out;

	/* 部分 LTO 内核会把它内联掉；找不到时只告警，不影响其它三处隐藏 */
	ret = sel_hide_install_hook("string_to_context_struct",
				    my_string_to_context_struct,
				    (void **)&orig_string_to_context_struct);
	if (ret == -ENOENT)
		pr_warn("selinux_hide: string_to_context_struct unavailable, /context 探针未覆盖\n");
	else if (ret)
		goto out;

	ret = ksu_lsm_hook(&selinux_setprocattr_hook);
	if (ret) {
		pr_err("selinux_hide: selinux_setprocattr_hook err: %d\n", ret);
		goto out;
	}

	return 0;

out:
	sel_hide_remove_hooks();
	return ret;
}

static void ksu_selinux_hide_unhook(void)
{
	ksu_lsm_unhook(&selinux_setprocattr_hook);
	sel_hide_remove_hooks();
}

static void ksu_selinux_hide_disable(void)
{
	pr_info("selinux_hide: exit selinux hide\n");
	ksu_selinux_hide_unhook();
}

/* ==========================================================================
 * feature 注册
 * ========================================================================== */

static int selinux_hide_feature_get(u64 *value)
{
	*value = ksu_selinux_hide_enabled ? 1 : 0;
	return 0;
}

static int selinux_hide_feature_set(u64 value)
{
	bool enable = value != 0;
	int ret = 0;

	pr_info("selinux_hide: set to %d\n", enable);
	mutex_lock(&selinux_hide_mutex);
	ksu_selinux_hide_enabled = enable;
	if (enable) {
		if (!ksu_selinux_hide_running) {
			ret = ksu_selinux_hide_enable();
			if (!ret)
				ksu_selinux_hide_running = true;
		}
	} else {
		if (ksu_selinux_hide_running) {
			ksu_selinux_hide_disable();
			ksu_selinux_hide_running = false;
		}
	}
	mutex_unlock(&selinux_hide_mutex);
	return ret;
}

static const struct ksu_feature_handler selinux_hide_handler = {
	.feature_id = KSU_FEATURE_SELINUX_HIDE,
	.name = "selinux_hide",
	.get_handler = selinux_hide_feature_get,
	.set_handler = selinux_hide_feature_set,
};

/* ==========================================================================
 * 生命周期（对外语义保持不变）
 * ========================================================================== */

void ksu_selinux_hide_handle_second_stage(void)
{
	initialize_fake_status();
	// https://github.com/torvalds/linux/blame/e8c2f9fdadee7cbc75134dc463c1e0d856d6e5c7/security/selinux/selinuxfs.c#L2014
	if (fake_status) {
		static_key_disable(&fake_status_initialize_key.key);
	} else {
		pr_warn("selinux_hide: fake status need late initialization\n");
	}
}

void ksu_selinux_hide_handle_post_fs_data(void)
{
	static_key_disable(&fake_status_initialize_key.key);
	if (!fake_status) {
		pr_err("selinux_hide: fake status is not initialized after post-fs-data!\n");
	}
}

void __init ksu_selinux_hide_init(void)
{
	if (ksu_register_feature_handler(&selinux_hide_handler)) {
		pr_err("Failed to register selinux_hide feature handler\n");
	}
	if (ksu_late_loaded) {
		initialize_fake_status();
	} else {
		static_key_enable(&fake_status_initialize_key.key);
	}
}

void __exit ksu_selinux_hide_exit(void)
{
	mutex_lock(&selinux_hide_mutex);
	if (ksu_selinux_hide_running) {
		ksu_selinux_hide_disable();
		ksu_selinux_hide_running = false;
	}
	mutex_unlock(&selinux_hide_mutex);
	ksu_unregister_feature_handler(KSU_FEATURE_SELINUX_HIDE);

	mutex_lock(&selinux_state.status_lock);
	if (fake_status)
		__free_page(fake_status);
	fake_status = NULL;
	mutex_unlock(&selinux_state.status_lock);
}

void ksu_selinux_hide_drop_backup_if_unused(void)
{
	mutex_lock(&selinux_hide_mutex);
	if (!ksu_selinux_hide_running && backup_sepolicy) {
		pr_info("selinux_hide is not enabled - drop backup_sepolicy\n");
		sidtab_destroy(backup_sepolicy->sidtab);
		kfree(backup_sepolicy->sidtab);
		ksu_destroy_sepolicy(backup_sepolicy);
		backup_sepolicy = NULL;
	}
	mutex_unlock(&selinux_hide_mutex);
}