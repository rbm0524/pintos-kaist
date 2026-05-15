#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "intrinsic.h"
#include "include/devices/timer.h"
#include "threads/fixed-point.h"
#include "include/lib/kernel/list.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* Random value for basic thread
   Do not modify this value. */
#define THREAD_BASIC 0xd42df210

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
struct list ready_list;
struct list blocked_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Thread destruction requests */
static struct list destruction_req;

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

// 시스템 부하량
/*
	현재 준비상태거나 실행중인 스레드들의 개수* 1/60 + 기존 load_avg * 59/60으로 가중평균하여 1초마다 새롭게 측정.
	마찬가지로 1초마다 갱신된 load_avg를 기반으로 모든 스레드들 각각의 cpu 사용량 측정.
	4틱마다 최종 변경된 정보들로 priority 갱신
*/
int load_avg;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static void do_schedule(int status);
static void schedule (void);
static tid_t allocate_tid (void);

/* Returns true if T appears to point to a valid thread. */
#define is_thread(t) ((t) != NULL && (t)->magic == THREAD_MAGIC)

/* Returns the running thread.
 * Read the CPU's stack pointer `rsp', and then round that
 * down to the start of a page.  Since `struct thread' is
 * always at the beginning of a page and the stack pointer is
 * somewhere in the middle, this locates the curent thread. */
#define running_thread() ((struct thread *) (pg_round_down (rrsp ())))


// Global descriptor table for the thread_start.
// Because the gdt will be setup after the thread_init, we should
// setup temporal gdt first.
static uint64_t gdt[3] = { 0, 0x00af9a000000ffff, 0x00cf92000000ffff };

// a : list's element
// b : compared struct
// 오름차순 정렬
bool less_priority(const struct list_elem *elem, const struct list_elem *e, void *aux UNUSED) {
	return list_entry(elem, struct thread, elem) -> priority > list_entry(e, struct thread, elem) -> priority;
}

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) {
	ASSERT (intr_get_level () == INTR_OFF);

	/* Reload the temporal gdt for the kernel
	 * This gdt does not include the user context.
	 * The kernel will rebuild the gdt with user context, in gdt_init (). */
	struct desc_ptr gdt_ds = {
		.size = sizeof (gdt) - 1,
		.address = (uint64_t) gdt
	};
	lgdt (&gdt_ds);

	/* Init the globla thread context */
	lock_init (&tid_lock);
	list_init (&ready_list);
	list_init (&blocked_list);
	list_init (&destruction_req);

	/* Set up a thread structure for the running thread. */
	initial_thread = running_thread ();
	init_thread (initial_thread, "main", PRI_DEFAULT);
	initial_thread->status = THREAD_RUNNING;
	initial_thread->tid = allocate_tid ();
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) {
	/* Create the idle thread. */
	struct semaphore idle_started;
	sema_init (&idle_started, 0);
	thread_create ("idle", PRI_MIN, idle, &idle_started);

	/* Start preemptive thread scheduling. */
	intr_enable ();

	/* Wait for the idle thread to initialize idle_thread. */
	sema_down (&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) {
	struct thread *t = thread_current ();

	/* Update statistics. */
	if (t == idle_thread)
		idle_ticks++;
#ifdef USERPROG
	else if (t->pml4 != NULL)
		user_ticks++;
#endif
	else
		kernel_ticks++;

	/* Enforce preemption. */
	if (++thread_ticks >= TIME_SLICE)
		intr_yield_on_return ();
}

/* Prints thread statistics. */
void
thread_print_stats (void) {
	printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
			idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.
   -- aux 인자로 넘겨받은 함수를 실행할 목적, 스레드를 만들면 ready_queue에 들어간다.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
		thread_func *function, void *aux) {
	struct thread *t;
	tid_t tid;

	ASSERT (function != NULL);

	/* Allocate thread. */
	t = palloc_get_page (PAL_ZERO);
	if (t == NULL)
		return TID_ERROR;

	
	/* Initialize thread. */
	init_thread (t, name, priority);
	tid = t->tid = allocate_tid ();

	/* Call the kernel_thread if it scheduled.
	 * Note) rdi is 1st argument, and rsi is 2nd argument. */
	// 이제 막 생성된 스레드는 저장된 값이 없으므로 세팅
	t->tf.rip = (uintptr_t) kernel_thread;
	t->tf.R.rdi = (uint64_t) function;
	t->tf.R.rsi = (uint64_t) aux;
	t->tf.ds = SEL_KDSEG;
	t->tf.es = SEL_KDSEG;
	t->tf.ss = SEL_KDSEG;
	t->tf.cs = SEL_KCSEG;
	t->tf.eflags = FLAG_IF;

	/* Add to run queue. */
	thread_unblock (t);

	if(!list_empty(&ready_list)) {
		struct thread *begin = list_entry(list_begin(&ready_list), struct thread, elem); // insert한 것이 begin으로 올라오면서 현재 실행중인 스레드보다 우선순위가 높을수도
		
		if(thread_get_priority() < begin -> priority) {
			thread_yield();
		}
	}

	return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) {
	ASSERT (!intr_context ());
	ASSERT (intr_get_level () == INTR_OFF);
	// 현재 실행중인 스레드는 list가 없음
	thread_current ()->status = THREAD_BLOCKED; // 반환받은 현재 스레드의 상태를 BLOCKED로 바꿈
	schedule (); // 스레드를 BLOCKED 상태로 바꾼 후 다른 스레드로 전환하기
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) {
	enum intr_level old_level;

	ASSERT (is_thread (t));

	old_level = intr_disable ();

	ASSERT (t->status == THREAD_BLOCKED);
	
	// list_push_back (&ready_list, &t->elem); // 실행 가능 상태로 만들어주기
	// 정렬해서 끼워넣기
	list_insert_ordered(&ready_list, &t->elem, less_priority, NULL);
	t->status = THREAD_READY;

	// 이제 interrupt가 가능하게 한 후 새롭게 넣은 스레드가 만약 begin에 있을 경우를 대비해 우선순위를 체크한다.
	intr_set_level (old_level);
	
}

/* Returns the name of the running thread. */
const char *
thread_name (void) {
	return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) {
	struct thread *t = running_thread ();

	/* Make sure T is really a thread.
	   If either of these assertions fire, then your thread may
	   have overflowed its stack.  Each thread has less than 4 kB
	   of stack, so a few big automatic arrays or moderate
	   recursion can cause stack overflow. */
	ASSERT (is_thread (t));
	ASSERT (t->status == THREAD_RUNNING);

	return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) {
	return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) {
	ASSERT (!intr_context ());

#ifdef USERPROG
	process_exit ();
#endif

	/* Just set our status to dying and schedule another process.
	   We will be destroyed during the call to schedule_tail(). */
	intr_disable ();
	do_schedule (THREAD_DYING);
	NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) {
	struct thread *curr = thread_current ();
	enum intr_level old_level;

	ASSERT (!intr_context ());

	old_level = intr_disable ();

	// 현재 스레드를 ready_list에 넣기
	if (curr != idle_thread)
		// list_push_back (&ready_list, &curr->elem);
		list_insert_ordered(&ready_list, &curr->elem, less_priority, NULL);
	
	do_schedule (THREAD_READY);

	intr_set_level (old_level);
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void
thread_set_priority (int new_priority) {
	enum intr_level old_level = intr_disable();
	struct thread *cur_thread = thread_current();
	
	cur_thread -> init_priority = new_priority;
	if(!thread_mlfqs) {
		cur_thread -> priority = new_priority;
	
		// 만약 기부받은 것이 있으면 기부받은 것들 or 내 현재 우선순위 비교해서 더 큰거 덮어쓰기
		if(!list_empty(&cur_thread -> donations)) {
			struct thread *donate_to_cur = list_entry(list_begin(&cur_thread -> donations), struct thread, donations_elem);
			if(cur_thread -> priority < donate_to_cur -> priority) {
				// 우선순위가 donate_to_cur보다 낮아졌으면 다시 올려주기
				cur_thread -> priority =  donate_to_cur -> priority;
			}
		}
	
		// 기부받은 것이 없으면 새 우선순위로 바로 조정되고, yield할 수 있다.		
		if(!list_empty(&ready_list)) {
			if(thread_current() -> priority < list_entry(list_begin(&ready_list), struct thread, elem) -> priority) {
				thread_yield();
			}
		}
	} else {
		cur_thread -> priority = PRI_MAX - (thread_current() -> recent_cpu / 4) - cur_thread -> nice * 2;
		cur_thread -> recent_cpu = (2*thread_get_load_avg()) / (2 * thread_get_load_avg() + 1) * cur_thread -> recent_cpu + cur_thread -> nice;
	}

	intr_set_level(old_level);
}

/* Returns the current thread's priority. */
int
thread_get_priority (void) {
	return thread_current ()->priority;
}

// nice : represents the 'niceness' of thread
// if the thread is nicer, it is willing to give up some time of it's CPU times
// 0 : not influence on priority
// positive : decrease priority
// negative : increase priority
// if the thread is nicer, lower the priority (우선순위를 낮춰야 ready_list에 집어넣어도 맨 앞으로 안옴)

/* Sets the current thread's nice value to NICE. */
void
thread_set_nice (int nice UNUSED) {
	thread_current() -> nice = nice;
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) {
	return thread_current() -> nice;
}

/* Returns 100 times the system load average. */
int
thread_get_load_avg (void) {
	return convert_f_to_i_nearest(mul_f_and_i(load_avg, 100));
}

/* Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) {
	return convert_f_to_i_nearest(mul_f_and_i(thread_current() -> recent_cpu, 100));
}

void calc_priority(struct thread *t) {
	t -> priority = convert_f_to_i_nearest(sub_f_from_f(sub_f_from_f(convert_i_to_f(PRI_MAX), (div_f_by_i(t -> recent_cpu, 4))), convert_i_to_f((t -> nice * 2))));
}

// recent_cpu, load_avg is a real number.
void calc_recent_cpu() {
	// decay도 결국 실수형이 된다.
	int decay = div_f_by_f(mul_f_and_i(load_avg, 2), add_f_and_i(mul_f_and_i(load_avg, 2), 1));
	thread_current() -> recent_cpu = add_f_and_i(mul_f_and_f(decay, thread_current() -> recent_cpu), thread_current() -> nice);

	enum intr_level old_level = intr_disable();

	if(!list_empty(&ready_list)) {
		struct list_elem *e = list_begin(&ready_list);
		while(e != list_end(&ready_list)) {
			struct thread *t = list_entry(e, struct thread, elem);
			t -> recent_cpu = add_f_and_i(mul_f_and_f(decay, t -> recent_cpu), t -> nice);
			e = list_next(e);
		}
	}

	if(!list_empty(&blocked_list)) {
		struct list_elem *e2 = list_begin(&blocked_list);
		while(e2 != list_end(&blocked_list)) {
			struct thread *t = list_entry(e2, struct thread, elem);
			t -> recent_cpu = add_f_and_i(mul_f_and_f(decay, t -> recent_cpu), t -> nice);
			e2 = list_next(e2);
		}
	}

	intr_set_level (old_level);
}

void calc_load_avg() {
	int ready_threads = list_size(&ready_list);
	// idle 스레드가 아니어야 하나로 쳐줄 수 있음
	if(thread_current() != idle_thread) {
		ready_threads++;
	}
	load_avg = add_f_and_f(mul_f_and_f(div_f_by_f(convert_i_to_f(59), convert_i_to_f(60)), load_avg), mul_f_and_i(div_f_by_f(convert_i_to_f(1), convert_i_to_f(60)), ready_threads));
}

void inc_recent_cpu() {
	thread_current() -> recent_cpu = add_f_and_i(thread_current() -> recent_cpu, 1);
}

void all_recalc_priority() {
	enum intr_level old_level = intr_disable();

	struct list_elem *e = list_begin(&ready_list);
	while(e != list_end(&ready_list)) {
		calc_priority(list_entry(e, struct thread, elem));
		e = list_next(e);
	}

	calc_priority(thread_current());

	if(!list_empty(&ready_list)) {

		list_sort(&ready_list, less_priority, NULL);
		if(list_entry(list_begin(&ready_list), struct thread, elem) -> priority > thread_current() -> priority) {
			intr_yield_on_return();

		}
	}

	intr_set_level (old_level);
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) {
	struct semaphore *idle_started = idle_started_;

	idle_thread = thread_current ();
	sema_up (idle_started);

	for (;;) {
		/* Let someone else run. */
		intr_disable ();
		thread_block ();

		/* Re-enable interrupts and wait for the next one.

		   The `sti' instruction disables interrupts until the
		   completion of the next instruction, so these two
		   instructions are executed atomically.  This atomicity is
		   important; otherwise, an interrupt could be handled
		   between re-enabling interrupts and waiting for the next
		   one to occur, wasting as much as one clock tick worth of
		   time.

		   See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
		   7.11.1 "HLT Instruction". */
		asm volatile ("sti; hlt" : : : "memory");
	}
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) {
	ASSERT (function != NULL);

	intr_enable ();       /* The scheduler runs with interrupts off. */
	function (aux);       /* Execute the thread function. */
	thread_exit ();       /* If function() returns, kill the thread. */
}


/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority) {
	ASSERT (t != NULL);
	ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
	ASSERT (name != NULL);

	memset (t, 0, sizeof *t);
	t->status = THREAD_BLOCKED; // 초기 스레드는 BLOCKED된 상태로 시작
	strlcpy (t->name, name, sizeof t->name);
	t->tf.rsp = (uint64_t) t + PGSIZE - sizeof (void *);
	t->priority = priority;
	t->init_priority = priority;
	t->magic = THREAD_MAGIC;
	t->nice = 0;
	t->recent_cpu = 0;
	list_init(&t->donations);
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) {
	if (list_empty (&ready_list))
		return idle_thread;
	else
		return list_entry (list_pop_front (&ready_list), struct thread, elem); // 맨 앞의 것을 뺀다.
}

/* Use iretq to launch the thread */
// 전달받은 tf 레지스터값을 복구시켜서 스레드를 전환한다.
void
do_iret (struct intr_frame *tf) {
	__asm __volatile(
			"movq %0, %%rsp\n"
			"movq 0(%%rsp),%%r15\n"
			"movq 8(%%rsp),%%r14\n"
			"movq 16(%%rsp),%%r13\n"
			"movq 24(%%rsp),%%r12\n"
			"movq 32(%%rsp),%%r11\n"
			"movq 40(%%rsp),%%r10\n"
			"movq 48(%%rsp),%%r9\n"
			"movq 56(%%rsp),%%r8\n"
			"movq 64(%%rsp),%%rsi\n"
			"movq 72(%%rsp),%%rdi\n"
			"movq 80(%%rsp),%%rbp\n"
			"movq 88(%%rsp),%%rdx\n"
			"movq 96(%%rsp),%%rcx\n"
			"movq 104(%%rsp),%%rbx\n"
			"movq 112(%%rsp),%%rax\n"
			"addq $120,%%rsp\n"
			"movw 8(%%rsp),%%ds\n"
			"movw (%%rsp),%%es\n"
			"addq $32, %%rsp\n"
			"iretq"
			: : "g" ((uint64_t) tf) : "memory");
}

/* Switching the thread by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function. */
static void
thread_launch (struct thread *th) {
	// 현재 interrupt frame
	uint64_t tf_cur = (uint64_t) &running_thread ()->tf; // interrupt frame을 uint64_t로 casting
	
	// 다음 interrupt frame
	uint64_t tf = (uint64_t) &th->tf; // 인자로 받은 th의 interrupt frame도 uint64_t로 casting
	ASSERT (intr_get_level () == INTR_OFF); // interrupt가 켜져있으면 스레드 전환 시에 인터럽트 걸릴 수 있으니

	/* The main switching logic.
	 * We first restore the whole execution context into the intr_frame
	 * and then switching to the next thread by calling do_iret.
	 * Note that, we SHOULD NOT use any stack from here
	 * until switching is done. */
	// AT&T 문법, 기본적으로 CPU의 레지스터 이름 앞에 % 기호가 붙는다.
	// %0: C 코드 영역에서 넘어온 데이터
	// %%rax: 실제 하드웨어 CPU의 RAX 레지스터
	__asm __volatile (
			/* Store registers that will be used. */
			"push %%rax\n"
			"push %%rbx\n"
			"push %%rcx\n"
			/* Fetch input once */
			"movq %0, %%rax\n" // 64bit 데이터 이동, 0번째 매개변수에서 rax 레지스터로 이동. 
			"movq %1, %%rcx\n"
			// rax 레지스터에 저장된 것은 tf_cur
			"movq %%r15, 0(%%rax)\n" // RAX 레지스터에 적힌 값을 '메모리 주소'로 취급하여 해당 메모리 공간에 저장 (*(rax + 0) = r15)
			"movq %%r14, 8(%%rax)\n" // 8byte가 64bit이므로 다음 레지스터는 8(=0+8)byte 떨어진 곳에 저장
			"movq %%r13, 16(%%rax)\n"
			"movq %%r12, 24(%%rax)\n"
			"movq %%r11, 32(%%rax)\n"
			"movq %%r10, 40(%%rax)\n"
			"movq %%r9, 48(%%rax)\n"
			"movq %%r8, 56(%%rax)\n"
			"movq %%rsi, 64(%%rax)\n"
			"movq %%rdi, 72(%%rax)\n"
			"movq %%rbp, 80(%%rax)\n"
			"movq %%rdx, 88(%%rax)\n" // rdx까지 현재 스레드 상태 저장한 상태
			"pop %%rbx\n"              // Saved rcx (마지막으로 stack에 저장한 레지스터값이 이전 rcx값)
			"movq %%rbx, 96(%%rax)\n" // rcx값을 interrupt frame의 rcx에 저장
			"pop %%rbx\n"              // Saved rbx
			"movq %%rbx, 104(%%rax)\n"
			"pop %%rbx\n"              // Saved rax
			"movq %%rbx, 112(%%rax)\n"
			// 여기까지 현재 스레드 상태 중 gp_registers를 tf_cur에 저장한 것
			"addq $120, %%rax\n" // 120바이트를 rax에 더하기(rax로부터 120바이트 떨어진 곳에 gp_registers 이후의 필드값들 존재)
			"movw %%es, (%%rax)\n" // 16bit 데이터 이동
			"movw %%ds, 8(%%rax)\n" // es의 시작점부터 8바이트 떨어진 곳에 ds 존재하니까
			"addq $32, %%rax\n" // vec_no, error_code는 건너뛰기
			"call __next\n"         // read the current rip. (rip를 직접 만질 수 없어서 call 명령어로 바로 다음 줄에 있는 명령어의 주소(Return Address)를 스택(Stack) 맨 위에 Push)
			"__next:\n" // __next 라벨
			"pop %%rbx\n" // rbx에 현재 rip값 저장(__next의 주소)됨
			"addq $(out_iret -  __next), %%rbx\n" // 두 라벨 사이의 바이트 차이를 rbx에 저장
			// 현재 스레드는 shcedule()에서 다음 스레드로 전환하기 직전의 상태
			// 즉, 기존 하던 작업을 중단하고 (BLOCKED되던지 등등) 현재 상태를 저장할건데, rip를 thread_launch 이후로 잡아줘야 return을 하면서 원래 자기가 하던 일을 이어서 할 수 있다.
			"movq %%rbx, 0(%%rax)\n" // rip
			"movw %%cs, 8(%%rax)\n"  // cs
			"pushfq\n" // eflags 레지스터값 stack에 저장 (상태 플래그(ZF, CF, SF, IF 등)를 스택에 보관)
			"popq %%rbx\n" // rbx에 eflags값 저장
			"mov %%rbx, 16(%%rax)\n" // eflags
			"mov %%rsp, 24(%%rax)\n" // rsp
			"movw %%ss, 32(%%rax)\n" // stack segment 레지스터값 저장
			"mov %%rcx, %%rdi\n" // 다음 스레드의 interrupt frame 주소 rdi에 저장(64bit 체계에서 homing space)
			"call do_iret\n" // 인터럽트를 종료하고 유저 프로그램(또는 기존 작업)으로 돌아가는 실제 함수
			"out_iret:\n" // just label
			: : "g"(tf_cur), "g" (tf) : "memory" // 매개변수들, 무조건 memory를 참조하도록 강제함. 레지스터에 캐싱된 값을 믿지 말라는 것
			); // g는 register, memory, 상수 중 최적화하기 가장 좋은 방식으로 데이터를 전달하라는 뜻
}

/* Schedules a new process. At entry, interrupts must be off.
 * This function modify current thread's status to status and then
 * finds another thread to run and switches to it.
 * It's not safe to call printf() in the schedule(). */
// Context Switching 전에 destruction_req 리스트에 들어있는 페이지들 free시킨 후 현재 상태 변경 후 스케줄링
static void
do_schedule(int status) {
	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (thread_current()->status == THREAD_RUNNING); // 여기서 PANIC
	while (!list_empty (&destruction_req)) {
		struct thread *victim =
			list_entry (list_pop_front (&destruction_req), struct thread, elem);
		palloc_free_page(victim);
	}
	thread_current ()->status = status; // 현재 스레드 상태 변경
	schedule ();
}

// 다른 스레드로 전환하기
static void
schedule (void) {
	struct thread *curr = running_thread (); // returns the currently running thread.
	struct thread *next = next_thread_to_run ();

	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (curr->status != THREAD_RUNNING); // 현재 스레드가 RUNNING이 아니어야 다른 스레드로 전환해야 한
	ASSERT (is_thread (next)); // 다음 스레드가 유효한 스레드인지 확인
	/* Mark us as running. */
	next->status = THREAD_RUNNING; // 다음 스레드를 RUNNING 상태로 바꾸기

	/* Start new time slice. */
	thread_ticks = 0; 

#ifdef USERPROG
	/* Activate the new address space. */
	process_activate (next);
#endif

	if (curr != next) {
		/* If the thread we switched from is dying, destroy its struct
		   thread. This must happen late so that thread_exit() doesn't
		   pull out the rug under itself. thread_exit()가 스스로 스레드를 메모리에서 지우면 자신이 동작하고 있던 스레드를 지우는 셈이 된다.
		   We just queuing the page free reqeust here because the page is
		   currently used by the stack.
		   The real destruction logic will be called at the beginning of the
		   schedule(). */
		if (curr && curr->status == THREAD_DYING && curr != initial_thread) {
			ASSERT (curr != next);
			list_push_back (&destruction_req, &curr->elem); // destruciton_req 리스트에 추가시킨다. 추후 삭제하도록
		}

		/* Before switching the thread, we first save the information
		 * of current running. */
		thread_launch (next); // 다음 스레드 시작
	}
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) {
	static tid_t next_tid = 1;
	tid_t tid;

	lock_acquire (&tid_lock);
	tid = next_tid++;
	lock_release (&tid_lock);

	return tid;
}
