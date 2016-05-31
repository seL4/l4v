/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

void abort(void);
typedef unsigned wchar_t;
typedef unsigned int size_t;
typedef int ptrdiff_t;
typedef unsigned int uintptr_t;
typedef int intptr_t;
typedef signed char int8_t;
typedef short int16_t;
typedef int int32_t;
typedef long long int64_t;
typedef long long intmax_t;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
typedef unsigned long long uintmax_t;
typedef int8_t int_fast8_t;
typedef int64_t int_fast64_t;
typedef int8_t int_least8_t;
typedef int16_t int_least16_t;
typedef int32_t int_least32_t;
typedef int64_t int_least64_t;
typedef uint8_t uint_fast8_t;
typedef uint64_t uint_fast64_t;
typedef uint8_t uint_least8_t;
typedef uint16_t uint_least16_t;
typedef uint32_t uint_least32_t;
typedef uint64_t uint_least64_t;
typedef int32_t int_fast16_t;
typedef int32_t int_fast32_t;
typedef uint32_t uint_fast16_t;
typedef uint32_t uint_fast32_t;
typedef uint32_t seL4_Word;
typedef seL4_Word seL4_CPtr;
typedef seL4_CPtr seL4_ARM_Page;
typedef seL4_CPtr seL4_ARM_PageTable;
typedef seL4_CPtr seL4_ARM_PageDirectory;
typedef seL4_CPtr seL4_ARM_ASIDControl;
typedef seL4_CPtr seL4_ARM_ASIDPool;
typedef struct seL4_UserContext_ {
  /* frame registers */
  seL4_Word pc, sp, cpsr, r0, r1, r8, r9, r10, r11, r12;
  /* other integer registers */
  seL4_Word r2, r3, r4, r5, r6, r7, r14;
} seL4_UserContext;
typedef enum {
  seL4_ARM_PageCacheable = 0x01,
  seL4_ARM_ParityEnabled = 0x02,
  seL4_ARM_Default_VMAttributes = 0x03,
  seL4_ARM_ExecuteNever = 0x04,
  /* seL4_ARM_PageCacheable | seL4_ARM_ParityEnabled */
  _enum_pad_seL4_ARM_VMAttributes = (1U << ((sizeof(int) * 8) - 1)) - 1,
} seL4_ARM_VMAttributes;
struct seL4_MessageInfo {
  uint32_t words[1];
};
typedef struct seL4_MessageInfo seL4_MessageInfo_t;
static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_new(uint32_t label, uint32_t capsUnwrapped, uint32_t extraCaps,
                     uint32_t length) {
  seL4_MessageInfo_t seL4_MessageInfo;
  seL4_MessageInfo.words[0] = 0;
  /* fail if user has passed bits that we will override */
  (void)0;
  seL4_MessageInfo.words[0] |= (label & 0xfffff) << 12;
  /* fail if user has passed bits that we will override */
  (void)0;
  seL4_MessageInfo.words[0] |= (capsUnwrapped & 0x7) << 9;
  /* fail if user has passed bits that we will override */
  (void)0;
  seL4_MessageInfo.words[0] |= (extraCaps & 0x3) << 7;
  /* fail if user has passed bits that we will override */
  (void)0;
  seL4_MessageInfo.words[0] |= (length & 0x7f) << 0;
  return seL4_MessageInfo;
}
static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_length(seL4_MessageInfo_t seL4_MessageInfo) {
  return (seL4_MessageInfo.words[0] & 0x7f) >> 0;
}
struct seL4_CapData {
  uint32_t words[1];
};
typedef struct seL4_CapData seL4_CapData_t;
enum seL4_CapData_tag { seL4_CapData_Badge = 0, seL4_CapData_Guard = 1 };
typedef enum seL4_CapData_tag seL4_CapData_tag_t;
typedef enum {
  seL4_SysCall = -1,
  seL4_SysReplyWait = -2,
  seL4_SysSend = -3,
  seL4_SysNBSend = -4,
  seL4_SysWait = -5,
  seL4_SysReply = -6,
  seL4_SysYield = -7,
  seL4_SysDebugPutChar = -8,
  seL4_SysDebugHalt = -9,
  seL4_SysDebugCapIdentify = -10,
  seL4_SysDebugSnapshot = -11,
  _enum_pad_seL4_Syscall_ID = (1U << ((sizeof(int) * 8) - 1)) - 1
} seL4_Syscall_ID;
typedef enum api_object {
  seL4_UntypedObject,
  seL4_TCBObject,
  seL4_EndpointObject,
  seL4_AsyncEndpointObject,
  seL4_CapTableObject,
  seL4_NonArchObjectTypeCount,
} seL4_ObjectType;
typedef uint32_t api_object_t;
typedef enum {
  seL4_NoError = 0,
  seL4_InvalidArgument,
  seL4_InvalidCapability,
  seL4_IllegalOperation,
  seL4_RangeError,
  seL4_AlignmentError,
  seL4_FailedLookup,
  seL4_TruncatedMessage,
  seL4_DeleteFirst,
  seL4_RevokeFirst,
  seL4_NotEnoughMemory,
} seL4_Error;
enum priorityConstants {
  seL4_InvalidPrio = -1,
  seL4_MinPrio = 0,
  seL4_MaxPrio = 255
};
enum seL4_MsgLimits { seL4_MsgLengthBits = 7, seL4_MsgExtraCapBits = 2 };
enum {
  seL4_MsgMaxLength = 120,
};
typedef enum {
  seL4_NoFault = 0,
  seL4_CapFault,
  seL4_VMFault,
  seL4_UnknownSyscall,
  seL4_UserException,
  seL4_Interrupt,
  _enum_pad_seL4_FaultType = (1U << ((sizeof(int) * 8) - 1)) - 1,
} seL4_FaultType;
typedef enum {
  seL4_NoFailure = 0,
  seL4_InvalidRoot,
  seL4_MissingCapability,
  seL4_DepthMismatch,
  seL4_GuardMismatch,
  _enum_pad_seL4_LookupFailureType = (1U << ((sizeof(int) * 8) - 1)) - 1,
} seL4_LookupFailureType;
typedef enum {
  seL4_CanWrite = 0x01,
  seL4_CanRead = 0x02,
  seL4_CanGrant = 0x04,
  seL4_AllRights = 0x07,
  /* seL4_CanWrite | seL4_CanRead | seL4_CanGrant */
  _enum_pad_seL4_CapRights = (1U << ((sizeof(int) * 8) - 1)) - 1,
} seL4_CapRights;
typedef struct seL4_IPCBuffer_ {
  seL4_MessageInfo_t tag;
  seL4_Word msg[seL4_MsgMaxLength];
  seL4_Word userData;
  seL4_Word caps_or_badges[((1ul << (seL4_MsgExtraCapBits)) - 1)];
  seL4_CPtr receiveCNode;
  seL4_CPtr receiveIndex;
  seL4_Word receiveDepth;
} seL4_IPCBuffer;
typedef seL4_CPtr seL4_CNode;
typedef seL4_CPtr seL4_IRQHandler;
typedef seL4_CPtr seL4_IRQControl;
typedef seL4_CPtr seL4_TCB;
typedef seL4_CPtr seL4_Untyped;
typedef seL4_CPtr seL4_DomainSet;
typedef enum _object {
  seL4_ARM_SmallPageObject = seL4_NonArchObjectTypeCount,
  seL4_ARM_LargePageObject,
  seL4_ARM_SectionObject,
  seL4_ARM_SuperSectionObject,
  seL4_ARM_PageTableObject,
  seL4_ARM_PageDirectoryObject,
  seL4_ObjectTypeCount
} seL4_ArchObjectType;
typedef uint32_t object_t;
enum invocation_label {
  InvalidInvocation,
  UntypedRetype,
  TCBReadRegisters,
  TCBWriteRegisters,
  TCBCopyRegisters,
  TCBConfigure,
  TCBSetPriority,
  TCBSetIPCBuffer,
  TCBSetSpace,
  TCBSuspend,
  TCBResume,
  CNodeRevoke,
  CNodeDelete,
  CNodeRecycle,
  CNodeCopy,
  CNodeMint,
  CNodeMove,
  CNodeMutate,
  CNodeRotate,
  CNodeSaveCaller,
  IRQIssueIRQHandler,
  IRQInterruptControl,
  IRQAckIRQ,
  IRQSetIRQHandler,
  IRQClearIRQHandler,
  IRQSetMode,
  DomainSetSet,
  nInvocationLabels
};
enum arch_invocation_label {
  ARMPDClean_Data = nInvocationLabels + 0,
  ARMPDInvalidate_Data = nInvocationLabels + 1,
  ARMPDCleanInvalidate_Data = nInvocationLabels + 2,
  ARMPDUnify_Instruction = nInvocationLabels + 3,
  ARMPageTableMap = nInvocationLabels + 4,
  ARMPageTableUnmap = nInvocationLabels + 5,
  ARMPageMap = nInvocationLabels + 6,
  ARMPageRemap = nInvocationLabels + 7,
  ARMPageUnmap = nInvocationLabels + 8,
  ARMPageClean_Data = nInvocationLabels + 9,
  ARMPageInvalidate_Data = nInvocationLabels + 10,
  ARMPageCleanInvalidate_Data = nInvocationLabels + 11,
  ARMPageUnify_Instruction = nInvocationLabels + 12,
  ARMPageGetAddress = nInvocationLabels + 13,
  ARMASIDControlMakePool = nInvocationLabels + 14,
  ARMASIDPoolAssign = nInvocationLabels + 15,
  nArchInvocationLabels
};
enum {
  seL4_GlobalsFrame = 0xffffc000,
};
static inline seL4_IPCBuffer *seL4_GetIPCBuffer(void) {
  return *(seL4_IPCBuffer **)seL4_GlobalsFrame;
}
static inline seL4_Word seL4_GetMR(int i) {
  return seL4_GetIPCBuffer()->msg[i];
}
static inline void seL4_SetMR(int i, seL4_Word mr) {
  seL4_GetIPCBuffer()->msg[i] = mr;
}
static inline void seL4_Send(seL4_CPtr dest, seL4_MessageInfo_t msgInfo) {
  register seL4_Word destptr asm("r0") = (seL4_Word)dest;
  register seL4_Word info asm("r1") = msgInfo.words[0];
  /* Load beginning of the message into registers. */
  register seL4_Word msg0 asm("r2") = seL4_GetMR(0);
  register seL4_Word msg1 asm("r3") = seL4_GetMR(1);
  register seL4_Word msg2 asm("r4") = seL4_GetMR(2);
  register seL4_Word msg3 asm("r5") = seL4_GetMR(3);
  /* Perform the system call. */
  register seL4_Word scno asm("r7") = seL4_SysSend;
asm volatile("swi %[swi_num]"
               : "+r"(destptr), "+r"(msg0), "+r"(msg1), "+r"(msg2), "+r"(msg3),
                 "+r"(info)
               : [swi_num] "i"((seL4_SysSend)&0x00ffffff), "r"(scno)
               : "memory");
}
static inline seL4_MessageInfo_t seL4_Wait(seL4_CPtr src, seL4_Word *sender) {
  register seL4_Word src_and_badge asm("r0") = (seL4_Word)src;
  register seL4_MessageInfo_t info asm("r1");
  /* Incoming message registers. */
  register seL4_Word msg0 asm("r2");
  register seL4_Word msg1 asm("r3");
  register seL4_Word msg2 asm("r4");
  register seL4_Word msg3 asm("r5");
  /* Perform the system call. */
  register seL4_Word scno asm("r7") = seL4_SysWait;
asm volatile("swi %[swi_num]"
               : "=r"(msg0), "=r"(msg1), "=r"(msg2), "=r"(msg3), "=r"(info),
                 "+r"(src_and_badge)
               : [swi_num] "i"((seL4_SysWait)&0x00ffffff), "r"(scno)
               : "memory");
  /* Write the message back out to memory. */
  seL4_SetMR(0, msg0);
  seL4_SetMR(1, msg1);
  seL4_SetMR(2, msg2);
  seL4_SetMR(3, msg3);
  /* Return back sender and message information. */
  if (sender) {
    *sender = src_and_badge;
  }
  return (seL4_MessageInfo_t){.words = {info.words[0]}};
}
typedef unsigned long
    __type_uint8_t_size_incorrect[(sizeof(uint8_t) == 1) ? 1 : -1];
typedef unsigned long
    __type_uint16_t_size_incorrect[(sizeof(uint16_t) == 2) ? 1 : -1];
typedef unsigned long
    __type_uint32_t_size_incorrect[(sizeof(uint32_t) == 4) ? 1 : -1];
typedef unsigned long
    __type_uint64_t_size_incorrect[(sizeof(uint64_t) == 8) ? 1 : -1];
typedef unsigned long __type_int_size_incorrect[(sizeof(int) == 4) ? 1 : -1];
typedef unsigned long __type_bool_size_incorrect[(sizeof(_Bool) == 1) ? 1 : -1];
typedef unsigned long
    __type_seL4_Word_size_incorrect[(sizeof(seL4_Word) == 4) ? 1 : -1];
typedef unsigned long
    __type_seL4_CapRights_size_incorrect[(sizeof(seL4_CapRights) == 4) ? 1
                                                                       : -1];
typedef unsigned long
    __type_seL4_CapData_t_size_incorrect[(sizeof(seL4_CapData_t) == 4) ? 1
                                                                       : -1];
typedef unsigned long
    __type_seL4_CPtr_size_incorrect[(sizeof(seL4_CPtr) == 4) ? 1 : -1];
typedef unsigned long
    __type_seL4_CNode_size_incorrect[(sizeof(seL4_CNode) == 4) ? 1 : -1];
typedef unsigned long
    __type_seL4_IRQHandler_size_incorrect[(sizeof(seL4_IRQHandler) == 4) ? 1
                                                                         : -1];
typedef unsigned long
    __type_seL4_IRQControl_size_incorrect[(sizeof(seL4_IRQControl) == 4) ? 1
                                                                         : -1];
typedef unsigned long
    __type_seL4_TCB_size_incorrect[(sizeof(seL4_TCB) == 4) ? 1 : -1];
typedef unsigned long
    __type_seL4_Untyped_size_incorrect[(sizeof(seL4_Untyped) == 4) ? 1 : -1];
typedef unsigned long
    __type_seL4_DomainSet_size_incorrect[(sizeof(seL4_DomainSet) == 4) ? 1
                                                                       : -1];
typedef unsigned long __type_seL4_ARM_VMAttributes_size_incorrect
    [(sizeof(seL4_ARM_VMAttributes) == 4) ? 1 : -1];
typedef unsigned long
    __type_seL4_ARM_Page_size_incorrect[(sizeof(seL4_ARM_Page) == 4) ? 1 : -1];
typedef unsigned long __type_seL4_ARM_PageTable_size_incorrect
    [(sizeof(seL4_ARM_PageTable) == 4) ? 1 : -1];
typedef unsigned long __type_seL4_ARM_PageDirectory_size_incorrect
    [(sizeof(seL4_ARM_PageDirectory) == 4) ? 1 : -1];
typedef unsigned long __type_seL4_ARM_ASIDControl_size_incorrect
    [(sizeof(seL4_ARM_ASIDControl) == 4) ? 1 : -1];
typedef unsigned long __type_seL4_ARM_ASIDPool_size_incorrect
    [(sizeof(seL4_ARM_ASIDPool) == 4) ? 1 : -1];
typedef unsigned long __type_seL4_UserContext_size_incorrect
    [(sizeof(seL4_UserContext) == 68) ? 1 : -1];
struct seL4_ARM_Page_GetAddress {
  int error;
  seL4_Word paddr;
};
typedef struct seL4_ARM_Page_GetAddress seL4_ARM_Page_GetAddress_t;
enum {
  seL4_CapNull = 0,
  /* null cap */
  seL4_CapInitThreadTCB = 1,
  /* initial thread's TCB cap */
  seL4_CapInitThreadCNode = 2,
  /* initial thread's root CNode cap */
  seL4_CapInitThreadVSpace = 3,
  /* initial thread's VSpace cap */
  seL4_CapIRQControl = 4,
  /* global IRQ controller cap */
  seL4_CapASIDControl = 5,
  /* global ASID controller cap */
  seL4_CapInitThreadASIDPool = 6,
  /* initial thread's ASID pool cap */
  seL4_CapIOPort = 7,
  /* global IO port cap (null cap if not supported) */
  seL4_CapIOSpace = 8,
  /* global IO space cap (null cap if no IOMMU support) */
  seL4_CapBootInfoFrame = 9,
  /* bootinfo frame cap */
  seL4_CapInitThreadIPCBuffer = 10,
  /* initial thread's IPC buffer frame cap */
  seL4_CapDomain = 11
  /* global domain controller cap */
};
typedef struct {
  seL4_Word start;
  /* first CNode slot position OF region */
  seL4_Word end;
  /* first CNode slot position AFTER region */
} seL4_SlotRegion;
typedef struct {
  seL4_Word basePaddr;
  /* base physical address of device region */
  seL4_Word frameSizeBits;
  /* size (2^n bytes) of a device-region frame */
  seL4_SlotRegion frames;
  /* device-region frame caps */
} seL4_DeviceRegion;
typedef struct {
  seL4_Word nodeID;
  /* ID [0..numNodes-1] of the seL4 node (0 if uniprocessor) */
  seL4_Word numNodes;
  /* number of seL4 nodes (1 if uniprocessor) */
  seL4_Word numIOPTLevels;
  /* number of IOMMU PT levels (0 if no IOMMU support) */
  seL4_IPCBuffer *ipcBuffer;
  /* pointer to initial thread's IPC buffer */
  seL4_SlotRegion empty;
  /* empty slots (null caps) */
  seL4_SlotRegion sharedFrames;
  /* shared-frame caps (shared between seL4 nodes) */
  seL4_SlotRegion userImageFrames;
  /* userland-image frame caps */
  seL4_SlotRegion userImagePDs;
  /* userland-image PD caps */
  seL4_SlotRegion userImagePTs;
  /* userland-image PT caps */
  seL4_SlotRegion untyped;
  /* untyped-object caps (untyped caps) */
  seL4_Word untypedPaddrList[167];
  /* physical address of each untyped cap */
  uint8_t untypedSizeBitsList[167];
  /* size (2^n) bytes of each untyped cap */
  uint8_t initThreadCNodeSizeBits;
  /* initial thread's root CNode size (2^n slots) */
  seL4_Word numDeviceRegions;
  /* number of device regions */
  seL4_DeviceRegion deviceRegions[199];
  /* device regions */
  uint32_t initThreadDomain;
  /* Initial thread's domain ID */
} seL4_BootInfo;
_Noreturn void abort(void);
typedef struct { int quot, rem; } div_t;
typedef struct { long quot, rem; } ldiv_t;
typedef struct { long long quot, rem; } lldiv_t;
typedef struct __locale_struct *locale_t;
void *memcpy(void *restrict, const void *restrict, size_t);
void *memset(void *, int, size_t);
typedef long time_t;
typedef long suseconds_t;
typedef int ssize_t;
typedef unsigned mode_t;
typedef unsigned int nlink_t;
typedef long long off_t;
typedef unsigned long long ino_t;
typedef unsigned long long dev_t;
typedef long blksize_t;
typedef long long blkcnt_t;
typedef unsigned long long fsblkcnt_t;
typedef unsigned long long fsfilcnt_t;
typedef void *timer_t;
typedef int clockid_t;
typedef long clock_t;
typedef int pid_t;
typedef unsigned id_t;
typedef unsigned uid_t;
typedef unsigned gid_t;
typedef int key_t;
typedef unsigned useconds_t;
typedef struct __pthread *pthread_t;
typedef int pthread_once_t;
typedef unsigned pthread_key_t;
typedef int pthread_spinlock_t;
typedef struct { unsigned __attr; } pthread_mutexattr_t;
typedef struct { unsigned __attr; } pthread_condattr_t;
typedef struct { unsigned __attr; } pthread_barrierattr_t;
typedef struct { unsigned __attr[2]; } pthread_rwlockattr_t;
void __builtin_unreachable(void);
typedef struct { struct list_node *head; } list_t;
struct list_node {
  void *data;
  struct list_node *next;
};
typedef char Buf[((1ul << (12)))];
typedef struct dataport_ptr_ {
  uint32_t id;
  off_t offset;
} dataport_ptr_t;
typedef enum {
  /* No error occurred. Used to indicate normal operation. */
  CE_NO_ERROR = 0,
  /* During marshalling, the next operation if we were to continue would
       * exceed the size of the target buffer. Note that continuing in the event
       * of such an error *will* cause an out-of-bounds memory write.
       */
  CE_BUFFER_LENGTH_EXCEEDED,
  /* In an RPC communication, the method index indicated by the caller was
       * out of range for the given interface. That is, the method index was
       * larger than the number of methods in this interface, or it was
   * negative.
       */
  CE_INVALID_METHOD_INDEX,
  /* The payload of an RPC (marshalled parameters) was somehow invalid. This
       * includes cases where an IPC recipient received a message that was
   * either
       * too long or too short for what it was expecting.
       */
  CE_MALFORMED_RPC_PAYLOAD,
  /* A system call that is never expected to fail in normal operation, did
       * so. Recovery actions are most likely dependent on what and where the
       * actual failure was.
       */
  CE_SYSCALL_FAILED,
  /* Some internal memory/bookkeeping allocation the glue code needed to
       * perform did not complete successfully. It will be difficult to diagnose
       * the cause of one of these without looking at the location at which the
       * error was triggered.
       */
  CE_ALLOCATION_FAILURE,
} camkes_error_type_t;
typedef enum {
  /* Used as a sentinel for a context where an action is invalid. Don't ever
       * return this from an error handler.
       */
  CEA_INVALID = -1,
  /* Terminate the currently running piece of glue code by returning. If the
       * offending code was called from a glue code event loop, this generally
       * means return to the event loop. If the offending code was called from
       * user code, this means return to user code where the calling function is
       * expected to be aware (by some out-of-band communication) that an error
       * has occurred.
       */
  CEA_DISCARD,
  /* Ignore the error and continue. This is generally dangerous and not what
       * you want.
       */
  CEA_IGNORE,
  /* Exit with failure in the current thread. Note that what 'exit' means
       * here depends on a number of things including whether the thread has a
       * cap to itself.
       */
  CEA_ABORT,
  /* Exit with failure and also try to halt the entire system if possible.
       * This action implies CEA_ABORT and only differs on a debug kernel where
       * it is possible to stop the system. If you have no error handlers
       * installed, this is the default action.
       */
  CEA_HALT,
} camkes_error_action_t;
typedef uint32_t sel4bench_counter_t;
typedef struct camkes_tls_t {
  seL4_CPtr tcb_cap;
  unsigned int thread_index;
} camkes_tls_t;
static inline camkes_tls_t *__attribute__((__unused__)) camkes_get_tls(void) {
  /* We store TLS data in the same page as the thread's IPC buffer, but at
       * the start of the page.
       */
  uintptr_t ipc_buffer = (uintptr_t)seL4_GetIPCBuffer();
  /* Normally we would just use MASK here, but the verification C parser
       * doesn't like the GCC extension used in that macro. The following
       * assertion could be checked at compile-time, but then it appears in
   * input
       * to the verification process that causes other problems.
       */
  (void)0;
  uintptr_t tls = ipc_buffer & ~(((1ul << (12)) - 1ul));
  /* We should have enough room for the TLS data preceding the IPC buffer. */
  (void)0;
  /* We'd better be returning a valid pointer. */
  (void)0;
  return (camkes_tls_t *)tls;
}
int RPCFrom__run(void) {
  /* Nothing to be done. */
  return 0;
}
static int echo_int_i_from_1;
static int echo_int_i_from_2;
static int *get_echo_int_i_from(void) __attribute__((__unused__));
static int *get_echo_int_i_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_i_from_1;
  case 2:
    return &echo_int_i_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_marshal_inputs_i(unsigned int _camkes_offset_13,
                                              int i) {
  void *_camkes_buffer_base_14 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_15 = (get_echo_int_i_from());
  *_camkes_ptr_15 = i;
  do {
    (void)0;
    if (!(!(_camkes_offset_13 + sizeof(*_camkes_ptr_15) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_14 + _camkes_offset_13, _camkes_ptr_15,
         sizeof(*_camkes_ptr_15));
  _camkes_offset_13 += sizeof(*_camkes_ptr_15);
  return _camkes_offset_13;
}
static const uint8_t _camkes_method_index_19 = 0;
static unsigned int echo_int_marshal_inputs(int i) {
  unsigned int _camkes_length_20 = 0;
  void *_camkes_buffer_base_21 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_20 + sizeof(_camkes_method_index_19) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_21, &_camkes_method_index_19,
         sizeof(_camkes_method_index_19));
  _camkes_length_20 += sizeof(_camkes_method_index_19);
  /* Marshal the parameters. */
  _camkes_length_20 = echo_int_marshal_inputs_i(_camkes_length_20, i);
  if (_camkes_length_20 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_20;
}
static unsigned int
echo_int_unmarshal_outputs__camkes_ret_fn_22(unsigned int _camkes_size_24,
                                             unsigned int _camkes_offset_23,
                                             int *_camkes_return_25) {
  void *_camkes_buffer_base_26 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_23 + sizeof(*_camkes_return_25) >
            _camkes_size_24))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_25, _camkes_buffer_base_26 + _camkes_offset_23,
         sizeof(*_camkes_return_25));
  _camkes_offset_23 += sizeof(*_camkes_return_25);
  return _camkes_offset_23;
}
static int echo_int_unmarshal_outputs(unsigned int _camkes_size_27,
                                      int *_camkes_return_28) {
  unsigned int _camkes_length_29 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_30 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_29 = echo_int_unmarshal_outputs__camkes_ret_fn_22(
      _camkes_size_27, _camkes_length_29, _camkes_return_28);
  if (_camkes_length_29 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  do {
    (void)0;
    if (!(!(((_camkes_length_29) +
             ((_camkes_length_29) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_29) % (sizeof(seL4_Word)))))) !=
            _camkes_size_27))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_31_1;
static int _camkes_ret_tls_var_from_31_2;
static int *get__camkes_ret_tls_var_from_31(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_31(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_31_1;
  case 2:
    return &_camkes_ret_tls_var_from_31_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_int(int i) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_33 __attribute__((__unused__));
  int *_camkes_return_ptr_34 = (get__camkes_ret_tls_var_from_31());
  unsigned int _camkes_length_35 = echo_int_marshal_inputs(i);
  if (__builtin_expect(!!(_camkes_length_35 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_34, 0, sizeof(*_camkes_return_ptr_34));
    return *_camkes_return_ptr_34;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_36 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_35) +
                ((_camkes_length_35) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_35) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_36);
  _camkes_info_36 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_37 =
      seL4_MessageInfo_get_length(_camkes_info_36) * sizeof(seL4_Word);
  int _camkes_error_38 =
      echo_int_unmarshal_outputs(_camkes_size_37, _camkes_return_ptr_34);
  if (__builtin_expect(!!(_camkes_error_38 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_34, 0, sizeof(*_camkes_return_ptr_34));
    return *_camkes_return_ptr_34;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_34;
}
static int echo_int_1_i_from_1;
static int echo_int_1_i_from_2;
static int *get_echo_int_1_i_from(void) __attribute__((__unused__));
static int *get_echo_int_1_i_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_i_from_1;
  case 2:
    return &echo_int_1_i_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_1_j_from_1;
static unsigned int echo_int_1_j_from_2;
static unsigned int *get_echo_int_1_j_from(void) __attribute__((__unused__));
static unsigned int *get_echo_int_1_j_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_j_from_1;
  case 2:
    return &echo_int_1_j_from_2;
  default:
    (void)0;
    abort();
  }
}
static int32_t echo_int_1_k_from_1;
static int32_t echo_int_1_k_from_2;
static int32_t *get_echo_int_1_k_from(void) __attribute__((__unused__));
static int32_t *get_echo_int_1_k_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_k_from_1;
  case 2:
    return &echo_int_1_k_from_2;
  default:
    (void)0;
    abort();
  }
}
static uint32_t echo_int_1_l_from_1;
static uint32_t echo_int_1_l_from_2;
static uint32_t *get_echo_int_1_l_from(void) __attribute__((__unused__));
static uint32_t *get_echo_int_1_l_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_l_from_1;
  case 2:
    return &echo_int_1_l_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_1_marshal_inputs_i(unsigned int _camkes_offset_39,
                                                int i) {
  void *_camkes_buffer_base_40 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_41 = (get_echo_int_1_i_from());
  *_camkes_ptr_41 = i;
  do {
    (void)0;
    if (!(!(_camkes_offset_39 + sizeof(*_camkes_ptr_41) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_40 + _camkes_offset_39, _camkes_ptr_41,
         sizeof(*_camkes_ptr_41));
  _camkes_offset_39 += sizeof(*_camkes_ptr_41);
  return _camkes_offset_39;
}
static unsigned int echo_int_1_marshal_inputs_j(unsigned int _camkes_offset_45,
                                                unsigned int j) {
  void *_camkes_buffer_base_46 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  unsigned int *_camkes_ptr_47 = (get_echo_int_1_j_from());
  *_camkes_ptr_47 = j;
  do {
    (void)0;
    if (!(!(_camkes_offset_45 + sizeof(*_camkes_ptr_47) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_46 + _camkes_offset_45, _camkes_ptr_47,
         sizeof(*_camkes_ptr_47));
  _camkes_offset_45 += sizeof(*_camkes_ptr_47);
  return _camkes_offset_45;
}
static unsigned int echo_int_1_marshal_inputs_k(unsigned int _camkes_offset_51,
                                                int32_t k) {
  void *_camkes_buffer_base_52 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int32_t *_camkes_ptr_53 = (get_echo_int_1_k_from());
  *_camkes_ptr_53 = k;
  do {
    (void)0;
    if (!(!(_camkes_offset_51 + sizeof(*_camkes_ptr_53) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_52 + _camkes_offset_51, _camkes_ptr_53,
         sizeof(*_camkes_ptr_53));
  _camkes_offset_51 += sizeof(*_camkes_ptr_53);
  return _camkes_offset_51;
}
static unsigned int echo_int_1_marshal_inputs_l(unsigned int _camkes_offset_57,
                                                uint32_t l) {
  void *_camkes_buffer_base_58 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  uint32_t *_camkes_ptr_59 = (get_echo_int_1_l_from());
  *_camkes_ptr_59 = l;
  do {
    (void)0;
    if (!(!(_camkes_offset_57 + sizeof(*_camkes_ptr_59) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_58 + _camkes_offset_57, _camkes_ptr_59,
         sizeof(*_camkes_ptr_59));
  _camkes_offset_57 += sizeof(*_camkes_ptr_59);
  return _camkes_offset_57;
}
static const uint8_t _camkes_method_index_63 = 1;
static unsigned int echo_int_1_marshal_inputs(int i, unsigned int j, int32_t k,
                                              uint32_t l) {
  unsigned int _camkes_length_64 = 0;
  void *_camkes_buffer_base_65 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_64 + sizeof(_camkes_method_index_63) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_65, &_camkes_method_index_63,
         sizeof(_camkes_method_index_63));
  _camkes_length_64 += sizeof(_camkes_method_index_63);
  /* Marshal the parameters. */
  _camkes_length_64 = echo_int_1_marshal_inputs_i(_camkes_length_64, i);
  if (_camkes_length_64 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_64 = echo_int_1_marshal_inputs_j(_camkes_length_64, j);
  if (_camkes_length_64 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_64 = echo_int_1_marshal_inputs_k(_camkes_length_64, k);
  if (_camkes_length_64 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_64 = echo_int_1_marshal_inputs_l(_camkes_length_64, l);
  if (_camkes_length_64 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_64;
}
static unsigned int
echo_int_1_unmarshal_outputs__camkes_ret_fn_66(unsigned int _camkes_size_68,
                                               unsigned int _camkes_offset_67,
                                               int *_camkes_return_69) {
  void *_camkes_buffer_base_70 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_67 + sizeof(*_camkes_return_69) >
            _camkes_size_68))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_69, _camkes_buffer_base_70 + _camkes_offset_67,
         sizeof(*_camkes_return_69));
  _camkes_offset_67 += sizeof(*_camkes_return_69);
  return _camkes_offset_67;
}
static int echo_int_1_unmarshal_outputs(unsigned int _camkes_size_71,
                                        int *_camkes_return_72) {
  unsigned int _camkes_length_73 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_74 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_73 = echo_int_1_unmarshal_outputs__camkes_ret_fn_66(
      _camkes_size_71, _camkes_length_73, _camkes_return_72);
  if (_camkes_length_73 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  do {
    (void)0;
    if (!(!(((_camkes_length_73) +
             ((_camkes_length_73) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_73) % (sizeof(seL4_Word)))))) !=
            _camkes_size_71))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_75_1;
static int _camkes_ret_tls_var_from_75_2;
static int *get__camkes_ret_tls_var_from_75(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_75(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_75_1;
  case 2:
    return &_camkes_ret_tls_var_from_75_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_int_1(int i, unsigned int j, int32_t k, uint32_t l) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_77 __attribute__((__unused__));
  int *_camkes_return_ptr_78 = (get__camkes_ret_tls_var_from_75());
  unsigned int _camkes_length_79 = echo_int_1_marshal_inputs(i, j, k, l);
  if (__builtin_expect(!!(_camkes_length_79 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_78, 0, sizeof(*_camkes_return_ptr_78));
    return *_camkes_return_ptr_78;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_80 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_79) +
                ((_camkes_length_79) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_79) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_80);
  _camkes_info_80 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_81 =
      seL4_MessageInfo_get_length(_camkes_info_80) * sizeof(seL4_Word);
  int _camkes_error_82 =
      echo_int_1_unmarshal_outputs(_camkes_size_81, _camkes_return_ptr_78);
  if (__builtin_expect(!!(_camkes_error_82 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_78, 0, sizeof(*_camkes_return_ptr_78));
    return *_camkes_return_ptr_78;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_78;
}
static int echo_parameter_pin_from_1;
static int echo_parameter_pin_from_2;
static int *get_echo_parameter_pin_from(void) __attribute__((__unused__));
static int *get_echo_parameter_pin_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_parameter_pin_from_1;
  case 2:
    return &echo_parameter_pin_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int
echo_parameter_marshal_inputs_pin(unsigned int _camkes_offset_83, int pin) {
  void *_camkes_buffer_base_84 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_85 = (get_echo_parameter_pin_from());
  *_camkes_ptr_85 = pin;
  do {
    (void)0;
    if (!(!(_camkes_offset_83 + sizeof(*_camkes_ptr_85) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_84 + _camkes_offset_83, _camkes_ptr_85,
         sizeof(*_camkes_ptr_85));
  _camkes_offset_83 += sizeof(*_camkes_ptr_85);
  return _camkes_offset_83;
}
static const uint8_t _camkes_method_index_89 = 2;
static unsigned int echo_parameter_marshal_inputs(int pin) {
  unsigned int _camkes_length_90 = 0;
  void *_camkes_buffer_base_91 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_90 + sizeof(_camkes_method_index_89) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_91, &_camkes_method_index_89,
         sizeof(_camkes_method_index_89));
  _camkes_length_90 += sizeof(_camkes_method_index_89);
  /* Marshal the parameters. */
  _camkes_length_90 = echo_parameter_marshal_inputs_pin(_camkes_length_90, pin);
  if (_camkes_length_90 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_90;
}
static unsigned int echo_parameter_unmarshal_outputs__camkes_ret_fn_92(
    unsigned int _camkes_size_94, unsigned int _camkes_offset_93,
    int *_camkes_return_95) {
  void *_camkes_buffer_base_96 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_93 + sizeof(*_camkes_return_95) >
            _camkes_size_94))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_95, _camkes_buffer_base_96 + _camkes_offset_93,
         sizeof(*_camkes_return_95));
  _camkes_offset_93 += sizeof(*_camkes_return_95);
  return _camkes_offset_93;
}
static unsigned int echo_parameter_unmarshal_outputs_pout(
    unsigned int _camkes_size_97, unsigned int _camkes_offset_98, int *pout) {
  void *_camkes_buffer_base_99 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_98 + sizeof(*pout) > _camkes_size_97))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(pout, _camkes_buffer_base_99 + _camkes_offset_98, sizeof(*pout));
  _camkes_offset_98 += sizeof(*pout);
  return _camkes_offset_98;
}
static int echo_parameter_unmarshal_outputs(unsigned int _camkes_size_100,
                                            int *_camkes_return_101,
                                            int *pout) {
  unsigned int _camkes_length_102 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_103 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_102 = echo_parameter_unmarshal_outputs__camkes_ret_fn_92(
      _camkes_size_100, _camkes_length_102, _camkes_return_101);
  if (_camkes_length_102 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  _camkes_length_102 = echo_parameter_unmarshal_outputs_pout(
      _camkes_size_100, _camkes_length_102, pout);
  if (_camkes_length_102 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_102) +
             ((_camkes_length_102) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_102) % (sizeof(seL4_Word)))))) !=
            _camkes_size_100))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_104_1;
static int _camkes_ret_tls_var_from_104_2;
static int *get__camkes_ret_tls_var_from_104(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_104(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_104_1;
  case 2:
    return &_camkes_ret_tls_var_from_104_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_parameter(int pin, int *pout) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_106 __attribute__((__unused__));
  int *_camkes_return_ptr_107 = (get__camkes_ret_tls_var_from_104());
  unsigned int _camkes_length_108 = echo_parameter_marshal_inputs(pin);
  if (__builtin_expect(!!(_camkes_length_108 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_107, 0, sizeof(*_camkes_return_ptr_107));
    return *_camkes_return_ptr_107;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_109 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_108) +
                ((_camkes_length_108) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_108) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_109);
  _camkes_info_109 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_110 =
      seL4_MessageInfo_get_length(_camkes_info_109) * sizeof(seL4_Word);
  int _camkes_error_111 = echo_parameter_unmarshal_outputs(
      _camkes_size_110, _camkes_return_ptr_107, pout);
  if (__builtin_expect(!!(_camkes_error_111 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_107, 0, sizeof(*_camkes_return_ptr_107));
    return *_camkes_return_ptr_107;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_107;
}
static char echo_char_i_from_1;
static char echo_char_i_from_2;
static char *get_echo_char_i_from(void) __attribute__((__unused__));
static char *get_echo_char_i_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_char_i_from_1;
  case 2:
    return &echo_char_i_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_char_marshal_inputs_i(unsigned int _camkes_offset_112,
                                               char i) {
  void *_camkes_buffer_base_113 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  char *_camkes_ptr_114 = (get_echo_char_i_from());
  *_camkes_ptr_114 = i;
  do {
    (void)0;
    if (!(!(_camkes_offset_112 + sizeof(*_camkes_ptr_114) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_113 + _camkes_offset_112, _camkes_ptr_114,
         sizeof(*_camkes_ptr_114));
  _camkes_offset_112 += sizeof(*_camkes_ptr_114);
  return _camkes_offset_112;
}
static const uint8_t _camkes_method_index_118 = 3;
static unsigned int echo_char_marshal_inputs(char i) {
  unsigned int _camkes_length_119 = 0;
  void *_camkes_buffer_base_120 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_119 + sizeof(_camkes_method_index_118) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_120, &_camkes_method_index_118,
         sizeof(_camkes_method_index_118));
  _camkes_length_119 += sizeof(_camkes_method_index_118);
  /* Marshal the parameters. */
  _camkes_length_119 = echo_char_marshal_inputs_i(_camkes_length_119, i);
  if (_camkes_length_119 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_119;
}
static unsigned int
echo_char_unmarshal_outputs__camkes_ret_fn_121(unsigned int _camkes_size_123,
                                               unsigned int _camkes_offset_122,
                                               int *_camkes_return_124) {
  void *_camkes_buffer_base_125 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_122 + sizeof(*_camkes_return_124) >
            _camkes_size_123))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_124, _camkes_buffer_base_125 + _camkes_offset_122,
         sizeof(*_camkes_return_124));
  _camkes_offset_122 += sizeof(*_camkes_return_124);
  return _camkes_offset_122;
}
static int echo_char_unmarshal_outputs(unsigned int _camkes_size_126,
                                       int *_camkes_return_127) {
  unsigned int _camkes_length_128 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_129 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_128 = echo_char_unmarshal_outputs__camkes_ret_fn_121(
      _camkes_size_126, _camkes_length_128, _camkes_return_127);
  if (_camkes_length_128 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  do {
    (void)0;
    if (!(!(((_camkes_length_128) +
             ((_camkes_length_128) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_128) % (sizeof(seL4_Word)))))) !=
            _camkes_size_126))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_130_1;
static int _camkes_ret_tls_var_from_130_2;
static int *get__camkes_ret_tls_var_from_130(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_130(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_130_1;
  case 2:
    return &_camkes_ret_tls_var_from_130_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_char(char i) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_132 __attribute__((__unused__));
  int *_camkes_return_ptr_133 = (get__camkes_ret_tls_var_from_130());
  unsigned int _camkes_length_134 = echo_char_marshal_inputs(i);
  if (__builtin_expect(!!(_camkes_length_134 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_133, 0, sizeof(*_camkes_return_ptr_133));
    return *_camkes_return_ptr_133;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_135 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_134) +
                ((_camkes_length_134) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_134) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_135);
  _camkes_info_135 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_136 =
      seL4_MessageInfo_get_length(_camkes_info_135) * sizeof(seL4_Word);
  int _camkes_error_137 =
      echo_char_unmarshal_outputs(_camkes_size_136, _camkes_return_ptr_133);
  if (__builtin_expect(!!(_camkes_error_137 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_133, 0, sizeof(*_camkes_return_ptr_133));
    return *_camkes_return_ptr_133;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_133;
}
static unsigned int
increment_char_marshal_inputs_x(unsigned int _camkes_offset_138, char *x) {
  void *_camkes_buffer_base_139 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  char *_camkes_ptr_140 = x;
  do {
    (void)0;
    if (!(!(_camkes_offset_138 + sizeof(*_camkes_ptr_140) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_139 + _camkes_offset_138, _camkes_ptr_140,
         sizeof(*_camkes_ptr_140));
  _camkes_offset_138 += sizeof(*_camkes_ptr_140);
  return _camkes_offset_138;
}
static const uint8_t _camkes_method_index_144 = 4;
static unsigned int increment_char_marshal_inputs(char *x) {
  unsigned int _camkes_length_145 = 0;
  void *_camkes_buffer_base_146 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_145 + sizeof(_camkes_method_index_144) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_146, &_camkes_method_index_144,
         sizeof(_camkes_method_index_144));
  _camkes_length_145 += sizeof(_camkes_method_index_144);
  /* Marshal the parameters. */
  _camkes_length_145 = increment_char_marshal_inputs_x(_camkes_length_145, x);
  if (_camkes_length_145 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_145;
}
static unsigned int
increment_char_unmarshal_outputs_x(unsigned int _camkes_size_148,
                                   unsigned int _camkes_offset_149, char *x) {
  void *_camkes_buffer_base_150 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_149 + sizeof(*x) > _camkes_size_148))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(x, _camkes_buffer_base_150 + _camkes_offset_149, sizeof(*x));
  _camkes_offset_149 += sizeof(*x);
  return _camkes_offset_149;
}
static int increment_char_unmarshal_outputs(unsigned int _camkes_size_151,
                                            char *x) {
  unsigned int _camkes_length_153 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_154 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the parameters. */
  _camkes_length_153 = increment_char_unmarshal_outputs_x(
      _camkes_size_151, _camkes_length_153, x);
  if (_camkes_length_153 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_153) +
             ((_camkes_length_153) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_153) % (sizeof(seL4_Word)))))) !=
            _camkes_size_151))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
void RPCFrom_increment_char(char *x) {
  /* nothing */
  ;
  /* nothing */
  ;
  unsigned int _camkes_length_159 = increment_char_marshal_inputs(x);
  if (__builtin_expect(!!(_camkes_length_159 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    return;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_160 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_159) +
                ((_camkes_length_159) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_159) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_160);
  _camkes_info_160 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_161 =
      seL4_MessageInfo_get_length(_camkes_info_160) * sizeof(seL4_Word);
  int _camkes_error_162 = increment_char_unmarshal_outputs(_camkes_size_161, x);
  if (__builtin_expect(!!(_camkes_error_162 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    return;
  }
  /* nothing */
  ;
}
static unsigned int
increment_parameter_marshal_inputs_x(unsigned int _camkes_offset_163, int *x) {
  void *_camkes_buffer_base_164 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_165 = x;
  do {
    (void)0;
    if (!(!(_camkes_offset_163 + sizeof(*_camkes_ptr_165) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_164 + _camkes_offset_163, _camkes_ptr_165,
         sizeof(*_camkes_ptr_165));
  _camkes_offset_163 += sizeof(*_camkes_ptr_165);
  return _camkes_offset_163;
}
static const uint8_t _camkes_method_index_169 = 5;
static unsigned int increment_parameter_marshal_inputs(int *x) {
  unsigned int _camkes_length_170 = 0;
  void *_camkes_buffer_base_171 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_170 + sizeof(_camkes_method_index_169) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_171, &_camkes_method_index_169,
         sizeof(_camkes_method_index_169));
  _camkes_length_170 += sizeof(_camkes_method_index_169);
  /* Marshal the parameters. */
  _camkes_length_170 =
      increment_parameter_marshal_inputs_x(_camkes_length_170, x);
  if (_camkes_length_170 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_170;
}
static unsigned int increment_parameter_unmarshal_outputs_x(
    unsigned int _camkes_size_173, unsigned int _camkes_offset_174, int *x) {
  void *_camkes_buffer_base_175 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_174 + sizeof(*x) > _camkes_size_173))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(x, _camkes_buffer_base_175 + _camkes_offset_174, sizeof(*x));
  _camkes_offset_174 += sizeof(*x);
  return _camkes_offset_174;
}
static int increment_parameter_unmarshal_outputs(unsigned int _camkes_size_176,
                                                 int *x) {
  unsigned int _camkes_length_178 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_179 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the parameters. */
  _camkes_length_178 = increment_parameter_unmarshal_outputs_x(
      _camkes_size_176, _camkes_length_178, x);
  if (_camkes_length_178 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_178) +
             ((_camkes_length_178) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_178) % (sizeof(seL4_Word)))))) !=
            _camkes_size_176))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
void RPCFrom_increment_parameter(int *x) {
  /* nothing */
  ;
  /* nothing */
  ;
  unsigned int _camkes_length_184 = increment_parameter_marshal_inputs(x);
  if (__builtin_expect(!!(_camkes_length_184 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    return;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_185 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_184) +
                ((_camkes_length_184) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_184) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_185);
  _camkes_info_185 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_186 =
      seL4_MessageInfo_get_length(_camkes_info_185) * sizeof(seL4_Word);
  int _camkes_error_187 =
      increment_parameter_unmarshal_outputs(_camkes_size_186, x);
  if (__builtin_expect(!!(_camkes_error_187 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    return;
  }
  /* nothing */
  ;
}
static int echo_int_2_i_from_1;
static int echo_int_2_i_from_2;
static int *get_echo_int_2_i_from(void) __attribute__((__unused__));
static int *get_echo_int_2_i_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_2_i_from_1;
  case 2:
    return &echo_int_2_i_from_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_2_j_from_1;
static int echo_int_2_j_from_2;
static int *get_echo_int_2_j_from(void) __attribute__((__unused__));
static int *get_echo_int_2_j_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_2_j_from_1;
  case 2:
    return &echo_int_2_j_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_2_marshal_inputs_i(unsigned int _camkes_offset_188,
                                                int i) {
  void *_camkes_buffer_base_189 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_190 = (get_echo_int_2_i_from());
  *_camkes_ptr_190 = i;
  do {
    (void)0;
    if (!(!(_camkes_offset_188 + sizeof(*_camkes_ptr_190) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_189 + _camkes_offset_188, _camkes_ptr_190,
         sizeof(*_camkes_ptr_190));
  _camkes_offset_188 += sizeof(*_camkes_ptr_190);
  return _camkes_offset_188;
}
static unsigned int echo_int_2_marshal_inputs_j(unsigned int _camkes_offset_194,
                                                int j) {
  void *_camkes_buffer_base_195 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_196 = (get_echo_int_2_j_from());
  *_camkes_ptr_196 = j;
  do {
    (void)0;
    if (!(!(_camkes_offset_194 + sizeof(*_camkes_ptr_196) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_195 + _camkes_offset_194, _camkes_ptr_196,
         sizeof(*_camkes_ptr_196));
  _camkes_offset_194 += sizeof(*_camkes_ptr_196);
  return _camkes_offset_194;
}
static const uint8_t _camkes_method_index_200 = 6;
static unsigned int echo_int_2_marshal_inputs(int i, int j) {
  unsigned int _camkes_length_201 = 0;
  void *_camkes_buffer_base_202 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_201 + sizeof(_camkes_method_index_200) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_202, &_camkes_method_index_200,
         sizeof(_camkes_method_index_200));
  _camkes_length_201 += sizeof(_camkes_method_index_200);
  /* Marshal the parameters. */
  _camkes_length_201 = echo_int_2_marshal_inputs_i(_camkes_length_201, i);
  if (_camkes_length_201 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_201 = echo_int_2_marshal_inputs_j(_camkes_length_201, j);
  if (_camkes_length_201 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_201;
}
static unsigned int
echo_int_2_unmarshal_outputs__camkes_ret_fn_203(unsigned int _camkes_size_205,
                                                unsigned int _camkes_offset_204,
                                                int *_camkes_return_206) {
  void *_camkes_buffer_base_207 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_204 + sizeof(*_camkes_return_206) >
            _camkes_size_205))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_206, _camkes_buffer_base_207 + _camkes_offset_204,
         sizeof(*_camkes_return_206));
  _camkes_offset_204 += sizeof(*_camkes_return_206);
  return _camkes_offset_204;
}
static int echo_int_2_unmarshal_outputs(unsigned int _camkes_size_208,
                                        int *_camkes_return_209) {
  unsigned int _camkes_length_210 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_211 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_210 = echo_int_2_unmarshal_outputs__camkes_ret_fn_203(
      _camkes_size_208, _camkes_length_210, _camkes_return_209);
  if (_camkes_length_210 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  do {
    (void)0;
    if (!(!(((_camkes_length_210) +
             ((_camkes_length_210) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_210) % (sizeof(seL4_Word)))))) !=
            _camkes_size_208))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_212_1;
static int _camkes_ret_tls_var_from_212_2;
static int *get__camkes_ret_tls_var_from_212(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_212(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_212_1;
  case 2:
    return &_camkes_ret_tls_var_from_212_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_int_2(int i, int j) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_214 __attribute__((__unused__));
  int *_camkes_return_ptr_215 = (get__camkes_ret_tls_var_from_212());
  unsigned int _camkes_length_216 = echo_int_2_marshal_inputs(i, j);
  if (__builtin_expect(!!(_camkes_length_216 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_215, 0, sizeof(*_camkes_return_ptr_215));
    return *_camkes_return_ptr_215;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_217 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_216) +
                ((_camkes_length_216) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_216) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_217);
  _camkes_info_217 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_218 =
      seL4_MessageInfo_get_length(_camkes_info_217) * sizeof(seL4_Word);
  int _camkes_error_219 =
      echo_int_2_unmarshal_outputs(_camkes_size_218, _camkes_return_ptr_215);
  if (__builtin_expect(!!(_camkes_error_219 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_215, 0, sizeof(*_camkes_return_ptr_215));
    return *_camkes_return_ptr_215;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_215;
}
static int echo_int_3_i_from_1;
static int echo_int_3_i_from_2;
static int *get_echo_int_3_i_from(void) __attribute__((__unused__));
static int *get_echo_int_3_i_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_3_i_from_1;
  case 2:
    return &echo_int_3_i_from_2;
  default:
    (void)0;
    abort();
  }
}
static char echo_int_3_j_from_1;
static char echo_int_3_j_from_2;
static char *get_echo_int_3_j_from(void) __attribute__((__unused__));
static char *get_echo_int_3_j_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_3_j_from_1;
  case 2:
    return &echo_int_3_j_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_3_marshal_inputs_i(unsigned int _camkes_offset_220,
                                                int i) {
  void *_camkes_buffer_base_221 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_222 = (get_echo_int_3_i_from());
  *_camkes_ptr_222 = i;
  do {
    (void)0;
    if (!(!(_camkes_offset_220 + sizeof(*_camkes_ptr_222) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_221 + _camkes_offset_220, _camkes_ptr_222,
         sizeof(*_camkes_ptr_222));
  _camkes_offset_220 += sizeof(*_camkes_ptr_222);
  return _camkes_offset_220;
}
static unsigned int echo_int_3_marshal_inputs_j(unsigned int _camkes_offset_226,
                                                char j) {
  void *_camkes_buffer_base_227 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  char *_camkes_ptr_228 = (get_echo_int_3_j_from());
  *_camkes_ptr_228 = j;
  do {
    (void)0;
    if (!(!(_camkes_offset_226 + sizeof(*_camkes_ptr_228) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_227 + _camkes_offset_226, _camkes_ptr_228,
         sizeof(*_camkes_ptr_228));
  _camkes_offset_226 += sizeof(*_camkes_ptr_228);
  return _camkes_offset_226;
}
static const uint8_t _camkes_method_index_232 = 7;
static unsigned int echo_int_3_marshal_inputs(int i, char j) {
  unsigned int _camkes_length_233 = 0;
  void *_camkes_buffer_base_234 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_233 + sizeof(_camkes_method_index_232) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_234, &_camkes_method_index_232,
         sizeof(_camkes_method_index_232));
  _camkes_length_233 += sizeof(_camkes_method_index_232);
  /* Marshal the parameters. */
  _camkes_length_233 = echo_int_3_marshal_inputs_i(_camkes_length_233, i);
  if (_camkes_length_233 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_233 = echo_int_3_marshal_inputs_j(_camkes_length_233, j);
  if (_camkes_length_233 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_233;
}
static unsigned int
echo_int_3_unmarshal_outputs__camkes_ret_fn_235(unsigned int _camkes_size_237,
                                                unsigned int _camkes_offset_236,
                                                int *_camkes_return_238) {
  void *_camkes_buffer_base_239 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_236 + sizeof(*_camkes_return_238) >
            _camkes_size_237))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_238, _camkes_buffer_base_239 + _camkes_offset_236,
         sizeof(*_camkes_return_238));
  _camkes_offset_236 += sizeof(*_camkes_return_238);
  return _camkes_offset_236;
}
static int echo_int_3_unmarshal_outputs(unsigned int _camkes_size_240,
                                        int *_camkes_return_241) {
  unsigned int _camkes_length_242 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_243 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_242 = echo_int_3_unmarshal_outputs__camkes_ret_fn_235(
      _camkes_size_240, _camkes_length_242, _camkes_return_241);
  if (_camkes_length_242 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  do {
    (void)0;
    if (!(!(((_camkes_length_242) +
             ((_camkes_length_242) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_242) % (sizeof(seL4_Word)))))) !=
            _camkes_size_240))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_244_1;
static int _camkes_ret_tls_var_from_244_2;
static int *get__camkes_ret_tls_var_from_244(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_244(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_244_1;
  case 2:
    return &_camkes_ret_tls_var_from_244_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_int_3(int i, char j) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_246 __attribute__((__unused__));
  int *_camkes_return_ptr_247 = (get__camkes_ret_tls_var_from_244());
  unsigned int _camkes_length_248 = echo_int_3_marshal_inputs(i, j);
  if (__builtin_expect(!!(_camkes_length_248 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_247, 0, sizeof(*_camkes_return_ptr_247));
    return *_camkes_return_ptr_247;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_249 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_248) +
                ((_camkes_length_248) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_248) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_249);
  _camkes_info_249 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_250 =
      seL4_MessageInfo_get_length(_camkes_info_249) * sizeof(seL4_Word);
  int _camkes_error_251 =
      echo_int_3_unmarshal_outputs(_camkes_size_250, _camkes_return_ptr_247);
  if (__builtin_expect(!!(_camkes_error_251 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_247, 0, sizeof(*_camkes_return_ptr_247));
    return *_camkes_return_ptr_247;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_247;
}
static unsigned int
increment_64_marshal_inputs_x(unsigned int _camkes_offset_252, uint64_t *x) {
  void *_camkes_buffer_base_253 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  uint64_t *_camkes_ptr_254 = x;
  do {
    (void)0;
    if (!(!(_camkes_offset_252 + sizeof(*_camkes_ptr_254) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_253 + _camkes_offset_252, _camkes_ptr_254,
         sizeof(*_camkes_ptr_254));
  _camkes_offset_252 += sizeof(*_camkes_ptr_254);
  return _camkes_offset_252;
}
static const uint8_t _camkes_method_index_258 = 8;
static unsigned int increment_64_marshal_inputs(uint64_t *x) {
  unsigned int _camkes_length_259 = 0;
  void *_camkes_buffer_base_260 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_259 + sizeof(_camkes_method_index_258) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_260, &_camkes_method_index_258,
         sizeof(_camkes_method_index_258));
  _camkes_length_259 += sizeof(_camkes_method_index_258);
  /* Marshal the parameters. */
  _camkes_length_259 = increment_64_marshal_inputs_x(_camkes_length_259, x);
  if (_camkes_length_259 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_259;
}
static unsigned int
increment_64_unmarshal_outputs_x(unsigned int _camkes_size_262,
                                 unsigned int _camkes_offset_263, uint64_t *x) {
  void *_camkes_buffer_base_264 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_263 + sizeof(*x) > _camkes_size_262))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(x, _camkes_buffer_base_264 + _camkes_offset_263, sizeof(*x));
  _camkes_offset_263 += sizeof(*x);
  return _camkes_offset_263;
}
static int increment_64_unmarshal_outputs(unsigned int _camkes_size_265,
                                          uint64_t *x) {
  unsigned int _camkes_length_267 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_268 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the parameters. */
  _camkes_length_267 =
      increment_64_unmarshal_outputs_x(_camkes_size_265, _camkes_length_267, x);
  if (_camkes_length_267 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_267) +
             ((_camkes_length_267) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_267) % (sizeof(seL4_Word)))))) !=
            _camkes_size_265))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
void RPCFrom_increment_64(uint64_t *x) {
  /* nothing */
  ;
  /* nothing */
  ;
  unsigned int _camkes_length_273 = increment_64_marshal_inputs(x);
  if (__builtin_expect(!!(_camkes_length_273 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    return;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_274 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_273) +
                ((_camkes_length_273) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_273) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_274);
  _camkes_info_274 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_275 =
      seL4_MessageInfo_get_length(_camkes_info_274) * sizeof(seL4_Word);
  int _camkes_error_276 = increment_64_unmarshal_outputs(_camkes_size_275, x);
  if (__builtin_expect(!!(_camkes_error_276 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    return;
  }
  /* nothing */
  ;
}
static int echo_int_4_i_from_1;
static int echo_int_4_i_from_2;
static int *get_echo_int_4_i_from(void) __attribute__((__unused__));
static int *get_echo_int_4_i_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_i_from_1;
  case 2:
    return &echo_int_4_i_from_2;
  default:
    (void)0;
    abort();
  }
}
static int64_t echo_int_4_j_from_1;
static int64_t echo_int_4_j_from_2;
static int64_t *get_echo_int_4_j_from(void) __attribute__((__unused__));
static int64_t *get_echo_int_4_j_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_j_from_1;
  case 2:
    return &echo_int_4_j_from_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_4_k_from_1;
static int echo_int_4_k_from_2;
static int *get_echo_int_4_k_from(void) __attribute__((__unused__));
static int *get_echo_int_4_k_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_k_from_1;
  case 2:
    return &echo_int_4_k_from_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_4_l_from_1;
static int echo_int_4_l_from_2;
static int *get_echo_int_4_l_from(void) __attribute__((__unused__));
static int *get_echo_int_4_l_from(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_l_from_1;
  case 2:
    return &echo_int_4_l_from_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_4_marshal_inputs_i(unsigned int _camkes_offset_277,
                                                int i) {
  void *_camkes_buffer_base_278 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_279 = (get_echo_int_4_i_from());
  *_camkes_ptr_279 = i;
  do {
    (void)0;
    if (!(!(_camkes_offset_277 + sizeof(*_camkes_ptr_279) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_278 + _camkes_offset_277, _camkes_ptr_279,
         sizeof(*_camkes_ptr_279));
  _camkes_offset_277 += sizeof(*_camkes_ptr_279);
  return _camkes_offset_277;
}
static unsigned int echo_int_4_marshal_inputs_j(unsigned int _camkes_offset_283,
                                                int64_t j) {
  void *_camkes_buffer_base_284 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int64_t *_camkes_ptr_285 = (get_echo_int_4_j_from());
  *_camkes_ptr_285 = j;
  do {
    (void)0;
    if (!(!(_camkes_offset_283 + sizeof(*_camkes_ptr_285) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_284 + _camkes_offset_283, _camkes_ptr_285,
         sizeof(*_camkes_ptr_285));
  _camkes_offset_283 += sizeof(*_camkes_ptr_285);
  return _camkes_offset_283;
}
static unsigned int echo_int_4_marshal_inputs_k(unsigned int _camkes_offset_289,
                                                int k) {
  void *_camkes_buffer_base_290 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_291 = (get_echo_int_4_k_from());
  *_camkes_ptr_291 = k;
  do {
    (void)0;
    if (!(!(_camkes_offset_289 + sizeof(*_camkes_ptr_291) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_290 + _camkes_offset_289, _camkes_ptr_291,
         sizeof(*_camkes_ptr_291));
  _camkes_offset_289 += sizeof(*_camkes_ptr_291);
  return _camkes_offset_289;
}
static unsigned int echo_int_4_marshal_inputs_l(unsigned int _camkes_offset_295,
                                                int l) {
  void *_camkes_buffer_base_296 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
  int *_camkes_ptr_297 = (get_echo_int_4_l_from());
  *_camkes_ptr_297 = l;
  do {
    (void)0;
    if (!(!(_camkes_offset_295 + sizeof(*_camkes_ptr_297) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_296 + _camkes_offset_295, _camkes_ptr_297,
         sizeof(*_camkes_ptr_297));
  _camkes_offset_295 += sizeof(*_camkes_ptr_297);
  return _camkes_offset_295;
}
static const uint8_t _camkes_method_index_301 = 9;
static unsigned int echo_int_4_marshal_inputs(int i, int64_t j, int k, int l) {
  unsigned int _camkes_length_302 = 0;
  void *_camkes_buffer_base_303 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the method index. */
  do {
    (void)0;
    if (!(!(_camkes_length_302 + sizeof(_camkes_method_index_301) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_303, &_camkes_method_index_301,
         sizeof(_camkes_method_index_301));
  _camkes_length_302 += sizeof(_camkes_method_index_301);
  /* Marshal the parameters. */
  _camkes_length_302 = echo_int_4_marshal_inputs_i(_camkes_length_302, i);
  if (_camkes_length_302 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_302 = echo_int_4_marshal_inputs_j(_camkes_length_302, j);
  if (_camkes_length_302 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_302 = echo_int_4_marshal_inputs_k(_camkes_length_302, k);
  if (_camkes_length_302 == 0xffffffffU) {
    return 0xffffffffU;
  }
  _camkes_length_302 = echo_int_4_marshal_inputs_l(_camkes_length_302, l);
  if (_camkes_length_302 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_302;
}
static unsigned int
echo_int_4_unmarshal_outputs__camkes_ret_fn_304(unsigned int _camkes_size_306,
                                                unsigned int _camkes_offset_305,
                                                int *_camkes_return_307) {
  void *_camkes_buffer_base_308 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Unmarshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_305 + sizeof(*_camkes_return_307) >
            _camkes_size_306))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_return_307, _camkes_buffer_base_308 + _camkes_offset_305,
         sizeof(*_camkes_return_307));
  _camkes_offset_305 += sizeof(*_camkes_return_307);
  return _camkes_offset_305;
}
static int echo_int_4_unmarshal_outputs(unsigned int _camkes_size_309,
                                        int *_camkes_return_310) {
  unsigned int _camkes_length_311 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_312 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  _camkes_length_311 = echo_int_4_unmarshal_outputs__camkes_ret_fn_304(
      _camkes_size_309, _camkes_length_311, _camkes_return_310);
  if (_camkes_length_311 == 0xffffffffU) {
    return -1;
  }
  /* Unmarshal the parameters. */
  do {
    (void)0;
    if (!(!(((_camkes_length_311) +
             ((_camkes_length_311) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_311) % (sizeof(seL4_Word)))))) !=
            _camkes_size_309))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static int _camkes_ret_tls_var_from_313_1;
static int _camkes_ret_tls_var_from_313_2;
static int *get__camkes_ret_tls_var_from_313(void) __attribute__((__unused__));
static int *get__camkes_ret_tls_var_from_313(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_ret_tls_var_from_313_1;
  case 2:
    return &_camkes_ret_tls_var_from_313_2;
  default:
    (void)0;
    abort();
  }
}
int RPCFrom_echo_int_4(int i, int64_t j, int k, int l) {
  /* nothing */
  ;
  /* nothing */
  ;
  int _camkes_return_315 __attribute__((__unused__));
  int *_camkes_return_ptr_316 = (get__camkes_ret_tls_var_from_313());
  unsigned int _camkes_length_317 = echo_int_4_marshal_inputs(i, j, k, l);
  if (__builtin_expect(!!(_camkes_length_317 == 0xffffffffU), 0)) {
    /* Error in marshalling; bail out. */
    memset(_camkes_return_ptr_316, 0, sizeof(*_camkes_return_ptr_316));
    return *_camkes_return_ptr_316;
  }
  /* nothing */
  ;
  /* Call the endpoint */
  seL4_MessageInfo_t _camkes_info_318 = seL4_MessageInfo_new(
      0, 0, 0, ((_camkes_length_317) +
                ((_camkes_length_317) % (sizeof(seL4_Word)) == 0
                     ? 0
                     : ((sizeof(seL4_Word)) -
                        ((_camkes_length_317) % (sizeof(seL4_Word)))))) /
                   sizeof(seL4_Word));
  seL4_Send(6, _camkes_info_318);
  _camkes_info_318 = seL4_Wait(6, ((void *)0));
  /* nothing */
  ;
  /* nothing */
  ;
  /* Unmarshal the response */
  unsigned int _camkes_size_319 =
      seL4_MessageInfo_get_length(_camkes_info_318) * sizeof(seL4_Word);
  int _camkes_error_320 =
      echo_int_4_unmarshal_outputs(_camkes_size_319, _camkes_return_ptr_316);
  if (__builtin_expect(!!(_camkes_error_320 != 0), 0)) {
    /* Error in unmarshalling; bail out. */
    memset(_camkes_return_ptr_316, 0, sizeof(*_camkes_return_ptr_316));
    return *_camkes_return_ptr_316;
  }
  /* nothing */
  ;
  return *_camkes_return_ptr_316;
}
extern int RPCTo_echo_int(int i);
static unsigned int echo_int_unmarshal_inputs_i(unsigned int _camkes_size_322,
                                                unsigned int _camkes_offset_323,
                                                int *i) {
  void *_camkes_buffer_base_324 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_323 + sizeof(*i) > _camkes_size_322))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(i, _camkes_buffer_base_324 + _camkes_offset_323, sizeof(*i));
  _camkes_offset_323 += sizeof(*i);
  return _camkes_offset_323;
}
static int echo_int_unmarshal_inputs(unsigned int _camkes_size_325, int *i) {
  unsigned int _camkes_length_326 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_327 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_326 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_326 =
      echo_int_unmarshal_inputs_i(_camkes_size_325, _camkes_length_326, i);
  if (_camkes_length_326 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_326) +
             ((_camkes_length_326) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_326) % (sizeof(seL4_Word)))))) !=
            _camkes_size_325))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
echo_int_marshal_outputs__camkes_ret_fn_328(unsigned int _camkes_offset_329,
                                            int *_camkes_return_330) {
  void *_camkes_buffer_base_331 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_329 + sizeof(*_camkes_return_330) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_331 + _camkes_offset_329, _camkes_return_330,
         sizeof(*_camkes_return_330));
  _camkes_offset_329 += sizeof(*_camkes_return_330);
  return _camkes_offset_329;
}
static unsigned int echo_int_marshal_outputs(int *_camkes_return_332) {
  unsigned int _camkes_length_333 = 0;
  _camkes_length_333 = echo_int_marshal_outputs__camkes_ret_fn_328(
      _camkes_length_333, _camkes_return_332);
  if (_camkes_length_333 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  (void)0;
  return _camkes_length_333;
}
static int echo_int_ret_to_1;
static int echo_int_ret_to_2;
static int *get_echo_int_ret_to(void) __attribute__((__unused__));
static int *get_echo_int_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_ret_to_1;
  case 2:
    return &echo_int_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_i_to_1;
static int echo_int_i_to_2;
static int *get_echo_int_i_to(void) __attribute__((__unused__));
static int *get_echo_int_i_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_i_to_1;
  case 2:
    return &echo_int_i_to_2;
  default:
    (void)0;
    abort();
  }
}
extern int RPCTo_echo_int_1(int i, unsigned int j, int32_t k, uint32_t l);
static unsigned int
echo_int_1_unmarshal_inputs_i(unsigned int _camkes_size_334,
                              unsigned int _camkes_offset_335, int *i) {
  void *_camkes_buffer_base_336 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_335 + sizeof(*i) > _camkes_size_334))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(i, _camkes_buffer_base_336 + _camkes_offset_335, sizeof(*i));
  _camkes_offset_335 += sizeof(*i);
  return _camkes_offset_335;
}
static unsigned int
echo_int_1_unmarshal_inputs_j(unsigned int _camkes_size_337,
                              unsigned int _camkes_offset_338,
                              unsigned int *j) {
  void *_camkes_buffer_base_339 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_338 + sizeof(*j) > _camkes_size_337))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(j, _camkes_buffer_base_339 + _camkes_offset_338, sizeof(*j));
  _camkes_offset_338 += sizeof(*j);
  return _camkes_offset_338;
}
static unsigned int
echo_int_1_unmarshal_inputs_k(unsigned int _camkes_size_340,
                              unsigned int _camkes_offset_341, int32_t *k) {
  void *_camkes_buffer_base_342 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_341 + sizeof(*k) > _camkes_size_340))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(k, _camkes_buffer_base_342 + _camkes_offset_341, sizeof(*k));
  _camkes_offset_341 += sizeof(*k);
  return _camkes_offset_341;
}
static unsigned int
echo_int_1_unmarshal_inputs_l(unsigned int _camkes_size_343,
                              unsigned int _camkes_offset_344, uint32_t *l) {
  void *_camkes_buffer_base_345 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_344 + sizeof(*l) > _camkes_size_343))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(l, _camkes_buffer_base_345 + _camkes_offset_344, sizeof(*l));
  _camkes_offset_344 += sizeof(*l);
  return _camkes_offset_344;
}
static int echo_int_1_unmarshal_inputs(unsigned int _camkes_size_346, int *i,
                                       unsigned int *j, int32_t *k,
                                       uint32_t *l) {
  unsigned int _camkes_length_347 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_348 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_347 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_347 =
      echo_int_1_unmarshal_inputs_i(_camkes_size_346, _camkes_length_347, i);
  if (_camkes_length_347 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_347 =
      echo_int_1_unmarshal_inputs_j(_camkes_size_346, _camkes_length_347, j);
  if (_camkes_length_347 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_347 =
      echo_int_1_unmarshal_inputs_k(_camkes_size_346, _camkes_length_347, k);
  if (_camkes_length_347 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_347 =
      echo_int_1_unmarshal_inputs_l(_camkes_size_346, _camkes_length_347, l);
  if (_camkes_length_347 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_347) +
             ((_camkes_length_347) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_347) % (sizeof(seL4_Word)))))) !=
            _camkes_size_346))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
echo_int_1_marshal_outputs__camkes_ret_fn_349(unsigned int _camkes_offset_350,
                                              int *_camkes_return_351) {
  void *_camkes_buffer_base_352 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_350 + sizeof(*_camkes_return_351) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_352 + _camkes_offset_350, _camkes_return_351,
         sizeof(*_camkes_return_351));
  _camkes_offset_350 += sizeof(*_camkes_return_351);
  return _camkes_offset_350;
}
static unsigned int echo_int_1_marshal_outputs(int *_camkes_return_353) {
  unsigned int _camkes_length_354 = 0;
  _camkes_length_354 = echo_int_1_marshal_outputs__camkes_ret_fn_349(
      _camkes_length_354, _camkes_return_353);
  if (_camkes_length_354 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  (void)0;
  return _camkes_length_354;
}
static int echo_int_1_ret_to_1;
static int echo_int_1_ret_to_2;
static int *get_echo_int_1_ret_to(void) __attribute__((__unused__));
static int *get_echo_int_1_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_ret_to_1;
  case 2:
    return &echo_int_1_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_1_i_to_1;
static int echo_int_1_i_to_2;
static int *get_echo_int_1_i_to(void) __attribute__((__unused__));
static int *get_echo_int_1_i_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_i_to_1;
  case 2:
    return &echo_int_1_i_to_2;
  default:
    (void)0;
    abort();
  }
}
static unsigned int echo_int_1_j_to_1;
static unsigned int echo_int_1_j_to_2;
static unsigned int *get_echo_int_1_j_to(void) __attribute__((__unused__));
static unsigned int *get_echo_int_1_j_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_j_to_1;
  case 2:
    return &echo_int_1_j_to_2;
  default:
    (void)0;
    abort();
  }
}
static int32_t echo_int_1_k_to_1;
static int32_t echo_int_1_k_to_2;
static int32_t *get_echo_int_1_k_to(void) __attribute__((__unused__));
static int32_t *get_echo_int_1_k_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_k_to_1;
  case 2:
    return &echo_int_1_k_to_2;
  default:
    (void)0;
    abort();
  }
}
static uint32_t echo_int_1_l_to_1;
static uint32_t echo_int_1_l_to_2;
static uint32_t *get_echo_int_1_l_to(void) __attribute__((__unused__));
static uint32_t *get_echo_int_1_l_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_1_l_to_1;
  case 2:
    return &echo_int_1_l_to_2;
  default:
    (void)0;
    abort();
  }
}
extern int RPCTo_echo_parameter(int pin, int *pout);
static unsigned int
echo_parameter_unmarshal_inputs_pin(unsigned int _camkes_size_355,
                                    unsigned int _camkes_offset_356, int *pin) {
  void *_camkes_buffer_base_357 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_356 + sizeof(*pin) > _camkes_size_355))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(pin, _camkes_buffer_base_357 + _camkes_offset_356, sizeof(*pin));
  _camkes_offset_356 += sizeof(*pin);
  return _camkes_offset_356;
}
static int echo_parameter_unmarshal_inputs(unsigned int _camkes_size_358,
                                           int *pin) {
  unsigned int _camkes_length_359 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_360 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_359 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_359 = echo_parameter_unmarshal_inputs_pin(
      _camkes_size_358, _camkes_length_359, pin);
  if (_camkes_length_359 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_359) +
             ((_camkes_length_359) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_359) % (sizeof(seL4_Word)))))) !=
            _camkes_size_358))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int echo_parameter_marshal_outputs__camkes_ret_fn_361(
    unsigned int _camkes_offset_362, int *_camkes_return_363) {
  void *_camkes_buffer_base_364 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_362 + sizeof(*_camkes_return_363) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_364 + _camkes_offset_362, _camkes_return_363,
         sizeof(*_camkes_return_363));
  _camkes_offset_362 += sizeof(*_camkes_return_363);
  return _camkes_offset_362;
}
static unsigned int
echo_parameter_marshal_outputs_pout(unsigned int _camkes_offset_365,
                                    int *pout) {
  void *_camkes_buffer_base_366 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_365 + sizeof(*pout) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_366 + _camkes_offset_365, pout, sizeof(*pout));
  _camkes_offset_365 += sizeof(*pout);
  return _camkes_offset_365;
}
static unsigned int echo_parameter_marshal_outputs(int *_camkes_return_367,
                                                   int *pout) {
  unsigned int _camkes_length_368 = 0;
  _camkes_length_368 = echo_parameter_marshal_outputs__camkes_ret_fn_361(
      _camkes_length_368, _camkes_return_367);
  if (_camkes_length_368 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  _camkes_length_368 =
      echo_parameter_marshal_outputs_pout(_camkes_length_368, pout);
  if (_camkes_length_368 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_368;
}
static int echo_parameter_ret_to_1;
static int echo_parameter_ret_to_2;
static int *get_echo_parameter_ret_to(void) __attribute__((__unused__));
static int *get_echo_parameter_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_parameter_ret_to_1;
  case 2:
    return &echo_parameter_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_parameter_pin_to_1;
static int echo_parameter_pin_to_2;
static int *get_echo_parameter_pin_to(void) __attribute__((__unused__));
static int *get_echo_parameter_pin_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_parameter_pin_to_1;
  case 2:
    return &echo_parameter_pin_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_parameter_pout_to_1;
static int echo_parameter_pout_to_2;
static int *get_echo_parameter_pout_to(void) __attribute__((__unused__));
static int *get_echo_parameter_pout_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_parameter_pout_to_1;
  case 2:
    return &echo_parameter_pout_to_2;
  default:
    (void)0;
    abort();
  }
}
extern int RPCTo_echo_char(char i);
static unsigned int
echo_char_unmarshal_inputs_i(unsigned int _camkes_size_369,
                             unsigned int _camkes_offset_370, char *i) {
  void *_camkes_buffer_base_371 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_370 + sizeof(*i) > _camkes_size_369))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(i, _camkes_buffer_base_371 + _camkes_offset_370, sizeof(*i));
  _camkes_offset_370 += sizeof(*i);
  return _camkes_offset_370;
}
static int echo_char_unmarshal_inputs(unsigned int _camkes_size_372, char *i) {
  unsigned int _camkes_length_373 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_374 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_373 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_373 =
      echo_char_unmarshal_inputs_i(_camkes_size_372, _camkes_length_373, i);
  if (_camkes_length_373 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_373) +
             ((_camkes_length_373) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_373) % (sizeof(seL4_Word)))))) !=
            _camkes_size_372))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
echo_char_marshal_outputs__camkes_ret_fn_375(unsigned int _camkes_offset_376,
                                             int *_camkes_return_377) {
  void *_camkes_buffer_base_378 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_376 + sizeof(*_camkes_return_377) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_378 + _camkes_offset_376, _camkes_return_377,
         sizeof(*_camkes_return_377));
  _camkes_offset_376 += sizeof(*_camkes_return_377);
  return _camkes_offset_376;
}
static unsigned int echo_char_marshal_outputs(int *_camkes_return_379) {
  unsigned int _camkes_length_380 = 0;
  _camkes_length_380 = echo_char_marshal_outputs__camkes_ret_fn_375(
      _camkes_length_380, _camkes_return_379);
  if (_camkes_length_380 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  (void)0;
  return _camkes_length_380;
}
static int echo_char_ret_to_1;
static int echo_char_ret_to_2;
static int *get_echo_char_ret_to(void) __attribute__((__unused__));
static int *get_echo_char_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_char_ret_to_1;
  case 2:
    return &echo_char_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static char echo_char_i_to_1;
static char echo_char_i_to_2;
static char *get_echo_char_i_to(void) __attribute__((__unused__));
static char *get_echo_char_i_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_char_i_to_1;
  case 2:
    return &echo_char_i_to_2;
  default:
    (void)0;
    abort();
  }
}
extern void RPCTo_increment_char(char *x);
static unsigned int
increment_char_unmarshal_inputs_x(unsigned int _camkes_size_381,
                                  unsigned int _camkes_offset_382, char *x) {
  void *_camkes_buffer_base_383 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_382 + sizeof(*x) > _camkes_size_381))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(x, _camkes_buffer_base_383 + _camkes_offset_382, sizeof(*x));
  _camkes_offset_382 += sizeof(*x);
  return _camkes_offset_382;
}
static int increment_char_unmarshal_inputs(unsigned int _camkes_size_384,
                                           char *x) {
  unsigned int _camkes_length_385 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_386 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_385 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_385 = increment_char_unmarshal_inputs_x(_camkes_size_384,
                                                         _camkes_length_385, x);
  if (_camkes_length_385 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_385) +
             ((_camkes_length_385) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_385) % (sizeof(seL4_Word)))))) !=
            _camkes_size_384))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
increment_char_marshal_outputs_x(unsigned int _camkes_offset_388, char *x) {
  void *_camkes_buffer_base_389 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_388 + sizeof(*x) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_389 + _camkes_offset_388, x, sizeof(*x));
  _camkes_offset_388 += sizeof(*x);
  return _camkes_offset_388;
}
static unsigned int increment_char_marshal_outputs(char *x) {
  unsigned int _camkes_length_391 = 0;
  /* Marshal output parameters. */
  _camkes_length_391 = increment_char_marshal_outputs_x(_camkes_length_391, x);
  if (_camkes_length_391 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_391;
}
static char increment_char_x_to_1;
static char increment_char_x_to_2;
static char *get_increment_char_x_to(void) __attribute__((__unused__));
static char *get_increment_char_x_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &increment_char_x_to_1;
  case 2:
    return &increment_char_x_to_2;
  default:
    (void)0;
    abort();
  }
}
extern void RPCTo_increment_parameter(int *x);
static unsigned int increment_parameter_unmarshal_inputs_x(
    unsigned int _camkes_size_392, unsigned int _camkes_offset_393, int *x) {
  void *_camkes_buffer_base_394 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_393 + sizeof(*x) > _camkes_size_392))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(x, _camkes_buffer_base_394 + _camkes_offset_393, sizeof(*x));
  _camkes_offset_393 += sizeof(*x);
  return _camkes_offset_393;
}
static int increment_parameter_unmarshal_inputs(unsigned int _camkes_size_395,
                                                int *x) {
  unsigned int _camkes_length_396 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_397 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_396 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_396 = increment_parameter_unmarshal_inputs_x(
      _camkes_size_395, _camkes_length_396, x);
  if (_camkes_length_396 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_396) +
             ((_camkes_length_396) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_396) % (sizeof(seL4_Word)))))) !=
            _camkes_size_395))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
increment_parameter_marshal_outputs_x(unsigned int _camkes_offset_399, int *x) {
  void *_camkes_buffer_base_400 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_399 + sizeof(*x) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_400 + _camkes_offset_399, x, sizeof(*x));
  _camkes_offset_399 += sizeof(*x);
  return _camkes_offset_399;
}
static unsigned int increment_parameter_marshal_outputs(int *x) {
  unsigned int _camkes_length_402 = 0;
  /* Marshal output parameters. */
  _camkes_length_402 =
      increment_parameter_marshal_outputs_x(_camkes_length_402, x);
  if (_camkes_length_402 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_402;
}
static int increment_parameter_x_to_1;
static int increment_parameter_x_to_2;
static int *get_increment_parameter_x_to(void) __attribute__((__unused__));
static int *get_increment_parameter_x_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &increment_parameter_x_to_1;
  case 2:
    return &increment_parameter_x_to_2;
  default:
    (void)0;
    abort();
  }
}
extern int RPCTo_echo_int_2(int i, int j);
static unsigned int
echo_int_2_unmarshal_inputs_i(unsigned int _camkes_size_403,
                              unsigned int _camkes_offset_404, int *i) {
  void *_camkes_buffer_base_405 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_404 + sizeof(*i) > _camkes_size_403))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(i, _camkes_buffer_base_405 + _camkes_offset_404, sizeof(*i));
  _camkes_offset_404 += sizeof(*i);
  return _camkes_offset_404;
}
static unsigned int
echo_int_2_unmarshal_inputs_j(unsigned int _camkes_size_406,
                              unsigned int _camkes_offset_407, int *j) {
  void *_camkes_buffer_base_408 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_407 + sizeof(*j) > _camkes_size_406))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(j, _camkes_buffer_base_408 + _camkes_offset_407, sizeof(*j));
  _camkes_offset_407 += sizeof(*j);
  return _camkes_offset_407;
}
static int echo_int_2_unmarshal_inputs(unsigned int _camkes_size_409, int *i,
                                       int *j) {
  unsigned int _camkes_length_410 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_411 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_410 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_410 =
      echo_int_2_unmarshal_inputs_i(_camkes_size_409, _camkes_length_410, i);
  if (_camkes_length_410 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_410 =
      echo_int_2_unmarshal_inputs_j(_camkes_size_409, _camkes_length_410, j);
  if (_camkes_length_410 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_410) +
             ((_camkes_length_410) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_410) % (sizeof(seL4_Word)))))) !=
            _camkes_size_409))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
echo_int_2_marshal_outputs__camkes_ret_fn_412(unsigned int _camkes_offset_413,
                                              int *_camkes_return_414) {
  void *_camkes_buffer_base_415 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_413 + sizeof(*_camkes_return_414) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_415 + _camkes_offset_413, _camkes_return_414,
         sizeof(*_camkes_return_414));
  _camkes_offset_413 += sizeof(*_camkes_return_414);
  return _camkes_offset_413;
}
static unsigned int echo_int_2_marshal_outputs(int *_camkes_return_416) {
  unsigned int _camkes_length_417 = 0;
  _camkes_length_417 = echo_int_2_marshal_outputs__camkes_ret_fn_412(
      _camkes_length_417, _camkes_return_416);
  if (_camkes_length_417 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  (void)0;
  return _camkes_length_417;
}
static int echo_int_2_ret_to_1;
static int echo_int_2_ret_to_2;
static int *get_echo_int_2_ret_to(void) __attribute__((__unused__));
static int *get_echo_int_2_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_2_ret_to_1;
  case 2:
    return &echo_int_2_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_2_i_to_1;
static int echo_int_2_i_to_2;
static int *get_echo_int_2_i_to(void) __attribute__((__unused__));
static int *get_echo_int_2_i_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_2_i_to_1;
  case 2:
    return &echo_int_2_i_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_2_j_to_1;
static int echo_int_2_j_to_2;
static int *get_echo_int_2_j_to(void) __attribute__((__unused__));
static int *get_echo_int_2_j_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_2_j_to_1;
  case 2:
    return &echo_int_2_j_to_2;
  default:
    (void)0;
    abort();
  }
}
extern int RPCTo_echo_int_3(int i, char j);
static unsigned int
echo_int_3_unmarshal_inputs_i(unsigned int _camkes_size_418,
                              unsigned int _camkes_offset_419, int *i) {
  void *_camkes_buffer_base_420 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_419 + sizeof(*i) > _camkes_size_418))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(i, _camkes_buffer_base_420 + _camkes_offset_419, sizeof(*i));
  _camkes_offset_419 += sizeof(*i);
  return _camkes_offset_419;
}
static unsigned int
echo_int_3_unmarshal_inputs_j(unsigned int _camkes_size_421,
                              unsigned int _camkes_offset_422, char *j) {
  void *_camkes_buffer_base_423 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_422 + sizeof(*j) > _camkes_size_421))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(j, _camkes_buffer_base_423 + _camkes_offset_422, sizeof(*j));
  _camkes_offset_422 += sizeof(*j);
  return _camkes_offset_422;
}
static int echo_int_3_unmarshal_inputs(unsigned int _camkes_size_424, int *i,
                                       char *j) {
  unsigned int _camkes_length_425 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_426 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_425 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_425 =
      echo_int_3_unmarshal_inputs_i(_camkes_size_424, _camkes_length_425, i);
  if (_camkes_length_425 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_425 =
      echo_int_3_unmarshal_inputs_j(_camkes_size_424, _camkes_length_425, j);
  if (_camkes_length_425 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_425) +
             ((_camkes_length_425) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_425) % (sizeof(seL4_Word)))))) !=
            _camkes_size_424))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
echo_int_3_marshal_outputs__camkes_ret_fn_427(unsigned int _camkes_offset_428,
                                              int *_camkes_return_429) {
  void *_camkes_buffer_base_430 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_428 + sizeof(*_camkes_return_429) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_430 + _camkes_offset_428, _camkes_return_429,
         sizeof(*_camkes_return_429));
  _camkes_offset_428 += sizeof(*_camkes_return_429);
  return _camkes_offset_428;
}
static unsigned int echo_int_3_marshal_outputs(int *_camkes_return_431) {
  unsigned int _camkes_length_432 = 0;
  _camkes_length_432 = echo_int_3_marshal_outputs__camkes_ret_fn_427(
      _camkes_length_432, _camkes_return_431);
  if (_camkes_length_432 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  (void)0;
  return _camkes_length_432;
}
static int echo_int_3_ret_to_1;
static int echo_int_3_ret_to_2;
static int *get_echo_int_3_ret_to(void) __attribute__((__unused__));
static int *get_echo_int_3_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_3_ret_to_1;
  case 2:
    return &echo_int_3_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_3_i_to_1;
static int echo_int_3_i_to_2;
static int *get_echo_int_3_i_to(void) __attribute__((__unused__));
static int *get_echo_int_3_i_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_3_i_to_1;
  case 2:
    return &echo_int_3_i_to_2;
  default:
    (void)0;
    abort();
  }
}
static char echo_int_3_j_to_1;
static char echo_int_3_j_to_2;
static char *get_echo_int_3_j_to(void) __attribute__((__unused__));
static char *get_echo_int_3_j_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_3_j_to_1;
  case 2:
    return &echo_int_3_j_to_2;
  default:
    (void)0;
    abort();
  }
}
extern void RPCTo_increment_64(uint64_t *x);
static unsigned int
increment_64_unmarshal_inputs_x(unsigned int _camkes_size_433,
                                unsigned int _camkes_offset_434, uint64_t *x) {
  void *_camkes_buffer_base_435 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_434 + sizeof(*x) > _camkes_size_433))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(x, _camkes_buffer_base_435 + _camkes_offset_434, sizeof(*x));
  _camkes_offset_434 += sizeof(*x);
  return _camkes_offset_434;
}
static int increment_64_unmarshal_inputs(unsigned int _camkes_size_436,
                                         uint64_t *x) {
  unsigned int _camkes_length_437 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_438 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_437 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_437 =
      increment_64_unmarshal_inputs_x(_camkes_size_436, _camkes_length_437, x);
  if (_camkes_length_437 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_437) +
             ((_camkes_length_437) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_437) % (sizeof(seL4_Word)))))) !=
            _camkes_size_436))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
increment_64_marshal_outputs_x(unsigned int _camkes_offset_440, uint64_t *x) {
  void *_camkes_buffer_base_441 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_440 + sizeof(*x) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_441 + _camkes_offset_440, x, sizeof(*x));
  _camkes_offset_440 += sizeof(*x);
  return _camkes_offset_440;
}
static unsigned int increment_64_marshal_outputs(uint64_t *x) {
  unsigned int _camkes_length_443 = 0;
  /* Marshal output parameters. */
  _camkes_length_443 = increment_64_marshal_outputs_x(_camkes_length_443, x);
  if (_camkes_length_443 == 0xffffffffU) {
    return 0xffffffffU;
  }
  (void)0;
  return _camkes_length_443;
}
static uint64_t increment_64_x_to_1;
static uint64_t increment_64_x_to_2;
static uint64_t *get_increment_64_x_to(void) __attribute__((__unused__));
static uint64_t *get_increment_64_x_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &increment_64_x_to_1;
  case 2:
    return &increment_64_x_to_2;
  default:
    (void)0;
    abort();
  }
}
extern int RPCTo_echo_int_4(int i, int64_t j, int k, int l);
static unsigned int
echo_int_4_unmarshal_inputs_i(unsigned int _camkes_size_444,
                              unsigned int _camkes_offset_445, int *i) {
  void *_camkes_buffer_base_446 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_445 + sizeof(*i) > _camkes_size_444))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(i, _camkes_buffer_base_446 + _camkes_offset_445, sizeof(*i));
  _camkes_offset_445 += sizeof(*i);
  return _camkes_offset_445;
}
static unsigned int
echo_int_4_unmarshal_inputs_j(unsigned int _camkes_size_447,
                              unsigned int _camkes_offset_448, int64_t *j) {
  void *_camkes_buffer_base_449 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_448 + sizeof(*j) > _camkes_size_447))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(j, _camkes_buffer_base_449 + _camkes_offset_448, sizeof(*j));
  _camkes_offset_448 += sizeof(*j);
  return _camkes_offset_448;
}
static unsigned int
echo_int_4_unmarshal_inputs_k(unsigned int _camkes_size_450,
                              unsigned int _camkes_offset_451, int *k) {
  void *_camkes_buffer_base_452 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_451 + sizeof(*k) > _camkes_size_450))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(k, _camkes_buffer_base_452 + _camkes_offset_451, sizeof(*k));
  _camkes_offset_451 += sizeof(*k);
  return _camkes_offset_451;
}
static unsigned int
echo_int_4_unmarshal_inputs_l(unsigned int _camkes_size_453,
                              unsigned int _camkes_offset_454, int *l) {
  void *_camkes_buffer_base_455 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  do {
    (void)0;
    if (!(!(_camkes_offset_454 + sizeof(*l) > _camkes_size_453))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(l, _camkes_buffer_base_455 + _camkes_offset_454, sizeof(*l));
  _camkes_offset_454 += sizeof(*l);
  return _camkes_offset_454;
}
static int echo_int_4_unmarshal_inputs(unsigned int _camkes_size_456, int *i,
                                       int64_t *j, int *k, int *l) {
  unsigned int _camkes_length_457 __attribute__((__unused__)) = 0;
  void *_camkes_buffer_base_458 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Step over the method index. */
  _camkes_length_457 += sizeof(uint8_t);
  /* Unmarshal input parameters. */
  _camkes_length_457 =
      echo_int_4_unmarshal_inputs_i(_camkes_size_456, _camkes_length_457, i);
  if (_camkes_length_457 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_457 =
      echo_int_4_unmarshal_inputs_j(_camkes_size_456, _camkes_length_457, j);
  if (_camkes_length_457 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_457 =
      echo_int_4_unmarshal_inputs_k(_camkes_size_456, _camkes_length_457, k);
  if (_camkes_length_457 == 0xffffffffU) {
    return -1;
  }
  _camkes_length_457 =
      echo_int_4_unmarshal_inputs_l(_camkes_size_456, _camkes_length_457, l);
  if (_camkes_length_457 == 0xffffffffU) {
    return -1;
  }
  do {
    (void)0;
    if (!(!(((_camkes_length_457) +
             ((_camkes_length_457) % (sizeof(seL4_Word)) == 0
                  ? 0
                  : ((sizeof(seL4_Word)) -
                     ((_camkes_length_457) % (sizeof(seL4_Word)))))) !=
            _camkes_size_456))) {
      for (;;)
        ;
    }
  } while (0);
  return 0;
}
static unsigned int
echo_int_4_marshal_outputs__camkes_ret_fn_459(unsigned int _camkes_offset_460,
                                              int *_camkes_return_461) {
  void *_camkes_buffer_base_462 __attribute__((__unused__)) =
      (void *)(((void *)&seL4_GetIPCBuffer()->msg[0]));
  /* Marshal the return value. */
  do {
    (void)0;
    if (!(!(_camkes_offset_460 + sizeof(*_camkes_return_461) >
            seL4_MsgMaxLength * sizeof(seL4_Word)))) {
      for (;;)
        ;
    }
  } while (0);
  memcpy(_camkes_buffer_base_462 + _camkes_offset_460, _camkes_return_461,
         sizeof(*_camkes_return_461));
  _camkes_offset_460 += sizeof(*_camkes_return_461);
  return _camkes_offset_460;
}
static unsigned int echo_int_4_marshal_outputs(int *_camkes_return_463) {
  unsigned int _camkes_length_464 = 0;
  _camkes_length_464 = echo_int_4_marshal_outputs__camkes_ret_fn_459(
      _camkes_length_464, _camkes_return_463);
  if (_camkes_length_464 == 0xffffffffU) {
    return 0xffffffffU;
  }
  /* Marshal output parameters. */
  (void)0;
  return _camkes_length_464;
}
static int echo_int_4_ret_to_1;
static int echo_int_4_ret_to_2;
static int *get_echo_int_4_ret_to(void) __attribute__((__unused__));
static int *get_echo_int_4_ret_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_ret_to_1;
  case 2:
    return &echo_int_4_ret_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_4_i_to_1;
static int echo_int_4_i_to_2;
static int *get_echo_int_4_i_to(void) __attribute__((__unused__));
static int *get_echo_int_4_i_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_i_to_1;
  case 2:
    return &echo_int_4_i_to_2;
  default:
    (void)0;
    abort();
  }
}
static int64_t echo_int_4_j_to_1;
static int64_t echo_int_4_j_to_2;
static int64_t *get_echo_int_4_j_to(void) __attribute__((__unused__));
static int64_t *get_echo_int_4_j_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_j_to_1;
  case 2:
    return &echo_int_4_j_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_4_k_to_1;
static int echo_int_4_k_to_2;
static int *get_echo_int_4_k_to(void) __attribute__((__unused__));
static int *get_echo_int_4_k_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_k_to_1;
  case 2:
    return &echo_int_4_k_to_2;
  default:
    (void)0;
    abort();
  }
}
static int echo_int_4_l_to_1;
static int echo_int_4_l_to_2;
static int *get_echo_int_4_l_to(void) __attribute__((__unused__));
static int *get_echo_int_4_l_to(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &echo_int_4_l_to_1;
  case 2:
    return &echo_int_4_l_to_2;
  default:
    (void)0;
    abort();
  }
}
static uint8_t _camkes_call_tls_var_to_465_1;
static uint8_t _camkes_call_tls_var_to_465_2;
static uint8_t *get__camkes_call_tls_var_to_465(void)
    __attribute__((__unused__));
static uint8_t *get__camkes_call_tls_var_to_465(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &_camkes_call_tls_var_to_465_1;
  case 2:
    return &_camkes_call_tls_var_to_465_2;
  default:
    (void)0;
    abort();
  }
}
int RPCTo__run(void) {
  while (1) {
    seL4_MessageInfo_t _camkes_info_466 = seL4_Wait(6, ((void *)0));
    unsigned int _camkes_size_467 =
        seL4_MessageInfo_get_length(_camkes_info_466) * sizeof(seL4_Word);
    (void)0;
    void *_camkes_buffer_468 __attribute__((__unused__)) =
        ((void *)&seL4_GetIPCBuffer()->msg[0]);
    uint8_t _camkes_call_469 __attribute__((__unused__));
    uint8_t *_camkes_call_ptr_470 = (get__camkes_call_tls_var_to_465());
    do {
      (void)0;
      if (!(!(sizeof(*_camkes_call_ptr_470) > _camkes_size_467))) {
        for (;;)
          ;
      }
    } while (0);
    memcpy(_camkes_call_ptr_470, _camkes_buffer_468,
           sizeof(*_camkes_call_ptr_470));
    switch (*_camkes_call_ptr_470) {
    case 0: {
      /* echo_int */
      int i __attribute__((__unused__));
      int *i_ptr = (get_echo_int_i_to());
      /* Unmarshal parameters */
      int _camkes_error_471 =
          echo_int_unmarshal_inputs(_camkes_size_467, i_ptr);
      if (__builtin_expect(!!(_camkes_error_471 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_472 __attribute__((__unused__));
      int *_camkes_ret_ptr_474 = (get_echo_int_ret_to());
      *_camkes_ret_ptr_474 = RPCTo_echo_int(*i_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_475 =
          echo_int_marshal_outputs(_camkes_ret_ptr_474);
      if (__builtin_expect(!!(_camkes_length_475 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_475) +
                     ((_camkes_length_475) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_475) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 1: {
      /* echo_int_1 */
      int i __attribute__((__unused__));
      int *i_ptr = (get_echo_int_1_i_to());
      unsigned int j __attribute__((__unused__));
      unsigned int *j_ptr = (get_echo_int_1_j_to());
      int32_t k __attribute__((__unused__));
      int32_t *k_ptr = (get_echo_int_1_k_to());
      uint32_t l __attribute__((__unused__));
      uint32_t *l_ptr = (get_echo_int_1_l_to());
      /* Unmarshal parameters */
      int _camkes_error_476 = echo_int_1_unmarshal_inputs(
          _camkes_size_467, i_ptr, j_ptr, k_ptr, l_ptr);
      if (__builtin_expect(!!(_camkes_error_476 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_477 __attribute__((__unused__));
      int *_camkes_ret_ptr_479 = (get_echo_int_1_ret_to());
      *_camkes_ret_ptr_479 = RPCTo_echo_int_1(*i_ptr, *j_ptr, *k_ptr, *l_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_480 =
          echo_int_1_marshal_outputs(_camkes_ret_ptr_479);
      if (__builtin_expect(!!(_camkes_length_480 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_480) +
                     ((_camkes_length_480) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_480) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 2: {
      /* echo_parameter */
      int pin __attribute__((__unused__));
      int *pin_ptr = (get_echo_parameter_pin_to());
      int pout __attribute__((__unused__));
      int *pout_ptr = (get_echo_parameter_pout_to());
      /* Unmarshal parameters */
      int _camkes_error_481 =
          echo_parameter_unmarshal_inputs(_camkes_size_467, pin_ptr);
      if (__builtin_expect(!!(_camkes_error_481 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_482 __attribute__((__unused__));
      int *_camkes_ret_ptr_484 = (get_echo_parameter_ret_to());
      *_camkes_ret_ptr_484 = RPCTo_echo_parameter(*pin_ptr, pout_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_485 =
          echo_parameter_marshal_outputs(_camkes_ret_ptr_484, pout_ptr);
      if (__builtin_expect(!!(_camkes_length_485 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_485) +
                     ((_camkes_length_485) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_485) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 3: {
      /* echo_char */
      char i __attribute__((__unused__));
      char *i_ptr = (get_echo_char_i_to());
      /* Unmarshal parameters */
      int _camkes_error_486 =
          echo_char_unmarshal_inputs(_camkes_size_467, i_ptr);
      if (__builtin_expect(!!(_camkes_error_486 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_487 __attribute__((__unused__));
      int *_camkes_ret_ptr_489 = (get_echo_char_ret_to());
      *_camkes_ret_ptr_489 = RPCTo_echo_char(*i_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_490 =
          echo_char_marshal_outputs(_camkes_ret_ptr_489);
      if (__builtin_expect(!!(_camkes_length_490 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_490) +
                     ((_camkes_length_490) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_490) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 4: {
      /* increment_char */
      char x __attribute__((__unused__));
      char *x_ptr = (get_increment_char_x_to());
      /* Unmarshal parameters */
      int _camkes_error_491 =
          increment_char_unmarshal_inputs(_camkes_size_467, x_ptr);
      if (__builtin_expect(!!(_camkes_error_491 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      RPCTo_increment_char(x_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_495 = increment_char_marshal_outputs(x_ptr);
      if (__builtin_expect(!!(_camkes_length_495 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_495) +
                     ((_camkes_length_495) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_495) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 5: {
      /* increment_parameter */
      int x __attribute__((__unused__));
      int *x_ptr = (get_increment_parameter_x_to());
      /* Unmarshal parameters */
      int _camkes_error_496 =
          increment_parameter_unmarshal_inputs(_camkes_size_467, x_ptr);
      if (__builtin_expect(!!(_camkes_error_496 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      RPCTo_increment_parameter(x_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_500 =
          increment_parameter_marshal_outputs(x_ptr);
      if (__builtin_expect(!!(_camkes_length_500 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_500) +
                     ((_camkes_length_500) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_500) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 6: {
      /* echo_int_2 */
      int i __attribute__((__unused__));
      int *i_ptr = (get_echo_int_2_i_to());
      int j __attribute__((__unused__));
      int *j_ptr = (get_echo_int_2_j_to());
      /* Unmarshal parameters */
      int _camkes_error_501 =
          echo_int_2_unmarshal_inputs(_camkes_size_467, i_ptr, j_ptr);
      if (__builtin_expect(!!(_camkes_error_501 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_502 __attribute__((__unused__));
      int *_camkes_ret_ptr_504 = (get_echo_int_2_ret_to());
      *_camkes_ret_ptr_504 = RPCTo_echo_int_2(*i_ptr, *j_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_505 =
          echo_int_2_marshal_outputs(_camkes_ret_ptr_504);
      if (__builtin_expect(!!(_camkes_length_505 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_505) +
                     ((_camkes_length_505) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_505) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 7: {
      /* echo_int_3 */
      int i __attribute__((__unused__));
      int *i_ptr = (get_echo_int_3_i_to());
      char j __attribute__((__unused__));
      char *j_ptr = (get_echo_int_3_j_to());
      /* Unmarshal parameters */
      int _camkes_error_506 =
          echo_int_3_unmarshal_inputs(_camkes_size_467, i_ptr, j_ptr);
      if (__builtin_expect(!!(_camkes_error_506 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_507 __attribute__((__unused__));
      int *_camkes_ret_ptr_509 = (get_echo_int_3_ret_to());
      *_camkes_ret_ptr_509 = RPCTo_echo_int_3(*i_ptr, *j_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_510 =
          echo_int_3_marshal_outputs(_camkes_ret_ptr_509);
      if (__builtin_expect(!!(_camkes_length_510 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_510) +
                     ((_camkes_length_510) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_510) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 8: {
      /* increment_64 */
      uint64_t x __attribute__((__unused__));
      uint64_t *x_ptr = (get_increment_64_x_to());
      /* Unmarshal parameters */
      int _camkes_error_511 =
          increment_64_unmarshal_inputs(_camkes_size_467, x_ptr);
      if (__builtin_expect(!!(_camkes_error_511 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      RPCTo_increment_64(x_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_515 = increment_64_marshal_outputs(x_ptr);
      if (__builtin_expect(!!(_camkes_length_515 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_515) +
                     ((_camkes_length_515) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_515) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    case 9: {
      /* echo_int_4 */
      int i __attribute__((__unused__));
      int *i_ptr = (get_echo_int_4_i_to());
      int64_t j __attribute__((__unused__));
      int64_t *j_ptr = (get_echo_int_4_j_to());
      int k __attribute__((__unused__));
      int *k_ptr = (get_echo_int_4_k_to());
      int l __attribute__((__unused__));
      int *l_ptr = (get_echo_int_4_l_to());
      /* Unmarshal parameters */
      int _camkes_error_516 = echo_int_4_unmarshal_inputs(
          _camkes_size_467, i_ptr, j_ptr, k_ptr, l_ptr);
      if (__builtin_expect(!!(_camkes_error_516 != 0), 0)) {
        /* Error in unmarshalling; return to event loop. */
        continue;
      }
      /* Call the implementation */
      /*_ set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
      int _camkes_ret_517 __attribute__((__unused__));
      int *_camkes_ret_ptr_519 = (get_echo_int_4_ret_to());
      *_camkes_ret_ptr_519 = RPCTo_echo_int_4(*i_ptr, *j_ptr, *k_ptr, *l_ptr);
      /* Marshal the response */
      unsigned int _camkes_length_520 =
          echo_int_4_marshal_outputs(_camkes_ret_ptr_519);
      if (__builtin_expect(!!(_camkes_length_520 == 0xffffffffU), 0)) {
        /* Error occurred in unmarshalling; return to event loop. */
        continue;
      }
      _camkes_info_466 = seL4_MessageInfo_new(
          0, 0, 0,
          /* length */
                    ((_camkes_length_520) +
                     ((_camkes_length_520) % (sizeof(seL4_Word)) == 0
                          ? 0
                          : ((sizeof(seL4_Word)) -
                             ((_camkes_length_520) % (sizeof(seL4_Word)))))) /
                    sizeof(seL4_Word));
      /* Send the response */
      seL4_Send(6, _camkes_info_466);
      break;
    }
    default: {
      do {
        (void)0;
        if (!(0)) {
          for (;;)
            ;
        }
      } while (0);
    }
    }
  }
  do {
    (void)0;
    __builtin_unreachable();
  } while (0);
}
