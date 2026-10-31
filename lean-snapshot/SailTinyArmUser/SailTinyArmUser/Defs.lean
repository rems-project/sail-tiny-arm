import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

namespace SailTinyArmUser

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive SecurityState where | SS_NonSecure | SS_Root | SS_Realm | SS_Secure
  deriving BEq, Inhabited, Repr
  open SecurityState

abbrev PARTIDtype := (BitVec 16)

abbrev PMGtype := (BitVec 8)

inductive PARTIDspaceType where | PIdSpace_Secure | PIdSpace_Root | PIdSpace_Realm | PIdSpace_NonSecure
  deriving BEq, Inhabited, Repr
  open PARTIDspaceType

structure MPAMinfo where
  mpam_sp : PARTIDspaceType
  partid : PARTIDtype
  pmg : PMGtype
  deriving BEq, Inhabited, Repr

inductive AccessType where | AccessType_IFETCH | AccessType_GPR | AccessType_ASIMD | AccessType_SVE | AccessType_SME | AccessType_IC | AccessType_DC | AccessType_DCZero | AccessType_AT | AccessType_NV2 | AccessType_SPE | AccessType_GCS | AccessType_GPTW | AccessType_TTW
  deriving BEq, Inhabited, Repr
  open AccessType

inductive VARange where | VARange_LOWER | VARange_UPPER
  deriving BEq, Inhabited, Repr
  open VARange

inductive MemAtomicOp where | MemAtomicOp_GCSSS1 | MemAtomicOp_ADD | MemAtomicOp_BIC | MemAtomicOp_EOR | MemAtomicOp_ORR | MemAtomicOp_SMAX | MemAtomicOp_SMIN | MemAtomicOp_UMAX | MemAtomicOp_UMIN | MemAtomicOp_SWP | MemAtomicOp_CAS
  deriving BEq, Inhabited, Repr
  open MemAtomicOp

inductive CacheOp where | CacheOp_Clean | CacheOp_Invalidate | CacheOp_CleanInvalidate
  deriving BEq, Inhabited, Repr
  open CacheOp

inductive CacheOpScope where | CacheOpScope_SetWay | CacheOpScope_PoU | CacheOpScope_PoC | CacheOpScope_PoE | CacheOpScope_PoP | CacheOpScope_PoDP | CacheOpScope_PoPA | CacheOpScope_ALLU | CacheOpScope_ALLUIS
  deriving BEq, Inhabited, Repr
  open CacheOpScope

inductive CacheType where | CacheType_Data | CacheType_Tag | CacheType_Data_Tag | CacheType_Instruction
  deriving BEq, Inhabited, Repr
  open CacheType

inductive CachePASpace where | CPAS_NonSecure | CPAS_Any | CPAS_RealmNonSecure | CPAS_Realm | CPAS_Root | CPAS_SecureNonSecure | CPAS_Secure
  deriving BEq, Inhabited, Repr
  open CachePASpace

structure AccessDescriptor where
  acctype : AccessType
  el : (BitVec 2)
  ss : SecurityState
  acqsc : Bool
  acqpc : Bool
  relsc : Bool
  limitedordered : Bool
  exclusive : Bool
  atomicop : Bool
  modop : MemAtomicOp
  nontemporal : Bool
  read : Bool
  write : Bool
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  pan : Bool
  transactional : Bool
  nonfault : Bool
  firstfault : Bool
  first : Bool
  contiguous : Bool
  streamingsve : Bool
  ls64 : Bool
  mops : Bool
  rcw : Bool
  rcws : Bool
  toplevel : Bool
  varange : VARange
  a32lsmd : Bool
  tagchecked : Bool
  tagaccess : Bool
  mpam : MPAMinfo
  deriving BEq, Inhabited, Repr

inductive MemType where | MemType_Normal | MemType_Device
  deriving BEq, Inhabited, Repr
  open MemType

inductive DeviceType where | DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE
  deriving BEq, Inhabited, Repr
  open DeviceType

structure MemAttrHints where
  attrs : (BitVec 2)
  hints : (BitVec 2)
  transient : Bool
  deriving BEq, Inhabited, Repr

inductive Shareability where | Shareability_NSH | Shareability_ISH | Shareability_OSH
  deriving BEq, Inhabited, Repr
  open Shareability

inductive MemTagType where | MemTag_Untagged | MemTag_AllocationTagged | MemTag_CanonicallyTagged
  deriving BEq, Inhabited, Repr
  open MemTagType

structure MemoryAttributes where
  memtype : MemType
  device : DeviceType
  inner : MemAttrHints
  outer : MemAttrHints
  shareability : Shareability
  tags : MemTagType
  notagaccess : Bool
  xs : (BitVec 1)
  deriving BEq, Inhabited, Repr

inductive PASpace where | PAS_NonSecure | PAS_Secure | PAS_Root | PAS_Realm
  deriving BEq, Inhabited, Repr
  open PASpace

structure FullAddress where
  paspace : PASpace
  address : (BitVec 56)
  deriving BEq, Inhabited, Repr

inductive GPCF where | GPCF_None | GPCF_AddressSize | GPCF_Walk | GPCF_EABT | GPCF_Fail
  deriving BEq, Inhabited, Repr
  open GPCF

structure GPCFRecord where
  gpf : GPCF
  level : Int
  deriving BEq, Inhabited, Repr

inductive Fault where | Fault_None | Fault_AccessFlag | Fault_Alignment | Fault_Background | Fault_Domain | Fault_Permission | Fault_Translation | Fault_AddressSize | Fault_SyncExternal | Fault_SyncExternalOnWalk | Fault_SyncParity | Fault_SyncParityOnWalk | Fault_GPCFOnWalk | Fault_GPCFOnOutput | Fault_AsyncParity | Fault_AsyncExternal | Fault_TagCheck | Fault_Debug | Fault_TLBConflict | Fault_BranchTarget | Fault_HWUpdateAccessFlag | Fault_Lockdown | Fault_Exclusive | Fault_ICacheMaint
  deriving BEq, Inhabited, Repr
  open Fault

inductive ErrorState where | ErrorState_UC | ErrorState_UEU | ErrorState_UEO | ErrorState_UER | ErrorState_CE | ErrorState_Uncategorized | ErrorState_IMPDEF
  deriving BEq, Inhabited, Repr
  open ErrorState

structure FaultRecord where
  statuscode : Fault
  access : AccessDescriptor
  ipaddress : FullAddress
  gpcf : GPCFRecord
  paddress : FullAddress
  gpcfs2walk : Bool
  s2fs1walk : Bool
  write : Bool
  s1tagnotdata : Bool
  tagaccess : Bool
  level : Int
  extflag : (BitVec 1)
  secondstage : Bool
  assuredonly : Bool
  toplevel : Bool
  overlay : Bool
  dirtybit : Bool
  domain : (BitVec 4)
  merrorstate : ErrorState
  debugmoe : (BitVec 4)
  deriving BEq, Inhabited, Repr

inductive MBReqDomain where | MBReqDomain_Nonshareable | MBReqDomain_InnerShareable | MBReqDomain_OuterShareable | MBReqDomain_FullSystem
  deriving BEq, Inhabited, Repr
  open MBReqDomain

inductive MBReqTypes where | MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All
  deriving BEq, Inhabited, Repr
  open MBReqTypes

structure CacheRecord where
  acctype : AccessType
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  regval : (BitVec 64)
  paddress : FullAddress
  vaddress : (BitVec 64)
  setnum : Int
  waynum : Int
  level : Int
  shareability : Shareability
  translated : Bool
  is_vmid_valid : Bool
  vmid : (BitVec 16)
  is_asid_valid : Bool
  asid : (BitVec 16)
  security : SecurityState
  cpas : CachePASpace
  deriving BEq, Inhabited, Repr

inductive Regime where | Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10
  deriving BEq, Inhabited, Repr
  open Regime

inductive TGx where | TGx_4KB | TGx_16KB | TGx_64KB
  deriving BEq, Inhabited, Repr
  open TGx

structure TLBContext where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  nG : (BitVec 1)
  ipaspace : PASpace
  includes_s1_name : Bool
  includes_s2_name : Bool
  includes_gpt_name : Bool
  ia : (BitVec 64)
  tg : TGx
  cnp : (BitVec 1)
  level : Int
  isd128 : Bool
  xs : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure AddressDescriptor where
  fault : FaultRecord
  memattrs : MemoryAttributes
  paddress : FullAddress
  tlbcontext : TLBContext
  s1assured : Bool
  s2fs1mro : Bool
  mecid : (BitVec 16)
  vaddress : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure TranslationStartInfo where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  va : (BitVec 64)
  cnp : (BitVec 1)
  accdesc : AccessDescriptor
  size : Int
  deriving BEq, Inhabited, Repr

inductive TLBILevel where | TLBILevel_Any | TLBILevel_Last
  deriving BEq, Inhabited, Repr
  open TLBILevel

inductive TLBIOp where | TLBIOp_DALL | TLBIOp_DASID | TLBIOp_DVA | TLBIOp_IALL | TLBIOp_IASID | TLBIOp_IVA | TLBIOp_ALL | TLBIOp_ASID | TLBIOp_IPAS2 | TLBIPOp_IPAS2 | TLBIOp_VAA | TLBIOp_VA | TLBIPOp_VAA | TLBIPOp_VA | TLBIOp_VMALL | TLBIOp_VMALLS12 | TLBIOp_RIPAS2 | TLBIPOp_RIPAS2 | TLBIOp_RVAA | TLBIOp_RVA | TLBIPOp_RVAA | TLBIPOp_RVA | TLBIOp_RPA | TLBIOp_PAALL
  deriving BEq, Inhabited, Repr
  open TLBIOp

inductive TLBIMemAttr where | TLBI_AllAttr | TLBI_ExcludeXS
  deriving BEq, Inhabited, Repr
  open TLBIMemAttr

structure TLBIRecord where
  op : TLBIOp
  from_aarch64 : Bool
  security : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  level : TLBILevel
  attr : TLBIMemAttr
  ipaspace : PASpace
  address : (BitVec 64)
  end_address_name : (BitVec 64)
  d64 : Bool
  d128 : Bool
  ttl : (BitVec 4)
  tg : (BitVec 2)
  deriving BEq, Inhabited, Repr

structure TLBIInfo where
  rec' : TLBIRecord
  shareability : Shareability
  deriving BEq, Inhabited, Repr

structure DxB where
  domain : MBReqDomain
  types : MBReqTypes
  nXS : Bool
  deriving BEq, Inhabited, Repr

inductive Barrier where
  | Barrier_DSB (_ : DxB)
  | Barrier_DMB (_ : DxB)
  | Barrier_ISB (_ : Unit)
  | Barrier_SSBB (_ : Unit)
  | Barrier_PSSBB (_ : Unit)
  | Barrier_SB (_ : Unit)
  deriving Inhabited, BEq, Repr
  open Barrier

abbrev reg_index := Nat

abbrev datasize := (BitVec 1)

abbrev addr_size  : Int := 64

abbrev addr_space := Unit

abbrev abort := Unit

inductive extend_type where | UXTB | UXTH | UXTW | UXTX | SXTB | SXTH | SXTW | SXTX
  deriving BEq, Inhabited, Repr
  open extend_type

inductive shift_type where | shift_LSL | shift_LSR | shift_ASR | shift_ROR
  deriving BEq, Inhabited, Repr
  open shift_type

inductive operand where
  | OperandRegExt (_ : (reg_index × extend_type × Nat))
  | OperandRegShift (_ : (reg_index × shift_type × Nat))
  | OperandImm (_ : (BitVec 64))
  deriving Inhabited, BEq, Repr
  open operand

inductive bitwise_op where | Eor | Or | And | AndSetFlags
  deriving BEq, Inhabited, Repr
  open bitwise_op

inductive cond where | EQ | NE | CS | CC | MI | PL | VS | VC | HI | LS | GE | LT | GT | LE | AL | NV
  deriving BEq, Inhabited, Repr
  open cond

inductive ast where
  | Load (_ : (Nat × reg_index × reg_index × operand × Bool × Bool × Bool))
  | Store (_ : (Nat × reg_index × reg_index × operand × Bool × (Option reg_index)))
  | AtomicRMW (_ : (Nat × reg_index × reg_index × reg_index × MemAtomicOp × Bool × Bool))
  | BitwiseLogic (_ : (datasize × bitwise_op × reg_index × reg_index × operand))
  | Movz (_ : (datasize × reg_index × (BitVec 16) × Nat))
  | BitfieldMove (_ : (datasize × Bool × reg_index × reg_index × (BitVec 6) × (BitVec 6)))
  | AddSub (_ : (datasize × (BitVec 1) × (BitVec 1) × reg_index × reg_index × operand))
  | DataMemoryBarrier (_ : (MBReqDomain × MBReqTypes))
  | DataSynchronizationBarrier (_ : (MBReqDomain × MBReqTypes))
  | InstructionSynchronizationBarrier (_ : Unit)
  | Nop (_ : Unit)
  | CompareAndBranch (_ : (datasize × reg_index × (BitVec 64) × Bool))
  | TestAndBranch (_ : (reg_index × Nat × (BitVec 64) × Bool))
  | Branch (_ : (BitVec 64))
  | ConditionalBranch (_ : ((BitVec 64) × cond))
  | PCRelativeAddress (_ : (Bool × reg_index × (BitVec 64)))
  | BranchRegister (_ : reg_index)
  deriving Inhabited, BEq, Repr
  open ast

inductive Register : Type where
  | SP_EL0
  | NZCV
  | R0
  | R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | R16
  | R17
  | R18
  | R19
  | R20
  | R21
  | R22
  | R23
  | R24
  | R25
  | R26
  | R27
  | R28
  | R29
  | R30
  | _PC
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .SP_EL0 => (BitVec 64)
  | .NZCV => (BitVec 4)
  | .R0 => (BitVec 64)
  | .R1 => (BitVec 64)
  | .R2 => (BitVec 64)
  | .R3 => (BitVec 64)
  | .R4 => (BitVec 64)
  | .R5 => (BitVec 64)
  | .R6 => (BitVec 64)
  | .R7 => (BitVec 64)
  | .R8 => (BitVec 64)
  | .R9 => (BitVec 64)
  | .R10 => (BitVec 64)
  | .R11 => (BitVec 64)
  | .R12 => (BitVec 64)
  | .R13 => (BitVec 64)
  | .R14 => (BitVec 64)
  | .R15 => (BitVec 64)
  | .R16 => (BitVec 64)
  | .R17 => (BitVec 64)
  | .R18 => (BitVec 64)
  | .R19 => (BitVec 64)
  | .R20 => (BitVec 64)
  | .R21 => (BitVec 64)
  | .R22 => (BitVec 64)
  | .R23 => (BitVec 64)
  | .R24 => (BitVec 64)
  | .R25 => (BitVec 64)
  | .R26 => (BitVec 64)
  | .R27 => (BitVec 64)
  | .R28 => (BitVec 64)
  | .R29 => (BitVec 64)
  | .R30 => (BitVec 64)
  | ._PC => (BitVec 64)

def mem_acc_is_explicit (acc : AccessDescriptor) : Bool :=
  (BEq.beq acc.acctype AccessType_GPR)

def mem_acc_is_ifetch (acc : AccessDescriptor) : Bool :=
  (BEq.beq acc.acctype AccessType_IFETCH)

def mem_acc_is_ttw (acc : AccessDescriptor) : Bool :=
  (BEq.beq acc.acctype AccessType_TTW)

def mem_acc_is_relaxed (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && ((! acc.acqpc) && ((! acc.acqsc) && (! acc.relsc))))

def mem_acc_is_rel_acq_rcpc (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && acc.acqpc)

def mem_acc_is_rel_acq_rcsc (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && (acc.acqsc || acc.relsc))

def mem_acc_is_standalone (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && ((! acc.exclusive) && (! acc.atomicop)))

def mem_acc_is_exclusive (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && acc.exclusive)

def mem_acc_is_atomic_rmw (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && acc.atomicop)

@[reducible]
instance : Arch where
  addr_size := addr_size
  addr_space := addr_space
  CHERI := false
  cap_size_log := 0
  register := Register
  register_type := RegisterType
  mem_acc := AccessDescriptor
  mem_acc_is_explicit := mem_acc_is_explicit
  mem_acc_is_ifetch := mem_acc_is_ifetch
  mem_acc_is_ttw := mem_acc_is_ttw
  mem_acc_is_relaxed := mem_acc_is_relaxed
  mem_acc_is_rel_acq_rcpc := mem_acc_is_rel_acq_rcpc
  mem_acc_is_rel_acq_rcsc := mem_acc_is_rel_acq_rcsc
  mem_acc_is_standalone := mem_acc_is_standalone
  mem_acc_is_exclusive := mem_acc_is_exclusive
  mem_acc_is_atomic_rmw := mem_acc_is_atomic_rmw
  trans_start := Unit
  trans_end := Unit
  abort := abort
  barrier := Barrier
  cache_op := Unit
  tlbi := Unit
  exn := Unit
  sys_reg_id := Unit

abbrev exception := Unit

abbrev SailM := PreSailM exception
abbrev SailME := PreSailME exception



instance : Inhabited (RegisterRef (BitVec 4)) where
  default := .Reg NZCV
instance : Inhabited (RegisterRef (BitVec 64)) where
  default := .Reg _PC