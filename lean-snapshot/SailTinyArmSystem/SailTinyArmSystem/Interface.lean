import SailTinyArmSystem.SailTinyArmSystem
import SailTinyArmSystem.Vector
import SailTinyArmSystem.ReadWriteV2

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

namespace SailTinyArmSystem

open ArchSem

namespace Functions

open shift_type
open option
open operand
open extend_type
open cond
open bitwise_op
open ast
open VARange
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open Shareability
open SecurityState
open Register
open Regime
open PASpace
open PARTIDspaceType
open MemType
open MemTagType
open MemAtomicOp
open MBReqTypes
open MBReqDomain
open GPCF
open Fault
open ErrorState
open DeviceType
open DescriptorType
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open Barrier
open AccessType

def addr_size' : Nat := 56

def base_AccessDescriptor (acctype : AccessType) : AccessDescriptor :=
  { acctype := acctype
    el := (BitVec.zero 2)
    ss := SS_NonSecure
    acqsc := false
    acqpc := false
    relsc := false
    limitedordered := false
    exclusive := false
    atomicop := false
    modop := MemAtomicOp_ADD
    nontemporal := false
    read := false
    write := false
    cacheop := CacheOp_Clean
    opscope := CacheOpScope_ALLU
    cachetype := CacheType_Data
    pan := false
    transactional := false
    nonfault := false
    firstfault := false
    first := false
    contiguous := false
    streamingsve := false
    ls64 := false
    mops := false
    rcw := false
    rcws := false
    toplevel := false
    varange := VARange_LOWER
    a32lsmd := false
    tagchecked := false
    tagaccess := false
    mpam := { mpam_sp := PIdSpace_NonSecure
              partid := 0x0000#16
              pmg := 0x00#8 } }

/-- Type quantifiers: k_ex29066_ : Bool, k_ex29065_ : Bool -/
def create_writeAccessDescriptor (release : Bool) (exclusive : Bool) : SailM AccessDescriptor := do
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with exclusive := exclusive }
  (pure { accdesc with el := ← readReg CurrentEL })

/-- Type quantifiers: k_ex29069_ : Bool, k_ex29068_ : Bool, k_ex29067_ : Bool -/
def create_readAccessDescriptor (acquire : Bool) (rcpc : Bool) (exclusive : Bool) : SailM AccessDescriptor := do
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with acqsc := (acquire && (! rcpc)) }
  let accdesc : AccessDescriptor := { accdesc with acqpc := (acquire && rcpc) }
  let accdesc : AccessDescriptor := { accdesc with exclusive := exclusive }
  (pure { accdesc with el := ← readReg CurrentEL })

/-- Type quantifiers: k_ex29071_ : Bool, k_ex29070_ : Bool -/
def create_RMWAccessDescriptor (modop : MemAtomicOp) (acquire : Bool) (release : Bool) : SailM AccessDescriptor := do
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with acqsc := acquire }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc ← (pure { accdesc with el := ← readReg CurrentEL })
  (pure { accdesc with modop := modop })

def create_iFetchAccessDescriptor (_ : Unit) : SailM AccessDescriptor := do
  let accdesc := (base_AccessDescriptor AccessType_IFETCH)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := false }
  (pure { accdesc with el := ← readReg CurrentEL })

def undefined_DescriptorType (_ : Unit) : SailM DescriptorType := do
  (internal_pick [DescriptorType_Table, DescriptorType_Leaf, DescriptorType_Invalid])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def DescriptorType_of_num (arg_ : Nat) : DescriptorType :=
  match arg_ with
  | 0 => DescriptorType_Table
  | 1 => DescriptorType_Leaf
  | _ => DescriptorType_Invalid

def num_of_DescriptorType (arg_ : DescriptorType) : Int :=
  match arg_ with
  | .DescriptorType_Table => 0
  | .DescriptorType_Leaf => 1
  | .DescriptorType_Invalid => 2

def base_FullAddress (_ : Unit) : FullAddress :=
  { paspace := PAS_NonSecure
    address := (BitVec.zero 56) }

def base_FaultRecord (accdesc : AccessDescriptor) : FaultRecord :=
  { statuscode := Fault_None
    access := accdesc
    ipaddress := (base_FullAddress ())
    gpcf := { gpf := GPCF_None
              level := 0 }
    paddress := (base_FullAddress ())
    gpcfs2walk := false
    s2fs1walk := false
    write := ((! accdesc.read) && accdesc.write)
    s1tagnotdata := false
    tagaccess := false
    level := 0
    extflag := (BitVec.zero 1)
    secondstage := false
    assuredonly := false
    toplevel := false
    overlay := false
    dirtybit := false
    domain := (BitVec.zero 4)
    merrorstate := ErrorState_UC
    debugmoe := (BitVec.zero 4) }

def base_MemoryAttributes (_ : Unit) : MemoryAttributes :=
  { memtype := MemType_Normal
    device := DeviceType_GRE
    inner := { attrs := (BitVec.zero 2)
               hints := (BitVec.zero 2)
               transient := false }
    outer := { attrs := (BitVec.zero 2)
               hints := (BitVec.zero 2)
               transient := false }
    shareability := Shareability_ISH
    tags := MemTag_Untagged
    notagaccess := false
    xs := (BitVec.zero 1) }

def base_TLBContext (_ : Unit) : TLBContext :=
  { ss := SS_NonSecure
    regime := Regime_EL10
    vmid := (BitVec.zero 16)
    asid := (BitVec.zero 16)
    nG := (BitVec.zero 1)
    ipaspace := PAS_NonSecure
    includes_s1_name := false
    includes_s2_name := false
    includes_gpt_name := false
    ia := (BitVec.zero 64)
    tg := TGx_4KB
    cnp := (BitVec.zero 1)
    level := 0
    isd128 := false
    xs := (BitVec.zero 1) }

def base_AddressDescriptor (accdesc : AccessDescriptor) : AddressDescriptor :=
  { fault := (base_FaultRecord accdesc)
    memattrs := (base_MemoryAttributes ())
    paddress := (base_FullAddress ())
    tlbcontext := (base_TLBContext ())
    s1assured := false
    s2fs1mro := false
    mecid := (BitVec.zero 16)
    vaddress := (BitVec.zero 64) }

def base_TLBIRecord (op : TLBIOp) : TLBIRecord :=
  { op := op
    from_aarch64 := true
    security := SS_NonSecure
    regime := Regime_EL10
    vmid := 0x0000#16
    asid := 0x0000#16
    level := TLBILevel_Any
    attr := TLBI_AllAttr
    ipaspace := PAS_NonSecure
    address := (BitVec.zero 64)
    end_address_name := (BitVec.zero 64)
    d64 := true
    d128 := false
    ttl := 0b0000#4
    tg := 0b00#2 }

def addr_space_def := PAS_NonSecure

/-- Type quantifiers: N : Nat, N > 0 -/
def read_memory (N : Nat) (addr : (BitVec 56)) (accdesc : AccessDescriptor) : SailM (BitVec (8 * N)) := do
  let accdesc' := accdesc
  let accdesc' : AccessDescriptor := { accdesc' with relsc := false }
  let req : (Mem_request N 0 addr_size addr_space AccessDescriptor) :=
    { access_kind := accdesc'
      address := (Sail.BitVec.truncate addr addr_size')
      address_space := addr_space_def
      size := N
      num_tag := 0 }
  match (← (sail_mem_read req)) with
  | .Ok (bytes, _) => (pure (from_bytes_le (n := N) bytes))
  | .Err _e => throw Error.Exit

def iFetch (addr : (BitVec 56)) (accdesc : AccessDescriptor) : SailM (BitVec 32) := do
  (read_memory 4 addr accdesc)

/-- Type quantifiers: N : Nat, N > 0 -/
def rMem (N : Nat) (addr : (BitVec 56)) (accdesc : AccessDescriptor) : SailM (BitVec (8 * N)) := do
  (read_memory N addr accdesc)

def wMem_Addr (addr : (BitVec 56)) : Unit :=
  (sail_address_announce 64 (Sail.BitVec.zeroExtend addr 64))

/-- Type quantifiers: N : Nat, N > 0 -/
def wMem (N : Nat) (addr : (BitVec 56)) (value : (BitVec (8 * N))) (accdesc : AccessDescriptor) : SailM Unit := do
  let accdesc' := accdesc
  let accdesc' : AccessDescriptor := { accdesc' with acqsc := false }
  let accdesc' : AccessDescriptor := { accdesc' with acqpc := false }
  let req : (Mem_request N 0 addr_size addr_space AccessDescriptor) :=
    { access_kind := accdesc'
      address := (Sail.BitVec.truncate addr addr_size')
      address_space := addr_space_def
      size := N
      num_tag := 0 }
  match (← (sail_mem_write req (to_bytes_le (n := N) value) #v[])) with
  | .Ok _ => (pure ())
  | .Err _ => throw Error.Exit

def dataMemoryBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  (sail_barrier
    (Barrier_DMB
      { domain := domain
        types := types
        nXS := false }))

def dataSynchronizationBarrer (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  (sail_barrier
    (Barrier_DSB
      { domain := domain
        types := types
        nXS := false }))

def instructionSynchronizationBarrier (_ : Unit) : SailM Unit := do
  (sail_barrier (Barrier_ISB ()))

def reportTLBI (op : TLBIOp) (shareability : Shareability) (level : TLBILevel) (addr : (Option (BitVec 64))) (asid : (Option (BitVec 16))) : SailM Unit := do
  let r := (base_TLBIRecord op)
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord :=
    { r with address := match addr with
      | .some addr => addr
      | none => 0x0000000000000000#64 }
  let r : TLBIRecord :=
    { r with asid := match asid with
      | .some asid => asid
      | none => 0x0000#16 }
  (sail_tlbi
    { rec' := r
      shareability := shareability })

