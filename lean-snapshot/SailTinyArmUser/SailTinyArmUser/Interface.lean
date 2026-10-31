import SailTinyArmUser.SailTinyArmUser
import SailTinyArmUser.Vector
import SailTinyArmUser.Registers
import SailTinyArmUser.ReadWriteV2

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

namespace SailTinyArmUser

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
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open Barrier
open AccessType

def addr_size' : Nat := 64

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

/-- Type quantifiers: k_ex21919_ : Bool, k_ex21918_ : Bool -/
def create_writeAccessDescriptor (release : Bool) (exclusive : Bool) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with exclusive := exclusive }
  { accdesc with el := CurrentEL }

/-- Type quantifiers: k_ex21922_ : Bool, k_ex21921_ : Bool, k_ex21920_ : Bool -/
def create_readAccessDescriptor (acquire : Bool) (rcpc : Bool) (exclusive : Bool) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with acqsc := (acquire && (! rcpc)) }
  let accdesc : AccessDescriptor := { accdesc with acqpc := (acquire && rcpc) }
  let accdesc : AccessDescriptor := { accdesc with exclusive := exclusive }
  { accdesc with el := CurrentEL }

/-- Type quantifiers: k_ex21924_ : Bool, k_ex21923_ : Bool -/
def create_RMWAccessDescriptor (modop : MemAtomicOp) (acquire : Bool) (release : Bool) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with acqsc := acquire }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with el := CurrentEL }
  { accdesc with modop := modop }

def create_iFetchAccessDescriptor (_ : Unit) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_IFETCH)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := false }
  { accdesc with el := CurrentEL }

def addr_space_def := ()

/-- Type quantifiers: N : Nat, N > 0 -/
def read_memory (N : Nat) (addr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM (BitVec (8 * N)) := do
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

def iFetch (addr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM (BitVec 32) := do
  (read_memory 4 addr accdesc)

/-- Type quantifiers: N : Nat, N > 0 -/
def rMem (N : Nat) (addr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM (BitVec (8 * N)) := do
  (read_memory N addr accdesc)

def wMem_Addr (addr : (BitVec 64)) : Unit :=
  (sail_address_announce 64 (Sail.BitVec.zeroExtend addr 64))

/-- Type quantifiers: N : Nat, N > 0 -/
def wMem (N : Nat) (addr : (BitVec 64)) (value : (BitVec (8 * N))) (accdesc : AccessDescriptor) : SailM Unit := do
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

