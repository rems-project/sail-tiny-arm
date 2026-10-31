import Sail
import SailTinyArmUser.Defs
import SailTinyArmUser.SpecializationArchSem
import SailTinyArmUser.FakeReal

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

def undefined_SecurityState (_ : Unit) : SailM SecurityState := do
  (internal_pick [SS_NonSecure, SS_Root, SS_Realm, SS_Secure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def SecurityState_of_num (arg_ : Nat) : SecurityState :=
  match arg_ with
  | 0 => SS_NonSecure
  | 1 => SS_Root
  | 2 => SS_Realm
  | _ => SS_Secure

def num_of_SecurityState (arg_ : SecurityState) : Int :=
  match arg_ with
  | .SS_NonSecure => 0
  | .SS_Root => 1
  | .SS_Realm => 2
  | .SS_Secure => 3

def undefined_PARTIDspaceType (_ : Unit) : SailM PARTIDspaceType := do
  (internal_pick [PIdSpace_Secure, PIdSpace_Root, PIdSpace_Realm, PIdSpace_NonSecure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PARTIDspaceType_of_num (arg_ : Nat) : PARTIDspaceType :=
  match arg_ with
  | 0 => PIdSpace_Secure
  | 1 => PIdSpace_Root
  | 2 => PIdSpace_Realm
  | _ => PIdSpace_NonSecure

def num_of_PARTIDspaceType (arg_ : PARTIDspaceType) : Int :=
  match arg_ with
  | .PIdSpace_Secure => 0
  | .PIdSpace_Root => 1
  | .PIdSpace_Realm => 2
  | .PIdSpace_NonSecure => 3

def undefined_MPAMinfo (_ : Unit) : SailM MPAMinfo := do
  (pure { mpam_sp := ← (undefined_PARTIDspaceType ())
          partid := ← (undefined_bitvector 16)
          pmg := ← (undefined_bitvector 8) })

def undefined_AccessType (_ : Unit) : SailM AccessType := do
  (internal_pick
    [AccessType_IFETCH, AccessType_GPR, AccessType_ASIMD, AccessType_SVE, AccessType_SME, AccessType_IC, AccessType_DC, AccessType_DCZero, AccessType_AT, AccessType_NV2, AccessType_SPE, AccessType_GCS, AccessType_GPTW, AccessType_TTW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 13 -/
def AccessType_of_num (arg_ : Nat) : AccessType :=
  match arg_ with
  | 0 => AccessType_IFETCH
  | 1 => AccessType_GPR
  | 2 => AccessType_ASIMD
  | 3 => AccessType_SVE
  | 4 => AccessType_SME
  | 5 => AccessType_IC
  | 6 => AccessType_DC
  | 7 => AccessType_DCZero
  | 8 => AccessType_AT
  | 9 => AccessType_NV2
  | 10 => AccessType_SPE
  | 11 => AccessType_GCS
  | 12 => AccessType_GPTW
  | _ => AccessType_TTW

def num_of_AccessType (arg_ : AccessType) : Int :=
  match arg_ with
  | .AccessType_IFETCH => 0
  | .AccessType_GPR => 1
  | .AccessType_ASIMD => 2
  | .AccessType_SVE => 3
  | .AccessType_SME => 4
  | .AccessType_IC => 5
  | .AccessType_DC => 6
  | .AccessType_DCZero => 7
  | .AccessType_AT => 8
  | .AccessType_NV2 => 9
  | .AccessType_SPE => 10
  | .AccessType_GCS => 11
  | .AccessType_GPTW => 12
  | .AccessType_TTW => 13

def undefined_VARange (_ : Unit) : SailM VARange := do
  (internal_pick [VARange_LOWER, VARange_UPPER])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def VARange_of_num (arg_ : Nat) : VARange :=
  match arg_ with
  | 0 => VARange_LOWER
  | _ => VARange_UPPER

def num_of_VARange (arg_ : VARange) : Int :=
  match arg_ with
  | .VARange_LOWER => 0
  | .VARange_UPPER => 1

def undefined_MemAtomicOp (_ : Unit) : SailM MemAtomicOp := do
  (internal_pick
    [MemAtomicOp_GCSSS1, MemAtomicOp_ADD, MemAtomicOp_BIC, MemAtomicOp_EOR, MemAtomicOp_ORR, MemAtomicOp_SMAX, MemAtomicOp_SMIN, MemAtomicOp_UMAX, MemAtomicOp_UMIN, MemAtomicOp_SWP, MemAtomicOp_CAS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def MemAtomicOp_of_num (arg_ : Nat) : MemAtomicOp :=
  match arg_ with
  | 0 => MemAtomicOp_GCSSS1
  | 1 => MemAtomicOp_ADD
  | 2 => MemAtomicOp_BIC
  | 3 => MemAtomicOp_EOR
  | 4 => MemAtomicOp_ORR
  | 5 => MemAtomicOp_SMAX
  | 6 => MemAtomicOp_SMIN
  | 7 => MemAtomicOp_UMAX
  | 8 => MemAtomicOp_UMIN
  | 9 => MemAtomicOp_SWP
  | _ => MemAtomicOp_CAS

def num_of_MemAtomicOp (arg_ : MemAtomicOp) : Int :=
  match arg_ with
  | .MemAtomicOp_GCSSS1 => 0
  | .MemAtomicOp_ADD => 1
  | .MemAtomicOp_BIC => 2
  | .MemAtomicOp_EOR => 3
  | .MemAtomicOp_ORR => 4
  | .MemAtomicOp_SMAX => 5
  | .MemAtomicOp_SMIN => 6
  | .MemAtomicOp_UMAX => 7
  | .MemAtomicOp_UMIN => 8
  | .MemAtomicOp_SWP => 9
  | .MemAtomicOp_CAS => 10

def undefined_CacheOp (_ : Unit) : SailM CacheOp := do
  (internal_pick [CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CacheOp_of_num (arg_ : Nat) : CacheOp :=
  match arg_ with
  | 0 => CacheOp_Clean
  | 1 => CacheOp_Invalidate
  | _ => CacheOp_CleanInvalidate

def num_of_CacheOp (arg_ : CacheOp) : Int :=
  match arg_ with
  | .CacheOp_Clean => 0
  | .CacheOp_Invalidate => 1
  | .CacheOp_CleanInvalidate => 2

def undefined_CacheOpScope (_ : Unit) : SailM CacheOpScope := do
  (internal_pick
    [CacheOpScope_SetWay, CacheOpScope_PoU, CacheOpScope_PoC, CacheOpScope_PoE, CacheOpScope_PoP, CacheOpScope_PoDP, CacheOpScope_PoPA, CacheOpScope_ALLU, CacheOpScope_ALLUIS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def CacheOpScope_of_num (arg_ : Nat) : CacheOpScope :=
  match arg_ with
  | 0 => CacheOpScope_SetWay
  | 1 => CacheOpScope_PoU
  | 2 => CacheOpScope_PoC
  | 3 => CacheOpScope_PoE
  | 4 => CacheOpScope_PoP
  | 5 => CacheOpScope_PoDP
  | 6 => CacheOpScope_PoPA
  | 7 => CacheOpScope_ALLU
  | _ => CacheOpScope_ALLUIS

def num_of_CacheOpScope (arg_ : CacheOpScope) : Int :=
  match arg_ with
  | .CacheOpScope_SetWay => 0
  | .CacheOpScope_PoU => 1
  | .CacheOpScope_PoC => 2
  | .CacheOpScope_PoE => 3
  | .CacheOpScope_PoP => 4
  | .CacheOpScope_PoDP => 5
  | .CacheOpScope_PoPA => 6
  | .CacheOpScope_ALLU => 7
  | .CacheOpScope_ALLUIS => 8

def undefined_CacheType (_ : Unit) : SailM CacheType := do
  (internal_pick [CacheType_Data, CacheType_Tag, CacheType_Data_Tag, CacheType_Instruction])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def CacheType_of_num (arg_ : Nat) : CacheType :=
  match arg_ with
  | 0 => CacheType_Data
  | 1 => CacheType_Tag
  | 2 => CacheType_Data_Tag
  | _ => CacheType_Instruction

def num_of_CacheType (arg_ : CacheType) : Int :=
  match arg_ with
  | .CacheType_Data => 0
  | .CacheType_Tag => 1
  | .CacheType_Data_Tag => 2
  | .CacheType_Instruction => 3

def undefined_CachePASpace (_ : Unit) : SailM CachePASpace := do
  (internal_pick
    [CPAS_NonSecure, CPAS_Any, CPAS_RealmNonSecure, CPAS_Realm, CPAS_Root, CPAS_SecureNonSecure, CPAS_Secure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def CachePASpace_of_num (arg_ : Nat) : CachePASpace :=
  match arg_ with
  | 0 => CPAS_NonSecure
  | 1 => CPAS_Any
  | 2 => CPAS_RealmNonSecure
  | 3 => CPAS_Realm
  | 4 => CPAS_Root
  | 5 => CPAS_SecureNonSecure
  | _ => CPAS_Secure

def num_of_CachePASpace (arg_ : CachePASpace) : Int :=
  match arg_ with
  | .CPAS_NonSecure => 0
  | .CPAS_Any => 1
  | .CPAS_RealmNonSecure => 2
  | .CPAS_Realm => 3
  | .CPAS_Root => 4
  | .CPAS_SecureNonSecure => 5
  | .CPAS_Secure => 6

def undefined_AccessDescriptor (_ : Unit) : SailM AccessDescriptor := do
  (pure { acctype := ← (undefined_AccessType ())
          el := ← (undefined_bitvector 2)
          ss := ← (undefined_SecurityState ())
          acqsc := ← (undefined_bool ())
          acqpc := ← (undefined_bool ())
          relsc := ← (undefined_bool ())
          limitedordered := ← (undefined_bool ())
          exclusive := ← (undefined_bool ())
          atomicop := ← (undefined_bool ())
          modop := ← (undefined_MemAtomicOp ())
          nontemporal := ← (undefined_bool ())
          read := ← (undefined_bool ())
          write := ← (undefined_bool ())
          cacheop := ← (undefined_CacheOp ())
          opscope := ← (undefined_CacheOpScope ())
          cachetype := ← (undefined_CacheType ())
          pan := ← (undefined_bool ())
          transactional := ← (undefined_bool ())
          nonfault := ← (undefined_bool ())
          firstfault := ← (undefined_bool ())
          first := ← (undefined_bool ())
          contiguous := ← (undefined_bool ())
          streamingsve := ← (undefined_bool ())
          ls64 := ← (undefined_bool ())
          mops := ← (undefined_bool ())
          rcw := ← (undefined_bool ())
          rcws := ← (undefined_bool ())
          toplevel := ← (undefined_bool ())
          varange := ← (undefined_VARange ())
          a32lsmd := ← (undefined_bool ())
          tagchecked := ← (undefined_bool ())
          tagaccess := ← (undefined_bool ())
          mpam := ← (undefined_MPAMinfo ()) })

def undefined_MemType (_ : Unit) : SailM MemType := do
  (internal_pick [MemType_Normal, MemType_Device])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def MemType_of_num (arg_ : Nat) : MemType :=
  match arg_ with
  | 0 => MemType_Normal
  | _ => MemType_Device

def num_of_MemType (arg_ : MemType) : Int :=
  match arg_ with
  | .MemType_Normal => 0
  | .MemType_Device => 1

def undefined_DeviceType (_ : Unit) : SailM DeviceType := do
  (internal_pick [DeviceType_GRE, DeviceType_nGRE, DeviceType_nGnRE, DeviceType_nGnRnE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def DeviceType_of_num (arg_ : Nat) : DeviceType :=
  match arg_ with
  | 0 => DeviceType_GRE
  | 1 => DeviceType_nGRE
  | 2 => DeviceType_nGnRE
  | _ => DeviceType_nGnRnE

def num_of_DeviceType (arg_ : DeviceType) : Int :=
  match arg_ with
  | .DeviceType_GRE => 0
  | .DeviceType_nGRE => 1
  | .DeviceType_nGnRE => 2
  | .DeviceType_nGnRnE => 3

def undefined_MemAttrHints (_ : Unit) : SailM MemAttrHints := do
  (pure { attrs := ← (undefined_bitvector 2)
          hints := ← (undefined_bitvector 2)
          transient := ← (undefined_bool ()) })

def undefined_Shareability (_ : Unit) : SailM Shareability := do
  (internal_pick [Shareability_NSH, Shareability_ISH, Shareability_OSH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Shareability_of_num (arg_ : Nat) : Shareability :=
  match arg_ with
  | 0 => Shareability_NSH
  | 1 => Shareability_ISH
  | _ => Shareability_OSH

def num_of_Shareability (arg_ : Shareability) : Int :=
  match arg_ with
  | .Shareability_NSH => 0
  | .Shareability_ISH => 1
  | .Shareability_OSH => 2

def undefined_MemTagType (_ : Unit) : SailM MemTagType := do
  (internal_pick [MemTag_Untagged, MemTag_AllocationTagged, MemTag_CanonicallyTagged])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemTagType_of_num (arg_ : Nat) : MemTagType :=
  match arg_ with
  | 0 => MemTag_Untagged
  | 1 => MemTag_AllocationTagged
  | _ => MemTag_CanonicallyTagged

def num_of_MemTagType (arg_ : MemTagType) : Int :=
  match arg_ with
  | .MemTag_Untagged => 0
  | .MemTag_AllocationTagged => 1
  | .MemTag_CanonicallyTagged => 2

def undefined_MemoryAttributes (_ : Unit) : SailM MemoryAttributes := do
  (pure { memtype := ← (undefined_MemType ())
          device := ← (undefined_DeviceType ())
          inner := ← (undefined_MemAttrHints ())
          outer := ← (undefined_MemAttrHints ())
          shareability := ← (undefined_Shareability ())
          tags := ← (undefined_MemTagType ())
          notagaccess := ← (undefined_bool ())
          xs := ← (undefined_bitvector 1) })

def undefined_PASpace (_ : Unit) : SailM PASpace := do
  (internal_pick [PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PASpace_of_num (arg_ : Nat) : PASpace :=
  match arg_ with
  | 0 => PAS_NonSecure
  | 1 => PAS_Secure
  | 2 => PAS_Root
  | _ => PAS_Realm

def num_of_PASpace (arg_ : PASpace) : Int :=
  match arg_ with
  | .PAS_NonSecure => 0
  | .PAS_Secure => 1
  | .PAS_Root => 2
  | .PAS_Realm => 3

def undefined_FullAddress (_ : Unit) : SailM FullAddress := do
  (pure { paspace := ← (undefined_PASpace ())
          address := ← (undefined_bitvector 56) })

def undefined_GPCF (_ : Unit) : SailM GPCF := do
  (internal_pick [GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def GPCF_of_num (arg_ : Nat) : GPCF :=
  match arg_ with
  | 0 => GPCF_None
  | 1 => GPCF_AddressSize
  | 2 => GPCF_Walk
  | 3 => GPCF_EABT
  | _ => GPCF_Fail

def num_of_GPCF (arg_ : GPCF) : Int :=
  match arg_ with
  | .GPCF_None => 0
  | .GPCF_AddressSize => 1
  | .GPCF_Walk => 2
  | .GPCF_EABT => 3
  | .GPCF_Fail => 4

def undefined_GPCFRecord (_ : Unit) : SailM GPCFRecord := do
  (pure { gpf := ← (undefined_GPCF ())
          level := ← (undefined_int ()) })

def undefined_Fault (_ : Unit) : SailM Fault := do
  (internal_pick
    [Fault_None, Fault_AccessFlag, Fault_Alignment, Fault_Background, Fault_Domain, Fault_Permission, Fault_Translation, Fault_AddressSize, Fault_SyncExternal, Fault_SyncExternalOnWalk, Fault_SyncParity, Fault_SyncParityOnWalk, Fault_GPCFOnWalk, Fault_GPCFOnOutput, Fault_AsyncParity, Fault_AsyncExternal, Fault_TagCheck, Fault_Debug, Fault_TLBConflict, Fault_BranchTarget, Fault_HWUpdateAccessFlag, Fault_Lockdown, Fault_Exclusive, Fault_ICacheMaint])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def Fault_of_num (arg_ : Nat) : Fault :=
  match arg_ with
  | 0 => Fault_None
  | 1 => Fault_AccessFlag
  | 2 => Fault_Alignment
  | 3 => Fault_Background
  | 4 => Fault_Domain
  | 5 => Fault_Permission
  | 6 => Fault_Translation
  | 7 => Fault_AddressSize
  | 8 => Fault_SyncExternal
  | 9 => Fault_SyncExternalOnWalk
  | 10 => Fault_SyncParity
  | 11 => Fault_SyncParityOnWalk
  | 12 => Fault_GPCFOnWalk
  | 13 => Fault_GPCFOnOutput
  | 14 => Fault_AsyncParity
  | 15 => Fault_AsyncExternal
  | 16 => Fault_TagCheck
  | 17 => Fault_Debug
  | 18 => Fault_TLBConflict
  | 19 => Fault_BranchTarget
  | 20 => Fault_HWUpdateAccessFlag
  | 21 => Fault_Lockdown
  | 22 => Fault_Exclusive
  | _ => Fault_ICacheMaint

def num_of_Fault (arg_ : Fault) : Int :=
  match arg_ with
  | .Fault_None => 0
  | .Fault_AccessFlag => 1
  | .Fault_Alignment => 2
  | .Fault_Background => 3
  | .Fault_Domain => 4
  | .Fault_Permission => 5
  | .Fault_Translation => 6
  | .Fault_AddressSize => 7
  | .Fault_SyncExternal => 8
  | .Fault_SyncExternalOnWalk => 9
  | .Fault_SyncParity => 10
  | .Fault_SyncParityOnWalk => 11
  | .Fault_GPCFOnWalk => 12
  | .Fault_GPCFOnOutput => 13
  | .Fault_AsyncParity => 14
  | .Fault_AsyncExternal => 15
  | .Fault_TagCheck => 16
  | .Fault_Debug => 17
  | .Fault_TLBConflict => 18
  | .Fault_BranchTarget => 19
  | .Fault_HWUpdateAccessFlag => 20
  | .Fault_Lockdown => 21
  | .Fault_Exclusive => 22
  | .Fault_ICacheMaint => 23

def undefined_ErrorState (_ : Unit) : SailM ErrorState := do
  (internal_pick
    [ErrorState_UC, ErrorState_UEU, ErrorState_UEO, ErrorState_UER, ErrorState_CE, ErrorState_Uncategorized, ErrorState_IMPDEF])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def ErrorState_of_num (arg_ : Nat) : ErrorState :=
  match arg_ with
  | 0 => ErrorState_UC
  | 1 => ErrorState_UEU
  | 2 => ErrorState_UEO
  | 3 => ErrorState_UER
  | 4 => ErrorState_CE
  | 5 => ErrorState_Uncategorized
  | _ => ErrorState_IMPDEF

def num_of_ErrorState (arg_ : ErrorState) : Int :=
  match arg_ with
  | .ErrorState_UC => 0
  | .ErrorState_UEU => 1
  | .ErrorState_UEO => 2
  | .ErrorState_UER => 3
  | .ErrorState_CE => 4
  | .ErrorState_Uncategorized => 5
  | .ErrorState_IMPDEF => 6

def undefined_FaultRecord (_ : Unit) : SailM FaultRecord := do
  (pure { statuscode := ← (undefined_Fault ())
          access := ← (undefined_AccessDescriptor ())
          ipaddress := ← (undefined_FullAddress ())
          gpcf := ← (undefined_GPCFRecord ())
          paddress := ← (undefined_FullAddress ())
          gpcfs2walk := ← (undefined_bool ())
          s2fs1walk := ← (undefined_bool ())
          write := ← (undefined_bool ())
          s1tagnotdata := ← (undefined_bool ())
          tagaccess := ← (undefined_bool ())
          level := ← (undefined_int ())
          extflag := ← (undefined_bitvector 1)
          secondstage := ← (undefined_bool ())
          assuredonly := ← (undefined_bool ())
          toplevel := ← (undefined_bool ())
          overlay := ← (undefined_bool ())
          dirtybit := ← (undefined_bool ())
          domain := ← (undefined_bitvector 4)
          merrorstate := ← (undefined_ErrorState ())
          debugmoe := ← (undefined_bitvector 4) })

def undefined_MBReqDomain (_ : Unit) : SailM MBReqDomain := do
  (internal_pick
    [MBReqDomain_Nonshareable, MBReqDomain_InnerShareable, MBReqDomain_OuterShareable, MBReqDomain_FullSystem])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def MBReqDomain_of_num (arg_ : Nat) : MBReqDomain :=
  match arg_ with
  | 0 => MBReqDomain_Nonshareable
  | 1 => MBReqDomain_InnerShareable
  | 2 => MBReqDomain_OuterShareable
  | _ => MBReqDomain_FullSystem

def num_of_MBReqDomain (arg_ : MBReqDomain) : Int :=
  match arg_ with
  | .MBReqDomain_Nonshareable => 0
  | .MBReqDomain_InnerShareable => 1
  | .MBReqDomain_OuterShareable => 2
  | .MBReqDomain_FullSystem => 3

def undefined_MBReqTypes (_ : Unit) : SailM MBReqTypes := do
  (internal_pick [MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MBReqTypes_of_num (arg_ : Nat) : MBReqTypes :=
  match arg_ with
  | 0 => MBReqTypes_Reads
  | 1 => MBReqTypes_Writes
  | _ => MBReqTypes_All

def num_of_MBReqTypes (arg_ : MBReqTypes) : Int :=
  match arg_ with
  | .MBReqTypes_Reads => 0
  | .MBReqTypes_Writes => 1
  | .MBReqTypes_All => 2

def undefined_CacheRecord (_ : Unit) : SailM CacheRecord := do
  (pure { acctype := ← (undefined_AccessType ())
          cacheop := ← (undefined_CacheOp ())
          opscope := ← (undefined_CacheOpScope ())
          cachetype := ← (undefined_CacheType ())
          regval := ← (undefined_bitvector 64)
          paddress := ← (undefined_FullAddress ())
          vaddress := ← (undefined_bitvector 64)
          setnum := ← (undefined_int ())
          waynum := ← (undefined_int ())
          level := ← (undefined_int ())
          shareability := ← (undefined_Shareability ())
          translated := ← (undefined_bool ())
          is_vmid_valid := ← (undefined_bool ())
          vmid := ← (undefined_bitvector 16)
          is_asid_valid := ← (undefined_bool ())
          asid := ← (undefined_bitvector 16)
          security := ← (undefined_SecurityState ())
          cpas := ← (undefined_CachePASpace ()) })

def undefined_Regime (_ : Unit) : SailM Regime := do
  (internal_pick [Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Regime_of_num (arg_ : Nat) : Regime :=
  match arg_ with
  | 0 => Regime_EL3
  | 1 => Regime_EL30
  | 2 => Regime_EL2
  | 3 => Regime_EL20
  | _ => Regime_EL10

def num_of_Regime (arg_ : Regime) : Int :=
  match arg_ with
  | .Regime_EL3 => 0
  | .Regime_EL30 => 1
  | .Regime_EL2 => 2
  | .Regime_EL20 => 3
  | .Regime_EL10 => 4

def undefined_TGx (_ : Unit) : SailM TGx := do
  (internal_pick [TGx_4KB, TGx_16KB, TGx_64KB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TGx_of_num (arg_ : Nat) : TGx :=
  match arg_ with
  | 0 => TGx_4KB
  | 1 => TGx_16KB
  | _ => TGx_64KB

def num_of_TGx (arg_ : TGx) : Int :=
  match arg_ with
  | .TGx_4KB => 0
  | .TGx_16KB => 1
  | .TGx_64KB => 2

def undefined_TLBContext (_ : Unit) : SailM TLBContext := do
  (pure { ss := ← (undefined_SecurityState ())
          regime := ← (undefined_Regime ())
          vmid := ← (undefined_bitvector 16)
          asid := ← (undefined_bitvector 16)
          nG := ← (undefined_bitvector 1)
          ipaspace := ← (undefined_PASpace ())
          includes_s1_name := ← (undefined_bool ())
          includes_s2_name := ← (undefined_bool ())
          includes_gpt_name := ← (undefined_bool ())
          ia := ← (undefined_bitvector 64)
          tg := ← (undefined_TGx ())
          cnp := ← (undefined_bitvector 1)
          level := ← (undefined_int ())
          isd128 := ← (undefined_bool ())
          xs := ← (undefined_bitvector 1) })

def undefined_AddressDescriptor (_ : Unit) : SailM AddressDescriptor := do
  (pure { fault := ← (undefined_FaultRecord ())
          memattrs := ← (undefined_MemoryAttributes ())
          paddress := ← (undefined_FullAddress ())
          tlbcontext := ← (undefined_TLBContext ())
          s1assured := ← (undefined_bool ())
          s2fs1mro := ← (undefined_bool ())
          mecid := ← (undefined_bitvector 16)
          vaddress := ← (undefined_bitvector 64) })

def undefined_TranslationStartInfo (_ : Unit) : SailM TranslationStartInfo := do
  (pure { ss := ← (undefined_SecurityState ())
          regime := ← (undefined_Regime ())
          vmid := ← (undefined_bitvector 16)
          asid := ← (undefined_bitvector 16)
          va := ← (undefined_bitvector 64)
          cnp := ← (undefined_bitvector 1)
          accdesc := ← (undefined_AccessDescriptor ())
          size := ← (undefined_int ()) })

def undefined_TLBILevel (_ : Unit) : SailM TLBILevel := do
  (internal_pick [TLBILevel_Any, TLBILevel_Last])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBILevel_of_num (arg_ : Nat) : TLBILevel :=
  match arg_ with
  | 0 => TLBILevel_Any
  | _ => TLBILevel_Last

def num_of_TLBILevel (arg_ : TLBILevel) : Int :=
  match arg_ with
  | .TLBILevel_Any => 0
  | .TLBILevel_Last => 1

def undefined_TLBIOp (_ : Unit) : SailM TLBIOp := do
  (internal_pick
    [TLBIOp_DALL, TLBIOp_DASID, TLBIOp_DVA, TLBIOp_IALL, TLBIOp_IASID, TLBIOp_IVA, TLBIOp_ALL, TLBIOp_ASID, TLBIOp_IPAS2, TLBIPOp_IPAS2, TLBIOp_VAA, TLBIOp_VA, TLBIPOp_VAA, TLBIPOp_VA, TLBIOp_VMALL, TLBIOp_VMALLS12, TLBIOp_RIPAS2, TLBIPOp_RIPAS2, TLBIOp_RVAA, TLBIOp_RVA, TLBIPOp_RVAA, TLBIPOp_RVA, TLBIOp_RPA, TLBIOp_PAALL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def TLBIOp_of_num (arg_ : Nat) : TLBIOp :=
  match arg_ with
  | 0 => TLBIOp_DALL
  | 1 => TLBIOp_DASID
  | 2 => TLBIOp_DVA
  | 3 => TLBIOp_IALL
  | 4 => TLBIOp_IASID
  | 5 => TLBIOp_IVA
  | 6 => TLBIOp_ALL
  | 7 => TLBIOp_ASID
  | 8 => TLBIOp_IPAS2
  | 9 => TLBIPOp_IPAS2
  | 10 => TLBIOp_VAA
  | 11 => TLBIOp_VA
  | 12 => TLBIPOp_VAA
  | 13 => TLBIPOp_VA
  | 14 => TLBIOp_VMALL
  | 15 => TLBIOp_VMALLS12
  | 16 => TLBIOp_RIPAS2
  | 17 => TLBIPOp_RIPAS2
  | 18 => TLBIOp_RVAA
  | 19 => TLBIOp_RVA
  | 20 => TLBIPOp_RVAA
  | 21 => TLBIPOp_RVA
  | 22 => TLBIOp_RPA
  | _ => TLBIOp_PAALL

def num_of_TLBIOp (arg_ : TLBIOp) : Int :=
  match arg_ with
  | .TLBIOp_DALL => 0
  | .TLBIOp_DASID => 1
  | .TLBIOp_DVA => 2
  | .TLBIOp_IALL => 3
  | .TLBIOp_IASID => 4
  | .TLBIOp_IVA => 5
  | .TLBIOp_ALL => 6
  | .TLBIOp_ASID => 7
  | .TLBIOp_IPAS2 => 8
  | .TLBIPOp_IPAS2 => 9
  | .TLBIOp_VAA => 10
  | .TLBIOp_VA => 11
  | .TLBIPOp_VAA => 12
  | .TLBIPOp_VA => 13
  | .TLBIOp_VMALL => 14
  | .TLBIOp_VMALLS12 => 15
  | .TLBIOp_RIPAS2 => 16
  | .TLBIPOp_RIPAS2 => 17
  | .TLBIOp_RVAA => 18
  | .TLBIOp_RVA => 19
  | .TLBIPOp_RVAA => 20
  | .TLBIPOp_RVA => 21
  | .TLBIOp_RPA => 22
  | .TLBIOp_PAALL => 23

def undefined_TLBIMemAttr (_ : Unit) : SailM TLBIMemAttr := do
  (internal_pick [TLBI_AllAttr, TLBI_ExcludeXS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBIMemAttr_of_num (arg_ : Nat) : TLBIMemAttr :=
  match arg_ with
  | 0 => TLBI_AllAttr
  | _ => TLBI_ExcludeXS

def num_of_TLBIMemAttr (arg_ : TLBIMemAttr) : Int :=
  match arg_ with
  | .TLBI_AllAttr => 0
  | .TLBI_ExcludeXS => 1

def undefined_TLBIRecord (_ : Unit) : SailM TLBIRecord := do
  (pure { op := ← (undefined_TLBIOp ())
          from_aarch64 := ← (undefined_bool ())
          security := ← (undefined_SecurityState ())
          regime := ← (undefined_Regime ())
          vmid := ← (undefined_bitvector 16)
          asid := ← (undefined_bitvector 16)
          level := ← (undefined_TLBILevel ())
          attr := ← (undefined_TLBIMemAttr ())
          ipaspace := ← (undefined_PASpace ())
          address := ← (undefined_bitvector 64)
          end_address_name := ← (undefined_bitvector 64)
          d64 := ← (undefined_bool ())
          d128 := ← (undefined_bool ())
          ttl := ← (undefined_bitvector 4)
          tg := ← (undefined_bitvector 2) })

def undefined_TLBIInfo (_ : Unit) : SailM TLBIInfo := do
  (pure { rec' := ← (undefined_TLBIRecord ())
          shareability := ← (undefined_Shareability ()) })

def undefined_DxB (_ : Unit) : SailM DxB := do
  (pure { domain := ← (undefined_MBReqDomain ())
          types := ← (undefined_MBReqTypes ())
          nXS := ← (undefined_bool ()) })

