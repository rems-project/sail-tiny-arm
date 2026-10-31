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

/-- Type quantifiers: k_ex21277_ : Bool, k_ex21276_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: k_n : Nat, y : Nat, k_n ≥ 0 ∧ y ≥ 0 -/
def eq_bits_int (x : (BitVec k_n)) (y : Nat) : Bool :=
  ((BitVec.toNatInt x) == y)

