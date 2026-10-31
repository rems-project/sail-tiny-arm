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

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def sail_instr_announce (x_0 : (BitVec k_n)) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, List.elem x_0 [32, 64] -/
def sail_branch_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

def sail_reset_registers (_ : Unit) : Unit :=
  ()

def sail_synchronize_registers (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_a : Type -/
def sail_mark_register (x_0 : (RegisterRef k_a)) (x_1 : String) : Unit :=
  ()

/-- Type quantifiers: k_a : Type, k_b : Type -/
def sail_mark_register_pair (x_0 : (RegisterRef k_a)) (x_1 : (RegisterRef k_b)) (x_2 : String) : Unit :=
  ()

/-- Type quantifiers: k_a : Type -/
def sail_ignore_write_to (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "ignore_write")

/-- Type quantifiers: k_a : Type -/
def sail_pick_dependency (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "pick")

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def __monomorphize (bv : (BitVec k_n)) : (BitVec k_n) :=
  bv

/-- Type quantifiers: n : Int -/
def __monomorphize_int (n : Int) : Int :=
  n

/-- Type quantifiers: k_b : Bool -/
def __monomorphize_bool (b : Bool) : Bool :=
  b

