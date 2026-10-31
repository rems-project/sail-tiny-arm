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

/-- Type quantifiers: k_a : Type, k_b : Type -/
def is_ok (r : (Result k_a k_b)) : Bool :=
  match r with
  | .Ok _ => true
  | .Err _ => false

/-- Type quantifiers: k_a : Type, k_b : Type -/
def is_err (r : (Result k_a k_b)) : Bool :=
  match r with
  | .Ok _ => false
  | .Err _ => true

/-- Type quantifiers: k_a : Type, k_b : Type -/
def ok_option (r : (Result k_a k_b)) : (Option k_a) :=
  match r with
  | .Ok x => (some x)
  | .Err _ => none

/-- Type quantifiers: k_a : Type, k_b : Type -/
def err_option (r : (Result k_a k_b)) : (Option k_b) :=
  match r with
  | .Ok _ => none
  | .Err err => (some err)

/-- Type quantifiers: k_a : Type, k_b : Type -/
def unwrap_or (r : (Result k_a k_b)) (y : k_a) : k_a :=
  match r with
  | .Ok x => x
  | .Err _ => y

