import SailTinyArmUser.SailTinyArmUser
import SailTinyArmUser.Vector
import SailTinyArmUser.Prelude
import SailTinyArmUser.Registers

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

def undefined_extend_type (_ : Unit) : SailM extend_type := do
  (internal_pick [UXTB, UXTH, UXTW, UXTX, SXTB, SXTH, SXTW, SXTX])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def extend_type_of_num (arg_ : Nat) : extend_type :=
  match arg_ with
  | 0 => UXTB
  | 1 => UXTH
  | 2 => UXTW
  | 3 => UXTX
  | 4 => SXTB
  | 5 => SXTH
  | 6 => SXTW
  | _ => SXTX

def num_of_extend_type (arg_ : extend_type) : Int :=
  match arg_ with
  | .UXTB => 0
  | .UXTH => 1
  | .UXTW => 2
  | .UXTX => 3
  | .SXTB => 4
  | .SXTH => 5
  | .SXTW => 6
  | .SXTX => 7

def ext_bits_forwards (arg_ : extend_type) : (BitVec 3) :=
  match arg_ with
  | .UXTB => 0b000#3
  | .UXTH => 0b001#3
  | .UXTW => 0b010#3
  | .UXTX => 0b011#3
  | .SXTB => 0b100#3
  | .SXTH => 0b101#3
  | .SXTW => 0b110#3
  | .SXTX => 0b111#3

def ext_bits_backwards (arg_ : (BitVec 3)) : extend_type :=
  match arg_ with
  | 0b000 => UXTB
  | 0b001 => UXTH
  | 0b010 => UXTW
  | 0b011 => UXTX
  | 0b100 => SXTB
  | 0b101 => SXTH
  | 0b110 => SXTW
  | _ => SXTX

def ext_bits_forwards_matches (arg_ : extend_type) : Bool :=
  match arg_ with
  | .UXTB => true
  | .UXTH => true
  | .UXTW => true
  | .UXTX => true
  | .SXTB => true
  | .SXTH => true
  | .SXTW => true
  | .SXTX => true

def ext_bits_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | 0b100 => true
  | 0b101 => true
  | 0b110 => true
  | 0b111 => true
  | _ => false

def extend_reg (v : (BitVec 64)) (ext : extend_type) : (BitVec 64) :=
  match ext with
  | .UXTB => (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb v 7 0) 64)
  | .UXTH => (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb v 15 0) 64)
  | .UXTW => (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb v 31 0) 64)
  | .UXTX => v
  | .SXTB => (Sail.BitVec.signExtend (Sail.BitVec.extractLsb v 7 0) 64)
  | .SXTH => (Sail.BitVec.signExtend (Sail.BitVec.extractLsb v 15 0) 64)
  | .SXTW => (Sail.BitVec.signExtend (Sail.BitVec.extractLsb v 31 0) 64)
  | .SXTX => v

def undefined_shift_type (_ : Unit) : SailM shift_type := do
  (internal_pick [shift_LSL, shift_LSR, shift_ASR, shift_ROR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def shift_type_of_num (arg_ : Nat) : shift_type :=
  match arg_ with
  | 0 => shift_LSL
  | 1 => shift_LSR
  | 2 => shift_ASR
  | _ => shift_ROR

def num_of_shift_type (arg_ : shift_type) : Int :=
  match arg_ with
  | .shift_LSL => 0
  | .shift_LSR => 1
  | .shift_ASR => 2
  | .shift_ROR => 3

def shift_bits_forwards (arg_ : shift_type) : (BitVec 2) :=
  match arg_ with
  | .shift_LSL => 0b00#2
  | .shift_LSR => 0b01#2
  | .shift_ASR => 0b10#2
  | .shift_ROR => 0b11#2

def shift_bits_backwards (arg_ : (BitVec 2)) : shift_type :=
  match arg_ with
  | 0b00 => shift_LSL
  | 0b01 => shift_LSR
  | 0b10 => shift_ASR
  | _ => shift_ROR

def shift_bits_forwards_matches (arg_ : shift_type) : Bool :=
  match arg_ with
  | .shift_LSL => true
  | .shift_LSR => true
  | .shift_ASR => true
  | .shift_ROR => true

def shift_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

/-- Type quantifiers: amount : Nat, k_N : Nat, List.elem k_N [32, 64], 0 ≤ amount ∧
  amount ≤ 63 -/
def shift_reg (v : (BitVec k_N)) (sh : shift_type) (amount : Nat) : SailM (BitVec k_N) := do
  match sh with
  | .shift_LSL => (pure (v <<< amount))
  | .shift_LSR => (pure (v >>> amount))
  | .shift_ASR => (pure (BitVec.sshiftRight v amount))
  | .shift_ROR => (fail "ROR unsupported")

/-- Type quantifiers: size : Nat, List.elem size [32, 64] -/
def eval_operand (size : Nat) (op : operand) : SailM (BitVec size) := do
  match op with
  | .OperandRegExt (n, ext, shift) =>
    (pure ((Sail.BitVec.extractLsb (extend_reg (← (rX n)) ext) (size -i 1) 0) <<< shift))
  | .OperandRegShift (n, sh, amount) => (shift_reg (← (rXS n size)) sh amount)
  | .OperandImm imm => (pure (Sail.BitVec.extractLsb imm (size -i 1) 0))

def zero_operand := (OperandImm 0x0000000000000000#64)

def undefined_bitwise_op (_ : Unit) : SailM bitwise_op := do
  (internal_pick [Eor, Or, And, AndSetFlags])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def bitwise_op_of_num (arg_ : Nat) : bitwise_op :=
  match arg_ with
  | 0 => Eor
  | 1 => Or
  | 2 => And
  | _ => AndSetFlags

def num_of_bitwise_op (arg_ : bitwise_op) : Int :=
  match arg_ with
  | .Eor => 0
  | .Or => 1
  | .And => 2
  | .AndSetFlags => 3

def undefined_cond (_ : Unit) : SailM cond := do
  (internal_pick [EQ, NE, CS, CC, MI, PL, VS, VC, HI, LS, GE, LT, GT, LE, AL, NV])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 15 -/
def cond_of_num (arg_ : Nat) : cond :=
  match arg_ with
  | 0 => EQ
  | 1 => NE
  | 2 => CS
  | 3 => CC
  | 4 => MI
  | 5 => PL
  | 6 => VS
  | 7 => VC
  | 8 => HI
  | 9 => LS
  | 10 => GE
  | 11 => LT
  | 12 => GT
  | 13 => LE
  | 14 => AL
  | _ => NV

def num_of_cond (arg_ : cond) : Int :=
  match arg_ with
  | .EQ => 0
  | .NE => 1
  | .CS => 2
  | .CC => 3
  | .MI => 4
  | .PL => 5
  | .VS => 6
  | .VC => 7
  | .HI => 8
  | .LS => 9
  | .GE => 10
  | .LT => 11
  | .GT => 12
  | .LE => 13
  | .AL => 14
  | .NV => 15

/-- Type quantifiers: r : Int, k_n : Int -/
def rotate_right (v : (BitVec k_n)) (r : Int) : (BitVec k_n) :=
  if ((r == 0) : Bool)
  then v
  else ((v >>> r) ||| (v <<< ((Sail.BitVec.length v) -i r)))

/-- Type quantifiers: k_ex21932_ : Bool -/
def decode_bitmask (N : (BitVec 1)) (imms : (BitVec 6)) (immr : (BitVec 6)) (immediate : Bool) : SailM ((BitVec 64) × (BitVec 64)) := do
  let len :=
    if ((N == 1#1) : Bool)
    then 6
    else (5 -i (BitVec.countLeadingZeros (Complement.complement imms)))
  sail_assert (len >b 0) "Invalid immediate encoding for bitwise operation"
  let s := (BitVec.toNatInt (Sail.BitVec.extractLsb imms (len -i 1) 0))
  let r := (BitVec.toNatInt (Sail.BitVec.extractLsb immr (len -i 1) 0))
  if (immediate : Bool)
  then
    sail_assert ((s +i 1) <b (2 ^i len)) "All-ones mask is not allowed in immediate bitwise operations"
  else (pure ())
  let welem := (Sail.BitVec.zeroExtend (sail_ones (s +i 1)) (2 ^i len))
  let relem := (rotate_right welem r)
  let wmask := (BitVec.replicateBits relem (2 ^i (6 -i len)))
  let diff := (s -i r)
  let d :=
    if ((diff ≥b 0) : Bool)
    then diff
    else ((2 ^i len) +i diff)
  let telem := (Sail.BitVec.zeroExtend (sail_ones (d +i 1)) (2 ^i len))
  let tmask := (BitVec.replicateBits telem (2 ^i (6 -i len)))
  (pure (wmask, tmask))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def smax (x : (BitVec k_n)) (y : (BitVec k_n)) : (BitVec k_n) :=
  if (((BitVec.toInt x) >b (BitVec.toInt y)) : Bool)
  then x
  else y

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def smin (x : (BitVec k_n)) (y : (BitVec k_n)) : (BitVec k_n) :=
  if (((BitVec.toInt x) <b (BitVec.toInt y)) : Bool)
  then x
  else y

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def umax (x : (BitVec k_n)) (y : (BitVec k_n)) : (BitVec k_n) :=
  if (((BitVec.toNatInt x) >b (BitVec.toNatInt y)) : Bool)
  then x
  else y

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def umin (x : (BitVec k_n)) (y : (BitVec k_n)) : (BitVec k_n) :=
  if (((BitVec.toNatInt x) <b (BitVec.toNatInt y)) : Bool)
  then x
  else y

