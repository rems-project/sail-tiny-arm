import SailTinyArmSystem.Flow
import SailTinyArmSystem.Prelude
import SailTinyArmSystem.Registers
import SailTinyArmSystem.Base

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

def decodeLoadStoreRegister (size : (BitVec 2)) (opc : (BitVec 2)) (Rm : (BitVec 5)) (option_v : (BitVec 3)) (S : (BitVec 1)) (Rn : (BitVec 5)) (Rt : (BitVec 5)) : SailM ast := do
  let size := (BitVec.toNatInt size)
  let t : reg_index := (BitVec.toNatInt Rt)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  let shift : Nat :=
    if ((S == 1#1) : Bool)
    then size
    else 0
  if (((BitVec.access option_v 1) == 0#1) : Bool)
  then (fail "Sub-word extend in Load/Store")
  else (pure ())
  let offset := (OperandRegExt (m, (ext_bits_backwards option_v), shift))
  match opc with
  | 0b01 => (pure (Load (size, t, n, offset, false, false, false)))
  | 0b00 => (pure (Store (size, t, n, offset, false, none)))
  | _ => (fail "Sign-extend loads are not supported")

def decodeLoadStoreImmediate (size : (BitVec 2)) (opc : (BitVec 2)) (imm12 : (BitVec 12)) (Rn : (BitVec 5)) (Rt : (BitVec 5)) : SailM ast := do
  let size := (BitVec.toNatInt size)
  let t : reg_index := (BitVec.toNatInt Rt)
  let n : reg_index := (BitVec.toNatInt Rn)
  let imm := ((Sail.BitVec.zeroExtend imm12 64) <<< size)
  let offset := (OperandImm imm)
  match opc with
  | 0b01 => (pure (Load (size, t, n, offset, false, false, false)))
  | 0b00 => (pure (Store (size, t, n, offset, false, none)))
  | _ => (fail "Sign-extend loads are not supported")

/-- Type quantifiers: size : Nat, 0 ≤ size ∧ size ≤ 3 -/
def check_load_store_alignment (size : Nat) (addr : (BitVec 64)) : SailM Unit := do
  let aligned :=
    if ((size == 0) : Bool)
    then true
    else ((Sail.BitVec.extractLsb addr (size -i 1) 0) == (BitVec.zero size))
  if ((! aligned) : Bool)
  then (fail "Misaligned Load/Store access")
  else (pure ())

def decode_bitwise_op (opc : (BitVec 2)) : bitwise_op :=
  match opc with
  | 0b00 => And
  | 0b10 => Eor
  | 0b01 => Or
  | _ => AndSetFlags

def decodeAddSubExt (sf : (BitVec 1)) (op : (BitVec 1)) (S : (BitVec 1)) (option_v : (BitVec 3)) (imm3 : (BitVec 3)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : SailM ast := do
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  let shift := (BitVec.toNatInt imm3)
  let shift ← (( do
    if ((shift >b 4) : Bool)
    then (fail "AddSub (extended register) shift is greater than 4")
    else (pure shift) ) : SailM Nat )
  let operand := (OperandRegExt ((BitVec.toNatInt Rm), (ext_bits_backwards option_v), shift))
  (pure (AddSub (sf, op, S, d, n, operand)))

def decodeAddSubShift (sf : (BitVec 1)) (op : (BitVec 1)) (S : (BitVec 1)) (shift : (BitVec 2)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : SailM ast := do
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  if ((shift == 0b11#2) : Bool)
  then (fail "ADD/SUB doesn't support ROR")
  else (pure ())
  if (((sf == 0#1) && ((BitVec.access imm6 5) == 1#1)) : Bool)
  then (fail "ADD/SUB: shift by more than 31 bits on 32 bit operation")
  else (pure ())
  let operand :=
    (OperandRegShift ((BitVec.toNatInt Rm), (shift_bits_backwards shift), (BitVec.toNatInt imm6)))
  (pure (AddSub (sf, op, S, d, n, operand)))

def decodeAddSubImm (sf : (BitVec 1)) (op : (BitVec 1)) (S : (BitVec 1)) (sh : (BitVec 1)) (imm12 : (BitVec 12)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : ast :=
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  let imm :=
    if ((sh == 0#1) : Bool)
    then (0x0000000000000#52 +++ imm12)
    else (0x0000000000#40 +++ (imm12 +++ 0x000#12))
  (AddSub (sf, op, S, d, n, (OperandImm imm)))

/-- Type quantifiers: k_ex29103_ : Bool -/
def decodeDataBarrier (CRm : (BitVec 4)) (is_sync : Bool) : SailM ast := do
  let domain : MBReqDomain :=
    match (Sail.BitVec.extractLsb CRm 3 2) with
    | 0b11 => MBReqDomain_FullSystem
    | 0b10 => MBReqDomain_InnerShareable
    | 0b01 => MBReqDomain_Nonshareable
    | _ => MBReqDomain_OuterShareable
  let types ← (( do
    match (Sail.BitVec.extractLsb CRm 1 0) with
    | 0b01 => (pure MBReqTypes_Reads)
    | 0b10 => (pure MBReqTypes_Writes)
    | 0b11 => (pure MBReqTypes_All)
    | _ => (fail "DxB: Invalid encoding of kind of barrier") ) : SailM MBReqTypes )
  if (is_sync : Bool)
  then (pure (DataSynchronizationBarrier (domain, types)))
  else (pure (DataMemoryBarrier (domain, types)))

def decodeCompareAndBranch (sf : (BitVec 1)) (op : (BitVec 1)) (imm19 : (BitVec 19)) (Rt : (BitVec 5)) : ast :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let offset : (BitVec 64) := (Sail.BitVec.signExtend (imm19 +++ 0b00#2) 64)
  let iszero : Bool := (op == 0#1)
  (CompareAndBranch (sf, t, offset, iszero))

def decodeTestAndBranch (b5 : (BitVec 1)) (op : (BitVec 1)) (b40 : (BitVec 5)) (imm14 : (BitVec 14)) (Rt : (BitVec 5)) : ast :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let bit_pos : Nat := (BitVec.toNatInt (b5 +++ b40))
  let offset : (BitVec 64) := (Sail.BitVec.signExtend (imm14 +++ 0b00#2) 64)
  let iszero : Bool := (op == 0#1)
  (TestAndBranch (t, bit_pos, offset, iszero))

def cond_bits_forwards (arg_ : cond) : (BitVec 4) :=
  match arg_ with
  | .EQ => 0b0000#4
  | .NE => 0b0001#4
  | .CS => 0b0010#4
  | .CC => 0b0011#4
  | .MI => 0b0100#4
  | .PL => 0b0101#4
  | .VS => 0b0110#4
  | .VC => 0b0111#4
  | .HI => 0b1000#4
  | .LS => 0b1001#4
  | .GE => 0b1010#4
  | .LT => 0b1011#4
  | .GT => 0b1100#4
  | .LE => 0b1101#4
  | .AL => 0b1110#4
  | .NV => 0b1111#4

def cond_bits_backwards (arg_ : (BitVec 4)) : cond :=
  match arg_ with
  | 0b0000 => EQ
  | 0b0001 => NE
  | 0b0010 => CS
  | 0b0011 => CC
  | 0b0100 => MI
  | 0b0101 => PL
  | 0b0110 => VS
  | 0b0111 => VC
  | 0b1000 => HI
  | 0b1001 => LS
  | 0b1010 => GE
  | 0b1011 => LT
  | 0b1100 => GT
  | 0b1101 => LE
  | 0b1110 => AL
  | _ => NV

def cond_bits_forwards_matches (arg_ : cond) : Bool :=
  match arg_ with
  | .EQ => true
  | .NE => true
  | .CS => true
  | .CC => true
  | .MI => true
  | .PL => true
  | .VS => true
  | .VC => true
  | .HI => true
  | .LS => true
  | .GE => true
  | .LT => true
  | .GT => true
  | .LE => true
  | .AL => true
  | .NV => true

def cond_bits_backwards_matches (arg_ : (BitVec 4)) : Bool :=
  match arg_ with
  | 0b0000 => true
  | 0b0001 => true
  | 0b0010 => true
  | 0b0011 => true
  | 0b0100 => true
  | 0b0101 => true
  | 0b0110 => true
  | 0b0111 => true
  | 0b1000 => true
  | 0b1001 => true
  | 0b1010 => true
  | 0b1011 => true
  | 0b1100 => true
  | 0b1101 => true
  | 0b1110 => true
  | 0b1111 => true
  | _ => false

def condition_holds (cond : cond) : SailM Bool := do
  match cond with
  | .EQ => (pure ((← (rZ ())) == 1#1))
  | .NE => (pure ((← (rZ ())) == 0#1))
  | .CS => (pure ((← (rC ())) == 1#1))
  | .CC => (pure ((← (rC ())) == 0#1))
  | .MI => (pure ((← (rN ())) == 1#1))
  | .PL => (pure ((← (rN ())) == 0#1))
  | .VS => (pure ((← (rV ())) == 1#1))
  | .VC => (pure ((← (rV ())) == 0#1))
  | .HI => (pure ((← (rC ())) == 1#1)) <&&> (do (pure ((← (rZ ())) == 0#1)))
  | .LS => (pure ((← (rC ())) == 0#1)) <||> (do (pure ((← (rZ ())) == 1#1)))
  | .GE => (pure ((← (rN ())) == (← (rV ()))))
  | .LT => (pure ((← (rN ())) != (← (rV ()))))
  | .GT => (pure ((← (rN ())) == (← (rV ())))) <&&> (do (pure ((← (rZ ())) == 0#1)))
  | .LE => (pure ((← (rN ())) != (← (rV ())))) <||> (do (pure ((← (rZ ())) == 1#1)))
  | .AL => (pure true)
  | .NV => (pure true)

