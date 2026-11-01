import SailTinyArmUser.SailTinyArmUser
import SailTinyArmUser.Flow
import SailTinyArmUser.Vector
import SailTinyArmUser.Prelude
import SailTinyArmUser.Registers
import SailTinyArmUser.Interface
import SailTinyArmUser.Translation
import SailTinyArmUser.Base

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

/-- Type quantifiers: k_ex22042_ : Bool -/
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

/-- Type quantifiers: k_ex22045_ : Bool, bit_pos : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31, 0 ≤ bit_pos
  ∧ bit_pos ≤ 63 -/
def execute_TestAndBranch (t : Nat) (bit_pos : Nat) (offset : (BitVec 64)) (iszero : Bool) : SailM Unit := do
  let bit_is_zero ← do (pure ((BitVec.access ((← (rX t)) >>> bit_pos) 0) == 0#1))
  let condition_met :=
    if (iszero : Bool)
    then bit_is_zero
    else (! bit_is_zero)
  if (condition_met : Bool)
  then
    (do
      let base ← do (rPC ())
      (wPC (base + offset)))
  else writeReg _PC (BitVec.addInt (← readReg _PC) 4)

/-- Type quantifiers: k_ex22049_ : Bool, n : Nat, t : Nat, size : Nat, 0 ≤ size ∧ size ≤ 3, 0
  ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_Store (size : Nat) (t : Nat) (n : Nat) (offset : operand) (release : Bool) (s : (Option Nat)) : SailM Unit := SailME.run do
  let exclusive ← (( do
    match s with
    | none => (pure false)
    | .some s =>
      (do
        let success ← (( do (undefined_bool ()) ) : SailME Unit Bool )
        if (success : Bool)
        then
          (do
            (wX s (Sail.BitVec.zeroExtend 0#1 64))
            (pure true))
        else
          SailME.throw (← do
              writeReg _PC (BitVec.addInt (← readReg _PC) 4)
              (wX s (Sail.BitVec.zeroExtend 1#1 64)))) ) : SailME Unit Bool )
  let accdesc := (create_writeAccessDescriptor release exclusive)
  let base ← do
    if ((n == 31) : Bool)
    then (rSP ())
    else (rX n)
  let vaddr ← (( do (pure (base + (← (eval_operand 64 offset)))) ) : SailME Unit (BitVec 64) )
  (check_load_store_alignment size vaddr)
  let addr ← (( do
    match (translate_address vaddr (2 ^i size) accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let _ : Unit := (wMem_Addr addr)
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wMem (2 ^i size) addr (Sail.BitVec.extractLsb (← (rX t)) ((8 *i (2 ^i size)) -i 1) 0) accdesc)

/-- Type quantifiers: d : Nat, k_ex22050_ : Bool, 0 ≤ d ∧ d ≤ 31 -/
def execute_PCRelativeAddress (page : Bool) (d : Nat) (offset : (BitVec 64)) : SailM Unit := do
  let base ← (( do
    if (page : Bool)
    then (pure ((Sail.BitVec.extractLsb (← (rPC ())) 63 12) +++ 0x000#12))
    else (rPC ()) ) : SailM (BitVec 64) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wX d (base + offset))

def execute_Nop (_ : Unit) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)

/-- Type quantifiers: hw : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ hw ∧ hw ≤ 3 -/
def execute_Movz (sf : (BitVec 1)) (d : Nat) (imm : (BitVec 16)) (hw : Nat) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let res : (BitVec 64) := ((Sail.BitVec.zeroExtend imm 64) <<< (16 *i hw))
  (wXS d size (Sail.BitVec.extractLsb res (size -i 1) 0))

/-- Type quantifiers: k_ex22059_ : Bool, k_ex22058_ : Bool, k_ex22057_ : Bool, n : Nat, t : Nat, size
  : Nat, 0 ≤ size ∧ size ≤ 3, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_Load (size : Nat) (t : Nat) (n : Nat) (offset : operand) (acquire : Bool) (rcpc : Bool) (exclusive : Bool) : SailM Unit := SailME.run do
  let accdesc := (create_readAccessDescriptor acquire rcpc exclusive)
  let base ← do
    if ((n == 31) : Bool)
    then (rSP ())
    else (rX n)
  let vaddr ← (( do (pure (base + (← (eval_operand 64 offset)))) ) : SailME Unit (BitVec 64) )
  (check_load_store_alignment size vaddr)
  let addr ← (( do
    match (translate_address vaddr (2 ^i size) accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wX t (Sail.BitVec.zeroExtend (← (rMem (2 ^i size) addr accdesc)) 64))

def execute_InstructionSynchronizationBarrier (_ : Unit) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (instructionSynchronizationBarrier ())

def execute_DataSynchronizationBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (dataSynchronizationBarrer domain types)

def execute_DataMemoryBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (dataMemoryBarrier domain types)

def execute_ConditionalBranch (offset : (BitVec 64)) (cond : cond) : SailM Unit := do
  let base ← do (rPC ())
  if ((← (condition_holds cond)) : Bool)
  then
    (do
      let target := (base + offset)
      (wPC target))
  else (wPC (BitVec.addInt base 4))

/-- Type quantifiers: k_ex22061_ : Bool, t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_CompareAndBranch (sf : (BitVec 1)) (t : Nat) (offset : (BitVec 64)) (iszero : Bool) : SailM Unit := do
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let operand ← (( do (pure (Sail.BitVec.zeroExtend (← (rXS t size)) 64)) ) : SailM (BitVec 64)
    )
  let condition_met :=
    if (iszero : Bool)
    then (operand == 0x0000000000000000#64)
    else (operand != 0x0000000000000000#64)
  if (condition_met : Bool)
  then
    (do
      let base ← do (rPC ())
      let addr := (base + offset)
      (wPC addr))
  else writeReg _PC (BitVec.addInt (← readReg _PC) 4)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def execute_BranchRegister (n : Nat) : SailM Unit := do
  (wPC (← (rX n)))

def execute_Branch (offset : (BitVec 64)) : SailM Unit := do
  let base ← do (rPC ())
  let target := (base + offset)
  (wPC target)

/-- Type quantifiers: n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_BitwiseLogic (sf : (BitVec 1)) (op : bitwise_op) (d : Nat) (n : Nat) (op2 : operand) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let operand1 ← do (rXS n size)
  let operand2 ← do (eval_operand size op2)
  let result : (BitVec size) :=
    match op with
    | .Eor => (operand1 ^^^ operand2)
    | .Or => (operand1 ||| operand2)
    | .And => (operand1 &&& operand2)
    | .AndSetFlags => (operand1 &&& operand2)
  let setflags : Bool :=
    match op with
    | .AndSetFlags => true
    | _ => false
  let use_sp ← (( do
    match op2 with
    | .OperandRegShift _ => (pure false)
    | .OperandRegExt _ => (fail "bitwise operation shouldn't have OperandRegExt")
    | .OperandImm _ =>
      (if (setflags : Bool)
      then (pure false)
      else (pure true)) ) : SailM Bool )
  if ((use_sp && (d == 31)) : Bool)
  then (wSPS size result)
  else (wXS d size result)
  if (setflags : Bool)
  then
    (do
      let n := (BitVec.access result (size -i 1))
      let z :=
        if ((result == (BitVec.zero size)) : Bool)
        then 1#1
        else 0#1
      let c := 0#1
      let v := 0#1
      writeReg NZCV (n +++ (z +++ (c +++ v))))
  else (pure ())

/-- Type quantifiers: n : Nat, d : Nat, k_ex22065_ : Bool, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧
  n ≤ 31 -/
def execute_BitfieldMove (sf : (BitVec 1)) (signd : Bool) (d : Nat) (n : Nat) (imms : (BitVec 6)) (immr : (BitVec 6)) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let s := (BitVec.toNatInt imms)
  let r := (BitVec.toNatInt immr)
  sail_assert (s <b size) "instrs-user.sail:365.31-365.32"
  let (wmask, tmask) ← do (decode_bitmask sf imms immr false)
  let wmask := (Sail.BitVec.extractLsb wmask (size -i 1) 0)
  let tmask := (Sail.BitVec.extractLsb tmask (size -i 1) 0)
  let src ← do (rXS n size)
  let bot := ((rotate_right src r) &&& wmask)
  let top :=
    if ((signd && ((BitVec.access src s) == 1#1)) : Bool)
    then (sail_ones size)
    else (BitVec.zero size)
  (wXS d size ((top &&& (Complement.complement tmask)) ||| (bot &&& tmask)))

/-- Type quantifiers: k_ex22073_ : Bool, k_ex22072_ : Bool, n : Nat, t : Nat, s : Nat, var_0 : Nat, 0
  ≤ var_0 ∧ var_0 ≤ 3, 0 ≤ s ∧ s ≤ 31, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_AtomicRMW (var_0 : Nat) (s : Nat) (t : Nat) (n : Nat) (op : MemAtomicOp) (acq : Bool) (rel : Bool) : SailM Unit := SailME.run do
  let size := var_0
  let accdesc := (create_RMWAccessDescriptor op acq rel)
  let vaddr ← do
    if ((n == 31) : Bool)
    then (rSP ())
    else (rX n)
  let addr ← (( do
    match (translate_address vaddr (2 ^i size) accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let old_value ← do (rMem (2 ^i size) addr accdesc)
  (wX t (Sail.BitVec.zeroExtend old_value 64))
  let operand ← do (pure (Sail.BitVec.extractLsb (← (rX s)) ((8 *i (2 ^i size)) -i 1) 0))
  let new_value ← (( do
    match op with
    | .MemAtomicOp_ADD => (pure (old_value + operand))
    | .MemAtomicOp_BIC => (pure (old_value &&& (Complement.complement operand)))
    | .MemAtomicOp_EOR => (pure (old_value ^^^ operand))
    | .MemAtomicOp_ORR => (pure (old_value ||| operand))
    | .MemAtomicOp_SMAX => (pure (smax old_value operand))
    | .MemAtomicOp_SMIN => (pure (smin old_value operand))
    | .MemAtomicOp_UMAX => (pure (umax old_value operand))
    | .MemAtomicOp_UMIN => (pure (umin old_value operand))
    | _ => (fail "AtomicRMW: SWP, CAS and GCSS1 unsupported") ) : SailME Unit
    (BitVec (8 * 2 ^ size)) )
  (wMem (2 ^i size) addr new_value accdesc)

/-- Type quantifiers: n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_AddSub (sf : (BitVec 1)) (op : (BitVec 1)) (S : (BitVec 1)) (d : Nat) (n : Nat) (m : operand) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let addition := (op == 0#1)
  let use_sp : Bool :=
    match m with
    | .OperandRegShift _ => false
    | _ => true
  let op1 ← do
    if ((use_sp && (n == 31)) : Bool)
    then (rSPS size)
    else (rXS n size)
  let op2 ← do (eval_operand size m)
  let result :=
    if (addition : Bool)
    then (op1 + op2)
    else (op1 - op2)
  if ((use_sp && ((S == 0#1) && (d == 31))) : Bool)
  then (wSPS size result)
  else (wXS d size result)
  if ((S == 1#1) : Bool)
  then
    (do
      let n := (BitVec.access result (size -i 1))
      let z :=
        if ((result == (BitVec.zero size)) : Bool)
        then 1#1
        else 0#1
      let c :=
        if (addition : Bool)
        then
          (if (((BitVec.toNatInt result) <b (BitVec.toNatInt op1)) : Bool)
          then 1#1
          else 0#1)
        else
          (if (((BitVec.toNatInt op1) ≥b (BitVec.toNatInt op2)) : Bool)
          then 1#1
          else 0#1)
      let s1 := (BitVec.access op1 (size -i 1))
      let s2 :=
        if (addition : Bool)
        then (BitVec.access op2 (size -i 1))
        else (Complement.complement (BitVec.access op2 (size -i 1)))
      let v :=
        if ((s1 == s2) : Bool)
        then
          (if ((s1 != n) : Bool)
          then 1#1
          else 0#1)
        else 0#1
      writeReg NZCV (n +++ (z +++ (c +++ v))))
  else (pure ())

def execute (merge_var : ast) : SailM Unit := do
  match merge_var with
  | .Load (size, t, n, offset, acquire, rcpc, exclusive) =>
    (execute_Load size t n offset acquire rcpc exclusive)
  | .Store (size, t, n, offset, release, s) => (execute_Store size t n offset release s)
  | .AtomicRMW (arg0, s, t, n, op, acq, rel) => (execute_AtomicRMW arg0 s t n op acq rel)
  | .BitwiseLogic (sf, op, d, n, op2) => (execute_BitwiseLogic sf op d n op2)
  | .Movz (sf, d, imm, hw) => (execute_Movz sf d imm hw)
  | .BitfieldMove (sf, signd, d, n, imms, immr) => (execute_BitfieldMove sf signd d n imms immr)
  | .AddSub (sf, op, S, d, n, m) => (execute_AddSub sf op S d n m)
  | .DataMemoryBarrier (domain, types) => (execute_DataMemoryBarrier domain types)
  | .DataSynchronizationBarrier (domain, types) => (execute_DataSynchronizationBarrier domain types)
  | .InstructionSynchronizationBarrier arg0 => (execute_InstructionSynchronizationBarrier arg0)
  | .Nop arg0 => (execute_Nop arg0)
  | .CompareAndBranch (sf, t, offset, iszero) => (execute_CompareAndBranch sf t offset iszero)
  | .TestAndBranch (t, bit_pos, offset, iszero) => (execute_TestAndBranch t bit_pos offset iszero)
  | .Branch offset => (execute_Branch offset)
  | .ConditionalBranch (offset, cond) => (execute_ConditionalBranch offset cond)
  | .PCRelativeAddress (page, d, offset) => (execute_PCRelativeAddress page d offset)
  | .BranchRegister n => (execute_BranchRegister n)

