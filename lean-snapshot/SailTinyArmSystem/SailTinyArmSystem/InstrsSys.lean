import SailTinyArmSystem.SailTinyArmSystem
import SailTinyArmSystem.Flow
import SailTinyArmSystem.Vector
import SailTinyArmSystem.Prelude
import SailTinyArmSystem.Registers
import SailTinyArmSystem.Interface
import SailTinyArmSystem.Translation
import SailTinyArmSystem.Base
import SailTinyArmSystem.InstrsUser

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

def decodeTLBI (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (Rt : (BitVec 5)) : SailM ast := do
  let t : reg_index := (BitVec.toNatInt Rt)
  let (tlbi_op, shareability, level) ← (( do
    match (op1, CRn, CRm, op2) with
    | (0b100, 0b1000, 0b0111, 0b100) => (pure (TLBIOp_ALL, Shareability_NSH, TLBILevel_Any))
    | (0b000, 0b1000, 0b0011, 0b000) => (pure (TLBIOp_VMALL, Shareability_ISH, TLBILevel_Any))
    | (0b000, 0b1000, 0b0011, 0b001) => (pure (TLBIOp_VA, Shareability_ISH, TLBILevel_Any))
    | (0b000, 0b1000, 0b0111, 0b001) => (pure (TLBIOp_VA, Shareability_NSH, TLBILevel_Any))
    | (0b000, 0b1000, 0b0011, 0b010) => (pure (TLBIOp_ASID, Shareability_ISH, TLBILevel_Any))
    | (0b000, 0b1000, 0b0011, 0b011) => (pure (TLBIOp_VAA, Shareability_ISH, TLBILevel_Any))
    | (0b000, 0b1000, 0b0011, 0b101) => (pure (TLBIOp_VA, Shareability_ISH, TLBILevel_Last))
    | (0b000, 0b1000, 0b0011, 0b111) => (pure (TLBIOp_VAA, Shareability_ISH, TLBILevel_Last))
    | (0b000, 0b1000, 0b0111, 0b011) => (pure (TLBIOp_VAA, Shareability_NSH, TLBILevel_Any))
    | _ => (fail "Unsupported TLBI operation encoding") ) : SailM
    (TLBIOp × Shareability × TLBILevel) )
  (pure (TLBInvalidation (tlbi_op, shareability, level, t)))

def decodeASID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def decodeVA (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb v 43 0) +++ 0x000#12) 64)

/-- Type quantifiers: k_ex29195_ : Bool -/
def decodeSystemRegisterMove (is_read : Bool) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (Rt : (BitVec 5)) : ast :=
  let sys_reg_id := (op0 +++ (op1 +++ (CRn +++ (CRm +++ op2))))
  (SystemRegisterMove (is_read, sys_reg_id, (BitVec.toNatInt Rt)))

def check_sys_reg_el (min_el : (BitVec 2)) : SailM Unit := do
  sail_assert ((BitVec.toNatInt (← readReg CurrentEL)) ≥b (BitVec.toNatInt min_el)) "Trying to access system register from too-low EL, fault not implemented"

def read_sys_reg (sys_reg_id : (BitVec 16)) : SailM (BitVec 64) := do
  let v__0 := sys_reg_id
  if ((v__0 == (0xC038#16 : (BitVec 16))) : Bool)
  then
    (do
      (check_sys_reg_el 0b01#2)
      (sail_sys_reg_read sys_reg_id (.Reg ID_AA64MMFR0_EL1)))
  else
    (do
      if ((v__0 == (0xC039#16 : (BitVec 16))) : Bool)
      then
        (do
          (check_sys_reg_el 0b01#2)
          (sail_sys_reg_read sys_reg_id (.Reg ID_AA64MMFR1_EL1)))
      else
        (do
          if ((v__0 == (0xC03A#16 : (BitVec 16))) : Bool)
          then
            (do
              (check_sys_reg_el 0b01#2)
              (sail_sys_reg_read sys_reg_id (.Reg ID_AA64MMFR2_EL1)))
          else
            (do
              if ((v__0 == (0xC03B#16 : (BitVec 16))) : Bool)
              then
                (do
                  (check_sys_reg_el 0b01#2)
                  (sail_sys_reg_read sys_reg_id (.Reg ID_AA64MMFR3_EL1)))
              else
                (do
                  if ((v__0 == (0xC03C#16 : (BitVec 16))) : Bool)
                  then
                    (do
                      (check_sys_reg_el 0b01#2)
                      (sail_sys_reg_read sys_reg_id (.Reg ID_AA64MMFR4_EL1)))
                  else
                    (do
                      if ((v__0 == (0xC080#16 : (BitVec 16))) : Bool)
                      then
                        (do
                          (check_sys_reg_el 0b01#2)
                          (sail_sys_reg_read sys_reg_id (.Reg SCTLR_EL1)))
                      else
                        (do
                          if ((v__0 == (0xC100#16 : (BitVec 16))) : Bool)
                          then
                            (do
                              (check_sys_reg_el 0b01#2)
                              (sail_sys_reg_read sys_reg_id (.Reg TTBR0_EL1)))
                          else
                            (do
                              if ((v__0 == (0xC101#16 : (BitVec 16))) : Bool)
                              then
                                (do
                                  (check_sys_reg_el 0b01#2)
                                  (sail_sys_reg_read sys_reg_id (.Reg TTBR1_EL1)))
                              else
                                (do
                                  if ((v__0 == (0xC102#16 : (BitVec 16))) : Bool)
                                  then
                                    (do
                                      (check_sys_reg_el 0b01#2)
                                      (sail_sys_reg_read sys_reg_id (.Reg TCR_EL1)))
                                  else
                                    (do
                                      if ((v__0 == (0xC200#16 : (BitVec 16))) : Bool)
                                      then
                                        (do
                                          (check_sys_reg_el 0b01#2)
                                          (sail_sys_reg_read sys_reg_id (.Reg SPSR_EL1)))
                                      else
                                        (do
                                          if ((v__0 == (0xC201#16 : (BitVec 16))) : Bool)
                                          then
                                            (do
                                              (check_sys_reg_el 0b01#2)
                                              (sail_sys_reg_read sys_reg_id (.Reg ELR_EL1)))
                                          else
                                            (do
                                              if ((v__0 == (0xC212#16 : (BitVec 16))) : Bool)
                                              then
                                                (do
                                                  (check_sys_reg_el 0b01#2)
                                                  (pure (Sail.BitVec.zeroExtend
                                                      ((← readReg CurrentEL) +++ 0b00#2) 64)))
                                              else
                                                (do
                                                  if ((v__0 == (0xC290#16 : (BitVec 16))) : Bool)
                                                  then
                                                    (do
                                                      (check_sys_reg_el 0b01#2)
                                                      (sail_sys_reg_read sys_reg_id (.Reg ESR_EL1)))
                                                  else
                                                    (do
                                                      if ((v__0 == (0xC300#16 : (BitVec 16))) : Bool)
                                                      then
                                                        (do
                                                          (check_sys_reg_el 0b01#2)
                                                          (sail_sys_reg_read sys_reg_id
                                                            (.Reg FAR_EL1)))
                                                      else
                                                        (do
                                                          if ((v__0 == (0xC3A0#16 : (BitVec 16))) : Bool)
                                                          then
                                                            (do
                                                              (check_sys_reg_el 0b01#2)
                                                              (sail_sys_reg_read sys_reg_id
                                                                (.Reg PAR_EL1)))
                                                          else
                                                            (do
                                                              if ((v__0 == (0xC600#16 : (BitVec 16))) : Bool)
                                                              then
                                                                (do
                                                                  (check_sys_reg_el 0b01#2)
                                                                  (sail_sys_reg_read sys_reg_id
                                                                    (.Reg VBAR_EL1)))
                                                              else
                                                                (do
                                                                  if ((v__0 == (0xDA10#16 : (BitVec 16))) : Bool)
                                                                  then
                                                                    (do
                                                                      (check_sys_reg_el 0b00#2)
                                                                      (pure (Sail.BitVec.zeroExtend
                                                                          ((← readReg NZCV) +++ 0x0000000#28)
                                                                          64)))
                                                                  else
                                                                    (do
                                                                      if ((v__0 == (0xDA11#16 : (BitVec 16))) : Bool)
                                                                      then
                                                                        (do
                                                                          (check_sys_reg_el 0b01#2)
                                                                          (pure (Sail.BitVec.zeroExtend
                                                                              ((← readReg DAIF) +++ 0b000000#6)
                                                                              64)))
                                                                      else
                                                                        (fail
                                                                          "Unsupported System Register"))))))))))))))))))

def write_sys_reg (sys_reg_id : (BitVec 16)) (value : (BitVec 64)) : SailM Unit := do
  let v__108 := sys_reg_id
  if ((v__108 == (0xC038#16 : (BitVec 16))) : Bool)
  then
    (do
      (check_sys_reg_el 0b01#2)
      (fail "ID_AA64MMFR0_EL1 is not writable"))
  else
    (do
      if ((v__108 == (0xC039#16 : (BitVec 16))) : Bool)
      then
        (do
          (check_sys_reg_el 0b01#2)
          (fail "ID_AA64MMFR1_EL1 is not writable"))
      else
        (do
          if ((v__108 == (0xC03A#16 : (BitVec 16))) : Bool)
          then
            (do
              (check_sys_reg_el 0b01#2)
              (fail "ID_AA64MMFR2_EL1 is not writable"))
          else
            (do
              if ((v__108 == (0xC03B#16 : (BitVec 16))) : Bool)
              then
                (do
                  (check_sys_reg_el 0b01#2)
                  (fail "ID_AA64MMFR3_EL1 is not writable"))
              else
                (do
                  if ((v__108 == (0xC03C#16 : (BitVec 16))) : Bool)
                  then
                    (do
                      (check_sys_reg_el 0b01#2)
                      (fail "ID_AA64MMFR4_EL1 is not writable"))
                  else
                    (do
                      if ((v__108 == (0xC080#16 : (BitVec 16))) : Bool)
                      then
                        (do
                          (check_sys_reg_el 0b01#2)
                          (sail_sys_reg_write sys_reg_id (.Reg SCTLR_EL1) value))
                      else
                        (do
                          if ((v__108 == (0xC100#16 : (BitVec 16))) : Bool)
                          then
                            (do
                              (check_sys_reg_el 0b01#2)
                              (sail_sys_reg_write sys_reg_id (.Reg TTBR0_EL1) value))
                          else
                            (do
                              if ((v__108 == (0xC101#16 : (BitVec 16))) : Bool)
                              then
                                (do
                                  (check_sys_reg_el 0b01#2)
                                  (sail_sys_reg_write sys_reg_id (.Reg TTBR1_EL1) value))
                              else
                                (do
                                  if ((v__108 == (0xC102#16 : (BitVec 16))) : Bool)
                                  then
                                    (do
                                      (check_sys_reg_el 0b01#2)
                                      (sail_sys_reg_write sys_reg_id (.Reg TCR_EL1) value))
                                  else
                                    (do
                                      if ((v__108 == (0xC200#16 : (BitVec 16))) : Bool)
                                      then
                                        (do
                                          (check_sys_reg_el 0b01#2)
                                          (sail_sys_reg_write sys_reg_id (.Reg SPSR_EL1) value))
                                      else
                                        (do
                                          if ((v__108 == (0xC201#16 : (BitVec 16))) : Bool)
                                          then
                                            (do
                                              (check_sys_reg_el 0b01#2)
                                              (sail_sys_reg_write sys_reg_id (.Reg ELR_EL1) value))
                                          else
                                            (do
                                              if ((v__108 == (0xC212#16 : (BitVec 16))) : Bool)
                                              then
                                                (do
                                                  (check_sys_reg_el 0b01#2)
                                                  (fail "CurrentEL is not writable"))
                                              else
                                                (do
                                                  if ((v__108 == (0xC290#16 : (BitVec 16))) : Bool)
                                                  then
                                                    (do
                                                      (check_sys_reg_el 0b01#2)
                                                      (sail_sys_reg_write sys_reg_id (.Reg ESR_EL1)
                                                        value))
                                                  else
                                                    (do
                                                      if ((v__108 == (0xC300#16 : (BitVec 16))) : Bool)
                                                      then
                                                        (do
                                                          (check_sys_reg_el 0b01#2)
                                                          (sail_sys_reg_write sys_reg_id
                                                            (.Reg FAR_EL1) value))
                                                      else
                                                        (do
                                                          if ((v__108 == (0xC3A0#16 : (BitVec 16))) : Bool)
                                                          then
                                                            (do
                                                              (check_sys_reg_el 0b01#2)
                                                              (sail_sys_reg_write sys_reg_id
                                                                (.Reg PAR_EL1) value))
                                                          else
                                                            (do
                                                              if ((v__108 == (0xC600#16 : (BitVec 16))) : Bool)
                                                              then
                                                                (do
                                                                  (check_sys_reg_el 0b01#2)
                                                                  (sail_sys_reg_write sys_reg_id
                                                                    (.Reg VBAR_EL1) value))
                                                              else
                                                                (do
                                                                  if ((v__108 == (0xDA10#16 : (BitVec 16))) : Bool)
                                                                  then
                                                                    (do
                                                                      (check_sys_reg_el 0b00#2)
                                                                      writeReg NZCV (Sail.BitVec.extractLsb
                                                                        value 31 28))
                                                                  else
                                                                    (do
                                                                      if ((v__108 == (0xDA11#16 : (BitVec 16))) : Bool)
                                                                      then
                                                                        (do
                                                                          (check_sys_reg_el 0b01#2)
                                                                          writeReg DAIF (Sail.BitVec.extractLsb
                                                                            value 9 6))
                                                                      else
                                                                        (fail
                                                                          "Unsupported System Register"))))))))))))))))))

/-- Type quantifiers: k_ex29198_ : Bool, bit_pos : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31, 0 ≤ bit_pos
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

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_TLBInvalidation (op : TLBIOp) (shareability : Shareability) (level : TLBILevel) (t : Nat) : SailM Unit := SailME.run do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let (va, asid) ← (( do
    match op with
    | .TLBIOp_ALL => (pure (none, none))
    | .TLBIOp_VMALL => (pure (none, none))
    | .TLBIOp_VA =>
      (do
        let v ← do (rX t)
        (pure ((some (decodeVA v)), (some (decodeASID v)))))
    | .TLBIOp_ASID => (pure (none, (some (decodeASID (← (rX t))))))
    | .TLBIOp_VAA => (pure ((some (decodeVA (← (rX t)))), none))
    | _ => SailME.throw (() : Unit) ) : SailME Unit ((Option (BitVec 64)) × (Option (BitVec 16))) )
  (reportTLBI op shareability level va asid)

/-- Type quantifiers: t : Nat, k_ex29200_ : Bool, 0 ≤ t ∧ t ≤ 31 -/
def execute_SystemRegisterMove (is_read : Bool) (sys_reg_id : (BitVec 16)) (t : Nat) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  if (is_read : Bool)
  then (wX t (← (read_sys_reg sys_reg_id)))
  else (write_sys_reg sys_reg_id (← (rX t)))

def execute_SupervisorCall (imm16 : (BitVec 16)) : SailM Unit := do
  let target_el := 0b01#2
  writeReg ELR_EL1 (BitVec.addInt (← readReg _PC) 4)
  let ec : (BitVec 6) := 0b010101#6
  let il := 1#1
  let iss : (BitVec 25) := (Sail.BitVec.zeroExtend imm16 25)
  writeReg ESR_EL1 (Sail.BitVec.zeroExtend ((ec +++ il) +++ iss) 64)
  (take_exception target_el none)

/-- Type quantifiers: k_ex29205_ : Bool, n : Nat, t : Nat, size : Nat, 0 ≤ size ∧ size ≤ 3, 0
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
  let accdesc ← do (create_writeAccessDescriptor release exclusive)
  let base ← do
    if ((n == 31) : Bool)
    then (rSP ())
    else (rX n)
  let vaddr ← (( do (pure (base + (← (eval_operand 64 offset)))) ) : SailME Unit (BitVec 64) )
  (check_load_store_alignment size vaddr)
  let addr ← (( do
    match (← (translate_address vaddr (2 ^i size) accdesc)) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let _ : Unit := (wMem_Addr addr)
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wMem (2 ^i size) addr (Sail.BitVec.extractLsb (← (rX t)) ((8 *i (2 ^i size)) -i 1) 0) accdesc)

/-- Type quantifiers: d : Nat, k_ex29206_ : Bool, 0 ≤ d ∧ d ≤ 31 -/
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

/-- Type quantifiers: k_ex29215_ : Bool, k_ex29214_ : Bool, k_ex29213_ : Bool, n : Nat, t : Nat, size
  : Nat, 0 ≤ size ∧ size ≤ 3, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_Load (size : Nat) (t : Nat) (n : Nat) (offset : operand) (acquire : Bool) (rcpc : Bool) (exclusive : Bool) : SailM Unit := SailME.run do
  let accdesc ← do (create_readAccessDescriptor acquire rcpc exclusive)
  let base ← do
    if ((n == 31) : Bool)
    then (rSP ())
    else (rX n)
  let vaddr ← (( do (pure (base + (← (eval_operand 64 offset)))) ) : SailME Unit (BitVec 64) )
  (check_load_store_alignment size vaddr)
  let addr ← (( do
    match (← (translate_address vaddr (2 ^i size) accdesc)) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wX t (Sail.BitVec.zeroExtend (← (rMem (2 ^i size) addr accdesc)) 64))

def execute_InstructionSynchronizationBarrier (_ : Unit) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (instructionSynchronizationBarrier ())

def execute_ExceptionReturn (_ : Unit) : SailM Unit := do
  sail_assert ((← readReg CurrentEL) != 0b00#2) "Trying to ERET from EL0, fault not implemented"
  writeReg _PC (← readReg ELR_EL1)
  (sail_return_exception ())
  let spsr ← do readReg SPSR_EL1
  sail_assert ((Sail.BitVec.extractLsb spsr 4 4) == 0#1) "AArch32 not supported"
  sail_assert (((Sail.BitVec.extractLsb spsr 3 2) == 0b00#2) || ((Sail.BitVec.extractLsb spsr 3 2) == 0b01#2)) "EL2 and EL3 not supported"
  sail_assert ((Sail.BitVec.extractLsb spsr 3 0) != 0b0001#4) "Can't have SPSel set to 1 in EL0"
  writeReg NZCV (Sail.BitVec.extractLsb spsr 31 28)
  writeReg DAIF (Sail.BitVec.extractLsb spsr 9 6)
  writeReg CurrentEL (Sail.BitVec.extractLsb spsr 3 2)
  writeReg SPSel (Sail.BitVec.extractLsb spsr 0 0)

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

/-- Type quantifiers: k_ex29217_ : Bool, t : Nat, 0 ≤ t ∧ t ≤ 31 -/
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

/-- Type quantifiers: n : Nat, d : Nat, k_ex29221_ : Bool, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧
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

/-- Type quantifiers: k_ex29229_ : Bool, k_ex29228_ : Bool, n : Nat, t : Nat, s : Nat, var_0 : Nat, 0
  ≤ var_0 ∧ var_0 ≤ 3, 0 ≤ s ∧ s ≤ 31, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_AtomicRMW (var_0 : Nat) (s : Nat) (t : Nat) (n : Nat) (op : MemAtomicOp) (acq : Bool) (rel : Bool) : SailM Unit := SailME.run do
  let size := var_0
  let accdesc ← do (create_RMWAccessDescriptor op acq rel)
  let vaddr ← do
    if ((n == 31) : Bool)
    then (rSP ())
    else (rX n)
  let addr ← (( do
    match (← (translate_address vaddr (2 ^i size) accdesc)) with
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
  | .TLBInvalidation (op, shareability, level, t) =>
    (execute_TLBInvalidation op shareability level t)
  | .SupervisorCall imm16 => (execute_SupervisorCall imm16)
  | .ExceptionReturn arg0 => (execute_ExceptionReturn arg0)
  | .SystemRegisterMove (is_read, sys_reg_id, t) =>
    (execute_SystemRegisterMove is_read sys_reg_id t)

