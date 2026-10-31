import SailTinyArmUser.Flow

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

def rPC (_ : Unit) : SailM (BitVec 64) := do
  readReg _PC

def wPC (pc : (BitVec 64)) : SailM Unit := do
  writeReg _PC pc

def GPRs : (Vector (RegisterRef (BitVec 64)) 31) :=
  #v[(.Reg R0), (.Reg R1), (.Reg R2), (.Reg R3), (.Reg R4), (.Reg R5), (.Reg R6), (.Reg R7), (.Reg R8), (.Reg R9), (.Reg R10), (.Reg R11), (.Reg R12), (.Reg R13), (.Reg R14), (.Reg R15), (.Reg R16), (.Reg R17), (.Reg R18), (.Reg R19), (.Reg R20), (.Reg R21), (.Reg R22), (.Reg R23), (.Reg R24), (.Reg R25), (.Reg R26), (.Reg R27), (.Reg R28), (.Reg R29), (.Reg R30)]

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def wX (n : Nat) (value : (BitVec 64)) : SailM Unit := do
  if ((n != 31) : Bool)
  then writeRegRef (GetElem?.getElem! GPRs n) value
  else (pure ())

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def rX (n : Nat) : SailM (BitVec 64) := do
  if ((n != 31) : Bool)
  then (reg_deref (GetElem?.getElem! GPRs n))
  else (pure 0x0000000000000000#64)

/-- Type quantifiers: n : Nat, size : Nat, List.elem size [8, 16, 32, 64], 0 ≤ n ∧ n ≤ 31 -/
def rXS (n : Nat) (size : Nat) : SailM (BitVec size) := do
  (pure (Sail.BitVec.extractLsb (← (rX n)) (size -i 1) 0))

/-- Type quantifiers: n : Nat, size : Nat, List.elem size [8, 16, 32, 64], 0 ≤ n ∧ n ≤ 31 -/
def wXS (n : Nat) (size : Nat) (value : (BitVec size)) : SailM Unit := do
  (wX n (Sail.BitVec.zeroExtend value 64))

def CurrentEL : (BitVec 2) := 0b00#2

def rN (_ : Unit) : SailM (BitVec 1) := do
  (pure (BitVec.access (← readReg NZCV) 3))

def wN (bit : (BitVec 1)) : SailM Unit := do
  writeReg NZCV (BitVec.update (← readReg NZCV) 3 bit)

def rZ (_ : Unit) : SailM (BitVec 1) := do
  (pure (BitVec.access (← readReg NZCV) 2))

def wZ (bit : (BitVec 1)) : SailM Unit := do
  writeReg NZCV (BitVec.update (← readReg NZCV) 2 bit)

def rC (_ : Unit) : SailM (BitVec 1) := do
  (pure (BitVec.access (← readReg NZCV) 1))

def wC (bit : (BitVec 1)) : SailM Unit := do
  writeReg NZCV (BitVec.update (← readReg NZCV) 1 bit)

def rV (_ : Unit) : SailM (BitVec 1) := do
  (pure (BitVec.access (← readReg NZCV) 0))

def wV (bit : (BitVec 1)) : SailM Unit := do
  writeReg NZCV (BitVec.update (← readReg NZCV) 0 bit)

def rSP (_ : Unit) : SailM (BitVec 64) := do
  readReg SP_EL0

def wSP (sp : (BitVec 64)) : SailM Unit := do
  writeReg SP_EL0 sp

/-- Type quantifiers: size : Nat, List.elem size [8, 16, 32, 64] -/
def rSPS (size : Nat) : SailM (BitVec size) := do
  (pure (Sail.BitVec.extractLsb (← (rSP ())) (size -i 1) 0))

/-- Type quantifiers: size : Nat, List.elem size [8, 16, 32, 64] -/
def wSPS (size : Nat) (value : (BitVec size)) : SailM Unit := do
  (wSP (Sail.BitVec.zeroExtend value 64))

