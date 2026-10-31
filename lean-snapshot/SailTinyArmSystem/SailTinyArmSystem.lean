import SailTinyArmSystem.TinyArm

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

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg _PC (← (undefined_bitvector 64))
  writeReg R30 (← (undefined_bitvector 64))
  writeReg R29 (← (undefined_bitvector 64))
  writeReg R28 (← (undefined_bitvector 64))
  writeReg R27 (← (undefined_bitvector 64))
  writeReg R26 (← (undefined_bitvector 64))
  writeReg R25 (← (undefined_bitvector 64))
  writeReg R24 (← (undefined_bitvector 64))
  writeReg R23 (← (undefined_bitvector 64))
  writeReg R22 (← (undefined_bitvector 64))
  writeReg R21 (← (undefined_bitvector 64))
  writeReg R20 (← (undefined_bitvector 64))
  writeReg R19 (← (undefined_bitvector 64))
  writeReg R18 (← (undefined_bitvector 64))
  writeReg R17 (← (undefined_bitvector 64))
  writeReg R16 (← (undefined_bitvector 64))
  writeReg R15 (← (undefined_bitvector 64))
  writeReg R14 (← (undefined_bitvector 64))
  writeReg R13 (← (undefined_bitvector 64))
  writeReg R12 (← (undefined_bitvector 64))
  writeReg R11 (← (undefined_bitvector 64))
  writeReg R10 (← (undefined_bitvector 64))
  writeReg R9 (← (undefined_bitvector 64))
  writeReg R8 (← (undefined_bitvector 64))
  writeReg R7 (← (undefined_bitvector 64))
  writeReg R6 (← (undefined_bitvector 64))
  writeReg R5 (← (undefined_bitvector 64))
  writeReg R4 (← (undefined_bitvector 64))
  writeReg R3 (← (undefined_bitvector 64))
  writeReg R2 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg R0 (← (undefined_bitvector 64))
  writeReg CurrentEL (← (undefined_bitvector 2))
  writeReg NZCV (← (undefined_bitvector 4))
  writeReg SP_EL0 (← (undefined_bitvector 64))
  writeReg SPSel (← (undefined_bitvector 1))
  writeReg DAIF (← (undefined_bitvector 4))
  writeReg SP_EL1 (← (undefined_bitvector 64))
  writeReg SP_EL2 (← (undefined_bitvector 64))
  writeReg SP_EL3 (← (undefined_bitvector 64))
  writeReg ELR_EL1 (← (undefined_bitvector 64))
  writeReg ELR_EL2 (← (undefined_bitvector 64))
  writeReg ELR_EL3 (← (undefined_bitvector 64))
  writeReg ESR_EL1 (← (undefined_bitvector 64))
  writeReg ESR_EL2 (← (undefined_bitvector 64))
  writeReg ESR_EL3 (← (undefined_bitvector 64))
  writeReg FAR_EL1 (← (undefined_bitvector 64))
  writeReg FAR_EL2 (← (undefined_bitvector 64))
  writeReg FAR_EL3 (← (undefined_bitvector 64))
  writeReg PAR_EL1 (← (undefined_bitvector 64))
  writeReg TTBR0_EL1 (← (undefined_bitvector 64))
  writeReg TTBR1_EL1 (← (undefined_bitvector 64))
  writeReg TTBR0_EL2 (← (undefined_bitvector 64))
  writeReg TTBR1_EL2 (← (undefined_bitvector 64))
  writeReg TTBR0_EL3 (← (undefined_bitvector 64))
  writeReg VTTBR_EL2 (← (undefined_bitvector 64))
  writeReg VBAR_EL1 (← (undefined_bitvector 64))
  writeReg VBAR_EL2 (← (undefined_bitvector 64))
  writeReg VBAR_EL3 (← (undefined_bitvector 64))
  writeReg SPSR_EL1 (← (undefined_bitvector 64))
  writeReg SPSR_EL2 (← (undefined_bitvector 64))
  writeReg SPSR_EL3 (← (undefined_bitvector 64))
  writeReg ID_AA64MMFR0_EL1 (← (undefined_bitvector 64))
  writeReg ID_AA64MMFR1_EL1 (← (undefined_bitvector 64))
  writeReg ID_AA64MMFR2_EL1 (← (undefined_bitvector 64))
  writeReg ID_AA64MMFR3_EL1 (← (undefined_bitvector 64))
  writeReg ID_AA64MMFR4_EL1 (← (undefined_bitvector 64))
  writeReg TCR_EL1 (← (undefined_bitvector 64))
  writeReg TCR_EL2 (← (undefined_bitvector 64))
  writeReg TCR_EL3 (← (undefined_bitvector 64))
  writeReg VTCR_EL2 (← (undefined_bitvector 64))
  writeReg SCTLR_EL1 (← (undefined_bitvector 64))
  writeReg SCTLR_EL2 (← (undefined_bitvector 64))
  writeReg SCTLR_EL3 (← (undefined_bitvector 64))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end SailTinyArmSystem.Functions
