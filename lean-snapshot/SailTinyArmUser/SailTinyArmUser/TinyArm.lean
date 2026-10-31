import SailTinyArmUser.Flow
import SailTinyArmUser.Prelude
import SailTinyArmUser.Interface
import SailTinyArmUser.Translation
import SailTinyArmUser.Base
import SailTinyArmUser.InstrsUser

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

def decode (v__0 : (BitVec 32)) : SailM ast := do
  if ((((Sail.BitVec.extractLsb v__0 29 24) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
             v__0 21 21) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb v__0 11 10) == (0b10#2 : (BitVec 2))))) : Bool)
  then
    (do
      let S := (BitVec.access v__0 12)
      let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
      let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
      let option_v : (BitVec 3) := (Sail.BitVec.extractLsb v__0 15 13)
      let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
      let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
      let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
      let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
      (decodeLoadStoreRegister size opc Rm option_v S Rn Rt))
  else
    (do
      if (((Sail.BitVec.extractLsb v__0 29 24) == (0b111001#6 : (BitVec 6))) : Bool)
      then
        (do
          let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
          let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
          let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
          let imm12 : (BitVec 12) := (Sail.BitVec.extractLsb v__0 21 10)
          let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
          let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
          (decodeLoadStoreImmediate size opc imm12 Rn Rt))
      else
        (do
          if ((((Sail.BitVec.extractLsb v__0 29 23) == (0b0010001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                   v__0 21 10) == (0x7FF#12 : (BitVec 12)))) : Bool)
          then
            (let L := (BitVec.access v__0 22)
            let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
            let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
            let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
            let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
            let size := (BitVec.toNatInt size)
            let t : reg_index := (BitVec.toNatInt Rt)
            let n : reg_index := (BitVec.toNatInt Rn)
            if ((L == 1#1) : Bool)
            then (pure (Load (size, t, n, zero_operand, true, false, false)))
            else (pure (Store (size, t, n, zero_operand, true, none))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__0 29 10) == (0xE2FF0#20 : (BitVec 20))) : Bool)
              then
                (let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                let size := (BitVec.toNatInt size)
                let t : reg_index := (BitVec.toNatInt Rt)
                let n : reg_index := (BitVec.toNatInt Rn)
                (pure (Load (size, t, n, zero_operand, true, true, false))))
              else
                (do
                  if ((((Sail.BitVec.extractLsb v__0 29 16) == (0b00100001011111#14 : (BitVec 14))) && ((Sail.BitVec.extractLsb
                           v__0 14 10) == (0b11111#5 : (BitVec 5)))) : Bool)
                  then
                    (let o0 := (BitVec.access v__0 15)
                    let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                    let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                    let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                    let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                    let size := (BitVec.toNatInt size)
                    let t : reg_index := (BitVec.toNatInt Rt)
                    let n : reg_index := (BitVec.toNatInt Rn)
                    let acquire := (o0 == 1#1)
                    (pure (Load (size, t, n, zero_operand, acquire, false, true))))
                  else
                    (do
                      if ((((Sail.BitVec.extractLsb v__0 29 21) == (0b001000000#9 : (BitVec 9))) && ((Sail.BitVec.extractLsb
                               v__0 14 10) == (0b11111#5 : (BitVec 5)))) : Bool)
                      then
                        (do
                          let o0 := (BitVec.access v__0 15)
                          let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                          let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                          let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                          let Rs : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
                          let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                          let size := (BitVec.toNatInt size)
                          let t : reg_index := (BitVec.toNatInt Rt)
                          let n : reg_index := (BitVec.toNatInt Rn)
                          let s : reg_index := (BitVec.toNatInt Rs)
                          let release := (o0 == 1#1)
                          sail_assert (s != t) "Store exclusive can't store value and success to same register"
                          sail_assert ((s == 31) || (s != n)) "Store exclusive success can't be stored to address register"
                          (pure (Store (size, t, n, zero_operand, release, (some s)))))
                      else
                        (do
                          if ((((Sail.BitVec.extractLsb v__0 29 24) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__0 21 21) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                     v__0 11 10) == (0b00#2 : (BitVec 2))))) : Bool)
                          then
                            (do
                              let A := (BitVec.access v__0 23)
                              let R := (BitVec.access v__0 22)
                              let o3 := (BitVec.access v__0 15)
                              let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                              let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
                              let opc : (BitVec 3) := (Sail.BitVec.extractLsb v__0 14 12)
                              let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                              let Rs : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
                              let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                              let size := (BitVec.toNatInt size)
                              let s : reg_index := (BitVec.toNatInt Rs)
                              let t : reg_index := (BitVec.toNatInt Rt)
                              let n : reg_index := (BitVec.toNatInt Rn)
                              sail_assert (s != t) "sail-tiny-arm doesn't support RMW atomic with twice the same destination register"
                              let op ← (( do
                                if ((o3 == 1#1) : Bool)
                                then
                                  (do
                                    if ((opc == 0b000#3) : Bool)
                                    then (fail "Instruction not supported by design: SWP variants")
                                    else (fail "RCW instruction usupported"))
                                else
                                  (match opc with
                                  | 0b000 => (pure MemAtomicOp_ADD)
                                  | 0b001 => (pure MemAtomicOp_BIC)
                                  | 0b010 => (pure MemAtomicOp_EOR)
                                  | 0b011 => (pure MemAtomicOp_ORR)
                                  | 0b100 => (pure MemAtomicOp_SMAX)
                                  | 0b101 => (pure MemAtomicOp_SMIN)
                                  | 0b110 => (pure MemAtomicOp_UMAX)
                                  | _ => (pure MemAtomicOp_UMIN)) ) : SailM MemAtomicOp )
                              let acquire := ((A == 1#1) && (t != 31))
                              let release := (R == 1#1)
                              (pure (AtomicRMW (size, s, t, n, op, acquire, release))))
                          else
                            (do
                              if ((((Sail.BitVec.extractLsb v__0 28 24) == (0b01010#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb
                                       v__0 21 21) == (0#1 : (BitVec 1)))) : Bool)
                              then
                                (do
                                  let sf := (BitVec.access v__0 31)
                                  let shift : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
                                  let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 30 29)
                                  let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb v__0 15 10)
                                  let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                                  let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
                                  let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                                  let op := (decode_bitwise_op opc)
                                  if (((sf == 0#1) && ((BitVec.access imm6 5) == 1#1)) : Bool)
                                  then
                                    (fail
                                      "bitwise_op: shift by more than 31 bits on 32 bit operation")
                                  else (pure ())
                                  let operand :=
                                    (OperandRegShift
                                      ((BitVec.toNatInt Rm), (shift_bits_backwards shift), (BitVec.toNatInt
                                        imm6)))
                                  (pure (BitwiseLogic
                                      (sf, op, (BitVec.toNatInt Rd), (BitVec.toNatInt Rn), operand))))
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb v__0 28 23) == (0b100100#6 : (BitVec 6))) : Bool)
                                  then
                                    (do
                                      let sf := (BitVec.access v__0 31)
                                      let N := (BitVec.access v__0 22)
                                      let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 30 29)
                                      let imms : (BitVec 6) := (Sail.BitVec.extractLsb v__0 15 10)
                                      let immr : (BitVec 6) := (Sail.BitVec.extractLsb v__0 21 16)
                                      let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                                      let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                                      let op := (decode_bitwise_op opc)
                                      if (((N == 1#1) && (sf == 0#1)) : Bool)
                                      then (fail "64 bit mask in 32 bit bitwise operation")
                                      else (pure ())
                                      let (mask, _) ← do (decode_bitmask N imms immr true)
                                      (pure (BitwiseLogic
                                          (sf, op, (BitVec.toNatInt Rd), (BitVec.toNatInt Rn), (OperandImm
                                            mask)))))
                                  else
                                    (do
                                      if (((Sail.BitVec.extractLsb v__0 30 23) == (0xA5#8 : (BitVec 8))) : Bool)
                                      then
                                        (do
                                          let sf := (BitVec.access v__0 31)
                                          let imm16 : (BitVec 16) :=
                                            (Sail.BitVec.extractLsb v__0 20 5)
                                          let hw : (BitVec 2) := (Sail.BitVec.extractLsb v__0 22 21)
                                          let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                                          let d : reg_index := (BitVec.toNatInt Rd)
                                          if (((sf == 0#1) && ((BitVec.access hw 1) == 1#1)) : Bool)
                                          then
                                            (fail
                                              "MOVZ: writing the top 32 bits in a 32 bit operation")
                                          else (pure ())
                                          (pure (Movz (sf, d, imm16, (BitVec.toNatInt hw)))))
                                      else
                                        (do
                                          if (((Sail.BitVec.extractLsb v__0 28 23) == (0b100110#6 : (BitVec 6))) : Bool)
                                          then
                                            (do
                                              let sf := (BitVec.access v__0 31)
                                              let N := (BitVec.access v__0 22)
                                              let opc : (BitVec 2) :=
                                                (Sail.BitVec.extractLsb v__0 30 29)
                                              let imms : (BitVec 6) :=
                                                (Sail.BitVec.extractLsb v__0 15 10)
                                              let immr : (BitVec 6) :=
                                                (Sail.BitVec.extractLsb v__0 21 16)
                                              let Rn : (BitVec 5) :=
                                                (Sail.BitVec.extractLsb v__0 9 5)
                                              let Rd : (BitVec 5) :=
                                                (Sail.BitVec.extractLsb v__0 4 0)
                                              let d : reg_index := (BitVec.toNatInt Rd)
                                              let n : reg_index := (BitVec.toNatInt Rn)
                                              sail_assert (sf == N) "xBFM mask sizes doesn't match operation size"
                                              if ((sf == 0#1) : Bool)
                                              then
                                                sail_assert (((BitVec.access imms 5) == 0#1) && ((BitVec.access
                                                      immr 5) == 0#1)) "32bit xBFM has masks larger than 32 bits"
                                              else (pure ())
                                              let signd ← (( do
                                                match opc with
                                                | 0b00 => (pure true)
                                                | 0b10 => (pure false)
                                                | _ => (fail "xBFM opc has unsupported value") ) :
                                                SailM Bool )
                                              (pure (BitfieldMove (sf, signd, d, n, imms, immr))))
                                          else
                                            (do
                                              if (((Sail.BitVec.extractLsb v__0 28 21) == (0x59#8 : (BitVec 8))) : Bool)
                                              then
                                                (do
                                                  let sf := (BitVec.access v__0 31)
                                                  let op := (BitVec.access v__0 30)
                                                  let S := (BitVec.access v__0 29)
                                                  let option_v : (BitVec 3) :=
                                                    (Sail.BitVec.extractLsb v__0 15 13)
                                                  let imm3 : (BitVec 3) :=
                                                    (Sail.BitVec.extractLsb v__0 12 10)
                                                  let Rn : (BitVec 5) :=
                                                    (Sail.BitVec.extractLsb v__0 9 5)
                                                  let Rm : (BitVec 5) :=
                                                    (Sail.BitVec.extractLsb v__0 20 16)
                                                  let Rd : (BitVec 5) :=
                                                    (Sail.BitVec.extractLsb v__0 4 0)
                                                  (decodeAddSubExt sf op S option_v imm3 Rm Rn Rd))
                                              else
                                                (do
                                                  if ((((Sail.BitVec.extractLsb v__0 28 24) == (0b01011#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb
                                                           v__0 21 21) == (0#1 : (BitVec 1)))) : Bool)
                                                  then
                                                    (do
                                                      let sf := (BitVec.access v__0 31)
                                                      let op := (BitVec.access v__0 30)
                                                      let S := (BitVec.access v__0 29)
                                                      let shift : (BitVec 2) :=
                                                        (Sail.BitVec.extractLsb v__0 23 22)
                                                      let imm6 : (BitVec 6) :=
                                                        (Sail.BitVec.extractLsb v__0 15 10)
                                                      let Rn : (BitVec 5) :=
                                                        (Sail.BitVec.extractLsb v__0 9 5)
                                                      let Rm : (BitVec 5) :=
                                                        (Sail.BitVec.extractLsb v__0 20 16)
                                                      let Rd : (BitVec 5) :=
                                                        (Sail.BitVec.extractLsb v__0 4 0)
                                                      (decodeAddSubShift sf op S shift imm6 Rm Rn Rd))
                                                  else
                                                    (do
                                                      if (((Sail.BitVec.extractLsb v__0 28 23) == (0b100010#6 : (BitVec 6))) : Bool)
                                                      then
                                                        (let sf := (BitVec.access v__0 31)
                                                        let op := (BitVec.access v__0 30)
                                                        let S := (BitVec.access v__0 29)
                                                        let sh := (BitVec.access v__0 22)
                                                        let imm12 : (BitVec 12) :=
                                                          (Sail.BitVec.extractLsb v__0 21 10)
                                                        let Rn : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__0 9 5)
                                                        let Rd : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__0 4 0)
                                                        (pure (decodeAddSubImm sf op S sh imm12 Rn
                                                            Rd)))
                                                      else
                                                        (do
                                                          if ((((Sail.BitVec.extractLsb v__0 29 23) == (0b0010001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__0 21 21) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                     v__0 14 10) == (0b11111#5 : (BitVec 5))))) : Bool)
                                                          then
                                                            (fail
                                                              "Instruction not supported by design: CAS/CASB/CASH variants")
                                                          else
                                                            (do
                                                              if ((((Sail.BitVec.extractLsb v__0 30
                                                                       21) == (0b0011010100#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb
                                                                       v__0 11 10) == (0b00#2 : (BitVec 2)))) : Bool)
                                                              then
                                                                (fail
                                                                  "Instruction not supported by design: CSEL")
                                                              else
                                                                (do
                                                                  if ((((Sail.BitVec.extractLsb v__0
                                                                           31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
                                                                           v__0 7 0) == (0xBF#8 : (BitVec 8)))) : Bool)
                                                                  then
                                                                    (do
                                                                      let CRm : (BitVec 4) :=
                                                                        (Sail.BitVec.extractLsb v__0
                                                                          11 8)
                                                                      (decodeDataBarrier CRm false))
                                                                  else
                                                                    (do
                                                                      if ((((Sail.BitVec.extractLsb
                                                                               v__0 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
                                                                               v__0 7 0) == (0x9F#8 : (BitVec 8)))) : Bool)
                                                                      then
                                                                        (do
                                                                          let CRm : (BitVec 4) :=
                                                                            (Sail.BitVec.extractLsb
                                                                              v__0 11 8)
                                                                          (decodeDataBarrier CRm
                                                                            true))
                                                                      else
                                                                        (do
                                                                          if ((((Sail.BitVec.extractLsb
                                                                                   v__0 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
                                                                                   v__0 7 0) == (0xDF#8 : (BitVec 8)))) : Bool)
                                                                          then
                                                                            (pure (InstructionSynchronizationBarrier
                                                                                ()))
                                                                          else
                                                                            (do
                                                                              if ((v__0 == (0xD503201F#32 : (BitVec 32))) : Bool)
                                                                              then (pure (Nop ()))
                                                                              else
                                                                                (do
                                                                                  if (((Sail.BitVec.extractLsb
                                                                                         v__0 30 25) == (0b011010#6 : (BitVec 6))) : Bool)
                                                                                  then
                                                                                    (let sf :=
                                                                                      (BitVec.access
                                                                                        v__0 31)
                                                                                    let op :=
                                                                                      (BitVec.access
                                                                                        v__0 24)
                                                                                    let imm19 : (BitVec 19) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__0 23 5)
                                                                                    let Rt : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__0 4 0)
                                                                                    (pure (decodeCompareAndBranch
                                                                                        sf op imm19
                                                                                        Rt)))
                                                                                  else
                                                                                    (do
                                                                                      if (((Sail.BitVec.extractLsb
                                                                                             v__0 30
                                                                                             25) == (0b011011#6 : (BitVec 6))) : Bool)
                                                                                      then
                                                                                        (let b5 :=
                                                                                          (BitVec.access
                                                                                            v__0 31)
                                                                                        let op :=
                                                                                          (BitVec.access
                                                                                            v__0 24)
                                                                                        let imm14 : (BitVec 14) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__0 18
                                                                                            5)
                                                                                        let b40 : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__0 23
                                                                                            19)
                                                                                        let Rt : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__0 4 0)
                                                                                        (pure (decodeTestAndBranch
                                                                                            b5 op
                                                                                            b40
                                                                                            imm14 Rt)))
                                                                                      else
                                                                                        (do
                                                                                          if (((Sail.BitVec.extractLsb
                                                                                                 v__0
                                                                                                 31
                                                                                                 26) == (0b000101#6 : (BitVec 6))) : Bool)
                                                                                          then
                                                                                            (let imm26 : (BitVec 26) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__0
                                                                                                25 0)
                                                                                            let offset : (BitVec 64) :=
                                                                                              (Sail.BitVec.signExtend
                                                                                                (imm26 +++ 0b00#2)
                                                                                                64)
                                                                                            (pure (Branch
                                                                                                offset)))
                                                                                          else
                                                                                            (do
                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                       v__0
                                                                                                       31
                                                                                                       24) == (0x54#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb
                                                                                                       v__0
                                                                                                       4
                                                                                                       4) == (0#1 : (BitVec 1)))) : Bool)
                                                                                              then
                                                                                                (let imm19 : (BitVec 19) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__0
                                                                                                    23
                                                                                                    5)
                                                                                                let cond : (BitVec 4) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__0
                                                                                                    3
                                                                                                    0)
                                                                                                let offset : (BitVec 64) :=
                                                                                                  (Sail.BitVec.signExtend
                                                                                                    (imm19 +++ 0b00#2)
                                                                                                    64)
                                                                                                (pure (ConditionalBranch
                                                                                                    (offset, (cond_bits_backwards
                                                                                                      cond)))))
                                                                                              else
                                                                                                (do
                                                                                                  if (((Sail.BitVec.extractLsb
                                                                                                         v__0
                                                                                                         28
                                                                                                         24) == (0b10000#5 : (BitVec 5))) : Bool)
                                                                                                  then
                                                                                                    (let page :=
                                                                                                      (BitVec.access
                                                                                                        v__0
                                                                                                        31)
                                                                                                    let immlo : (BitVec 2) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__0
                                                                                                        30
                                                                                                        29)
                                                                                                    let immhi : (BitVec 19) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__0
                                                                                                        23
                                                                                                        5)
                                                                                                    let Rd : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__0
                                                                                                        4
                                                                                                        0)
                                                                                                    let is_page :=
                                                                                                      (page == 1#1)
                                                                                                    let offset : (BitVec 64) :=
                                                                                                      if (is_page : Bool)
                                                                                                      then
                                                                                                        (Sail.BitVec.signExtend
                                                                                                          ((immhi +++ immlo) +++ 0x000#12)
                                                                                                          64)
                                                                                                      else
                                                                                                        (Sail.BitVec.signExtend
                                                                                                          (immhi +++ immlo)
                                                                                                          64)
                                                                                                    (pure (PCRelativeAddress
                                                                                                        (is_page, (BitVec.toNatInt
                                                                                                          Rd), offset))))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                               v__0
                                                                                                               31
                                                                                                               10) == (0b1101011000011111000000#22 : (BitVec 22))) && ((Sail.BitVec.extractLsb
                                                                                                               v__0
                                                                                                               4
                                                                                                               0) == (0b00000#5 : (BitVec 5)))) : Bool)
                                                                                                      then
                                                                                                        (let Rn : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__0
                                                                                                            9
                                                                                                            5)
                                                                                                        (pure (BranchRegister
                                                                                                            (BitVec.toNatInt
                                                                                                              Rn))))
                                                                                                      else
                                                                                                        (fail
                                                                                                          "Unsupported Encoding"))))))))))))))))))))))))))

def fetch_and_execute (_ : Unit) : SailM Unit := SailME.run do
  let accdesc := (create_iFetchAccessDescriptor ())
  let addr ← (( do
    match (translate_address (← readReg _PC) 4 accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let machineCode ← do (iFetch addr accdesc)
  let instr ← do (decode machineCode)
  (execute instr)

