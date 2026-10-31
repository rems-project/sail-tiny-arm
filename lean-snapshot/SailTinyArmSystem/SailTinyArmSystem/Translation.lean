import SailTinyArmSystem.SailTinyArmSystem
import SailTinyArmSystem.Prelude
import SailTinyArmSystem.Interface

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

def undefined_Permissions (_ : Unit) : SailM Permissions := do
  (pure { allow_write := ← (undefined_bool ())
          allow_unprivileged_data := ← (undefined_bool ())
          allow_unprivileged_exec := ← (undefined_bool ())
          allow_privileged_exec := ← (undefined_bool ()) })

def extract_perms_table (descriptor : (BitVec 64)) : Permissions :=
  let ap_table := (Sail.BitVec.extractLsb descriptor 62 61)
  { allow_write := ((BitVec.access ap_table 1) == 0#1)
    allow_unprivileged_data := ((BitVec.access ap_table 0) == 0#1)
    allow_unprivileged_exec := ((BitVec.access descriptor 60) == 0#1)
    allow_privileged_exec := ((BitVec.access descriptor 59) == 0#1) }

def extract_perms_leaf (descriptor : (BitVec 64)) : Permissions :=
  let ap := (Sail.BitVec.extractLsb descriptor 7 6)
  { allow_write := ((BitVec.access ap 1) == 0#1)
    allow_unprivileged_data := ((BitVec.access ap 0) == 1#1)
    allow_unprivileged_exec := ((BitVec.access descriptor 54) == 0#1)
    allow_privileged_exec := ((BitVec.access descriptor 53) == 0#1) }

def leaf_access_flag_set (descriptor : (BitVec 64)) : Bool :=
  ((BitVec.access descriptor 10) == 1#1)

def leaf_dirty_bit_set (descriptor : (BitVec 64)) : Bool :=
  ((BitVec.access descriptor 51) == 1#1)

/-- Type quantifiers: k_ex29074_ : Bool -/
def create_AccessDescriptorTTW (toplevel : Bool) (varange : VARange) : SailM AccessDescriptor := do
  let accdesc : AccessDescriptor := (base_AccessDescriptor AccessType_TTW)
  let accdesc ← (pure { accdesc with el := ← readReg CurrentEL })
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with toplevel := toplevel }
  (pure { accdesc with varange := varange })

def get_VARange (va : (BitVec 64)) : VARange :=
  if (((BitVec.access va 48) == 0#1) : Bool)
  then VARange_LOWER
  else VARange_UPPER

def va_out_of_range (va : (BitVec 64)) : Bool :=
  (! (((Sail.BitVec.extractLsb va 63 48) == 0x0000#16) || ((Sail.BitVec.extractLsb va 63 48) == 0xFFFF#16)))

def get_translation_base_address (varange : VARange) : SailM (BitVec 56) := do
  let ttbr ← (( do
    match varange with
    | .VARange_LOWER => readReg TTBR0_EL1
    | .VARange_UPPER => readReg TTBR1_EL1 ) : SailM (BitVec 64) )
  let baddr := (BitVec.zero 56)
  (pure (Sail.BitVec.updateSubrange baddr 47 5 (Sail.BitVec.extractLsb ttbr 47 5)))

def ASID_read (_ : Unit) : SailM (BitVec 16) := do
  if (((BitVec.slice (← readReg TCR_EL1) 22 1) == (BitVec.zero 1)) : Bool)
  then (pure (BitVec.slice (← readReg TTBR0_EL1) 48 16))
  else (pure (BitVec.slice (← readReg TTBR1_EL1) 48 16))

def is_fault (addrdesc : AddressDescriptor) : Bool :=
  match addrdesc.fault.statuscode with
  | .Fault_None => false
  | _ => true

def check_permission (perms : Permissions) (accdesc : AccessDescriptor) : Bool :=
  let at_el0 := (accdesc.el == 0b00#2)
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then
    (if (at_el0 : Bool)
    then perms.allow_unprivileged_exec
    else perms.allow_privileged_exec)
  else
    (if ((accdesc.write && (! perms.allow_write)) : Bool)
    then false
    else
      (if ((at_el0 && (! perms.allow_unprivileged_data)) : Bool)
      then false
      else true))

/-- Type quantifiers: level : Nat, 0 ≤ level ∧ level ≤ 3 -/
def get_TTEntryAddress (level : Nat) (ia : (BitVec 64)) (baseaddress : (BitVec 56)) : (BitVec 56) :=
  let stride := 9
  let lsb := (((3 -i level) *i stride) +i 12)
  let msb := ((lsb +i stride) -i 1)
  let index := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb ia msb lsb) +++ (BitVec.zero 3)) 56)
  (baseaddress ||| index)

/-- Type quantifiers: level : Int -/
def decode_desc_type (descriptor : (BitVec 64)) (level : Int) : DescriptorType :=
  if (((BitVec.access descriptor 0) == 0#1) : Bool)
  then DescriptorType_Invalid
  else
    (if (((BitVec.access descriptor 1) == 1#1) : Bool)
    then
      (if ((level == 3) : Bool)
      then DescriptorType_Leaf
      else DescriptorType_Table)
    else
      (if (((BitVec.access descriptor 1) == 0#1) : Bool)
      then
        (if (((level == 1) || (level == 2)) : Bool)
        then DescriptorType_Leaf
        else DescriptorType_Invalid)
      else DescriptorType_Invalid))

def pgt_walk (va : (BitVec 64)) (accdesc : AccessDescriptor) : SailM AddressDescriptor := SailME.run do
  let varange := (get_VARange va)
  let baseaddress ← do (get_translation_base_address varange)
  let descaddress := (get_TTEntryAddress 0 va baseaddress)
  let addrdesc := (base_AddressDescriptor accdesc)
  let addrdesc : AddressDescriptor := { addrdesc with vaddress := va }
  let addrdesc : AddressDescriptor :=
    { addrdesc with fault := { addrdesc.fault with write := accdesc.write } }
  let addrdesc : AddressDescriptor :=
    { addrdesc with fault := { addrdesc.fault with access := accdesc } }
  let (addrdesc, descaddress) ← (( do
    let loop_level_lower := 0
    let loop_level_upper := 3
    let mut loop_vars := (addrdesc, descaddress)
    for level in [loop_level_lower:loop_level_upper:1]i do
      let (addrdesc, descaddress) := loop_vars
      loop_vars ← do
        let addrdesc : AddressDescriptor :=
          { addrdesc with fault := { addrdesc.fault with level := level } }
        let walkaccess ← do (create_AccessDescriptorTTW (level == 0) varange)
        let descriptor ← do (read_memory 8 descaddress walkaccess)
        let (addrdesc, descaddress) ← (( do
          match (decode_desc_type descriptor level) with
          | .DescriptorType_Table =>
            (do
              let perms := (extract_perms_table descriptor)
              let (addrdesc, descaddress) ← (( do
                if ((! (check_permission perms accdesc)) : Bool)
                then
                  (do
                    let a__120 : AddressDescriptor :=
                      ({ addrdesc with fault := { addrdesc.fault with statuscode := Fault_Permission } } : AddressDescriptor)
                    SailME.throw a__120)
                else
                  (do
                    let next_baseaddress :=
                      (0x00#8 +++ ((Sail.BitVec.extractLsb descriptor 47 12) +++ 0x000#12))
                    sail_assert (level <b 3) "Table entry at level 3"
                    let descaddress : (BitVec 56) :=
                      (get_TTEntryAddress (level +i 1) va next_baseaddress)
                    (pure (addrdesc, descaddress))) ) : SailME AddressDescriptor
                (AddressDescriptor × (BitVec 56)) )
              (pure (addrdesc, descaddress)))
          | .DescriptorType_Leaf =>
            (do
              let a__121 ← (( do
                if ((! (leaf_access_flag_set descriptor)) : Bool)
                then
                  (pure { addrdesc with fault := { addrdesc.fault with statuscode := Fault_AccessFlag } })
                else
                  (do
                    if ((leaf_dirty_bit_set descriptor) : Bool)
                    then (fail "Dirty bit set in translation descriptor")
                    else (pure ())
                    let perms := (extract_perms_leaf descriptor)
                    if ((! (check_permission perms accdesc)) : Bool)
                    then
                      (pure { addrdesc with fault := { addrdesc.fault with statuscode := Fault_Permission } })
                    else
                      (let offset := (12 +i ((3 -i level) *i 9))
                      let out_pa :=
                        (0x00#8 +++ ((Sail.BitVec.extractLsb descriptor 47 offset) +++ (Sail.BitVec.extractLsb
                              va (offset -i 1) 0)))
                      (pure { addrdesc with paddress := { addrdesc.paddress with address := out_pa } })))
                ) : SailME AddressDescriptor AddressDescriptor )
              SailME.throw a__121)
          | .DescriptorType_Invalid =>
            (do
              let a__123 : AddressDescriptor :=
                ({ addrdesc with fault := { addrdesc.fault with statuscode := Fault_Translation } } : AddressDescriptor)
              SailME.throw a__123) ) : SailME AddressDescriptor (AddressDescriptor × (BitVec 56)) )
        (pure (addrdesc, descaddress))
    (pure loop_vars) ) : SailME AddressDescriptor (AddressDescriptor × (BitVec 56)) )
  throw Error.Exit

def take_exception (target_el : (BitVec 2)) (fault : (Option FaultRecord)) : SailM Unit := do
  (sail_take_exception fault)
  let source_el ← do readReg CurrentEL
  let vect_offset ← (( do
    if ((source_el == target_el) : Bool)
    then
      (do
        if (((← readReg SPSel) == 0#1) : Bool)
        then (pure 0x000#12)
        else (pure 0x200#12))
    else (pure 0x400#12) ) : SailM (BitVec 12) )
  writeReg _PC ((Sail.BitVec.extractLsb (← readReg VBAR_EL1) 63 12) +++ vect_offset)
  writeReg SPSR_EL1 ((BitVec.zero 32) +++ ((← readReg NZCV) +++ ((BitVec.zero 18) +++ ((← readReg DAIF) +++ (0b00#2 +++ ((← readReg CurrentEL) +++ (0#1 +++ (← readReg SPSel))))))))
  writeReg CurrentEL 0b01#2
  writeReg SPSel 1#1
  writeReg DAIF 0b1111#4

def handle_fault (addrdesc : AddressDescriptor) : SailM Unit := do
  let fault : FaultRecord := addrdesc.fault
  let vaddress := addrdesc.vaddress
  let source_el := fault.access.el
  let target_el := 0b01#2
  let ec := 0b000000#6
  let il := 1#1
  let ec ← (( do
    if ((BEq.beq fault.access.acctype AccessType_IFETCH) : Bool)
    then
      (if ((source_el == target_el) : Bool)
      then (pure 0b100001#6)
      else (pure 0b100000#6))
    else
      (do
        if ((BEq.beq fault.access.acctype AccessType_GPR) : Bool)
        then
          (if ((source_el == target_el) : Bool)
          then (pure 0b100101#6)
          else (pure 0b100100#6))
        else
          (do
            throw Error.Exit
            (pure ec))) ) : SailM (BitVec 6) )
  let level_bit ← (( do
    match fault.level with
    | 0 => (pure 0b00#2)
    | 1 => (pure 0b01#2)
    | 2 => (pure 0b10#2)
    | 3 => (pure 0b11#2)
    | _ => throw Error.Exit ) : SailM (BitVec 2) )
  let dfsc : (BitVec 6) :=
    if ((BEq.beq fault.statuscode Fault_Translation) : Bool)
    then (0b0001#4 +++ level_bit)
    else
      (if ((BEq.beq fault.statuscode Fault_AccessFlag) : Bool)
      then (0b0010#4 +++ level_bit)
      else
        (if ((BEq.beq fault.statuscode Fault_Permission) : Bool)
        then (0b0011#4 +++ level_bit)
        else 0b000000#6))
  let wnr :=
    if (fault.write : Bool)
    then 1#1
    else 0#1
  let iss := (Sail.BitVec.zeroExtend (wnr +++ dfsc) 25)
  writeReg ESR_EL1 (Sail.BitVec.zeroExtend ((ec +++ il) +++ iss) 64)
  writeReg FAR_EL1 vaddress
  writeReg ELR_EL1 (← readReg _PC)
  (take_exception target_el (some fault))

/-- Type quantifiers: access_size : Int -/
def translate_address (va : (BitVec 64)) (access_size : Int) (accdesc : AccessDescriptor) : SailM (Option (BitVec 56)) := do
  if (((BitVec.access (← readReg SCTLR_EL1) 0) == 0#1) : Bool)
  then (pure (some (Sail.BitVec.truncate va addr_size')))
  else
    (do
      let cnp ← do
        if ((BEq.beq (get_VARange va) VARange_LOWER) : Bool)
        then (pure (BitVec.slice (← readReg TTBR0_EL1) 0 1))
        else (pure (BitVec.slice (← readReg TTBR1_EL1) 0 1))
      let tsi ← (( do
        (pure { ss := SS_NonSecure
                regime := Regime_EL10
                vmid := 0x0000#16
                asid := ← (ASID_read ())
                va := va
                cnp := cnp
                accdesc := accdesc
                size := access_size }) ) : SailM TranslationStartInfo )
      (sail_translation_start tsi)
      let addrdesc ← do
        if ((va_out_of_range va) : Bool)
        then
          (let addrdesc := (base_AddressDescriptor accdesc)
          let addrdesc : AddressDescriptor := { addrdesc with vaddress := va }
          let addrdesc : AddressDescriptor :=
            { addrdesc with fault := { addrdesc.fault with statuscode := Fault_Translation } }
          let addrdesc : AddressDescriptor :=
            { addrdesc with fault := { addrdesc.fault with write := accdesc.write } }
          (pure { addrdesc with fault := { addrdesc.fault with access := accdesc } }))
        else (pgt_walk va accdesc)
      (sail_translation_end addrdesc)
      if ((is_fault addrdesc) : Bool)
      then
        (do
          (handle_fault addrdesc)
          (pure none))
      else (pure (some addrdesc.paddress.address)))

