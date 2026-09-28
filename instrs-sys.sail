$ifdef SYSTEM_TINY_ARM
/* TLBI */
union clause ast = TLBInvalidation : (TLBIOp, Shareability, TLBILevel, reg_index)

val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> ast
function clause decode (0b1101010100001@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  let t : reg_index = unsigned(Rt);
  let (tlbi_op, shareability, level) : (TLBIOp, Shareability, TLBILevel) =
    match (op1, CRn, CRm, op2) {
      /* TLBI ALL (TLBI ALLE1) */
      (0b100, 0b1000, 0b0111, 0b100) => (TLBIOp_ALL, Shareability_NSH, TLBILevel_Any),
      /* TLBI by VMID, all ASIDs (TLBI VMALLE1IS) */
      (0b000, 0b1000, 0b0011, 0b000) => (TLBIOp_VMALL, Shareability_ISH, TLBILevel_Any),
      /* TLBI by VA (TLBI VAE1IS) */
      (0b000, 0b1000, 0b0011, 0b001) => (TLBIOp_VA, Shareability_ISH, TLBILevel_Any),
      /* TLBI by VA (TLBI VAE1) */
      (0b000, 0b1000, 0b0111, 0b001) => (TLBIOp_VA, Shareability_NSH, TLBILevel_Any),
      /* TLBI by ASID (TLBI ASIDE1IS) */
      (0b000, 0b1000, 0b0011, 0b010) => (TLBIOp_ASID, Shareability_ISH, TLBILevel_Any),
      /* TLBI by VA, all ASIDs (TLBI VAAE1IS) */
      (0b000, 0b1000, 0b0011, 0b011) => (TLBIOp_VAA, Shareability_ISH, TLBILevel_Any),
      /* TLBI by VA, last-level only (TLBI VALE1IS) */
      (0b000, 0b1000, 0b0011, 0b101) => (TLBIOp_VA, Shareability_ISH, TLBILevel_Last),
      /* TLBI by VA, all ASIDs, last-level only (TLBI VAALE1IS) */
      (0b000, 0b1000, 0b0011, 0b111) => (TLBIOp_VAA, Shareability_ISH, TLBILevel_Last),
      /* TLBI by VA, all ASIDs (TLBI VAAE1) */
      (0b000, 0b1000, 0b0111, 0b011) => (TLBIOp_VAA, Shareability_NSH, TLBILevel_Any),
      _ => fail("Unsupported TLBI operation encoding")
    };
  TLBInvalidation(tlbi_op, shareability, level, t)
}

function decodeASID(v: bits(64)) -> bits(16) = v[63..48]

function decodeVA(v: bits(64)) -> bits(64) =
  sail_zero_extend(v[43..0] @ 0x000, 64)

function clause execute TLBInvalidation(op, shareability, level, t) = {
  _PC = _PC + 4;

  let (va, asid) : (option(bits(64)), option(bits(16))) =
    match op {
      TLBIOp_ALL => (None(), None()),
      TLBIOp_VMALL => (None(), None()),
      TLBIOp_VA => {
        let v = X(t);
        (Some(decodeVA(v)), Some(decodeASID(v)))
      },
      TLBIOp_ASID => (None(), Some(decodeASID(X(t)))),
      TLBIOp_VAA => (Some(decodeVA(X(t))), None()),
      _ => return ()
    };
  reportTLBI(op, shareability, level, va, asid);
}


/* Supervisor Call (SVC) */
union clause ast = SupervisorCall : bits(16)

/* SVC #imm16: 1101 0100 000 imm16 000 01 */
function clause decode (0b11010100000@(imm16:bits(16))@0b00001) = {
  SupervisorCall(imm16)
}

function clause execute SupervisorCall(imm16) = {
  let target_el = 0b01; /* SVC always targets EL1 */

  /* Save return address (next instruction after SVC) - must be done before _PC is modified */
  ELR_EL1 = _PC + 4;

  /* Build ESR_EL1: EC=0b010101 (SVC from AArch64), IL=1, ISS=imm16 */
  let ec : bits(6) = 0b010101;
  let il : bits(1) = 0b1;
  let iss : bits(25) = sail_zero_extend(imm16, 25);
  ESR_EL1 = sail_zero_extend((ec @ il) @ iss, 64);

  take_exception(target_el, None())
}


/* Exception Return (ERET) - EL1 only */
union clause ast = ExceptionReturn : unit

/* ERET: 1101 0110 1001 1111 0000 0011 1110 0000 */
function clause decode (0b11010110100111110000001111100000) = {
  ExceptionReturn()
}

function clause execute ExceptionReturn() = {
  assert (CurrentEL != 0b00, "Trying to ERET from EL0, fault not implemented");
  /* Set PC to the exception link register (no +4 increment) */
  _PC = ELR_EL1;

  /* Read saved program status register */
  let spsr = SPSR_EL1;
  assert (spsr[4..4] == 0b0, "AArch32 not supported");
  assert (spsr[3..2] == 0b00 | spsr[3..2] == 0b01,
          "EL2 and EL3 not supported");
  assert (spsr[3..0] != 0b0001, "Can't have SPSel set to 1 in EL0");

  NZCV = spsr[31..28];
  DAIF = spsr[9..6];
  CurrentEL = spsr[3..2];
  SPSel = spsr[0..0];
}

/* MRS/MSR: Move to/from system registers */
/* is_read: true = MRS (read from system register), false = MSR (write to system register) */
/* The SysRegID is op0 @ op1 @ CRn @ CRm @ op2, taken from the instruction bits:
     sys_reg_id[15..14] = op0 = 0b1 @ instr[19] (o0)
     sys_reg_id[13..11] = op1 = instr[18..16]
     sys_reg_id[10..7]  = CRn = instr[15..12]
     sys_reg_id[6..3]   = CRm = instr[11..8]
     sys_reg_id[2..0]   = op2 = instr[7..5] */
union clause ast = SystemRegisterMove : (/*is_read */bool, SysRegID, reg_index)

val decodeSystemRegisterMove :
    (bool, bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> ast

/* MRS: 1101 0101 0011 op1 CRn CRm op2 Rt (L=1) */
/* MSR: 1101 0101 0001 op1 CRn CRm op2 Rt (L=0) */
function clause decode (0b1101010100@[L]@0b1@(o0:bits(1))@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  let op0 : bits(2) = 0b1 @ o0;
  decodeSystemRegisterMove(L == bitone, op0, op1, CRn, CRm, op2, Rt)
}

function decodeSystemRegisterMove(is_read, op0, op1, CRn, CRm, op2, Rt) = {
  let sys_reg_id = op0 @ op1 @ CRn @ CRm @ op2;
  SystemRegisterMove(is_read, sys_reg_id, unsigned(Rt))
}


val check_sys_reg_el : bits(2) -> unit
function check_sys_reg_el(min_el) =
  assert(unsigned(CurrentEL) >= unsigned(min_el),
         "Trying to access system register from too-low EL, fault not implemented")

val read_sys_reg : SysRegID -> bits(64)
function read_sys_reg(sys_reg_id) = {
  match sys_reg_id {
    0b11@0b000@0b0000@0b0111@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ID_AA64MMFR0_EL1) },
    0b11@0b000@0b0000@0b0111@0b001 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ID_AA64MMFR1_EL1) },
    0b11@0b000@0b0000@0b0111@0b010 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ID_AA64MMFR2_EL1) },
    0b11@0b000@0b0000@0b0111@0b011 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ID_AA64MMFR3_EL1) },
    0b11@0b000@0b0000@0b0111@0b100 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ID_AA64MMFR4_EL1) },
    0b11@0b000@0b0001@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref SCTLR_EL1) },
    0b11@0b000@0b0010@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref TTBR0_EL1) },
    0b11@0b000@0b0010@0b0000@0b001 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref TTBR1_EL1) },
    0b11@0b000@0b0010@0b0000@0b010 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref TCR_EL1) },
    0b11@0b000@0b0100@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref SPSR_EL1) },
    0b11@0b000@0b0100@0b0000@0b001 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ELR_EL1) },
    0b11@0b000@0b0100@0b0010@0b010 => { check_sys_reg_el(0b01); sail_zero_extend(CurrentEL @ 0b00, 64) },
    0b11@0b000@0b0101@0b0010@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref ESR_EL1) },
    0b11@0b000@0b0110@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref FAR_EL1) },
    0b11@0b000@0b0111@0b0100@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref PAR_EL1) },
    0b11@0b000@0b1100@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_read(sys_reg_id, ref VBAR_EL1) },
    0b11@0b011@0b0100@0b0010@0b000 => { check_sys_reg_el(0b00); sail_zero_extend(NZCV @ 0x0000000, 64) },
    0b11@0b011@0b0100@0b0010@0b001 => { check_sys_reg_el(0b01); sail_zero_extend(DAIF @ 0b000000, 64) },
    _ => fail("Unsupported System Register")
  }
}

val write_sys_reg : (SysRegID, bits(64)) -> unit
function write_sys_reg(sys_reg_id, value) = {
  match sys_reg_id {
    0b11@0b000@0b0000@0b0111@0b000 => { check_sys_reg_el(0b01); fail("ID_AA64MMFR0_EL1 is not writable") },
    0b11@0b000@0b0000@0b0111@0b001 => { check_sys_reg_el(0b01); fail("ID_AA64MMFR1_EL1 is not writable") },
    0b11@0b000@0b0000@0b0111@0b010 => { check_sys_reg_el(0b01); fail("ID_AA64MMFR2_EL1 is not writable") },
    0b11@0b000@0b0000@0b0111@0b011 => { check_sys_reg_el(0b01); fail("ID_AA64MMFR3_EL1 is not writable") },
    0b11@0b000@0b0000@0b0111@0b100 => { check_sys_reg_el(0b01); fail("ID_AA64MMFR4_EL1 is not writable") },
    0b11@0b000@0b0001@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref SCTLR_EL1, value) },
    0b11@0b000@0b0010@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref TTBR0_EL1, value) },
    0b11@0b000@0b0010@0b0000@0b001 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref TTBR1_EL1, value) },
    0b11@0b000@0b0010@0b0000@0b010 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref TCR_EL1, value) },
    0b11@0b000@0b0100@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref SPSR_EL1, value) },
    0b11@0b000@0b0100@0b0000@0b001 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref ELR_EL1, value) },
    0b11@0b000@0b0100@0b0010@0b010 => { check_sys_reg_el(0b01); fail("CurrentEL is not writable") },
    0b11@0b000@0b0101@0b0010@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref ESR_EL1, value) },
    0b11@0b000@0b0110@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref FAR_EL1, value) },
    0b11@0b000@0b0111@0b0100@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref PAR_EL1, value) },
    0b11@0b000@0b1100@0b0000@0b000 => { check_sys_reg_el(0b01); sail_sys_reg_write(sys_reg_id, ref VBAR_EL1, value) },
    0b11@0b011@0b0100@0b0010@0b000 => { check_sys_reg_el(0b00); NZCV = value[31..28] },
    0b11@0b011@0b0100@0b0010@0b001 => { check_sys_reg_el(0b01); DAIF = value[9..6] },
    _ => fail("Unsupported System Register")
  }
}


function clause execute SystemRegisterMove(is_read, sys_reg_id, t) = {
  _PC = _PC + 4;

  if is_read then X(t) = read_sys_reg(sys_reg_id)
  else write_sys_reg(sys_reg_id, X(t))
}
$endif
