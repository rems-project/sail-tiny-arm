$ifdef SYSTEM_TINY_ARM
/* TLBI */
union clause ast = TLBInvalidation : (bits(3), bits(4), bits(4), bits(3), reg_index)

val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)
function clause decode (0b1101010100001@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  Some(TLBInvalidation(op1, CRn, CRm, op2, unsigned(Rt)))
}

val lookup_tlbi : (bits(3), bits(4), bits(4), bits(3)) -> option(TLBIOp)
function lookup_tlbi(op1, CRn, CRm, op2) = {
  /* We are only considering invalidations applied to EL1 in the ISH domain */
  match (op1, CRn, CRm, op2) {
    /* TLBI ALL (TLBI ALLE1IS) */
    (0b100, 0b1000, 0b0111, 0b100) => Some(TLBIOp_ALL),
    /* TLBI by VA (TLBI VAE1IS) */
    (0b000, 0b1000, 0b0011, 0b001) => Some(TLBIOp_VA),
    /* TLBI by ASID (TLBI ASIDE1IS) */
    (0b000, 0b1000, 0b0011, 0b010) => Some(TLBIOp_ASID),
    /* TLBI by VA, all ASIDs (TLBI VAAE1IS) */
    (0b000, 0b1000, 0b0011, 0b011) => Some(TLBIOp_VAA),
    _ => None()
  }
}

function clause execute TLBInvalidation(op1, CRn, CRm, op2, t) = {
  let tlbi_op_opt = lookup_tlbi(op1, CRn, CRm, op2);
  match tlbi_op_opt {
    Some(op) => {
      let (va, asid) : (option(bits(64)), option(bits(16))) =
        match op {
          TLBIOp_ALL => (None(), None()),
          TLBIOp_VA => (Some(X(t)), None()),
          TLBIOp_ASID => (None(), Some(X(t)[63..48])),
          TLBIOp_VAA => (Some(X(t)), None()),
          _ => return ()
        };

      _PC = _PC + 4;
      reportTLBI(op, va, asid);
    },
    None() => assert(false, "Unsupported TLBI Operation")
  }
}


union clause ast = SystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), reg_index)

val decodeSystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)

/* MRS: 1 1 0 1 0 1 0 1 0 0 1 1 op1CRnCRmop2 Rt */
/* MSR: 1 1 0 1 0 1 0 1 0 0 0 1 op1CRnCRmop2 Rt */
/* Combined: 1101010100 L 1 ... */
function clause decode (0b1101010100@(L:bits(1))@0b11@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeSystemRegisterMove(L == 0b1, op1, CRn, CRm, op2, Rt)
}

function decodeSystemRegisterMove(is_read, op1, CRn, CRm, op2, Rt) = {
   Some(SystemRegisterMove(is_read, op1, CRn, CRm, op2, unsigned(Rt)))
}

val lookup_sys_reg : (bits(3), bits(4), bits(4), bits(3)) -> option(register(bits(64)))
function lookup_sys_reg(op1, CRn, CRm, op2) = {
  match (op1, CRn, CRm, op2) {
    (0b000, 0b0001, 0b0000, 0b000) => Some(ref SCTLR_EL1),
    (0b000, 0b0010, 0b0000, 0b000) => Some(ref TTBR0_EL1),
    (0b000, 0b0010, 0b0000, 0b001) => Some(ref TTBR1_EL1),
    (0b000, 0b0010, 0b0000, 0b010) => Some(ref TCR_EL1),
    (0b000, 0b0100, 0b0000, 0b000) => Some(ref SPSR_EL1),
    (0b000, 0b0100, 0b0000, 0b001) => Some(ref ELR_EL1),
    (0b000, 0b0101, 0b0010, 0b000) => Some(ref ESR_EL1),
    (0b000, 0b0110, 0b0000, 0b000) => Some(ref FAR_EL1),
    (0b000, 0b0111, 0b0100, 0b000) => Some(ref PAR_EL1),
    (0b000, 0b1100, 0b0000, 0b000) => Some(ref VBAR_EL1),
    _ => None()
  }
}

function clause execute SystemRegisterMove(is_read, op1, CRn, CRm, op2, t) = {
  _PC = _PC + 4;
  let sys_reg_opt = lookup_sys_reg(op1, CRn, CRm, op2);
  match sys_reg_opt {
    Some(reg_ref) => {
      if is_read then {
        /* MRS Xt, <reg> */
        X(t) = *reg_ref
      } else {
        /* MSR <reg>, Xt */
        *reg_ref = X(t)
      }
    },
    None() => assert(false, "Unsupported System Register")
  }
}

/* Supervisor Call (SVC) */
union clause ast = SupervisorCall : bits(16)

/* SVC #imm16: 1101 0100 000 imm16 000 01 */
function clause decode (0b11010100000@(imm16:bits(16))@0b00001) = {
  Some(SupervisorCall(imm16))
}

function clause execute SupervisorCall(imm16) = {
  let source_el = PSTATE.EL;
  let target_el = 0b01; // SVC always targets EL1

  /* Determine vector offset based on source EL */
  let vect_offset =
    if source_el == target_el then {
      if PSTATE.SP == 0b0 then {
        0x000
      } else {
        0x200
      }
    } else {
      0x400
    };

  /* Report exception for tracing (no fault record for SVC) */
  sail_take_exception(None());

  /* Build ESR_EL1: EC=0b010101 (SVC from AArch64), IL=1, ISS=imm16 */
  let ec = 0b010101;
  let il = 0b1;
  let iss = sail_zero_extend(imm16, 25);
  ESR_EL1 = sail_zero_extend((ec @ il) @ iss, 64);

  /* Save PSTATE to SPSR_EL1 */
  SPSR_EL1 = sail_zero_extend(
    PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V @
    0b0000000000000000000 @
    PSTATE.D @
    PSTATE.A @
    PSTATE.I @
    PSTATE.F @
    0b00 @
    PSTATE.EL @
    0b0 @
    PSTATE.SP,
    64
  );

  /* Save return address (next instruction after SVC) */
  ELR_EL1 = _PC + 4;

  /* Transition to EL1 and use SP_EL1 */
  PSTATE.EL = 0b01;
  PSTATE.SP = 0b1;

  /* Mask interrupts on exception entry */
  PSTATE.D = 0b1;
  PSTATE.A = 0b1;
  PSTATE.I = 0b1;
  PSTATE.F = 0b1;

  /* Jump to exception vector */
  _PC = slice(VBAR_EL1, 12, 52) @ vect_offset;
}

/* Exception Return (ERET) - EL1 only */
union clause ast = ExceptionReturn : unit

/* ERET: 1101 0110 1001 1111 0000 0011 1110 0000 */
function clause decode (0b11010110100111110000001111100000) = {
  Some(ExceptionReturn())
}

function clause execute ExceptionReturn() = {
  /* Read saved program status register */
  let spsr = SPSR_EL1;

  /* Restore PSTATE fields from SPSR */
  PSTATE.N = spsr[31..31];
  PSTATE.Z = spsr[30..30];
  PSTATE.C = spsr[29..29];
  PSTATE.V = spsr[28..28];
  PSTATE.D = spsr[9..9];
  PSTATE.A = spsr[8..8];
  PSTATE.I = spsr[7..7];
  PSTATE.F = spsr[6..6];
  PSTATE.EL = spsr[3..2];
  PSTATE.SP = spsr[0..0];

  /* Set PC to the exception link register (no +4 increment) */
  _PC = ELR_EL1;
}
$endif
