$ifdef SYSTEM_TINY_ARM
/* TLBI */
union clause ast = TLBInvalidation : (TLBIOp, reg_index)

val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)
function clause decode (0b1101010100001@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  let t : reg_index = unsigned(Rt);
  /* We are only considering invalidations applied to EL1 in the ISH domain */
  let tlbi_op : TLBIOp =
    match (op1, CRn, CRm, op2) {
      /* TLBI ALL (TLBI ALLE1IS) */
      (0b100, 0b1000, 0b0111, 0b100) => TLBIOp_ALL,
      /* TLBI by VA (TLBI VAE1IS) */
      (0b000, 0b1000, 0b0011, 0b001) => TLBIOp_VA,
      /* TLBI by ASID (TLBI ASIDE1IS) */
      (0b000, 0b1000, 0b0011, 0b010) => TLBIOp_ASID,
      /* TLBI by VA, all ASIDs (TLBI VAAE1IS) */
      (0b000, 0b1000, 0b0011, 0b011) => TLBIOp_VAA,
      _ => return None()
    };
  Some(TLBInvalidation(tlbi_op, t))
}

function decodeASID(v: bits(64)) -> bits(16) = v[63..48]

function decodeVA(v: bits(64)) -> bits(64) =
  sail_zero_extend(v[43..0] @ 0x000, 64)

function clause execute TLBInvalidation(op, t) = {
  _PC = _PC + 4;

  let (va, asid) : (option(bits(64)), option(bits(16))) =
    match op {
      TLBIOp_ALL => (None(), None()),
      TLBIOp_VA => {
        let v = X(t);
        (Some(decodeVA(v)), Some(decodeASID(v)))
      },
      TLBIOp_ASID => (None(), Some(decodeASID(X(t)))),
      TLBIOp_VAA => (Some(decodeVA(X(t))), None()),
      _ => return ()
    };
  reportTLBI(op, va, asid);
}

/* Supervisor Call (SVC) */
union clause ast = SupervisorCall : bits(16)

/* SVC #imm16: 1101 0100 000 imm16 000 01 */
function clause decode (0b11010100000@(imm16:bits(16))@0b00001) = {
  Some(SupervisorCall(imm16))
}

function clause execute SupervisorCall(imm16) = {
  let source_el = PSTATE.EL;
  let target_el = 0b01; /* SVC always targets EL1 */

  /* Determine vector offset based on source EL */
  let vect_offset : bits(12) =
    if source_el == target_el then {
      if PSTATE.SP == 0b0 then 0x000 else 0x200
    } else {
      0x400
    };

  /* Report exception for tracing (no fault record for SVC) */
  sail_take_exception(None());

  /* Save return address (next instruction after SVC) - must be done before _PC is modified */
  ELR_EL1 = _PC + 4;

  /* Jump to exception vector */
  _PC = VBAR_EL1[63..12] @ vect_offset;

  /* Build ESR_EL1: EC=0b010101 (SVC from AArch64), IL=1, ISS=imm16 */
  let ec : bits(6) = 0b010101;
  let il : bits(1) = 0b1;
  let iss : bits(25) = sail_zero_extend(imm16, 25);
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

  /* Transition to EL1 and use SP_EL1 */
  /* Mask interrupts on exception entry */
  PSTATE = {PSTATE with
    EL = 0b01,
    SP = 0b1,
    D = 0b1,
    A = 0b1,
    I = 0b1,
    F = 0b1
  };
}

/* Exception Return (ERET) - EL1 only */
union clause ast = ExceptionReturn : unit

/* ERET: 1101 0110 1001 1111 0000 0011 1110 0000 */
function clause decode (0b11010110100111110000001111100000) = {
  Some(ExceptionReturn())
}

function clause execute ExceptionReturn() = {
  /* Set PC to the exception link register (no +4 increment) */
  _PC = ELR_EL1;

  /* Read saved program status register */
  let spsr = SPSR_EL1;

  /* Restore PSTATE fields from SPSR */
  let new_pstate = {PSTATE with
    N = spsr[31..31],
    Z = spsr[30..30],
    C = spsr[29..29],
    V = spsr[28..28],
    D = spsr[9..9],
    A = spsr[8..8],
    I = spsr[7..7],
    F = spsr[6..6],
    EL = spsr[3..2],
    SP = spsr[0..0]
  };
  PSTATE = new_pstate;
}

/* CMP Xn/Wn, Xm/Wm or CMP Xn/Wn, #imm - sets NZCV flags (system mode) */
function clause execute Compare(sf, n, op) = {
  _PC = _PC + 4;
  if sf == bitone then {
    /* 64-bit */
    let op1 : bits(64) = X(n);
    let op2 : bits(64) = match op {
      OperandReg(m) => X(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 64)
    };
    let result : bits(65) = sail_zero_extend(op1, 65) + sail_zero_extend(not_vec(op2), 65) + 1;
    let result64 : bits(64) = result[63..0];
    /* Set condition flags */
    let sign1 = op1[63..63];
    let sign2 = op2[63..63];
    let signr = result64[63..63];
    let overflow : bool = (sign1 != sign2) & (sign1 != signr);
    PSTATE = {PSTATE with
      N = signr,
      Z = if result64 == 0x0000000000000000 then 0b1 else 0b0,
      C = result[64..64],
      V = if overflow then 0b1 else 0b0
    };
  } else {
    /* 32-bit */
    let op1 : bits(32) = W(n);
    let op2 : bits(32) = match op {
      OperandReg(m) => W(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 32)
    };
    let result : bits(33) = sail_zero_extend(op1, 33) + sail_zero_extend(not_vec(op2), 33) + 1;
    let result32 : bits(32) = result[31..0];
    /* Set condition flags */
    let sign1 = op1[31..31];
    let sign2 = op2[31..31];
    let signr = result32[31..31];
    let overflow : bool = (sign1 != sign2) & (sign1 != signr);
    PSTATE = {PSTATE with
      N = signr,
      Z = if result32 == 0x00000000 then 0b1 else 0b0,
      C = result[32..32],
      V = if overflow then 0b1 else 0b0
    };
  }
}

/* Helper: Check condition code against NZCV flags */
val condition_holds : bits(4) -> bool
function condition_holds(cond) = {
  let n = PSTATE.N == 0b1;
  let z = PSTATE.Z == 0b1;
  let c = PSTATE.C == 0b1;
  let v = PSTATE.V == 0b1;
  match cond {
    0b0000 => z,              /* EQ: Z == 1 */
    0b0001 => not_bool(z),    /* NE: Z == 0 */
    0b0010 => c,              /* CS/HS: C == 1 */
    0b0011 => not_bool(c),    /* CC/LO: C == 0 */
    0b0100 => n,              /* MI: N == 1 */
    0b0101 => not_bool(n),    /* PL: N == 0 */
    0b0110 => v,              /* VS: V == 1 */
    0b0111 => not_bool(v),    /* VC: V == 0 */
    0b1000 => c & not_bool(z),     /* HI: C == 1 && Z == 0 */
    0b1001 => not_bool(c) | z,     /* LS: C == 0 || Z == 1 */
    0b1010 => n == v,         /* GE: N == V */
    0b1011 => n != v,         /* LT: N != V */
    0b1100 => not_bool(z) & (n == v), /* GT: Z == 0 && N == V */
    0b1101 => z | (n != v),   /* LE: Z == 1 || N != V */
    0b1110 => true,           /* AL: always */
    0b1111 => true            /* NV: always (as AL) */
  }
}

/* CSEL Xd/Wd, Xn/Wn, Xm/Wm, cond - Conditional Select */
function clause execute ConditionalSelect(sf, d, n, m, cond) = {
  _PC = _PC + 4;
  let cond_holds = condition_holds(cond);
  if sf == bitone then {
    /* 64-bit */
    X(d) = if cond_holds then X(n) else X(m);
  } else {
    /* 32-bit */
    W(d) = if cond_holds then W(n) else W(m);
  }
}

/* MRS/MSR: Move to/from System Register */
/* is_read: true = MRS (read from system register), false = MSR (write to system register) */
union clause ast = SystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), reg_index)

val decodeSystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)

/* MRS: 1101 0101 0011 op1 CRn CRm op2 Rt (L=1) */
/* MSR: 1101 0101 0001 op1 CRn CRm op2 Rt (L=0) */
function clause decode (0b1101010100@[L]@0b11@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeSystemRegisterMove(L == bitone, op1, CRn, CRm, op2, Rt)
}

function decodeSystemRegisterMove(is_read, op1, CRn, CRm, op2, Rt) = {
   Some(SystemRegisterMove(is_read, op1, CRn, CRm, op2, unsigned(Rt)))
}

/* Lookup system register by encoding */
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

/* TODO: System register access should use sys_reg_read/sys_reg_write outcomes
 * instead of plain register access. Waiting for decision on identifier format. */
function clause execute SystemRegisterMove(is_read, op1, CRn, CRm, op2, t) = {
  _PC = _PC + 4;
  let sys_reg_opt = lookup_sys_reg(op1, CRn, CRm, op2);
  match sys_reg_opt {
    Some(reg_ref) => {
      if is_read then {
        /* MRS Xt, <reg> - read from system register */
        /* TODO: use sys_reg_read outcome */
        X(t) = *reg_ref
      } else {
        /* MSR <reg>, Xt - write to system register */
        /* TODO: use sys_reg_write outcome */
        *reg_ref = X(t)
      }
    },
    None() =>
      assert(false,
        concat_str("Unsupported System Register: ", concat_str((if is_read then "MRS" else "MSR"),
        concat_str(" op1=", concat_str(bits_str(op1),
        concat_str(" CRn=", concat_str(bits_str(CRn),
        concat_str(" CRm=", concat_str(bits_str(CRm),
        concat_str(" op2=", concat_str(bits_str(op2),
        concat_str(" Rt=", dec_str(t)))))))))))))
  }
}
$endif
