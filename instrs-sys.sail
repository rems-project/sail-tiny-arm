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
$endif
