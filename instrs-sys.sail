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
}
$endif
