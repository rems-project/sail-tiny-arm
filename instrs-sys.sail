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

function clause execute TLBInvalidation(op, t) = {
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
}


union clause ast = SystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), reg_index)

val decodeSystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)

/* MRS: 1 1 0 1 0 1 0 1 0 0 1 1 op1CRnCRmop2 Rt */
/* MSR: 1 1 0 1 0 1 0 1 0 0 0 1 op1CRnCRmop2 Rt */
/* Combined: 1101010100 L 1 ... */
function clause decode (0b1101010100@(L:bits(1))@0b1@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeSystemRegisterMove(L == 0b1, op1, CRn, CRm, op2, Rt)
}

function decodeSystemRegisterMove(is_read, op1, CRn, CRm, op2, Rt) = {
   Some(SystemRegisterMove(is_read, op1, CRn, CRm, op2, unsigned(Rt)))
   /* Note: We defer validation to execution time or we could check lookup here.
      Sail's decode generally allows returning Some(ast) for valid encodings even if the specific system register is potentially unsupported,
      but checking here is also valid.
      For now, we return Some(ast) for all encodings matching the MSR/MRS pattern to keep decoders simple. */
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
$endif
