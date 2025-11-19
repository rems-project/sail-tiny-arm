$ifdef SYSTEM_TINY_ARM
/* TLBI */
val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)

function clause decode (0b110101010000@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  /* We are only considering EL1 operations here */
  match (op1, CRn, CRm, op2) {
    /* TLBI ALL */
    (0b001, 0b1000, 0b0111, 0b100) => Some(TLBInvalidation(TLBIOp_ALL, None())),
    /* TLBI by VA (TLBI VAE1) */
    (0b000, 0b1000, 0b0111, 0b001) => Some(TLBInvalidation(TLBIOp_VA, Some(unsigned(Rt)))),
    /* TLBI by ASID */
    (0b000, 0b1001, 0b0011, 0b010) => Some(TLBInvalidation(TLBIOp_ASID, Some(unsigned(Rt)))),
    /* TLBI by VA, all ASIDs */
    (0b000, 0b1000, 0b0011, 0b011) => Some(TLBInvalidation(TLBIOp_VAA, Some(unsigned(Rt)))),
    _ => None()
  }
}

function clause execute TLBInvalidation(op, t_opt) = {
  let addr : bits(64) = match t_opt {
    Some(t) => X(t),
    None() => 0x0000000000000000
  };
  let asid = ASID_read();

  reportTLBI(op, addr, asid);
}
$endif
