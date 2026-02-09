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
$endif
