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

/* MRS/MSR: Move to/from System Register */
/* is_read: true = MRS (read from system register), false = MSR (write to system register) */
union clause ast = SystemRegisterMove : (bool, bits(3), bits(4), bits(4), bits(3), reg_index)

val decodeSystemRegisterMove :
    (bool, bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)

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
