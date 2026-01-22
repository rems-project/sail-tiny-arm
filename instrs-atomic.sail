union clause ast = LoadExclusive : (reg_index, reg_index)

/* LDXR Xt, [Xn]
 * Encoding: 11 001000 0 1 0 11111 0 11111 Rn Rt */
function clause decode (0b11@0b001000@0b0@0b1@0b0@0b11111@0b0@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(LoadExclusive(unsigned(Rt), unsigned(Rn)))
}

/* LDXR Xt, [Xn] - 64-bit */
function clause execute LoadExclusive(t, n) = {
  let addr = X(n);
  let accdesc = create_readAccessDescriptor(true, false, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  _PC = _PC + 4;
  let data = rMem(addr, accdesc);
  X(t) = data;
}

union clause ast = StoreExclusive : (reg_index, reg_index, reg_index)

/* STXR Ws, Xt, [Xn]
 * Encoding: 11 001000 0 0 0 Rs 0 11111 Rn Rt */
function clause decode (0b11@0b001000@0b0@0b0@0b0@(Rs:bits(5))@0b0@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(StoreExclusive(unsigned(Rs), unsigned(Rt), unsigned(Rn)))
}

/* STXR Ws, Xt, [Xn] - 64-bit */
function clause execute StoreExclusive(s, t, n) = {
  let addr = X(n);
  let accdesc = create_writeAccessDescriptor(true, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  wMem_Addr(addr);
  _PC = _PC + 4;
  let data = X(t);

  /* Attempt the exclusive write; status is 0 on success, 1 on failure */
  let status = wMemExclusive(addr, data, accdesc);
  X(s) = sail_zero_extend(status, 64);
}

union clause ast = LoadAcquireExclusive : (reg_index, reg_index)

/* LDAXR Xt, [Xn]
 * Encoding: 11 001000 0 1 0 11111 1 11111 Rn Rt */
function clause decode (0b11@0b001000@0b0@0b1@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(LoadAcquireExclusive(unsigned(Rt), unsigned(Rn)))
}

/* LDAXR Xt, [Xn] - 64-bit */
function clause execute LoadAcquireExclusive(t, n) = {
  let addr = X(n);
  let accdesc = create_readAccessDescriptor(true, true, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  _PC = _PC + 4;
  let data = rMem(addr, accdesc);
  X(t) = data;
}

union clause ast = StoreReleaseExclusive : (reg_index, reg_index, reg_index)

/* STLXR Ws, Xt, [Xn]
 * Encoding: 11 001000 0 0 0 Rs 1 11111 Rn Rt */
function clause decode (0b11@0b001000@0b0@0b0@0b0@(Rs:bits(5))@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(StoreReleaseExclusive(unsigned(Rs), unsigned(Rt), unsigned(Rn)))
}

/* STLXR Ws, Xt, [Xn] - 64-bit */
function clause execute StoreReleaseExclusive(s, t, n) = {
  let addr = X(n);
  let accdesc = create_writeAccessDescriptor(true, true);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  wMem_Addr(addr);
  _PC = _PC + 4;
  let data = X(t);

  let status = wMemExclusive(addr, data, accdesc);
  X(s) = sail_zero_extend(status, 64);
}

/* ========================================================================
 * Load-Acquire Register (LDAR) - 64-bit
 * ========================================================================
 *
 * Load with acquire semantics - all loads and stores after this
 * instruction in program order are guaranteed to be observed after
 * this load.
 */

union clause ast = LoadAcquire : (reg_index, reg_index)

/* LDAR Xt, [Xn]
 * Encoding: 11 001000 1 1 0 11111 1 11111 Rn Rt */
function clause decode (0b11@0b001000@0b1@0b1@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(LoadAcquire(unsigned(Rt), unsigned(Rn)))
}

/* LDAR Xt, [Xn] - 64-bit */
function clause execute LoadAcquire(t, n) = {
  let addr = X(n);
  let accdesc = create_readAccessDescriptor(false, true, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  _PC = _PC + 4;
  let data = rMem(addr, accdesc);
  X(t) = data;
}

union clause ast = StoreRelease : (reg_index, reg_index)

/* STLR Xt, [Xn]
 * Encoding: 11 001000 1 0 0 11111 1 11111 Rn Rt */
function clause decode (0b11@0b001000@0b1@0b0@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(StoreRelease(unsigned(Rt), unsigned(Rn)))
}

/* STLR Xt, [Xn] - 64-bit */
function clause execute StoreRelease(t, n) = {
  let addr = X(n);
  let accdesc = create_writeAccessDescriptor(false, true);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  wMem_Addr(addr);
  _PC = _PC + 4;
  let data = X(t);
  wMem(addr, data, accdesc);
}
