// This catch-all clause MUST be the last clause for the `decode` function.
function clause decode(_) = { None() }


function fetch_and_execute () = {
  let accdesc = create_iFetchAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(_PC, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  let machineCode = iFetch(addr, accdesc);
  let instr = decode(machineCode);
  match instr {
    Some (instr) => execute(instr),
    None () => assert (false, concat_str("Unsupported Encoding: ", bits_str(machineCode)))
  }
}
