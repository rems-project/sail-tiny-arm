scattered union ast

union clause ast = LoadRegister : (reg_index, reg_index, reg_index)
union clause ast = StoreRegister : (reg_index, reg_index, reg_index)
union clause ast = ExclusiveOr : (reg_index, reg_index, reg_index)
union clause ast = DataMemoryBarrier : MBReqTypes
union clause ast = DataSynchronizationBarrier : MBReqTypes
union clause ast = InstructionSynchronizationBarrier : unit
union clause ast = CompareAndBranch : (reg_index, bits(64))

$ifdef SYSTEM_TINY_ARM
union clause ast = TLBInvalidation : (TLBIOp, option(reg_index))
$endif

val decode : bits(32) -> option(ast)
scattered function decode

val execute : ast -> unit
scattered function execute

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit

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
    None () => assert (false, "Unsupported Encoding")
  }
}
