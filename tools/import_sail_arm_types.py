#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

START = "Definition bits (n : Z) : Type := mword n.\n\n"
END = "#[export]\nInstance dummy_Barrier : Inhabited (Barrier) := { inhabitant := Barrier_DSB inhabitant }.\n\n"
SAIL_ARM_IMPORT = "Require Import SailArm.armv9_types.\n"
SAIL_ARM_EXPORT = "From SailArm Require Export armv9_types.\n"
LATE_REGISTER_REF = "Definition register_ref := @register_ref register type_of_register.\n"
REGISTER_BLOCK_END = "Definition register_accessors : SailStdpp.Values.register_accessors regstate register type_of_register := (@register_lookup, @register_set).\n"
MODEL_HELPER_INSERTION_POINT = "Open Scope Z.\n\n"
SYSTEM_REGISTER_HELPERS = """
Definition read_TTBR0_EL1_64 '(tt : unit) : M (mword 64) :=
  ((read_reg TTBR0_EL1) : M (mword 128)) >>= fun w =>
  returnM (subrange_vec_dec w 63 0).

Definition read_TTBR1_EL1_64 '(tt : unit) : M (mword 64) :=
  ((read_reg TTBR1_EL1) : M (mword 128)) >>= fun w =>
  returnM (subrange_vec_dec w 63 0).

Definition write_PAR_EL1_64 (w : mword 64) : M unit :=
  write_reg _PAR_EL1 (zero_extend w 128).

Definition write_TTBR0_EL1_64 (w : mword 64) : M unit :=
  write_reg TTBR0_EL1 (zero_extend w 128).

Definition write_TTBR1_EL1_64 (w : mword 64) : M unit :=
  write_reg TTBR1_EL1 (zero_extend w 128).

Definition write_TTBR0_EL2_64 (w : mword 64) : M unit :=
  write_reg TTBR0_EL2 (zero_extend w 128).

Definition write_TTBR1_EL2_64 (w : mword 64) : M unit :=
  write_reg TTBR1_EL2 (zero_extend w 128).

Definition write_VTTBR_EL2_64 (w : mword 64) : M unit :=
  write_reg VTTBR_EL2 (zero_extend w 128).

"""


def remove_local_register_block(text: str) -> str:
    start = text.find("\nVariant register_")
    if start == -1:
        raise SystemExit("local register block start not found")
    start += 1
    end = text.find(REGISTER_BLOCK_END, start)
    if end == -1:
        raise SystemExit("local register block end not found")
    return text[:start] + text[end:]


def fix_register_namespace(text: str) -> str:
    text = text.replace(
        "Definition register_accessors : register_accessors regstate register type_of_register :=",
        "Definition register_accessors : SailStdpp.Values.register_accessors regstate register type_of_register :=",
    )
    text = text.replace(
        "Definition read_reg {E} := @read_reg register type_of_register E.",
        "Definition read_reg {E} := @SailStdpp.Prompt_monad.read_reg register type_of_register E.",
    )
    text = text.replace(
        "Definition write_reg {E} := @write_reg register type_of_register E.",
        "Definition write_reg {E} := @SailStdpp.Prompt_monad.write_reg register type_of_register E.",
    )
    text = text.replace(
        "Module Arch <: Arch.",
        "Module Arch <: SailStdpp.ConcurrencyInterfaceV2.Arch.",
    )
    text = text.replace(
        "Module Interface := Interface Arch.",
        "Module Interface := SailStdpp.ConcurrencyInterfaceV2.Interface Arch.",
    )
    text = text.replace(
        "Module Defs := Defs Arch Interface.",
        "Module Defs := SailStdpp.ConcurrencyInterfaceBuiltinsV2.Defs Arch Interface.",
    )
    text = "\n".join(line for line in text.splitlines() if line != LATE_REGISTER_REF.rstrip("\n"))
    text = remove_local_register_block(text)
    return text


def remove_shared_interface_block(path: Path, text: str) -> str:
    if SAIL_ARM_IMPORT in text:
        text = text.replace(SAIL_ARM_IMPORT, SAIL_ARM_EXPORT, 1)
    elif SAIL_ARM_EXPORT not in text:
        raise SystemExit(f"{path}: SailArm Coq import not found; expected --coq-alt-modules")

    if START not in text:
        raise SystemExit(f"{path}: shared interface type block start not found")

    start = text.index(START)
    try:
        end = text.index(END, start) + len(END)
    except ValueError as exc:
        raise SystemExit(f"{path}: shared interface type block end not found") from exc
    return text[:start] + text[end:]


def import_sail_arm_types(path: Path) -> None:
    text = path.read_text()
    text = remove_shared_interface_block(path, text)
    path.write_text(fix_register_namespace(text))


def align_sail_arm_register_uses(path: Path) -> None:
    text = path.read_text()
    text = text.replace(SAIL_ARM_IMPORT, "", 1)
    replacements = {
        "((read_reg TTBR0_EL1)  : M (mword 64))": "((read_TTBR0_EL1_64 (tt))  : M (mword 64))",
        "((read_reg TTBR1_EL1)  : M (mword 64))": "((read_TTBR1_EL1_64 (tt))  : M (mword 64))",
        "write_reg PAR_EL1 ": "write_PAR_EL1_64 ",
        "write_reg TTBR0_EL1 ": "write_TTBR0_EL1_64 ",
        "write_reg TTBR1_EL1 ": "write_TTBR1_EL1_64 ",
        "write_reg TTBR0_EL2 ": "write_TTBR0_EL2_64 ",
        "write_reg TTBR1_EL2 ": "write_TTBR1_EL2_64 ",
        "write_reg VTTBR_EL2 ": "write_VTTBR_EL2_64 ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    if "read_TTBR0_EL1_64" in text and SYSTEM_REGISTER_HELPERS not in text:
        if MODEL_HELPER_INSERTION_POINT not in text:
            raise SystemExit(f"{path}: model helper insertion point not found")
        text = text.replace(
            MODEL_HELPER_INSERTION_POINT,
            MODEL_HELPER_INSERTION_POINT + SYSTEM_REGISTER_HELPERS,
            1,
        )
    path.write_text(text)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        raise SystemExit("usage: import_sail_arm_types.py <Coq types file>...")
    for arg in argv[1:]:
        path = Path(arg)
        if path.name.endswith("_types.v"):
            import_sail_arm_types(path)
        else:
            align_sail_arm_register_uses(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
