#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

START = "Definition bits (n : Z) : Type := mword n.\n\n"
END = "#[export]\nInstance dummy_Barrier : Inhabited (Barrier) := { inhabitant := Barrier_DSB inhabitant }.\n\n"
REPLACEMENT = "From SailArm Require Export armv9_types.\n\n"
EARLY_REGISTER_REF = "Definition register_ref := @SailStdpp.Values.register_ref register type_of_register.\n\n"
LATE_REGISTER_REF = "Definition register_ref := @register_ref register type_of_register.\n"


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
    first_ref = text.find(" : register_ref _ :=")
    if first_ref == -1:
        raise SystemExit("register_ref use not found")
    line_start = text.rfind("\nDefinition ", 0, first_ref)
    if line_start == -1:
        raise SystemExit("register_ref definition line not found")
    line_start += 1
    if EARLY_REGISTER_REF not in text[:line_start]:
        text = text[:line_start] + EARLY_REGISTER_REF + text[line_start:]
    return text


def import_sail_arm_types(path: Path) -> None:
    text = path.read_text()
    if START in text:
        start = text.index(START)
        try:
            end = text.index(END, start) + len(END)
        except ValueError as exc:
            raise SystemExit(f"{path}: shared interface type block end not found") from exc
        text = text[:start] + REPLACEMENT + text[end:]
    elif REPLACEMENT not in text:
        raise SystemExit(f"{path}: shared interface type block start not found")

    path.write_text(fix_register_namespace(text))


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        raise SystemExit("usage: import_sail_arm_types.py <Coq types file>...")
    for arg in argv[1:]:
        import_sail_arm_types(Path(arg))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
