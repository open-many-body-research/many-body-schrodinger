#!/usr/bin/env python3
"""Run `#print axioms` on every Lean declaration cited by a tier-L claim.

Generates lean/.axiom_audit/AxiomAudit.lean, runs it with `lake env lean`
inside lean/, and fails unless every declaration depends only on the standard
axioms propext, Classical.choice and Quot.sound.
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    claims = yaml.safe_load((ROOT / "claims" / "registry.yaml").read_text())["claims"]
    targets = []
    for c in claims:
        if c.get("tier") == "L":
            for d in c.get("lean") or []:
                targets.append((c["id"], d["module"], d["decl"]))
    if not targets:
        print("axiom_audit: no tier-L declarations")
        return 0

    # One audit file per module: foundation modules are never imported together,
    # and co-importing independent versions could clash on declaration names.
    out_dir = LEAN / ".axiom_audit"
    out_dir.mkdir(exist_ok=True)
    output = ""
    for module in sorted({m for _, m, _ in targets}):
        decls = [d for _, m, d in targets if m == module]
        audit = out_dir / f"Audit_{module}.lean"
        audit.write_text(f"import {module}\n\n" + "".join(f"#print axioms {d}\n" for d in decls))
        proc = subprocess.run(
            ["lake", "env", "lean", str(audit.relative_to(LEAN))],
            cwd=LEAN, capture_output=True, text=True,
        )
        output += f"== {module}\n{proc.stdout}{proc.stderr}"
        if proc.returncode != 0:
            (out_dir / "axiom-audit.log").write_text(output)
            print(output)
            print(f"axiom_audit: FAIL (lean exited with an error on {module})")
            return 1
    (out_dir / "axiom-audit.log").write_text(output)

    # Messages look like:
    #   'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]
    #   'Foo.baz' does not depend on any axioms
    found: dict[str, set[str]] = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S):
        found[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        found[m.group(1)] = set()

    errors = []
    for cid, _, decl in targets:
        if decl not in found:
            errors.append(f"{cid}: no axiom report for {decl}")
        elif found[decl] - ALLOWED:
            errors.append(f"{cid}: {decl} uses non-standard axioms {sorted(found[decl] - ALLOWED)}")
        else:
            print(f"  ok  {cid}  {decl}  {sorted(found[decl])}")
    if errors:
        print("\n".join(errors))
        print(f"axiom_audit: FAIL ({len(errors)} errors)")
        return 1
    print(f"axiom_audit: PASS ({len(targets)} declarations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
