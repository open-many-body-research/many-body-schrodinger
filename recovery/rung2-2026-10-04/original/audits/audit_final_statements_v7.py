#!/usr/bin/env python3
"""Read-only proof-source audit against the disclosed pinned object cache.

Version 7 uses declaration helper v2 for exact pinned Mathlib infinite sum/product tokens.
Version 6 printer failure, fallback, and resource-omission checks are unchanged.
Raw-on-error diagnostics are enabled for investigation, never accepted as strict evidence.
Version 5 conservative declaration discovery and version 4 axiom-free parsing remain.
All version 3 completeness, unexpected-axiom, immutability and ellipsis checks remain.
Produces a new timestamped source, log, and source/object hash receipt each run.
The source modules and successful previous records are never changed. Run only
after the selected modules have compiled from their final source revisions.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from lean_declaration_discovery_v2 import discover_declarations

HERE = Path(__file__).resolve().parent
CONTINUATION = HERE.parent
ROOT = CONTINUATION.parents[1]
MODULES = sys.argv[1:]
if not MODULES or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", x) for x in MODULES):
    raise SystemExit("supply valid, already-built module names")
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
OUT = HERE / "formal_semantics" / STAMP
OUT.mkdir(parents=True, exist_ok=False)
LEAN = ROOT / "formal/.lake/tooling/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean"
PATHS = [CONTINUATION / "lean/build", ROOT / "THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/lean/build"]
PATHS.extend(p / ".lake/build/lib/lean" for p in sorted((ROOT / "formal/.lake/packages").iterdir())
             if (p / ".lake/build/lib/lean").is_dir())
ENV = dict(os.environ, LEAN_PATH=":".join(map(str, PATHS)), GIT_OPTIONAL_LOCKS="0")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def printer_failure_diagnostics(log):
    """Fail closed on known Lean printer failure/fallback/omission diagnostics.

    Literal patterns come from pinned Lean/Util/PPExt.lean and
    Lean/PrettyPrinter/Delaborator/Basic.lean. Matching entire log lines is
    intentionally conservative; a matching quoted literal also rejects the run.
    Raw fallback text is retained for diagnosis but cannot satisfy strict output.
    """
    patterns = (
        "failed to pretty print",
        "[Error pretty printing",
        "Falling back to raw printer",
        "Term omitted due to reaching",
        "maximum recursion depth has been reached",
    )
    return [{"line": number, "text": line}
            for number, line in enumerate(log.splitlines(), 1)
            if any(pattern.casefold() in line.casefold() for pattern in patterns)]

records = []
declarations = []
for module in MODULES:
    source = CONTINUATION / "lean" / (module + ".lean")
    obj = CONTINUATION / "lean/build" / (module + ".olean")
    if not obj.is_file():
        raise SystemExit(f"required built object missing: {obj}")
    text = source.read_text()
    namespace, names = discover_declarations(text)
    declarations.extend((namespace + "." + name) for name in names)
    records.append({"module": module, "source": str(source), "source_sha256": sha(source),
                    "object": str(obj), "object_sha256": sha(obj), "declarations": names,
                    "forbidden_source_tokens": re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", text)})

definitions = ["Coordinate", "Configuration", "Position", "SpinConfiguration", "SpatialL2", "SpinSpace",
               "permuteSpace", "permuteSpin", "pullback", "fermionicSubspace", "coulombPotential",
               "WeakPartial", "HasH2", "targetDomain", "scalarHamiltonianGraph", "hamiltonianGraph"]
lines = [*("import " + module for module in MODULES), "", "-- Human-readable physical definitions."]
if any(module in MODULES for module in ("GraphAssembly_v2", "WeakDomainAlgebra_v2", "CoulombOperatorCore_v2")):
    lines.extend("#print TheoremT.Continuum." + definition for definition in definitions)
lines.extend(["", "-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.",
              "-- Instance implementations are suppressed; proof arguments in types are printed.",
              "set_option pp.all true", "set_option pp.universes true",
              "set_option pp.instances false", "set_option pp.proofs true",
              "set_option pp.maxSteps 2000000", "set_option maxRecDepth 16384",
              "set_option pp.rawOnError true"])
lines.extend("#check @" + declaration for declaration in declarations)
lines.extend(["", "set_option pp.all false", "set_option pp.universes false",
              "-- Kernel axiom dependencies for every local declaration."])
lines.extend("#print axioms " + declaration for declaration in declarations)
audit = OUT / "ExpandedStatements_v7.lean"
audit.write_text("\n".join(lines) + "\n")
command = [str(LEAN), "-o", str(OUT / "ExpandedStatements_v7.olean"), str(audit)]
started = time.monotonic()
with (OUT / "ExpandedStatements_v7.log").open("w") as logfile:
    result = subprocess.run(command, cwd=OUT, env=ENV,
                            stdout=logfile, stderr=subprocess.STDOUT)
for record in records:
    record["source_unchanged_during_audit"] = sha(Path(record["source"])) == record["source_sha256"]
    record["object_unchanged_during_audit"] = sha(Path(record["object"])) == record["object_sha256"]
log = (OUT / "ExpandedStatements_v7.log").read_text()
axiom_records = re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", log, re.M | re.S)
axiom_records.extend((name, "") for name in
    re.findall(r"^'([^\n]+)' does not depend on any axioms$", log, re.M))
axiom_lines = [f"{name}: [{','.join(axioms.splitlines())}]" for name, axioms in axiom_records]
unexpected_axioms = sorted({re.sub(r"\.\{[^}]*\}", "", name.strip())
    for _, axioms in axiom_records for name in axioms.split(",")
    if name.strip() and re.sub(r"\.\{[^}]*\}", "", name.strip())
       not in {"propext", "Classical.choice", "Quot.sound"}})
receipt = {"declaration_discovery": "lean_declaration_discovery_v2.py",
           "declaration_discovery_sha256": sha(HERE / "lean_declaration_discovery_v2.py"),
           "auditor_sha256": sha(Path(__file__).resolve()),
           "timestamp_utc": STAMP, "command": command, "exit_code": result.returncode,
           "elapsed_seconds": time.monotonic() - started, "lean_path": ENV["LEAN_PATH"],
           "cache_disclosure": "Existing pinned library/prior-audit object cache and newly compiled continuation objects reused; this is not a source dependency rebuild.",
           "audit_source_sha256": sha(audit), "audit_log_sha256": sha(OUT / "ExpandedStatements_v7.log"),
           "module_records": records, "axiom_lines": axiom_lines, "unexpected_axioms": unexpected_axioms,
           "expected_declarations": declarations, "axiom_report_complete":
               {name for name, _ in axiom_records} == set(declarations),
           "printer_ellipsis_count": log.count("⋯"),
           "printer_failure_diagnostics": printer_failure_diagnostics(log)}
(OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({"receipt": str(OUT / "receipt.json"), "exit_code": result.returncode,
                  "unexpected_axioms": unexpected_axioms, "declarations": len(declarations),
                  "printer_failure_count": len(receipt["printer_failure_diagnostics"])}))
raise SystemExit(result.returncode or bool(unexpected_axioms) or
                 not receipt["axiom_report_complete"] or receipt["printer_ellipsis_count"] > 0 or
                 bool(receipt["printer_failure_diagnostics"]) or
                 any(r["forbidden_source_tokens"] or not r["source_unchanged_during_audit"] or
                     not r["object_unchanged_during_audit"] for r in records))
