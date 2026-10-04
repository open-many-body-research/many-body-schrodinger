#!/usr/bin/env python3
"""Pure independent lexer review corpus. Does not launch Lean or edit proof sources."""
from pathlib import Path
import ast
import datetime
import hashlib
import json

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(version):
    path = HERE / f"lean_declaration_discovery_v{version}.py"
    scope = {}
    exec(compile(path.read_bytes(), str(path), "exec"), scope)
    return scope


old, new = load(2), load(3)


def wrap(body):
    return "namespace Review\n" + body + "\nend Review\n"


def discover(scope, source):
    try:
        return {"result": scope["discover_declarations"](source)}
    except ValueError as error:
        return {"rejected": str(error)}


cases = []
for name, term in [
    ("comment_before", "f /- comment -/'' A"),
    ("comment_after", "f ''/- comment -/ A"),
    ("line_comment_after", "f ''-- comment\n  A"),
    ("paren_adjacency", "(f)''(A)"),
    ("nested_no_spaces", "(f)''((g)''(A))"),
    ("unicode_identifier", "φ '' Ω"),
    ("primed_unicode_identifier", "φ'' '' Ω'"),
    ("primed_ascii_identifier", "f''' '' A''"),
    ("mixed_preimage_image", "f '' (g ⁻¹' A)"),
    ("tabs", "f\t''\tA"),
    ("newlines", "f\n  ''\n  A"),
]:
    cases.append((name, wrap(f"def image := {term}\ntheorem sentinel : True := by trivial"), ["image", "sentinel"]))

for literal in [
    '"f \'\' A\ntheorem fake : False := by sorry"',
    'r#"f \'\' A\ntheorem fake : False := by sorry"#',
    'r###"f \'\' A\n\"#\ntheorem fake : False := by sorry"###',
    "'\\''",
    "'\\x27'",
    "'\\u0027'",
]:
    cases.append(("shield_" + repr(literal), wrap(f"def literal := {literal}\ndef image := f '' A\ntheorem sentinel : True := by trivial"), ["literal", "image", "sentinel"]))

for command in [
    "axiom hidden : False",
    "opaque hidden : Nat",
    "private theorem hidden : True := by trivial",
    "unsafe def hidden := 0",
    "instance hidden : Inhabited Nat := inferInstance",
    'macro "hidden" : command => pure default',
    'notation "hidden" => True',
    "theorem «hidden» : True := by trivial",
    "theorem hidden. : True := by trivial",
    "theorem _root_.hidden : True := by trivial",
    "def image := f '' A; theorem hidden : True := by trivial",
]:
    cases.append(("reject_" + command, wrap("def image := f '' A\n" + command), None))

for count in range(3, 9):
    term = "f " + "'" * count + " A"
    cases.append((f"standalone_primes_{count}", wrap(f"def image := {term}\ntheorem sentinel : True := by trivial"), None))

for literal in ['"f \'\' A', 'r#"f \'\' A"', "'", "'\\x2'", "'\\u027'"]:
    cases.append(("malformed_" + repr(literal), wrap(f"def bad := {literal}\ntheorem sentinel : True := by trivial"), None))

results = []
for name, source, expected in cases:
    actual = discover(new, source)
    passed = "rejected" in actual if expected is None else actual == {"result": ("Review", expected)}
    if expected is not None:
        masked = new["mask_lean_literals_and_comments"](source)
        passed = passed and len(masked) == len(source)
        passed = passed and [i for i, c in enumerate(masked) if c == "\n"] == [i for i, c in enumerate(source) if c == "\n"]
    results.append({"name": name, "source": source, "expected": expected, "actual": actual, "pass": passed})

target = HERE.parent / "lean/PhysicalSpectatorL2BudgetTransport_v1.lean"
expected_target = ("TheoremT.Continuum", [
    "physicalSpectatorReindexAt_symm_measurePreserving",
    "physicalSpectatorReindexAt_regionL2Budget",
    "physicalSpectatorReindexAt_locallyL2",
])
assert new["discover_declarations"](target.read_text()) == expected_target
assert "rejected" in discover(old, target.read_text())


def normalized_auditor(path, normalize=False):
    source = path.read_text()
    if normalize:
        source = source.replace("lean_declaration_discovery_v3", "lean_declaration_discovery_v2").replace("ExpandedStatements_v8", "ExpandedStatements_v7")
    tree = ast.parse(source)
    assert isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant)
    tree.body = tree.body[1:]
    return ast.dump(tree, include_attributes=False)


assert normalized_auditor(HERE / "audit_final_statements_v7.py") == normalized_auditor(HERE / "audit_final_statements_v8.py", True)
report = {
    "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "script_sha256": sha(Path(__file__)),
    "helper_v2_sha256": sha(HERE / "lean_declaration_discovery_v2.py"),
    "helper_v3_sha256": sha(HERE / "lean_declaration_discovery_v3.py"),
    "auditor_v7_sha256": sha(HERE / "audit_final_statements_v7.py"),
    "auditor_v8_sha256": sha(HERE / "audit_final_statements_v8.py"),
    "auditor_ast_unchanged_after_version_normalization": True,
    "actual_target": {"path": str(target), "sha256": sha(target), "expected": expected_target},
    "cases": results,
    "all_pass": all(item["pass"] for item in results),
    "limits": "Scanner test strings do not claim Lean validity. The source compiler remains responsible for validity. No Lean or proof audit was launched.",
}
stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
out = HERE / f"IMAGE_TOKEN_INDEPENDENT_REGRESSION_v1_{stamp}.json"
with out.open("x") as stream:
    json.dump(report, stream, indent=2)
    stream.write("\n")
print(json.dumps({"path": str(out), "sha256": sha(out), "cases": len(results), "all_pass": report["all_pass"], "failures": [item for item in results if not item["pass"]]}))
raise SystemExit(not report["all_pass"])
