#!/usr/bin/env python3
"""Hash-check and rebuild the recovered local import closure in an empty directory.

Only pinned third-party library artifacts and the official Lean runtime are reused.
No foundation or continuation project objects enter LEAN_PATH.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
RECOVERY = ROOT / "recovery/rung2-2026-10-04"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXTERNAL = {"Mathlib", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible",
            "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def check_manifest():
    manifest = json.loads((RECOVERY / "MANIFEST.json").read_text())
    modules = {r["module"]: r for r in manifest["modules"]}
    assert len(modules) == len(manifest["modules"]), "Duplicate modules"
    policy = load_module("recovery_policy", ROOT / "tools/lean_policy.py")
    for row in manifest["modules"] + manifest["evidence"]:
        if "path" not in row:
            continue
        path = ROOT / row["path"]
        assert path.is_relative_to(ROOT) and ".." not in Path(row["path"]).parts
        assert sha(path) == row["sha256"], "Changed artifact: " + row["path"]
    seen = set()
    def visit(name):
        if name in seen:
            return
        assert name in modules, "Missing local import: " + name
        seen.add(name)
        row = modules[name]
        text = policy.strip_comments_and_strings((ROOT / row["path"]).read_text())
        for regex, label in policy.FORBIDDEN:
            assert not regex.search(text), name + ": forbidden " + label
        actual = [m for line in re.findall(r"^import\s+([^\n]+)", text, re.M) for m in line.split()]
        assert actual == row["imports"], "Import manifest differs: " + name
        for imp in actual:
            if imp in modules:
                visit(imp)
            else:
                assert imp.split(".")[0] in EXTERNAL, "Unresolved local dependency: " + imp
    for name in manifest["roots"]:
        visit(name)
    assert seen == set(modules), "Manifest includes unrelated modules"
    assert sha(RECOVERY / "dependency-pins.json") == manifest["dependency_pins_sha256"]
    return manifest, modules

def axiom_reports(text):
    reports = {name: {re.sub(r"\.\{[^}]*\}", "", a.strip()) for a in axioms.split(",") if a.strip()}
               for name, axioms in re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", text, re.M | re.S)}
    reports.update({name: set() for name in re.findall(r"^'([^\n]+)' does not depend on any axioms$", text, re.M)})
    return reports

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--lean", type=Path, help="Pinned Lean compiler executable")
    parser.add_argument("--packages", type=Path, help="Pinned Lake packages directory (read-only inputs)")
    parser.add_argument("--prior-run", type=Path, help="Successful earlier source rebuild to extend; all source, object and log hashes are checked")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--output", type=Path, help="New directory; must not already exist")
    args = parser.parse_args()
    manifest, modules = check_manifest()
    if args.check_only:
        print(f"PASS: {len(modules)} local source hashes/imports and {len(manifest['evidence'])} historical artifact hashes")
        return 0
    assert args.lean and args.packages and args.jobs > 0
    lean, packages = args.lean.resolve(), args.packages.resolve()
    assert not git("status", "--porcelain"), "A clean committed checkout is required"
    commit, tree = git("rev-parse", "HEAD"), git("rev-parse", "HEAD^{tree}")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = (args.output or ROOT / ".local-ci" / ("rung2-" + stamp + "-" + commit[:12])).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build, logs, audits = out / "build", out / "logs", out / "audits"
    for p in (build, logs, audits):
        p.mkdir()
    assert not list(build.iterdir()), "Build must start empty"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    assert "version 4.34.0-rc2," in version, version
    pins = json.loads((RECOVERY / "dependency-pins.json").read_text())["packages"]
    pin_records, library_paths = [], []
    for pin in pins:
        package = packages / pin["name"]
        assert git("rev-parse", "HEAD", cwd=package) == pin["rev"], pin["name"] + " revision mismatch"
        assert not git("status", "--porcelain", "--untracked-files=no", cwd=package), "Modified dependency " + pin["name"]
        pin_records.append({"package": pin["name"], "revision": pin["rev"]})
        lib = package / ".lake/build/lib/lean"
        if lib.is_dir():
            library_paths.append(lib)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [build, *library_paths])), LEAN_NUM_THREADS="1")
    # Record portable commands; historical absolute commands are in original receipts.
    summary = {"status": "RUNNING", "tested_commit": commit, "tested_tree": tree, "lean_version": version,
               "compiler_sha256": sha(lean), "manifest_sha256": sha(RECOVERY / "MANIFEST.json"),
               "verifier_sha256": sha(Path(__file__)), "started_utc": stamp, "jobs": args.jobs,
               "pins": pin_records, "local_module_count": len(modules), "compiler_calls": [], "audits": [],
               "cache_disclosure": "Empty local project output; every local foundation and continuation module is compiled from its recorded source. Official Lean compiler/core and pinned third-party library artifacts are reused. No project development objects, prior rebuild objects, or incremental snapshots are reused; third-party Mathlib/dependencies are not rebuilt by this run."}
    def save():
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    save()
    started = time.monotonic()
    completed = set()
    todo = set(modules)
    inherited_audits = {}
    summary["reused_source_generated_module_count"] = 0
    if args.prior_run:
        prior = args.prior_run.resolve()
        parent = json.loads((prior / "summary.json").read_text())
        assert parent["status"] == "PASS", "Prior run did not pass"
        assert parent["compiler_sha256"] == summary["compiler_sha256"], "Different compiler binary"
        assert parent["pins"] == pin_records, "Different dependency revisions"
        assert parent["verifier_sha256"] == sha(ROOT / "tools/verify_rung2_recovery.py"), "Prior run is not the preserved initial clean-source verifier"
        assert parent["local_module_count"] == len(parent["compiler_calls"]) == parent["completed_local_module_count"]
        assert parent["completed_audit_module_count"] == len(parent["audits"])
        assert subprocess.run(["git", "merge-base", "--is-ancestor", parent["tested_commit"], commit], cwd=ROOT).returncode == 0
        inherited = {r["module"]: r for r in parent["compiler_calls"]}
        assert len(inherited) == len(parent["compiler_calls"])
        assert set(inherited) <= set(modules), "Prior modules must belong to the current closure"
        inventory = []
        for name, record in sorted(inherited.items()):
            assert record["exit_code"] == 0 and record["source_sha256"] == modules[name]["sha256"], "Changed inherited source: " + name
            assert sha(prior / "build" / (name + ".olean")) == record["object_sha256"], "Changed inherited object: " + name
            assert sha(prior / record["log"]) == record["log_sha256"], "Changed inherited build log"
            for artifact in sorted((prior / "build").glob(name + ".*")):
                assert artifact.is_file() and not artifact.is_symlink()
                digest = sha(artifact)
                destination = build / artifact.name
                import shutil
                shutil.copyfile(artifact, destination)
                assert sha(destination) == digest
                inventory.append({"path": artifact.name, "sha256": digest})
            import shutil
            shutil.copyfile(prior / record["log"], out / record["log"])
            row = dict(record, execution_kind="inherited_from_verified_source_run", original_tested_commit=parent["tested_commit"])
            summary["compiler_calls"].append(row)
        for row in parent["audits"]:
            assert row["module"] in inherited and not row["errors"] and row["exit_code"] == 0
            for field in ("source", "log"):
                assert sha(prior / row[field]) == row[field + "_sha256"], "Changed inherited audit artifact"
                import shutil
                shutil.copyfile(prior / row[field], out / row[field])
            reports = axiom_reports((out / row["log"]).read_text())
            assert set(reports) == set(row["declarations"]) and all(not (a - ALLOWED) for a in reports.values())
            inherited_audits[row["module"]] = dict(row, execution_kind="inherited_from_verified_source_run", original_tested_commit=parent["tested_commit"])
        summary["reused_source_generated_module_count"] = len(inherited)
        summary["prior_source_run"] = {"tested_commit": parent["tested_commit"], "tested_tree": parent["tested_tree"],
            "summary_sha256": sha(prior / "summary.json"), "original_manifest_sha256": parent["manifest_sha256"],
            "object_inventory": inventory, "audit_module_count": len(inherited_audits)}
        summary["cache_disclosure"] = "Cumulative clean local-source rebuild: the earlier successful initially empty source run supplies exactly the inherited modules recorded here; each source, object, build-log and audit hash is checked before reuse, and every generated project artifact is inventoried and copied into a new output directory. Only remaining new modules/declarations are compiled/audited in this extension. No historical development project objects or incremental snapshots are used. Official Lean compiler/core and pinned third-party library artifacts are reused; Lean and Mathlib are not rebuilt from source. This extension is not a single empty-cache compiler invocation."
        completed.update(inherited)
        todo.difference_update(inherited)
        save()
        print(f"Validated {len(inherited)} earlier source-built modules and {len(inherited_audits)} complete audits; compiling {len(todo)} additional modules", flush=True)
    dependencies = {n: set(r["imports"]) & set(modules) for n, r in modules.items()}
    def compile_one(name):
        row = modules[name]
        source, obj = ROOT / row["path"], build / (name + ".olean")
        log = logs / (name + ".log")
        command = [str(lean), "-j1", "-R", str(source.parent.relative_to(ROOT)), "-o", str(obj), row["path"]]
        now = time.monotonic()
        with log.open("w") as handle:
            proc = subprocess.run(command, cwd=ROOT, env=env, stdout=handle, stderr=subprocess.STDOUT)
        return {"module": name, "source_sha256": sha(source), "exit_code": proc.returncode,
                "seconds": time.monotonic() - now, "object_sha256": sha(obj) if obj.exists() else None,
                "log": str(log.relative_to(out)), "log_sha256": sha(log),
                "command": ["lean", "-j1", "-R", str(source.parent.relative_to(ROOT)), "-o", "<output>/build/" + obj.name, row["path"]]}
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            running = {}
            while todo or running:
                ready = sorted(n for n in todo if dependencies[n] <= completed)
                for name in ready[:args.jobs - len(running)]:
                    todo.remove(name)
                    running[pool.submit(compile_one, name)] = name
                assert running, "Dependency cycle"
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    row = future.result()
                    del running[future]
                    summary["compiler_calls"].append(row)
                    save()
                    assert row["exit_code"] == 0, "Compile failed: " + row["module"]
                    assert row["source_sha256"] == modules[row["module"]]["sha256"], "Source changed during build"
                    completed.add(row["module"])
                if len(completed) // 25 > (len(completed) - len(done)) // 25:
                    print(f"Compiled {len(completed)}/{len(modules)} local modules", flush=True)
        discover = load_module("original_discovery", RECOVERY / "original/audits/lean_declaration_discovery_v3.py").discover_declarations
        audit_modules = [n for n, r in modules.items() if r["kind"] == "recovered_continuation"]
        def audit_one(name):
            namespace, names = discover((ROOT / modules[name]["path"]).read_text())
            decls = [namespace + "." + n for n in names]
            if name in inherited_audits:
                row = inherited_audits[name]
                assert row["declarations"] == decls, "Changed inherited declaration set"
                return row
            source, log = audits / (name + ".lean"), audits / (name + ".log")
            lines = ["import " + name, "set_option pp.all true", "set_option pp.universes true",
                     "set_option pp.instances false", "set_option pp.proofs true", "set_option pp.maxSteps 2000000",
                     "set_option maxRecDepth 16384", "set_option pp.rawOnError true"]
            lines += ["#check @" + d for d in decls]
            lines += ["set_option pp.all false", "set_option pp.universes false"]
            lines += ["#print axioms " + d for d in decls]
            source.write_text("\n".join(lines) + "\n")
            with log.open("w") as handle:
                proc = subprocess.run([str(lean), "-j1", str(source.relative_to(ROOT))], cwd=ROOT, env=env, stdout=handle, stderr=subprocess.STDOUT)
            text = log.read_text()
            reports = axiom_reports(text)
            errors = []
            if proc.returncode:
                errors.append("Lean failed")
            if set(reports) != set(decls):
                errors.append("Missing or unexpected axiom reports")
            if any(a - ALLOWED for a in reports.values()):
                errors.append("Unexpected axiom")
            if "⋯" in text or any(p.casefold() in text.casefold() for p in
                                   ["failed to pretty print", "[Error pretty printing", "Falling back to raw printer",
                                    "Term omitted due to reaching", "maximum recursion depth has been reached"]):
                errors.append("Incomplete expanded statement output")
            return {"module": name, "declarations": decls, "exit_code": proc.returncode, "errors": errors,
                    "axioms": sorted(set().union(*reports.values()) if reports else set()),
                    "source": str(source.relative_to(out)), "source_sha256": sha(source),
                    "log": str(log.relative_to(out)), "log_sha256": sha(log)}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for index, row in enumerate(pool.map(audit_one, sorted(audit_modules)), 1):
                summary["audits"].append(row)
                save()
                assert not row["errors"], "Audit failed: " + row["module"] + " " + str(row["errors"])
                if index % 25 == 0:
                    print(f"Audited {index}/{len(audit_modules)} continuation modules", flush=True)
        if args.prior_run:
            for row in summary["prior_source_run"]["object_inventory"]:
                assert sha(args.prior_run.resolve() / "build" / row["path"]) == row["sha256"], "Prior source outputs changed during extension"
                assert sha(build / row["path"]) == row["sha256"], "Inherited source output changed during extension"
        summary["new_compiler_call_count"] = len(summary["compiler_calls"]) - summary["reused_source_generated_module_count"]
        check_manifest()
        assert git("rev-parse", "HEAD") == commit and not git("status", "--porcelain"), "Checkout changed during verification"
        summary["status"] = "PASS"
    except Exception as error:
        summary["status"] = "FAIL"
        summary["error"] = str(error)
        raise
    finally:
        summary["elapsed_seconds"] = time.monotonic() - started
        summary["completed_local_module_count"] = len(completed)
        summary["completed_audit_module_count"] = len(summary["audits"])
        save()
        print(json.dumps({"status": summary["status"], "tested_commit": commit,
                          "receipt": str(out / "summary.json")}), flush=True)
    return 0

if __name__ == "__main__":
    sys.exit(main())
