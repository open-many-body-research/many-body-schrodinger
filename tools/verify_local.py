#!/usr/bin/env python3
"""Maintainer-triggered verification with optional GitHub commit status.

Run only on a reviewed, trusted checkout. This is not a sandbox for PR code.
GitHub Actions, webhooks, and automatic PR execution are not used.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def assert_checkout(sha: str) -> None:
    if git("rev-parse", "HEAD") != sha or git("status", "--porcelain", "--untracked-files=all"):
        raise RuntimeError("Verification requires the same clean, committed checkout throughout the run")


def context(mode: str) -> str:
    return "local/verify" if mode == "full" else "local/quick"


def post_status(repository: str, sha: str, mode: str, state: str) -> None:
    description = {"pending": "Maintainer local verification is running",
                   "success": "Local verification passed for this commit",
                   "failure": "Local verification failed; inspect the maintainer receipt",
                   "error": "Local verification could not complete"}[state]
    payload = {"state": state, "context": context(mode), "description": description}
    subprocess.run(["gh", "api", "--method", "POST", f"repos/{repository}/statuses/{sha}",
                    "--input", "-"], input=json.dumps(payload), text=True,
                   stdout=subprocess.DEVNULL, check=True, timeout=60)


def verify_foundation() -> int:
    manifest = ROOT / "lean/SHA256SUMS"
    records = {}
    for line in manifest.read_text().splitlines():
        if not line.strip():
            continue
        digest, name = line.split(maxsplit=1)
        name = name.lstrip("*")
        path = ROOT / "lean" / name
        if not path.resolve().is_relative_to((ROOT / "lean").resolve()):
            raise RuntimeError("Foundation manifest path escapes lean/")
        if name in records or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise RuntimeError(f"Foundation hash mismatch or duplicate: {name}")
        records[name] = digest
    actual = {str(p.relative_to(ROOT / "lean")) for p in (ROOT / "lean/Foundation").rglob("*.lean")}
    if actual != set(records):
        raise RuntimeError("Foundation manifest does not cover exactly the foundation source files")
    return len(records)


def pipeline(mode: str):
    py = sys.executable
    steps = [("registry", [py, "-B", "tools/validate_registry.py"], ROOT),
             ("status-page", [py, "-B", "tools/render_status.py", "--check"], ROOT),
             ("lean-policy", [py, "-B", "tools/lean_policy.py"], ROOT)]
    if mode == "full":
        steps += [("lean-build", ["lake", "build"], ROOT / "lean"),
                  ("axiom-audit", [py, "-B", "tools/axiom_audit.py"], ROOT)]
    steps += [("certificates", [py, "-B", "certificates/run_checks.py", "--" + mode], ROOT)]
    return steps


def run_step(argv, cwd, stream, timeout):
    proc = subprocess.Popen(argv, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
                            start_new_session=True)
    try:
        return proc.wait(timeout=timeout)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        # Stop the whole compiler/checker process group, including child jobs.
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["quick", "full"], default="full")
    parser.add_argument("--report-status", metavar="OWNER/REPO",
                        help="Publish only a commit SHA, check name and outcome through gh")
    parser.add_argument("--trusted-checkout", action="store_true",
                        help="Confirm a maintainer reviewed this checkout before executing it")
    parser.add_argument("--timeout", type=int, default=21600, help="Seconds allowed per step")
    args = parser.parse_args()
    if not args.trusted_checkout:
        parser.error("--trusted-checkout is required; never execute an unreviewed PR on the host")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.report_status and not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", args.report_status):
        parser.error("--report-status must be OWNER/REPO")
    sha = git("rev-parse", "HEAD")
    assert_checkout(sha)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
    out = ROOT / ".local-ci" / (stamp + "-" + sha[:12])
    out.mkdir(parents=True)
    receipt = {"commit": sha, "tree": git("rev-parse", "HEAD^{tree}"),
               "started_utc": stamp, "mode": args.mode, "context": context(args.mode),
               "trust": "Maintainer-approved local execution; not a sandbox or independent attestation",
               "steps": [], "result": "error"}
    state = "error"
    try:
        if args.report_status:
            post_status(args.report_status, sha, args.mode, "pending")
        receipt["foundation_files_verified"] = verify_foundation()
        for name, argv, cwd in pipeline(args.mode):
            assert_checkout(sha)
            print(f"local-ci: {name} starting", flush=True)
            log = out / (name + ".log")
            start = time.monotonic()
            with log.open("w") as stream:
                code = run_step(argv, cwd, stream, args.timeout)
            receipt["steps"].append({"name": name, "exit_code": code,
                                      "seconds": round(time.monotonic() - start, 3),
                                      "log": log.name, "sha256": hashlib.sha256(log.read_bytes()).hexdigest()})
            print(f"local-ci: {name} {'PASS' if code == 0 else 'FAIL'}", flush=True)
            if code:
                state = "failure"
                break
        else:
            assert_checkout(sha)
            state = "success"
    except (Exception, KeyboardInterrupt) as exc:
        # Keep diagnostics local; never transmit local paths or exception text to GitHub.
        (out / "runner-error.log").write_text(str(exc) + "\n")
        state = "error"
    receipt["result"] = state
    receipt["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    if args.report_status:
        try:
            post_status(args.report_status, sha, args.mode, state)
            receipt["github_status"] = "reported"
        except Exception as exc:
            receipt["github_status"] = "not_reported"
            (out / "status-error.log").write_text(str(exc) + "\n")
    (out / "summary.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"local-ci: {state.upper()}; receipt {out.relative_to(ROOT)}/summary.json", flush=True)
    return 0 if state == "success" and receipt.get("github_status") != "not_reported" else 1


if __name__ == "__main__":
    raise SystemExit(main())
