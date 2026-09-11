#!/usr/bin/env python3
"""Re-derive published certificates from their rational inputs and compare.

Each checker runs in a temporary copy of the certificates/ tree. The
regenerated certificate must agree with the published one on every field the
published file contains, except run metadata (timings, runtime, code hashes).
"""
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
METADATA = {"certificate_wall_seconds_display_only", "wall_seconds_metadata",
            "runtime", "code_sha256", "host"}

HE = "helium-ground-state"
DY = "helium-dyadic-dictionary"


def hylleraas(trial, bits, regenerated, published):
    return (HE, ["check_trial.py", trial, "--bits", str(bits)], regenerated, published)


def dyadic(n, bits):
    name = f"certificate_E_{n}_{bits}.json"
    return (DY, ["certify.py", "E", str(n), "--bits", str(bits)], name, name)


QUICK = [
    hylleraas("trial_6.json", 512, "certificate_6_512.json", "certificate_6_512.json"),
    dyadic(4, 512),
]
FULL = QUICK + [
    hylleraas("trial_10.json", 512, "certificate_10_512.json", "certificate_10_512.json"),
    hylleraas("trial_residual_8.json", 512, "certificate_8_512.json", "certificate_residual_8_512.json"),
    hylleraas("trial_residual_10.json", 512, "certificate_10_512.json", "certificate_residual_10_512.json"),
    hylleraas("trial_residual_14.json", 512, "certificate_14_512.json", "certificate_residual_14_512.json"),
    hylleraas("trial_residual_20.json", 512, "certificate_20_512.json", "certificate_residual_20_512.json"),
    hylleraas("trial_residual_20.json", 768, "certificate_20_768.json", "certificate_residual_20_768.json"),
] + [dyadic(n, 512) for n in (2, 3, 5, 6, 7, 8, 9)] + [dyadic(10, 1024)]


def check(directory, argv, regenerated, published) -> bool:
    with tempfile.TemporaryDirectory() as tmp:
        work = pathlib.Path(tmp)
        for d in (HE, DY):
            shutil.copytree(HERE / d, work / d, ignore=shutil.ignore_patterns("certificate_*.json"))
        print(f"== {directory}: {' '.join(argv)}", flush=True)
        proc = subprocess.run([sys.executable, *argv], cwd=work / directory)
        if proc.returncode != 0:
            print(f"FAIL: checker exited {proc.returncode}")
            return False
        new = json.loads((work / directory / regenerated).read_text())
    old = json.loads((HERE / directory / published).read_text())
    diff = sorted(k for k in old if k not in METADATA and new.get(k) != old[k])
    if diff:
        print(f"FAIL: {published} differs from the regenerated certificate in {diff}")
        return False
    width = old.get("width_decimal") or old.get("width")
    print(f"ok: {published} reproduced (width {width} Ha)", flush=True)
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--quick", action="store_true")
    mode.add_argument("--full", action="store_true")
    args = ap.parse_args()
    ok = all([check(*spec) for spec in (QUICK if args.quick else FULL)])
    if args.full:
        print("== independent algebra audit", flush=True)
        with tempfile.TemporaryDirectory() as tmp:
            shutil.copytree(HERE / HE, pathlib.Path(tmp) / HE)
            ok = subprocess.run([sys.executable, "independent_audit.py"],
                                cwd=pathlib.Path(tmp) / HE).returncode == 0 and ok
    print("certificates: PASS" if ok else "certificates: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
