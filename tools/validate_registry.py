#!/usr/bin/env python3
"""Validate claims/registry.yaml against the rules in CONTRIBUTING.md.

Checks: schema, unique IDs, evidence paths exist, statement cards exist for
L/C/P2, two reviews for P2, errata for X, Lean declarations for L, and that no
claim depends on a claim of a weaker tier.
"""
from __future__ import annotations

import pathlib
import re
import sys

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "claims" / "registry.yaml"

TIERS = {"L", "C", "P2", "P1", "N", "O", "X"}
# Minimum tier a dependency must have, per tier of the dependent claim.
STRONG = {"L", "C", "P2"}
ALLOWED_DEPS = {
    "L": {"L"},
    "C": STRONG,
    "P2": STRONG,
    "P1": STRONG | {"P1"},
    "N": TIERS - {"X"},
    "O": TIERS - {"X"},
    "X": TIERS,
}
SECTORS = {f"S{i}" for i in range(1, 10)}
ID_RE = re.compile(r"^S[1-9]-\d{3}$")
REQUIRED = ["id", "sector", "title", "tier", "statement", "evidence"]
KNOWN_KEYS = set(REQUIRED) | {
    "status", "conditional_on", "lean", "card", "reviews", "depends_on",
    "erratum", "provenance", "caveats", "reference",
}


def main() -> int:
    data = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    claims = data.get("claims", [])
    errors: list[str] = []
    by_id: dict[str, dict] = {}

    for c in claims:
        cid = c.get("id", "<missing id>")
        for key in REQUIRED:
            if key not in c:
                errors.append(f"{cid}: missing required key '{key}'")
        for key in c:
            if key not in KNOWN_KEYS:
                errors.append(f"{cid}: unknown key '{key}'")
        if not ID_RE.match(str(cid)):
            errors.append(f"{cid}: id must match {ID_RE.pattern}")
        if cid in by_id:
            errors.append(f"{cid}: duplicate id")
        by_id[cid] = c
        if c.get("sector") not in SECTORS:
            errors.append(f"{cid}: unknown sector {c.get('sector')}")
        elif not str(cid).startswith(c["sector"] + "-"):
            errors.append(f"{cid}: id prefix does not match sector {c['sector']}")
        tier = c.get("tier")
        if tier not in TIERS:
            errors.append(f"{cid}: unknown tier {tier}")
            continue

        for p in c.get("evidence", []) or []:
            if not (ROOT / p).exists():
                errors.append(f"{cid}: evidence path does not exist: {p}")

        if tier in STRONG:
            card = c.get("card")
            if not card or not (ROOT / card).exists():
                errors.append(f"{cid}: tier {tier} requires an existing statement card")
        if tier == "L":
            decls = c.get("lean") or []
            if not decls:
                errors.append(f"{cid}: tier L requires at least one Lean declaration")
            for d in decls:
                if not isinstance(d, dict) or not {"module", "decl"} <= set(d):
                    errors.append(f"{cid}: lean entries must be {{module, decl}}")
        if tier == "P2":
            reviews = c.get("reviews") or []
            if len(reviews) < 2:
                errors.append(f"{cid}: tier P2 requires two independent review records")
            for r in reviews:
                if not (ROOT / r).exists():
                    errors.append(f"{cid}: review record does not exist: {r}")
        if tier == "X":
            err = c.get("erratum")
            if not err or not (ROOT / err).exists():
                errors.append(f"{cid}: tier X requires an existing erratum file")

    for cid, c in by_id.items():
        tier = c.get("tier")
        for dep in c.get("depends_on", []) or []:
            if dep not in by_id:
                errors.append(f"{cid}: depends on unknown claim {dep}")
                continue
            dtier = by_id[dep].get("tier")
            if tier in ALLOWED_DEPS and dtier not in ALLOWED_DEPS[tier]:
                errors.append(f"{cid} (tier {tier}) cannot depend on {dep} (tier {dtier})")

    counts: dict[str, int] = {}
    for c in claims:
        counts[c.get("tier")] = counts.get(c.get("tier"), 0) + 1
    summary = ", ".join(f"{t}={counts.get(t, 0)}" for t in ["L", "C", "P2", "P1", "N", "O", "X"])
    print(f"validate_registry: {len(claims)} claims ({summary})")
    if errors:
        print("\n".join(errors))
        print(f"validate_registry: FAIL ({len(errors)} errors)")
        return 1
    print("validate_registry: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
