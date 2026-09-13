#!/usr/bin/env python3
"""Validate accepted PR attribution and generate the contribution dashboard."""
from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime
from fractions import Fraction
import html
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
REPOSITORY = "open-many-body-research/many-body-schrodinger"
CATEGORIES = ("research", "review", "documentation", "infrastructure")
KEYS = {"schema", "id", "pr", "merged_commit", "merged_at", "category", "summary",
        "contributors", "ai", "supersedes", "correction_reason"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, keys):
    require(isinstance(value, dict) and set(value) == set(keys), "Missing or unknown record fields")


def plain(value):
    require(isinstance(value, str) and 0 < len(value) <= 600 and value.strip() == value
            and all(ord(c) >= 32 and ord(c) != 127 for c in value), "Expected nonempty single-line text")


def handle(value):
    require(isinstance(value, str) and re.fullmatch(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?", value),
            "Invalid GitHub handle")
    return value.lower()


def unique_keys(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, f"Duplicate JSON key: {key}")
        out[key] = value
    return out


def load_records(root=ROOT):
    folder = root / "contributions/records"
    require(folder.is_dir(), "Missing contributions/records directory")
    groups = defaultdict(list)
    for path in sorted(folder.iterdir()):
        require(path.is_file() and not path.is_symlink() and path.suffix == ".json", "Unexpected record file")
        record = json.loads(path.read_text(), object_pairs_hook=unique_keys)
        fields(record, KEYS)
        require(type(record["schema"]) is int and record["schema"] == 1, "Unsupported schema")
        pr = record["pr"]
        require(type(pr) is int and pr > 0, "PR number must be a positive integer")
        require(isinstance(record["id"], str), "Invalid record ID")
        match = re.fullmatch(rf"PR-{pr:06d}-v([1-9][0-9]*)", record["id"])
        require(match is not None and path.stem == record["id"], "Record ID/filename/PR mismatch")
        version = int(match.group(1))
        require(isinstance(record["merged_commit"], str) and
                re.fullmatch(r"[0-9a-f]{40}", record["merged_commit"]), "Invalid merge commit")
        require(isinstance(record["merged_at"], str) and
                re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", record["merged_at"]), "Invalid merge timestamp")
        datetime.strptime(record["merged_at"], "%Y-%m-%dT%H:%M:%SZ")
        require(record["category"] in CATEGORIES, "Invalid primary category")
        plain(record["summary"])
        people = record["contributors"]
        require(isinstance(people, list) and people, "At least one human contributor is required")
        names = set()
        total = 0
        for person in people:
            fields(person, {"github", "credit_bps"})
            name = handle(person["github"])
            require(name not in names, "Duplicate contributor")
            names.add(name)
            points = person["credit_bps"]
            require(type(points) is int and 0 < points <= 10000, "Invalid credit split")
            total += points
        require(total == 10000, "Credit split must total exactly 10000 basis points")
        require(isinstance(record["ai"], list), "AI disclosures must be a list")
        disclosed = set()
        for declaration in record["ai"]:
            fields(declaration, {"github", "assistance", "tools"})
            name = handle(declaration["github"])
            require(name in names and name not in disclosed, "Duplicate or unmatched AI disclosure")
            disclosed.add(name)
            state, tools = declaration["assistance"], declaration["tools"]
            require(state in ("used", "none", "unknown") and isinstance(tools, list), "Invalid AI declaration")
            require(bool(tools) == (state == "used"), "Only used AI requires a nonempty tools list")
            for tool in tools:
                fields(tool, {"provider", "tool", "model", "role"})
                for key in ("provider", "tool", "role"):
                    plain(tool[key])
                if tool["model"] is not None:
                    plain(tool["model"])
        require(disclosed == names, "Every human needs an explicit AI disclosure")
        if version == 1:
            require(record["supersedes"] is None and record["correction_reason"] is None,
                    "Initial records must not supersede another record")
        else:
            require(record["supersedes"] == f"PR-{pr:06d}-v{version - 1}", "Broken correction chain")
            plain(record["correction_reason"])
        groups[pr].append((version, record))
    active = []
    for pr, versions in sorted(groups.items()):
        versions.sort(key=lambda item: item[0])
        require([v for v, _ in versions] == list(range(1, len(versions) + 1)), "Missing or duplicate record version")
        original = versions[0][1]
        for _, record in versions:
            require(all(record[k] == original[k] for k in ("pr", "merged_commit", "merged_at")),
                    "A correction cannot change the source merged PR")
        active.append(versions[-1][1])
    return active


def preserve_base(base, root=ROOT):
    sha = subprocess.check_output(["git", "rev-parse", "--verify", "--end-of-options", base + "^{commit}"],
                                  cwd=root, text=True).strip()
    paths = subprocess.check_output(["git", "ls-tree", "-rz", "--name-only", sha, "--", "contributions/records/"], cwd=root)
    for name in paths.decode().split("\0"):
        if not name:
            continue
        path = root / name
        require(path.is_file() and not path.is_symlink(), f"Accepted record removed: {name}")
        old = subprocess.check_output(["git", "show", sha + ":" + name], cwd=root)
        require(path.read_bytes() == old, f"Accepted record edited: {name}; add a superseding version")


def verify_github(records):
    for record in records:
        raw = subprocess.check_output(["gh", "api", f"repos/{REPOSITORY}/pulls/{record['pr']}"], text=True, timeout=60)
        pr = json.loads(raw)
        require(pr.get("merged") is True and pr.get("merge_commit_sha") == record["merged_commit"]
                and pr.get("merged_at") == record["merged_at"], f"PR #{record['pr']} merge evidence does not match")


def totals(records):
    credits = defaultdict(Fraction)
    for record in records:
        for person in record["contributors"]:
            credits[person["github"].lower()] += Fraction(person["credit_bps"], 10000)
    return dict(credits)


def escape(value):
    return re.sub(r"([\\`*_\[\]|])", r"\\\1", html.escape(value))


def number(value):
    return f"{float(value):.2f}"


def table(records):
    lines = ["| Contributor | PRs participated in | Accepted-PR credits | Share of these credits |",
             "|---|---:|---:|---:|"]
    if not records:
        return ["No accepted PRs recorded in this category yet."]
    for name, credits in sorted(totals(records).items(), key=lambda item: (-item[1], item[0])):
        count = sum(any(p["github"].lower() == name for p in r["contributors"]) for r in records)
        lines.append(f"| [{name}](https://github.com/{name}) | {count} | {number(credits)} | {number(credits / len(records) * 100)}% |")
    return lines


def render(records):
    lines = ["# Contribution dashboard", "", "Generated from reviewed [accepted-PR records](contributions/records). "
             "Read the [attribution policy](contributions/README.md) before interpreting these numbers.", "",
             f"**Coverage: {len(records)} recorded merged PR(s).** Each carries one credit, split among its human contributors. "
             "The foundation import, pre-ledger work, unrecorded merged PRs, and pending PRs are excluded. "
             "Updates arrive through maintainer-reviewed follow-up PRs; this is not a live GitHub feed.", "",
             "**These percentages measure recorded accepted-PR credit only.** They do not measure effort, scientific value, "
             "ownership, or the percentage of the mathematical problem solved. A 100% share with one recorded PR means "
             "only that single tracked PR. Counts of PR participation can overlap for collaborators. Shares are rounded.", "",
             "## Overall", "", *table(records), ""]
    for category in CATEGORIES:
        subset = [r for r in records if r["category"] == category]
        lines += [f"## {category.title()} ({len(subset)} recorded PRs)", "", *table(subset), ""]
    lines += ["## Accepted work and AI attribution", "", "AI usage is self-reported. An unrecorded model is not inferred. "
              "AI tools receive attribution, not human contribution credit. Only the latest correction for a PR counts.", "",
              "| Source PR / accepted record | Human / PR credit share | AI declaration | Provider / tool / model | Role |",
              "|---|---|---|---|---|"]
    if not records:
        lines += ["| No records yet | — | — | — | — |"]
    for record in records:
        source = f"[#{record['pr']}](https://github.com/{REPOSITORY}/pull/{record['pr']}) / [{record['id']}](contributions/records/{record['id']}.json)"
        shares = {p["github"].lower(): p["credit_bps"] for p in record["contributors"]}
        for declaration in record["ai"]:
            name = declaration["github"].lower()
            person = f"{name} / {number(Fraction(shares[name], 100))}%"
            entries = declaration["tools"] or [None]
            for tool in entries:
                label = " / ".join(escape(tool[k] or "Not recorded") for k in ("provider", "tool", "model")) if tool else "—"
                role = escape(tool["role"]) if tool else "—"
                lines.append(f"| {source} | {person} | {declaration['assistance']} | {label} | {role} |")
    lines += ["", "Regenerate with `python3 tools/contributions.py`; validate with `python3 tools/contributions.py --check`.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Fail if the committed dashboard is stale; do not write")
    parser.add_argument("--base", help="Require existing records at this Git ref to remain byte-identical")
    parser.add_argument("--verify-github", action="store_true", help="Read GitHub via gh to verify source PR merge evidence")
    args = parser.parse_args()
    try:
        records = load_records()
        if args.base:
            preserve_base(args.base)
        if args.verify_github:
            verify_github(records)
        expected = render(records)
        target = ROOT / "CONTRIBUTORS.md"
        if args.check:
            require(target.exists() and target.read_text() == expected, "Stale CONTRIBUTORS.md; regenerate it")
        else:
            target.write_text(expected)
        print(f"contributions: PASS ({len(records)} recorded merged PRs)")
        return 0
    except (ValueError, TypeError, OSError, subprocess.SubprocessError) as exc:
        print(f"contributions: FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
