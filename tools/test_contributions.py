"""Accounting, attribution, and preservation boundaries for contribution credit."""
import copy
import contextlib
from fractions import Fraction
import json
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import contributions as ledger


def record():
    return {"schema": 1, "id": "PR-000001-v1", "pr": 1,
            "merged_commit": "a" * 40, "merged_at": "2026-09-13T00:00:00Z",
            "category": "research", "summary": "An accepted result",
            "contributors": [{"github": "alice", "credit_bps": 10000}],
            "ai": [{"github": "alice", "assistance": "none", "tools": []}],
            "supersedes": None, "correction_reason": None}


class ContributionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.folder = self.root / "contributions/records"
        self.folder.mkdir(parents=True)

    def write(self, item):
        path = self.folder / (item["id"] + ".json")
        path.write_text(json.dumps(item))
        return path

    def test_exact_splits_and_category_denominators(self):
        first = record()
        first["contributors"] = [{"github": "alice", "credit_bps": 2500}, {"github": "bob", "credit_bps": 7500}]
        first["ai"].append({"github": "bob", "assistance": "unknown", "tools": []})
        second = record()
        second.update(id="PR-000002-v1", pr=2, category="documentation")
        self.write(first)
        self.write(second)
        active = ledger.load_records(self.root)
        self.assertEqual(ledger.totals(active), {"alice": Fraction(5, 4), "bob": Fraction(3, 4)})
        rendered = ledger.render(active)
        self.assertIn("62.50%", rendered)
        self.assertIn("37.50%", rendered)
        self.assertIn("25.00%", rendered)
        self.assertIn("75.00%", rendered)

    def test_correction_replaces_credit_without_double_counting(self):
        old = record()
        new = copy.deepcopy(old)
        new.update(id="PR-000001-v2", supersedes=old["id"], correction_reason="Correct attribution")
        new["contributors"][0]["github"] = "bob"
        new["ai"][0]["github"] = "bob"
        self.write(old)
        self.write(new)
        active = ledger.load_records(self.root)
        self.assertEqual(len(active), 1)
        self.assertEqual(ledger.totals(active), {"bob": Fraction(1)})

    def test_invalid_splits_and_duplicate_humans_rejected(self):
        for people in ([{"github": "alice", "credit_bps": 9000}],
                       [{"github": "alice", "credit_bps": True}],
                       [{"github": "alice", "credit_bps": 5000}, {"github": "ALICE", "credit_bps": 5000}]):
            item = record()
            item["contributors"] = people
            self.write(item)
            with self.assertRaises(ValueError):
                ledger.load_records(self.root)

    def test_missing_or_inconsistent_ai_disclosure_rejected(self):
        for ai in ([], [{"github": "alice", "assistance": "used", "tools": []}],
                   [{"github": "outsider", "assistance": "none", "tools": []}]):
            item = record()
            item["ai"] = ai
            self.write(item)
            with self.assertRaises(ValueError):
                ledger.load_records(self.root)

    def test_unknown_model_is_allowed_and_rendered_as_unrecorded(self):
        item = record()
        item["ai"][0].update(assistance="used", tools=[{"provider": "Provider", "tool": "Assistant",
                                                       "model": None, "role": "Review | <script>"}])
        self.write(item)
        output = ledger.render(ledger.load_records(self.root))
        self.assertIn("Not recorded", output)
        self.assertNotIn("<script>", output)
        self.assertIn(r"Review \|", output)

    def test_missing_version_or_rebound_source_rejected(self):
        old = record()
        self.write(old)
        new = copy.deepcopy(old)
        new.update(id="PR-000001-v3", supersedes="PR-000001-v2", correction_reason="Correction")
        path = self.write(new)
        with self.assertRaises(ValueError):
            ledger.load_records(self.root)
        path.unlink()
        new.update(id="PR-000001-v2", supersedes=old["id"], merged_commit="b" * 40)
        self.write(new)
        with self.assertRaises(ValueError):
            ledger.load_records(self.root)

    def test_duplicate_json_keys_rejected(self):
        path = self.write(record())
        path.write_text(path.read_text().replace('"schema": 1', '"schema": 1, "schema": 1'))
        with self.assertRaises(ValueError):
            ledger.load_records(self.root)

    def test_unmerged_or_wrong_commit_evidence_rejected(self):
        item = record()
        for merged, sha in ((False, item["merged_commit"]), (True, "b" * 40)):
            response = {"merged": merged, "merge_commit_sha": sha, "merged_at": item["merged_at"]}
            with patch.object(ledger.subprocess, "check_output", return_value=json.dumps(response)):
                with self.assertRaises(ValueError):
                    ledger.verify_github([item])

    def test_empty_dashboard_does_not_assign_credit(self):
        output = ledger.render(ledger.load_records(self.root))
        self.assertIn("Coverage: 0 recorded", output)
        self.assertIn("No records yet", output)

    def test_check_rejects_stale_dashboard_without_writing(self):
        self.write(record())
        dashboard = self.root / "CONTRIBUTORS.md"
        dashboard.write_text("stale")
        with patch.object(ledger, "ROOT", self.root), \
             patch.object(ledger, "load_records", return_value=[record()]), \
             patch("sys.argv", ["contributions.py", "--check"]), \
             contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(ledger.main(), 1)
        self.assertEqual(dashboard.read_text(), "stale")

    def test_base_comparison_rejects_edited_or_deleted_records(self):
        path = self.write(record())
        def git(*args):
            subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)
        git("init")
        git("add", ".")
        git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-m", "record")
        ledger.preserve_base("HEAD", self.root)
        path.write_text(path.read_text() + "\n")
        with self.assertRaises(ValueError):
            ledger.preserve_base("HEAD", self.root)
        path.unlink()
        with self.assertRaises(ValueError):
            ledger.preserve_base("HEAD", self.root)


if __name__ == "__main__":
    unittest.main()
