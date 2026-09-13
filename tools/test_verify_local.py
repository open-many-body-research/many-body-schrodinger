"""Failure-boundary tests for the local verification service."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import verify_local as runner


class LocalVerificationTests(unittest.TestCase):
    def test_quick_cannot_satisfy_full_status(self):
        self.assertNotEqual(runner.context("quick"), runner.context("full"))
        full = {name for name, *_ in runner.pipeline("full")}
        quick = {name for name, *_ in runner.pipeline("quick")}
        self.assertTrue({"lean-build", "axiom-audit"}.issubset(full))
        self.assertTrue({"lean-build", "axiom-audit"}.isdisjoint(quick))

    def test_dirty_or_changed_checkout_rejected(self):
        for values in [("changed", ""), ("head", " M tools/check.py")]:
            with patch.object(runner, "git", side_effect=values):
                with self.assertRaises(RuntimeError):
                    runner.assert_checkout("head")

    def test_foundation_changes_and_unlisted_sources_rejected(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(runner, "ROOT", Path(tmp)):
            folder = Path(tmp) / "lean/Foundation"
            folder.mkdir(parents=True)
            source = folder / "A.lean"
            source.write_text("example : True := True.intro\n")
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            (folder.parent / "SHA256SUMS").write_text(digest + "  Foundation/A.lean\n")
            self.assertEqual(runner.verify_foundation(), 1)
            source.write_text("changed")
            with self.assertRaises(RuntimeError):
                runner.verify_foundation()
            source.write_text("example : True := True.intro\n")
            (folder / "B.lean").write_text("unlisted")
            with self.assertRaises(RuntimeError):
                runner.verify_foundation()

    def run_fake(self, codes, fail_status=False):
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(io.StringIO()):
            root = Path(tmp)
            with patch.object(runner, "ROOT", root), \
                 patch.object(runner, "git", return_value="a" * 40), \
                 patch.object(runner, "assert_checkout"), \
                 patch.object(runner, "verify_foundation", return_value=817), \
                 patch.object(runner, "run_step", side_effect=codes), \
                 patch.object(runner, "post_status") as status, \
                 patch("sys.argv", ["verify_local.py", "--trusted-checkout", "--report-status", "org/repo"]):
                if fail_status:
                    status.side_effect = [None, RuntimeError("network unavailable")]
                exit_code = runner.main()
                receipt = json.loads(next(root.glob(".local-ci/*/summary.json")).read_text())
                return exit_code, receipt, [call.args[-1] for call in status.call_args_list]

    def test_failure_stops_pipeline_and_never_reports_success(self):
        build_index = [name for name, *_ in runner.pipeline("full")].index("lean-build")
        code, receipt, states = self.run_fake([0] * build_index + [1])
        self.assertEqual(code, 1)
        self.assertEqual(receipt["result"], "failure")
        self.assertEqual(states, ["pending", "failure"])
        self.assertEqual(receipt["steps"][-1]["name"], "lean-build")

    def test_timeout_reports_error(self):
        code, receipt, states = self.run_fake([subprocess.TimeoutExpired("check", 1)])
        self.assertEqual(code, 1)
        self.assertEqual(receipt["result"], "error")
        self.assertEqual(states, ["pending", "error"])

    def test_status_upload_failure_cannot_exit_successfully(self):
        code, receipt, states = self.run_fake([0] * len(runner.pipeline("full")), fail_status=True)
        self.assertEqual(code, 1)
        self.assertEqual(receipt["result"], "success")
        self.assertEqual(receipt["github_status"], "not_reported")


if __name__ == "__main__":
    unittest.main()
