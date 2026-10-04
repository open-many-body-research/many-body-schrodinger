"""Corrupt parent receipts cannot become successful source-rebuild extensions."""
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("recovery_extension", TOOLS / "verify_rung2_recovery_v2.py")
extension = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extension)

class SourceExtensionTests(unittest.TestCase):
    def check_rejected_parent(self, change, message):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            recovery = root / "recovery"
            recovery.mkdir()
            (recovery / "MANIFEST.json").write_text("{}")
            (recovery / "dependency-pins.json").write_text('{"packages": []}')
            tools = root / "tools"
            tools.mkdir()
            (tools / "verify_rung2_recovery.py").write_text("preserved initial verifier")
            lean = root / "lean"
            lean.write_text("test compiler binary")
            prior = root / "prior"
            (prior / "build").mkdir(parents=True)
            (prior / "logs").mkdir()
            obj = prior / "build/A.olean"
            obj.write_text("original source-generated object")
            log = prior / "logs/A.log"
            log.write_text("successful compile")
            row = {"module": "A", "source_sha256": "a" * 64, "exit_code": 0,
                   "object_sha256": extension.sha(obj), "log": "logs/A.log", "log_sha256": extension.sha(log)}
            parent = {"status": "PASS", "tested_commit": "b" * 40, "compiler_sha256": extension.sha(lean),
                      "pins": [], "verifier_sha256": extension.sha(tools / "verify_rung2_recovery.py"),
                      "local_module_count": 1, "completed_local_module_count": 1,
                      "completed_audit_module_count": 0, "audits": [], "compiler_calls": [row]}
            change(parent, row, obj)
            (prior / "summary.json").write_text(json.dumps(parent))
            modules = {"A": {"sha256": "a" * 64, "kind": "published_foundation"}}
            def fake_git(*args, **kwargs):
                return "" if args[0] == "status" else "c" * 40
            argv = ["verify", "--lean", str(lean), "--packages", str(root),
                    "--prior-run", str(prior), "--output", str(root / ".local-ci/out")]
            with patch.object(extension, "ROOT", root), patch.object(extension, "RECOVERY", recovery), \
                 patch.object(extension, "check_manifest", return_value=({}, modules)), \
                 patch.object(extension, "git", side_effect=fake_git), \
                 patch.object(extension.subprocess, "check_output", return_value="Lean (version 4.34.0-rc2, test)"), \
                 patch.object(extension.subprocess, "run", return_value=SimpleNamespace(returncode=0)), \
                 patch("sys.argv", argv):
                with self.assertRaisesRegex(AssertionError, message):
                    extension.main()
            saved = json.loads((root / ".local-ci/out/summary.json").read_text())
            self.assertNotEqual(saved["status"], "PASS")

    def test_failed_prior_run(self):
        self.check_rejected_parent(lambda p, r, o: p.update(status="FAIL"), "Prior run did not pass")

    def test_changed_dependency_pins(self):
        self.check_rejected_parent(lambda p, r, o: p.update(pins=[{"package": "changed"}]), "Different dependency revisions")

    def test_changed_inherited_source(self):
        self.check_rejected_parent(lambda p, r, o: r.update(source_sha256="d" * 64), "Changed inherited source")

    def test_changed_inherited_object(self):
        self.check_rejected_parent(lambda p, r, o: o.write_text("tampered"), "Changed inherited object")

if __name__ == "__main__":
    unittest.main()
