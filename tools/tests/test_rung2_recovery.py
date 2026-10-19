import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("recovery_verifier", TOOLS / "verify_rung2_recovery.py")
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
policy = verifier.load_module("test_policy", TOOLS / "lean_policy.py")

class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.recovery = self.root / "recovery"
        self.recovery.mkdir()
        self.source = self.root / "A.lean"
        self.source.write_text("import Mathlib\nnamespace Example\ntheorem valid : True := True.intro\nend Example\n")
        pins = self.recovery / "dependency-pins.json"
        pins.write_text("{}\n")
        self.manifest = {"roots": ["A"], "modules": [{"module": "A", "path": "A.lean",
                         "sha256": verifier.sha(self.source), "imports": ["Mathlib"]}],
                         "evidence": [], "dependency_pins_sha256": verifier.sha(pins)}
        self.contexts = [patch.object(verifier, "ROOT", self.root), patch.object(verifier, "RECOVERY", self.recovery),
                         patch.object(verifier, "load_module", return_value=policy)]
        for context in self.contexts:
            context.start()
        self.write_manifest()

    def tearDown(self):
        for context in reversed(self.contexts):
            context.stop()
        self.temp.cleanup()

    def write_manifest(self):
        (self.recovery / "MANIFEST.json").write_text(json.dumps(self.manifest))

    def test_valid_closure(self):
        self.assertEqual(set(verifier.check_manifest()[1]), {"A"})

    def test_changed_source_is_rejected(self):
        self.source.write_text(self.source.read_text() + "-- Changed\n")
        with self.assertRaisesRegex(AssertionError, "Changed artifact"):
            verifier.check_manifest()

    def test_missing_local_import_is_rejected(self):
        self.source.write_text("import MissingLocal\n")
        self.manifest["modules"][0].update(sha256=verifier.sha(self.source), imports=["MissingLocal"])
        self.write_manifest()
        with self.assertRaisesRegex(AssertionError, "Unresolved local dependency"):
            verifier.check_manifest()

    def test_import_manifest_cannot_hide_an_edge(self):
        self.manifest["modules"][0]["imports"] = []
        self.write_manifest()
        with self.assertRaisesRegex(AssertionError, "Import manifest differs"):
            verifier.check_manifest()

    def test_forbidden_axiom_is_rejected(self):
        self.source.write_text("import Mathlib\naxiom unproved : False\n")
        self.manifest["modules"][0]["sha256"] = verifier.sha(self.source)
        self.write_manifest()
        with self.assertRaisesRegex(AssertionError, "forbidden axiom declaration"):
            verifier.check_manifest()

    def test_axiom_parser_retains_nonstandard_axioms(self):
        text = "'Example.bad' depends on axioms: [propext,\n sorryAx]\n'Example.good' does not depend on any axioms\n"
        reports = verifier.axiom_reports(text)
        self.assertEqual(reports["Example.bad"] - verifier.ALLOWED, {"sorryAx"})
        self.assertEqual(reports["Example.good"], set())

if __name__ == "__main__":
    unittest.main()
