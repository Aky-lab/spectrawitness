from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import export_source


class ExportSourceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.source = self.root / "source"
        self.source.mkdir()
        (self.source / "a.txt").write_text("a\n", encoding="utf-8")

    def tearDown(self) -> None:
        self.temp.cleanup()

    def allowlist(self, text: str) -> Path:
        path = self.source / "distribution-files.txt"
        path.write_text(text, encoding="utf-8")
        return path

    def test_export_and_manifest(self) -> None:
        output = self.root / "output"
        export_source.export(self.source, self.allowlist("a.txt\n"), output, self.root)
        self.assertEqual((output / "a.txt").read_text(encoding="utf-8"), "a\n")
        manifest = (output / export_source.MANIFEST_NAME).read_text(encoding="utf-8")
        self.assertIn("  a.txt\n", manifest)
        self.assertNotIn(export_source.MANIFEST_NAME, manifest)

    def test_rejects_traversal(self) -> None:
        with self.assertRaisesRegex(ValueError, "invalid allowlist path"):
            export_source.export(
                self.source, self.allowlist("../outside.txt\n"), self.root / "out", self.root
            )

    def test_rejects_missing_file(self) -> None:
        with self.assertRaisesRegex(FileNotFoundError, "missing allowlisted file"):
            export_source.export(
                self.source, self.allowlist("missing.txt\n"), self.root / "out", self.root
            )

    def test_rejects_output_inside_source(self) -> None:
        with self.assertRaisesRegex(ValueError, "must not contain"):
            export_source.export(
                self.source, self.allowlist("a.txt\n"), self.source / "out", self.root
            )


if __name__ == "__main__":
    unittest.main()
