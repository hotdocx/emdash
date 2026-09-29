import hashlib
import importlib.util
from io import BytesIO
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import Mock

spec = importlib.util.spec_from_file_location("verification_toolchain", Path(__file__).with_name("verification-toolchain.py"))
toolchain = importlib.util.module_from_spec(spec)
spec.loader.exec_module(toolchain)


class SourceArchiveTests(unittest.TestCase):
    def manifest(self, data=b"reviewed archive"):
        archive = {"name": "example", "version": "1.0", "url": "https://example.invalid/cache",
                   "sha256": hashlib.sha256(data).hexdigest(), "md5": hashlib.md5(data).hexdigest()}
        return {"opamPackages": {"example": "1.0"}, "opamSourceArchives": [archive]}

    def test_verified_bytes_populate_both_opam_cache_keys_and_reuse_without_network(self):
        with TemporaryDirectory() as temporary:
            cache = Path(temporary)
            manifest = self.manifest()
            fetch = Mock(return_value=BytesIO(b"reviewed archive"))
            toolchain.seed_source_archives(manifest, cache, fetch)
            archive = manifest["opamSourceArchives"][0]
            for kind in ("sha256", "md5"):
                self.assertEqual((cache / kind / archive[kind][:2] / archive[kind]).read_bytes(), b"reviewed archive")
            fetch.assert_called_once_with(archive["url"], timeout=30)
            toolchain.seed_source_archives(manifest, cache, Mock(side_effect=AssertionError("unexpected network")))

    def test_mismatching_source_or_cache_is_rejected_without_installing_new_bytes(self):
        with TemporaryDirectory() as temporary:
            cache = Path(temporary)
            manifest = self.manifest()
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                toolchain.seed_source_archives(manifest, cache, Mock(return_value=BytesIO(b"changed upstream bytes")))
            self.assertEqual(list(cache.rglob("*")), [])
            archive = manifest["opamSourceArchives"][0]
            target = cache / "sha256" / archive["sha256"][:2] / archive["sha256"]
            target.parent.mkdir(parents=True)
            target.write_bytes(b"bad cache")
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                toolchain.seed_source_archives(manifest, cache, Mock(side_effect=AssertionError("unexpected network")))

    def test_archive_cannot_silently_override_a_package_version(self):
        with TemporaryDirectory() as temporary:
            manifest = self.manifest()
            manifest["opamPackages"]["example"] = "2.0"
            with self.assertRaisesRegex(ValueError, "does not match"):
                toolchain.seed_source_archives(manifest, Path(temporary), Mock(side_effect=AssertionError("unexpected network")))


if __name__ == "__main__":
    unittest.main()
