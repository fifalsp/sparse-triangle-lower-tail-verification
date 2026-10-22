"""Recovery must reject changed proof inputs before starting Lean."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from resume_assembly import COMMIT, REQUIRED, TARGET, prior_evidence, restore


def archive(path, entries):
    with tarfile.open(path, 'w:gz') as stream:
        for name, data in entries.items():
            member = tarfile.TarInfo(name)
            member.size = len(data)
            stream.addfile(member, io.BytesIO(data))


class AssemblyResumeTests(unittest.TestCase):
    def test_restore_compares_handwritten_and_restores_generated_and_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / 'repo'
            handwritten = repo / 'lean/SparseLowerTail/Author.lean'
            handwritten.parent.mkdir(parents=True)
            handwritten.write_bytes(b'author proof')
            entries = {'lean/SparseLowerTail/Author.lean': b'author proof',
                       'lean/SparseLowerTail/Generated/Leaf.lean': b'generated proof',
                       'lean/SparseLowerTail/Unneeded.lean': b'not selected',
                       'lean/.lake/build/lib/lean/a.olean': b'cache',
                       'SOURCE_COMMIT': COMMIT.encode()}
            sources = {'SparseLowerTail.Author': hashlib.sha256(b'author proof').hexdigest(),
                       'SparseLowerTail.Generated.Leaf': hashlib.sha256(b'generated proof').hexdigest()}
            checkpoint = root / 'checkpoint.tar.gz'
            archive(checkpoint, entries)
            self.assertEqual(restore(checkpoint, repo, sources), 2)
            self.assertEqual(handwritten.read_bytes(), b'author proof')
            self.assertFalse((repo / 'lean/SparseLowerTail/Unneeded.lean').exists())
            self.assertEqual((repo / 'lean/.lake/build/lib/lean/a.olean').read_bytes(), b'cache')

    def test_changed_existing_source_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proof = root / 'repo/lean/SparseLowerTail/Author.lean'
            proof.parent.mkdir(parents=True)
            proof.write_bytes(b'current source')
            checkpoint = root / 'checkpoint.tar.gz'
            archive(checkpoint, {'lean/SparseLowerTail/Author.lean': b'old source'})
            with self.assertRaisesRegex(ValueError, 'overwrite'):
                restore(checkpoint, root / 'repo', {
                    'SparseLowerTail.Author': hashlib.sha256(b'old source').hexdigest()})
            self.assertEqual(proof.read_bytes(), b'current source')

    def test_wrong_manifest_hash_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkpoint = root / 'checkpoint.tar.gz'
            archive(checkpoint, {'lean/SparseLowerTail/Author.lean': b'modified'})
            with self.assertRaisesRegex(ValueError, 'manifest'):
                restore(checkpoint, root / 'repo', {'SparseLowerTail.Author': '0' * 64})

    def test_traversal_and_links_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkpoint = root / 'checkpoint.tar.gz'
            archive(checkpoint, {'lean/.lake/build/../../outside': b'x'})
            with self.assertRaisesRegex(ValueError, 'Unsafe'):
                restore(checkpoint, root / 'repo', {})
            with tarfile.open(checkpoint, 'w:gz') as stream:
                member = tarfile.TarInfo('lean/.lake/build/link')
                member.type = tarfile.SYMTYPE
                member.linkname = '/tmp/outside'
                stream.addfile(member)
            with self.assertRaisesRegex(ValueError, 'Unsafe'):
                restore(checkpoint, root / 'repo', {})

    def test_corrupt_gzip_trailer_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkpoint = root / 'checkpoint.tar.gz'
            archive(checkpoint, {})
            content = bytearray(checkpoint.read_bytes())
            content[-8] ^= 1
            checkpoint.write_bytes(content)
            with self.assertRaises(OSError):
                restore(checkpoint, root / 'repo', {})

    def test_prior_gate_requires_timeout_empty_failures_and_all_base_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'result.tar.gz'
            status = {'target': TARGET, 'total': 1, 'failed': {}}
            inputs = {'selected': {key: {} for key in REQUIRED}, 'missing': []}
            entries = {'logs/source-manifest.json': json.dumps({TARGET: '0' * 64}).encode(),
                       'logs/assembly-inputs.json': json.dumps(inputs).encode(),
                       'logs/combined-build/status.json': json.dumps(status).encode(),
                       'logs/exit-code.txt': b'124\n', 'logs/source-commit.txt': COMMIT.encode()}
            archive(path, entries)
            self.assertEqual(set(prior_evidence(path)[1]), {TARGET})
            for change in ['failures', 'inputs', 'exit']:
                changed = dict(entries)
                if change == 'failures':
                    changed['logs/combined-build/status.json'] = json.dumps(
                        dict(status, failed={TARGET: 1})).encode()
                elif change == 'inputs':
                    changed['logs/assembly-inputs.json'] = b'{"selected":{},"missing":[]}'
                else:
                    changed['logs/exit-code.txt'] = b'1'
                archive(path, changed)
                with self.assertRaises(ValueError):
                    prior_evidence(path)


if __name__ == '__main__':
    unittest.main()
