import io
from pathlib import Path
import tarfile
import tempfile
import unittest

from restore_family_checkpoint import restore


class FamilyRestoreTests(unittest.TestCase):
    def checkpoint(self, path, names):
        with tarfile.open(path, 'w:gz') as archive:
            for name in names:
                content = name.encode()
                member = tarfile.TarInfo(name)
                member.size = len(content)
                archive.addfile(member, io.BytesIO(content))

    def test_restores_generated_sources_and_cache_without_overwriting_author_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)/'repo'
            root.mkdir()
            handwritten = root/'lean/Audit.lean'
            handwritten.parent.mkdir()
            handwritten.write_text('unchanged audit')
            archive = Path(directory)/'checkpoint.tar.gz'
            selected = ['lean/SparseLowerTail/Section08/FamilyABBReplay/Full/Root.lean',
                        'lean/.lake/build/lib/lean/Root.olean']
            excluded = ['lean/Audit.lean', 'lean/SparseLowerTail/MainStatement.lean',
                        'lean/SparseLowerTail/Section08/FamilyExteriorReplay/Full/Root.lean']
            self.checkpoint(archive, selected+excluded)
            self.assertEqual(restore(archive, root, 'abb'), 2)
            for name in selected:
                self.assertEqual((root/name).read_text(), name)
            self.assertEqual(handwritten.read_text(), 'unchanged audit')
            for name in excluded[1:]:
                self.assertFalse((root/name).exists())

    def test_rejects_traversal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive = root/'checkpoint.tar.gz'
            self.checkpoint(archive, ['lean/.lake/build/../../escape'])
            with self.assertRaises(ValueError):
                restore(archive, root/'repo', 'exterior')


if __name__ == '__main__':
    unittest.main()
