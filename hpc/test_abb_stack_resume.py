import hashlib
from pathlib import Path
import tempfile
import tomllib
import unittest

from resume_abb_root import stack_profile, verify_sources


class StackResumeTests(unittest.TestCase):
    def test_profile_preserves_dependencies_and_bounds(self):
        base = (Path(__file__).parents[1] / 'lean/lakefile.toml').read_text()
        actual = tomllib.loads(stack_profile(base, 49152, 65536))
        self.assertEqual(actual.pop('weakLeanArgs'), ['-M49152', '-j1', '-s65536'])
        self.assertEqual(actual, tomllib.loads(base))

    def test_refuses_an_existing_resource_profile(self):
        with self.assertRaises(ValueError):
            stack_profile('weakLeanArgs=[]\ndefaultTargets=[]', 49152, 65536)

    def test_modified_preserved_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            lean = Path(directory)
            source = lean / 'SparseLowerTail/Test.lean'
            source.parent.mkdir()
            source.write_text('theorem test : True := True.intro\n')
            manifest = {'SparseLowerTail.Test': hashlib.sha256(source.read_bytes()).hexdigest()}
            verify_sources(lean, manifest)
            source.write_text('axiom test : False\n')
            with self.assertRaises(ValueError):
                verify_sources(lean, manifest)

    def test_unsafe_dependency_name_is_rejected(self):
        with self.assertRaises(ValueError):
            verify_sources(Path('/tmp'), {'SparseLowerTail...Test': '0' * 64})


if __name__ == '__main__':
    unittest.main()
