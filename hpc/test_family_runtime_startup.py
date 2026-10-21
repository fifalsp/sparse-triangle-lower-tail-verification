import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class RuntimeStartupTests(unittest.TestCase):
    def test_both_runners_select_pinned_toolchain_from_outside_project(self):
        for family in ['abb', 'exterior']:
            with self.subTest(family=family), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                repo, runtime, logs = root/'repo', root/'runtime', root/'logs'
                (repo/'lean').mkdir(parents=True)
                (runtime/'bin').mkdir(parents=True)
                logs.mkdir()
                (repo/'lean/lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
                compiler = runtime/'bin/lean'
                compiler.write_text('''#!/usr/bin/env bash
set -eu
[[ "$ELAN_TOOLCHAIN" == leanprover/lean4:v4.24.0 ]]
[[ "$PWD" == "$REPO/lean" ]]
[[ "$1" == --version ]]
printf 'Pinned compiler selected\n'
''')
                compiler.chmod(0o755)
                script = (Path(__file__).parent/f'bouchet-{family}-stack-resume.sbatch').read_text()
                setup = script[script.index('module load '):script.index('timeout --signal=')]
                env = dict(os.environ, REPO=str(repo), RUNTIME=str(runtime), RUN_DIR=str(logs))
                env.pop('ELAN_TOOLCHAIN', None)
                # Native stack limits differ on macOS; Linux already accepted
                # this setting. This test exercises compiler selection/CWD.
                prelude = 'module() { :; }\nulimit() { [[ "$*" == "-s 65536" ]]; }\n'
                subprocess.run(['bash', '-ec', prelude+setup],
                               cwd=root, env=env, check=True)
                self.assertEqual((logs/'lean-version.txt').read_text(), 'Pinned compiler selected\n')


if __name__ == '__main__':
    unittest.main()
