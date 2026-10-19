"""Negative controls: disabled assertions and unfinished searches must fail."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use -O or PYTHONOPTIMIZE.')

ROOT = Path(__file__).resolve().parents[1]


def main():
    results = []
    with tempfile.TemporaryDirectory(prefix='sparse-negative-controls-') as temporary:
        out = Path(temporary)
        env = dict(os.environ, SPARSE_VERIFICATION_RESULTS=str(out))
        for script in ['verification/cover/endpoint_common.py',
                       'verification/cover/build_templates.py',
                       'verification/apex/verify_apex.py',
                       'verification/apex/symbolic.py',
                       'verification/family/verify_family.py',
                       'verification/family/symbolic.py']:
            proc = subprocess.run([sys.executable,'-O',script],cwd=ROOT,env=env,
                                  capture_output=True,text=True)
            if proc.returncode == 0 or 'requires assertions' not in proc.stderr:
                raise RuntimeError(f'Optimized-Python guard failed: {script}')
            results.append(dict(test='assertions-enabled guard',script=script,passed=True))
        commands = [
            (['verification/cover/verify_endpoint.py','F1','apex','1'], out/'cover'/'verified_F1_apex.json'),
            (['verification/apex/verify_apex.py','--max-nodes','1','--output-dir',str(out/'apex')], out/'apex'/'apex.json')]
        for arguments,path in commands:
            proc = subprocess.run([sys.executable,*arguments],cwd=ROOT,env=env,
                                  capture_output=True,text=True)
            item = json.loads(path.read_text())
            if proc.returncode == 0 or item['status'] != 'incomplete' or item['pending'] == 0:
                raise RuntimeError(f'Node-budget rejection failed: {arguments[0]}')
            results.append(dict(test='unfinished search rejection',script=arguments[0],passed=True))
        proc = subprocess.run([sys.executable,'verification/family/verify_family.py',
                               '--max-nodes','1','--output-dir',str(out/'family')],
                              cwd=ROOT,env=env,capture_output=True,text=True)
        item = json.loads((out/'family'/'family.json').read_text())
        local = json.loads((out/'family'/'local1.json').read_text())
        if proc.returncode == 0 or item['status'] != 'incomplete' or local['pending'] == 0:
            raise RuntimeError('Family node-budget rejection failed')
        results.append(dict(test='unfinished search rejection',script='verification/family/verify_family.py',passed=True))
    print(json.dumps(dict(status='passed',controls=results),indent=2))


if __name__ == '__main__':
    main()
