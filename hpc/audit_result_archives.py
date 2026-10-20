#!/usr/bin/env python3
"""Inspect archived Lean evidence. This is a provenance check, not a kernel replay."""
import argparse, hashlib, io, json, re, tarfile
from pathlib import Path

AUDIT = re.compile(r'Axiom audit passed: (\d+) project declarations, (\d+) theorems; only propext, Classical.choice, Quot.sound allowed\.\s*')
SPECS = {
 'cover': ('cover-job-status.json','COVER_JOB_SUCCESS.txt','cover-job-audit.log','cover-build/status.json'),
 'apex': ('apex-status.json','APEX_SUCCESS.txt','apex-audit.log','apex-build/status.json'),
 'abb': ('family-abb-status.json','FAMILY_ABB_SUCCESS.txt','family-abb-audit.log','family-build/status.json'),
 'exterior': ('family-exterior-status.json','FAMILY_EXTERIOR_SUCCESS.txt','family-exterior-audit.log','exterior-build/status.json'),
 's1': ('s1-status.json','S1_SUCCESS.txt','s1-audit.log',None),
}

def inspect(data, name):
 with tarfile.open(fileobj=io.BytesIO(data)) as t:
  names=t.getnames()
  if len(names)!=len(set(names)): raise ValueError('Duplicate archive members')
  def read(n): return t.extractfile('logs/'+n).read().decode()
  for kind,(status,marker,audit,build) in SPECS.items():
   if 'logs/'+status not in names: continue
   s=json.loads(read(status))
   result=dict(archive=name,archive_sha256=hashlib.sha256(data).hexdigest(),kind=kind,status=s,verified=False)
   if s.get('phase')!='complete': return result
   assert read('exit-code.txt').strip()=='0'
   assert read('SUCCESS.txt').strip() and read(marker).strip()
   m=AUDIT.fullmatch(read(audit)); assert m, 'Axiom audit failed or missing'
   if build and 'logs/'+build in names:
    b=json.loads(read(build)); assert b['completed']==b['total'] and not b['failed']
    result['build']=b
   result.update(verified=True,source_commit=read('source-commit.txt').strip(),
                 audit_declarations=int(m[1]),audit_theorems=int(m[2]))
   result['key']=f'cover:{s["job"]}' if kind=='cover' else f'apex:{s["fan"]}' if kind=='apex' else 'cover:12' if kind=='s1' else kind
   for optional in ('proposal-sha256.txt','started.txt','finished.txt'):
    if 'logs/'+optional in names: result[optional]=read(optional).strip()
   return result
 return None

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('bundle',type=Path);p.add_argument('--output',required=True,type=Path);a=p.parse_args()
 records=[]
 with tarfile.open(a.bundle) as bundle:
  for m in bundle.getmembers():
   if not m.isfile() or not re.fullmatch(r'sparse-lean-results-\d+\.tar\.gz',m.name): raise ValueError(m.name)
   r=inspect(bundle.extractfile(m).read(),m.name)
   if r: records.append(r)
 complete=sorted(r['key'] for r in records if r['verified'])
 report=dict(bundle=a.bundle.name,bundle_sha256=hashlib.sha256(a.bundle.read_bytes()).hexdigest(),
             scope='Archived full-target build and axiom-audit evidence; not combined theorem integration',
             verified_regions=complete,records=records)
 a.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(dict(verified=len(complete),keys=complete)))
if __name__=='__main__': main()
