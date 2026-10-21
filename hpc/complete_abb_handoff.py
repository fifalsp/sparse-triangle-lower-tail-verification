#!/usr/bin/env python3
"""Finish the user-authorized ABB scale-up when its allocation becomes ready.

This coordinator performs no proof work on the login node. All checkpoint,
validation and signal operations run inside the two existing allocations.
"""
import argparse
import datetime
import json
from pathlib import Path
import subprocess
import time


def ready_to_retire(probe, checkpoint):
    build = probe.get('build') or {}
    return (probe.get('source_match') is True and probe.get('checkpoint_restored') is True
            and build.get('workers') == 8 and not build.get('failed')
            and build.get('completed', 0) >= checkpoint['preserved_module_count'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--old-job', required=True)
    p.add_argument('--new-job', required=True)
    p.add_argument('--integration-job', required=True)
    p.add_argument('--old-work', type=Path, required=True)
    p.add_argument('--handoff', type=Path, required=True)
    p.add_argument('--control', type=Path, required=True)
    a = p.parse_args()
    a.handoff.mkdir(parents=True, exist_ok=True)
    record = dict(old_job=a.old_job,new_job=a.new_job,integration_job=a.integration_job)
    def state(phase, **extra):
        record.update(phase=phase,checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**extra)
        temporary=a.handoff/'handoff-status.json.partial'
        temporary.write_text(json.dumps(record,indent=2)+'\n')
        temporary.rename(a.handoff/'handoff-status.json')
        print(json.dumps(record),flush=True)
    def run(command, timeout=60):
        return subprocess.check_output(command,text=True,timeout=timeout).strip()
    def inside(job, command, timeout=60, memory=512):
        return run(['srun','--overlap','--exact','--jobid='+job,'--ntasks=1',
                    '--cpus-per-task=1','--mem='+str(memory)+'M',*command],timeout)
    checkpoint=None
    retired=False
    try:
        state('waiting_for_replacement_readiness')
        deadline=time.monotonic()+12*3600
        while not (a.handoff/'replacement-ready.txt').is_file():
            if time.monotonic()>deadline:raise TimeoutError('Allocation readiness timeout; old run was left active')
            old=run(['squeue','-h','-j',a.old_job,'-o','%T'])
            if old!='RUNNING':raise RuntimeError('Original job no longer running; inspect its result before handoff: '+old)
            new=run(['squeue','-h','-j',a.new_job,'-o','%T'])
            if new not in ('PENDING','RUNNING','CONFIGURING'):raise RuntimeError('Replacement unavailable: '+new)
            time.sleep(30)
        new_job,new_work=(a.handoff/'replacement-ready.txt').read_text().splitlines()
        if new_job!=a.new_job or not new_work.startswith('/tmp/triangle-yale-'+a.new_job+'-'):
            raise ValueError('Replacement readiness identifies a different allocation')
        state('draining_and_saving_original')
        output=inside(a.old_job,['python3',str(a.control/'hpc/checkpoint_abb_scaleup.py'),
                     '--work',str(a.old_work),'--handoff',str(a.handoff),'--job',a.old_job],1800,memory=8192)
        (a.handoff/'checkpoint-helper.log').write_text(output+'\n')
        checkpoint=json.loads((a.handoff/'checkpoint.json').read_text())
        if checkpoint['old_job']!=a.old_job or checkpoint['old_work']!=str(a.old_work):
            raise ValueError('Wrong original checkpoint')
        state('validating_replacement_cache',preserved_module_count=checkpoint['preserved_module_count'])
        deadline=time.monotonic()+3600
        code='import json,sys;from pathlib import Path;r=Path(sys.argv[1])/"logs";p=r/"family-build/status.json";print(json.dumps(dict(source_match=(r/"checkpoint-source-match.txt").is_file(),checkpoint_restored=(r/"preserved-checkpoint.json").is_file(),build=json.loads(p.read_text()) if p.is_file() else None)))'
        while True:
            probe=json.loads(inside(a.new_job,['python3','-c',code,new_work]))
            if ready_to_retire(probe,checkpoint):break
            if (probe.get('build') or {}).get('failed'):raise RuntimeError('Replacement build failed')
            if time.monotonic()>deadline:raise TimeoutError('Replacement cache validation timeout')
            if run(['squeue','-h','-j',a.new_job,'-o','%T'])!='RUNNING':raise RuntimeError('Replacement stopped before validation')
            time.sleep(30)
        if run(['squeue','-h','-j',a.integration_job,'-o','%T'])!='PENDING':
            raise RuntimeError('Integration is no longer pending; do not change it')
        # The other four original regional dependencies are preserved exactly.
        dependencies='afterok:30082912:'+a.new_job+':30082914:30082915:30082916'
        run(['scontrol','update','JobId='+a.integration_job,'Dependency='+dependencies])
        details=run(['scontrol','show','job',a.integration_job,'-o'])
        (a.handoff/'integration-dependency.txt').write_text(details+'\n')
        if 'afterok:'+a.new_job not in details:raise RuntimeError('Integration dependency change was not confirmed')
        # Deliver TERM to the stopped coordinator, then CONT to let TERM take
        # effect. Its already-finished children and consistent cache are saved.
        code='import json,os,signal,sys;from pathlib import Path;sys.path.insert(0,sys.argv[2]);from checkpoint_abb_scaleup import process_table,matching_scheduler;c=json.loads(Path(sys.argv[1]).read_text());p=c["scheduler_pid"];t=process_table();assert p in t and t[p]["state"]=="T" and matching_scheduler(t[p]["argv"],Path(c["old_work"]));os.kill(p,signal.SIGTERM);os.kill(p,signal.SIGCONT);print("Original ABB coordinator retired after replacement validation")'
        inside(a.old_job,['python3','-c',code,str(a.handoff/'checkpoint.json'),str(a.control/'hpc')])
        retired=True
        state('handoff_complete',new_work=new_work,checkpoint_sha256=checkpoint['archive_sha256'],
              validated_replacement=probe,integration_dependencies=dependencies)
    except BaseException as error:
        if not retired:
            # Resume the exact old coordinator on an unsuccessful handoff.
            code='import os,signal,sys;from pathlib import Path;sys.path.insert(0,sys.argv[2]);from checkpoint_abb_scaleup import process_table,matching_scheduler;t=process_table();p=[p for p,r in t.items() if matching_scheduler(r["argv"],Path(sys.argv[1]))];assert len(p)==1;os.kill(p[0],signal.SIGCONT)'
            try:inside(a.old_job,['python3','-c',code,str(a.old_work),str(a.control/'hpc')])
            except Exception as resume_error:record['resume_error']=repr(resume_error)
        state('handoff_needs_review',error=repr(error))
        raise


if __name__=='__main__':main()
