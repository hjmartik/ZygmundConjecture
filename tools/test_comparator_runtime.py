#!/usr/bin/env python3
"""Small real Linux comparisons through the public runner, not paper checks. Apache-2.0."""
import argparse
from datetime import datetime,timezone
from pathlib import Path
import shutil
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from common import ROOT,LEAN,require,digest,compiler_bin,fresh_run,write_json,source_manifest,targets
from comparator import input_hashes,validate_cases,tool_paths,preflight
from comparator_runtime import external_config,runtime_environment,guarded,comparison_outcome

def main(args):
    inputs=input_hashes();sources=source_manifest();selected=targets();validate_cases()
    bindir=compiler_bin(args.lean_bin);bins=tool_paths(args.tools.resolve(),bindir)
    hashes={n:digest(p) for n,p in bins.items()}
    run=fresh_run('comparator-fixtures')
    report=dict(status='RUNNING',fixture_only=True,started_utc=datetime.now(timezone.utc).isoformat(),
                scope='Tiny checking-program fixtures; no main theorem runs',cases=[],tools=hashes,controls=inputs)
    print('Run: '+str(run),flush=True)
    def save():write_json(run/'report.json',report)
    challenge='theorem answer (n : Nat) : n = n := by sorry\n'
    valid='theorem answer (n : Nat) : n = n := rfl\n'
    cases=[('valid',challenge,valid,None),
           ('extra-assumption',challenge,'theorem answer (n : Nat) (h : n = n) : n = n := h\n','match'),
           ('changed-definition','def number : Nat := 2\ntheorem answer : number = 2 := by sorry\n',
            'def number : Nat := 3\ntheorem answer : number = 3 := rfl\n','match'),
           ('indirect-admission',challenge,'theorem helper (n : Nat) : n = n := by sorry\ntheorem answer (n : Nat) : n = n := helper n\n','sorryAx'),
           ('missing-nanoda',challenge,valid,'was not found'),
           ('failing-nanoda',challenge,valid,'nanoda kernel rejected'),
           ('missing-con-ron',challenge,valid,'was not found'),
           ('failing-con-ron',challenge,valid,'con-ron kernel rejected')]
    try:
        for name,statement,proof,rejection in cases:
            project=run/name;project.mkdir()
            scratch=project/'.lake/verification-tmp';scratch.mkdir(parents=True)
            (project/'Challenge.lean').write_text(statement);(project/'Solution.lean').write_text(proof)
            shutil.copyfile(LEAN/'lean-toolchain',project/'lean-toolchain')
            (project/'lakefile.toml').write_text('name = "checker_fixtures"\ndefaultTargets = []\n\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n')
            write_json(project/'lake-manifest.json',dict(version='1.3.0',packagesDir='.lake/packages',
                packages=[],name='checker_fixtures',lakeDir='.lake'))
            cfg=external_config(dict(challenge_module='Challenge',solution_module='Solution',theorem_names=['answer'],
                permitted_axioms=['propext','Classical.choice','Quot.sound']),bindir)
            marker=None;binary=None
            if name.startswith(('missing-','failing-')):
                kernel=name.split('-',1)[1];binary=project/('fixture-'+name)
                if name.startswith('failing-'):
                    marker='PUBLIC_FIXTURE_'+kernel.upper().replace('-','_')+'_EXIT_73'
                    source=project/'failure.c'
                    source.write_text('#include <stdio.h>\nint main(void) { puts("'+marker+'"); fflush(stdout); return 73; }\n')
                    result=subprocess.run(['cc','-static','-O2','-o',str(binary),str(source)],capture_output=True,text=True,timeout=60)
                    (project/'build.log').write_text(result.stdout+result.stderr)
                    require(result.returncode==0 and binary.is_file() and not binary.is_symlink(),'Static failure fixture did not build')
                # Deliberately mutate only this isolated fixture's runtime copy.
                cfg['external_kernels'][kernel]=[str(binary)]
            write_json(project/'config.json',cfg)
            frozen={p.name:digest(p) for p in project.iterdir() if p.is_file()}
            env=runtime_environment(bindir,scratch,bins['bwrap'])
            if name=='valid':report['preflight']=preflight(project,run,env)
            result=guarded(project,env,[sys.executable,ROOT/'tools/comparator-child.py',bindir/'lake',project/'config.json'],timeout=180)
            log=run/(name+'.log');log.write_text(result.stdout+result.stderr);text=log.read_text()
            outcome=comparison_outcome(result.returncode,text)
            row=dict(name=name,command=result.args,config=cfg,inputs=frozen,log_sha256=digest(log),outcome=outcome,
                     expected_failure=rejection,invocation_marker=marker)
            if marker:row['failure_executable_sha256']=digest(binary)
            report['cases'].append(row);save()
            if rejection is None:require(outcome['passed'],'Valid fixture did not pass')
            else:require(not outcome['passed'] and result.returncode!=0 and rejection in text and not outcome['comparator_accepted'],
                         'Fixture rejected for the wrong reason: '+name)
            if marker:
                other='con_ron_accepted' if kernel=='nanoda' else 'nanoda_accepted'
                require(marker in text and outcome['lean_accepted'] and outcome[other],
                        'Failure fixture did not execute alongside successful other kernels')
                require('bwrap:' not in text,'Unexpected sandbox launch failure')
            require(all(digest(project/n)==h for n,h in frozen.items()),'Fixture input changed')
            print('PASS '+name,flush=True)
        require(input_hashes()==inputs and source_manifest()==sources and targets()==selected,'Production inputs changed')
        require({n:digest(p) for n,p in bins.items()}==hashes,'Checker binaries changed')
        report['status']='PASS_FIXTURES_ONLY'
    except BaseException as error:
        report.update(status='FAIL',failure=str(error));raise
    finally:
        report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print('Report: '+str(run/'report.json'),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin')
    parser.add_argument('--tools',type=Path,default=ROOT/'.tools/checkers')
    main(parser.parse_args())
