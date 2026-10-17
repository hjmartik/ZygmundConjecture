#!/usr/bin/env python3
"""Twenty-two source-bound comparisons with the pinned rc4 bundled kernels. Apache-2.0."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (ROOT, LEAN, require, digest, read_json, write_json, source_manifest,
                    targets, check_dependencies, compiler_bin, fresh_run, imports, control_hashes)
from comparator_runtime import (guarded, comparison_outcome, require_comparison_success,
                                external_config, runtime_environment)

ADAPTERS = ROOT / 'verification/comparator'
NAMESPACE = 'ReyZygmund.MathlibOnly'
# Case order is stable; append new independently stated results.
# These are the defining modules, even when Solutions imports the public theorem.
PUBLIC_RESULTS = [dict(name=f'{NAMESPACE}.{theorem}', contract=f'{NAMESPACE}.{contract}',
                       module=f'{NAMESPACE}.{module}', contract_module=f'{NAMESPACE}.{spec}')
    for theorem, contract, module, spec in [
        ('weakly_incomparable_maximal_estimate', 'WeaklyIncomparableMaximalEstimate', 'Solutions', 'Statements'),
        ('weakly_incomparable_rey_conjecture', 'WeaklyIncomparableReyConjecture', 'Solutions', 'Statements'),
        ('zygmund_conjecture', 'ZygmundConjecture', 'Solutions', 'Statements'),
        ('rounded_dyadic_endpoint_estimate', 'RoundedDyadicEndpointEstimate', 'Solutions', 'SupportingStatements'),
        ('sparse_phi_zygmund_overlap_estimate', 'SparsePhiZygmundOverlapEstimate', 'Solutions', 'SupportingStatements'),
        ('classical_dyadic_zygmund_sharpness', 'ClassicalDyadicZygmundSharpness', 'Solutions', 'SupportingStatements'),
        ('maximal_square_function_estimate', 'MaximalSquareFunctionEstimate', 'Proof.MaximalSquareSolution', 'SupportingStatements'),
        ('weighted_square_function_estimate', 'WeightedSquareFunctionEstimate', 'Proof.SquareSolutions', 'SupportingStatements'),
        ('product_weighted_square_function_estimate', 'ProductWeightedSquareFunctionEstimate', 'Proof.ProductSquareSolution', 'SupportingStatements'),
        ('projection_preserves_averages', 'ProjectionPreservesAverages', 'Proof.ProjectionAverageSolutions', 'SupportingStatements'),
        ('projection_partial_averages', 'ProjectionPartialAverages', 'Proof.ProjectionAverageSolutions', 'SupportingStatements'),
        ('projection_differences', 'ProjectionDifferences', 'Proof.ProjectionDifferencesSolution', 'SupportingStatements'),
        ('averaging_family_geometry', 'AveragingFamilyGeometry', 'Proof.AveragingFamilySolutions', 'SupportingStatements'),
        ('representation_of_averages', 'RepresentationOfAverages', 'Proof.AveragingFamilySolutions', 'SupportingStatements'),
        ('maximal_square_function_reduction', 'MaximalSquareFunctionReduction', 'Proof.ProjectedSquareSolutions', 'SupportingStatements'),
        ('projected_square_function_estimate', 'ProjectedSquareFunctionEstimate', 'Proof.ProjectedSquareSolutions', 'SupportingStatements'),
        ('scalar_estimate', 'ScalarEstimate', 'Proof.SquareSolutions', 'SupportingStatements'),
        ('prescribed_scale_covering', 'PrescribedScaleCovering', 'Proof.CoveringSolution', 'SupportingStatements'),
        ('cordoba_fefferman_selection', 'CordobaFeffermanSelection', 'Proof.SelectionSolution', 'SupportingStatements'),
        ('weakly_incomparable_slices', 'WeaklyIncomparableSlices', 'Proof.SliceSolutions', 'SupportingStatements'),
        ('half_sparse_slices', 'HalfSparseSlices', 'Proof.SliceSolutions', 'SupportingStatements'),
        ('dyadic_zygmund_conjecture', 'DyadicZygmundConjecture', 'Proof.DyadicEndpointSolution', 'SupportingStatements')]]
SPECIFICATION_CLOSURES = {
    f'{NAMESPACE}.{spec}': [f'{NAMESPACE}.{name}' for name in names]
    for spec, names in {
        'Statements': ['Definitions', 'Statements'],
        'SupportingStatements': ['Definitions', 'Projections', 'SquareFunctions', 'SupportingStatements']
    }.items()}

def input_hashes():
    paths = list(ADAPTERS.iterdir()) + [ROOT/'verification/CHECKER-PINS.json']
    paths += [ROOT/'tools'/name for name in ('comparator.py','comparator_runtime.py',
              'comparator-child.py','comparator-preflight.py')]
    return {**control_hashes(), **{str(p.relative_to(ROOT)):digest(p) for p in paths if p.is_file()}}

def validate_cases():
    audit = read_json(ROOT/'verification/AUDIT-MANIFEST.json')
    require(audit['expected_comparisons'] == len(PUBLIC_RESULTS), 'Expected twenty-two comparisons')
    binding = audit['sha256']
    expected = {p for p in binding if p.startswith('verification/comparator/')}
    approved = {'verification/comparator/' + name for name in ('CASES.json', 'Solution.lean')}
    approved.update('verification/comparator/' + name for i in range(1, len(PUBLIC_RESULTS)+1)
                    for name in (f'Challenge{i}.lean', f'comparison-{i}.json'))
    actual = {str(p.relative_to(ROOT)) for p in ADAPTERS.iterdir()}
    require(actual == expected == approved, 'Comparator input inventory differs')
    for name in expected:
        p = ROOT/name
        require(p.is_file() and not p.is_symlink() and digest(p)==binding[name],
                'Reviewed Comparator input differs: '+name)
    cases = read_json(ADAPTERS/'CASES.json')['cases']
    require(len(cases)==len(PUBLIC_RESULTS), 'Expected twenty-two distinct public results')
    registered = [t for t in targets() if t['contract_module'] in SPECIFICATION_CLOSURES]
    require(len(registered)==len(PUBLIC_RESULTS) and
            {t['name']:t for t in registered} == {t['name']:t for t in PUBLIC_RESULTS},
            'Public target, contract or defining module differs')
    for i,(c,target) in enumerate(zip(cases,PUBLIC_RESULTS),1):
        require(c==dict(id=f'main-{i}', config=f'comparison-{i}.json',
                       production_target=target['name'], challenge_module=f'Challenge{i}',
                       solution_module='Solution'), 'Unexpected adapter mapping')
        cfg=read_json(ADAPTERS/c['config'])
        require(cfg==dict(challenge_module=c['challenge_module'], solution_module=c['solution_module'],
            theorem_names=[c['production_target']], permitted_axioms=['propext','Classical.choice','Quot.sound']),
            'Comparator configuration differs')
    return cases

def validate_import_separation(manifest):
    audit=read_json(ROOT/'verification/AUDIT-MANIFEST.json')
    specs={name for names in SPECIFICATION_CLOSURES.values() for name in names}
    require(audit['specification_modules']==sorted(specs) and
            audit['specification_closures']==SPECIFICATION_CLOSURES,
            'Specification module list or closure differs')
    modules={p[5:-5].replace('/','.'):ROOT/p for p in manifest['sha256']}
    modules.update({p.stem:p for p in ADAPTERS.glob('*.lean')})
    cases=validate_cases()
    challenges={c['challenge_module'] for c in cases}
    expected={c['challenge_module']:set(SPECIFICATION_CLOSURES[t['contract_module']])
              for c,t in zip(cases,PUBLIC_RESULTS)}
    def closure(root, independent):
        seen,active,external=set(),set(),set()
        def visit(name):
            require(name not in active,'Cyclic audit import')
            if name in seen:return
            if name not in modules:
                require(name.split('.')[0] in {'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq',
                    'Plausible','ProofWidgets','ImportGraph','LeanSearchClient'}, 'Unresolved audit import: '+name)
                external.add(name);return
            if independent:require(name in specs or name==root,'Proof-library import in Mathlib-only challenge: '+name)
            else:require(name not in challenges and not name.startswith('Verification.Fixtures.'),
                         'Challenge placeholder or fixture imported by solution: '+name)
            active.add(name)
            for child in imports(modules[name]):visit(child)
            active.remove(name);seen.add(name)
        visit(root)
        if independent:require(seen==expected[root]|{root},'Independent specification closure differs')
        return dict(local_modules=sorted(seen),external_imports=sorted(external))
    return {name:closure(name,name in challenges) for name in sorted(challenges|{'Solution'})}

def selected_cases(cases, number=None):
    require(len(cases)==len(PUBLIC_RESULTS), 'Expected twenty-two available cases')
    if number is None:return cases
    require(type(number) is int and 1<=number<=len(cases), 'Case number must be from 1 through 22')
    return [cases[number-1]]

def case_selection(cases):
    return [dict(id=c['id'], production_target=c['production_target']) for c in cases]

def finish_cases(cases, reports, number=None, unsandboxed=False):
    """Require every requested case exactly once before assigning a success label."""
    requested=case_selection(selected_cases(cases,number))
    completed=case_selection(reports)
    require(completed==requested, 'Completed comparison selection differs')
    for row in reports:require_comparison_success(row)
    status='PASS_ALL_TWENTY_TWO' if number is None else 'PASS_ONE_CASE_ONLY'
    if unsandboxed:status+='_UNSANDBOXED'
    return dict(status=status,completed_cases=completed)

def tool_paths(directory, bindir):
    pins=read_json(ROOT/'verification/CHECKER-PINS.json')
    result={name:bindir/name for name in ('lean','lake','leanexport','leanchecker','nanoda_bin','con-ron')}
    result['bwrap']=Path(directory)/'bwrap'
    for name,path in result.items():require(path.is_file() and os.access(path,os.X_OK),'Missing executable: '+name)
    version=subprocess.check_output([result['lean'],'--version'],text=True)
    require(pins['lean']['revision'] in version,'Checker compiler revision differs')
    version=subprocess.check_output([result['bwrap'],'--version'],text=True).strip()
    require(version=='bubblewrap '+pins['bubblewrap']['version'],'Bubblewrap version differs')
    return result

def preflight(project,parent,env):
    sentinel=parent/'preflight-read-only.txt'
    sentinel.write_text('preserve\n')
    namespace=os.readlink('/proc/self/ns/net')
    result=guarded(project,env,[sys.executable,ROOT/'tools/comparator-preflight.py',sentinel,namespace],timeout=60)
    log=parent/'preflight.log';log.write_text(result.stdout+result.stderr)
    require(result.returncode==0 and sentinel.read_text()=='preserve\n','Runtime preflight failed; inspect '+str(log))
    return dict(command=result.args,log_sha256=digest(log),status='PASS')

def run(args):
    manifest=source_manifest();cases=validate_cases();boundary=validate_import_separation(manifest)
    selected=selected_cases(cases,args.case)
    controls=input_hashes(); parent=fresh_run('comparator');project=parent/'project';project.mkdir()
    for name in manifest['sha256']:
        dest=project/name.removeprefix('lean/');dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/name,dest)
    for name in ('lean-toolchain','lakefile.toml','lake-manifest.json'):
        shutil.copyfile(LEAN/name,project/name)
    for p in ADAPTERS.iterdir():
        if p.name!='CASES.json':shutil.copyfile(p,project/p.name)
    packet={str(p.relative_to(project)):digest(p) for p in project.rglob('*') if p.is_file()}
    report=dict(status='PREPARED_NOT_CHECKED',started_utc=datetime.now(timezone.utc).isoformat(),
        scope=('Twenty-two independent results and their exported dependencies' if args.case is None else
               'One selected independent result and its exported dependencies'),
        cases=[],approved_cases=case_selection(cases),requested_cases=case_selection(selected),completed_cases=[],
        source_files=manifest['sha256'],
        packet_sha256=packet,controls=controls,import_separation=boundary,
        required_kernels=['Lean default','nanoda','con-ron'])
    def save():write_json(parent/'report.json',report)
    save();print('Packet: '+str(project),flush=True)
    if args.prepare_only:return
    try:
        require(platform.system()=='Linux' and os.geteuid()!=0,'Use an unprivileged Linux user')
        packages=(args.packages or LEAN/'.lake/packages').expanduser().resolve()
        deps=check_dependencies(packages);bindir=compiler_bin(args.lean_bin)
        bins=tool_paths(args.tools.expanduser().resolve(),bindir)
        require(shutil.disk_usage(parent).free>15*1024**3,'Need at least 15 GiB free disk')
        (project/'.lake').mkdir()
        subprocess.run(['cp','-a','--reflink=auto',str(packages),str(project/'.lake/packages')],check=True)
        scratch=project/'.lake/verification-tmp';scratch.mkdir()
        env=runtime_environment(bindir,scratch,bins['bwrap'])
        hashes={name:digest(p) for name,p in bins.items()}
        report.update(status='RUNNING',tool_sha256=hashes,dependency_sources=deps)
        report['preflight']=preflight(project,parent,env);save()
        for case in selected:
            cfg=external_config(read_json(project/case['config']),bindir)
            runtime=project/('runtime-'+case['config']);write_json(runtime,cfg)
            report.setdefault('runtime_configs',{})[runtime.name]=dict(sha256=digest(runtime),config=cfg)
            started=time.monotonic()
            result=guarded(project,env,[sys.executable,ROOT/'tools/comparator-child.py',bindir/'lake',runtime])
            log=parent/(case['id']+'.log');log.write_text(result.stdout+result.stderr)
            row=dict(id=case['id'],production_target=case['production_target'],command=result.args,
                     seconds=round(time.monotonic()-started,3),log=log.name,log_sha256=digest(log))
            row.update(comparison_outcome(result.returncode,log.read_text()))
            report['cases'].append(row);save();require_comparison_success(row)
            print('PASS '+case['id']+': Comparator, Lean, Nanoda and con-ron',flush=True)
        require(all(digest(project/n)==h for n,h in packet.items()),'Packet changed during checking')
        require(all(digest(project/n)==v['sha256'] for n,v in report['runtime_configs'].items()),'Runtime config changed')
        require(source_manifest()==manifest and input_hashes()==controls,'Original inputs changed')
        require(check_dependencies(packages)==deps and check_dependencies(project/'.lake/packages')==deps,
                'Dependency sources changed')
        require({n:digest(p) for n,p in bins.items()}==hashes,'Checker binaries changed')
        report.update(finish_cases(cases,report['cases'],args.case))
    except BaseException as error:
        report.update(status='FAIL',failure=str(error));raise
    finally:
        report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print('Report: '+str(parent/'report.json'))

def argument_parser():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only',action='store_true')
    parser.add_argument('--tools',type=Path,default=ROOT/'.tools/checkers',help='Directory containing pinned bwrap')
    parser.add_argument('--packages',type=Path)
    parser.add_argument('--lean-bin')
    parser.add_argument('--case',type=int,choices=range(1,len(PUBLIC_RESULTS)+1))
    return parser

if __name__=='__main__':
    run(argument_parser().parse_args())
