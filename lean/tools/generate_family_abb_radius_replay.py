#!/usr/bin/env python3
"""Propose padded ABB margins using the existing, unchanged replay source.

No endpoint or enclosure proof is regenerated. Lean checks new integer margins,
coefficient/contact bounds, the radius-transfer proof, and tree assembly.
The default smoke mode checks one entire subtree and the final-region leaf.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def field(text, name):
    match = re.search(r'^theorem '+name+r'\s*:.*? := (.+)$', text, re.M)
    if match is None:
        raise ValueError('Missing theorem expression: '+name)
    return match.group(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=['smoke', 'full'], default='smoke')
    args = parser.parse_args()
    mode = args.mode.title()
    old = 'SparseLowerTail.Section08.FamilyABBReplay.'+mode
    new = 'SparseLowerTail.Section08.FamilyABBRadiusReplay.'+mode
    source = ROOT/old.replace('.', '/')
    report = json.loads((source/'generation.json').read_text())
    if report['mode'] != args.mode:
        raise ValueError('Replay mode mismatch')
    out = ROOT/new.replace('.', '/')
    out.mkdir(parents=True, exist_ok=True)
    modules, hashes, leaf_count = [], {}, 0

    def header(imports):
        return '\n'.join('import '+m for m in imports)+f'''\n
/-! Generated proposals; every numerical assertion is checked by Lean. -/
namespace {new}
open SparseLowerTail.Numerics SparseLowerTail.Certificate SparseLowerTail.Section04
open SparseLowerTail.Certificate.HessianRadiusTransfer
open {old}
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''

    def read(name):
        path = source/(name+'.lean')
        hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        return path.read_text()

    def save(name, text):
        (out/(name+'.lean')).write_text(text+f'\nend {new}\n')
        modules.append(new+'.'+name)

    leaf_modules, coverage_modules = [], []
    for module in report['modules']:
        name = module.rsplit('.', 1)[1]
        if not name.startswith('Leaves'):
            continue
        txt = header([module, 'SparseLowerTail.Section08.FamilyHessianRadiusTransfer'])
        ids = re.findall(r'^def offsetBox(\d+) :', read(name), re.M)
        if not ids:
            raise ValueError('Empty leaf module')
        leaf_count += len(ids)
        for i in ids:
            txt += f'''
theorem padded_margins{i} : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate{i}.hessianIntervals) transform{i}) := by
  decide +kernel

theorem small_coefficients{i} : ∀j,SmallCoefficient (box{i}.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact{i} : BoundedContact box{i} := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion{i} : ∀x,offsetBox{i}.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate{i} certificate{i}_valid transform{i}
    padded_margins{i} enclosure{i} small_coefficients{i} bounded_contact{i}
'''
        save(name, txt)
        leaf_modules.append(new+'.'+name)
    if leaf_count != report['leaves']:
        raise ValueError('Leaf count mismatch')
    for module in report['modules']:
        name = module.rsplit('.', 1)[1]
        if not name.startswith('Coverage'):
            continue
        original = read(name)
        imports = re.findall(r'^import '+re.escape(old)+r'\.(Leaves\d+)$', original, re.M)
        txt = header([new+'.'+m for m in imports]+[module])
        expression = re.sub(r'\bconclusion(\d+)\b', r'radius_conclusion\1', field(original, 'leaf_proofs'))
        txt += f'''
namespace {name}
abbrev initialBox := {old}.{name}.initialBox
abbrev leafTable := {old}.{name}.leafTable
abbrev subdivision := {old}.{name}.subdivision
theorem leaf_proofs : leafTable.All (ReplayBoxProperty RadiusABBOffsetProperty) := {expression}
theorem covered : ∀x,initialBox.Contains x → RadiusABBOffsetProperty x :=
  subdivision.sound_table leaf_proofs {old}.{name}.valid
end {name}
'''
        save(name, txt)
        coverage_modules.append(new+'.'+name)
    final = 'CheckedSubtree' if args.mode == 'smoke' else 'FullNeighborhood'
    if args.mode == 'smoke':
        save(final, header(leaf_modules+coverage_modules))
    else:
        original = read(final)
        expression = field(original, 'chunk_proofs')
        txt = header(coverage_modules+[old+'.'+final])
        txt += f'''
abbrev chunkTable := {old}.chunkTable
abbrev subdivision := {old}.subdivision
theorem chunk_proofs : chunkTable.All (ReplayBoxProperty RadiusABBOffsetProperty) := {expression}
theorem hessian_positive {{z : ℝ}} (hz : 0<z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {{q : FamilyVector}} (hq : q∈familyCube (familyContactABB z)
      ManuscriptFamilyRadius.binary64Radius)
    {{v : FamilyVector}} (hv : v≠0) : 0<familyHessianForm z q v :=
  abb_hessian_of_table chunkTable subdivision {old}.valid chunk_proofs hz hL hq hv

theorem local_nonnegative_and_unique_zero {{z : ℝ}} (hz : 0<z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {{q : FamilyVector}} (hq : q∈familyCube (familyContactABB z)
      ManuscriptFamilyRadius.binary64Radius) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) :=
  abb_local_of_table chunkTable subdivision {old}.valid chunk_proofs hz hL hq
'''
        save(final, txt)
    result = {'trust_status': 'Generated; requires Lean build and axiom audit',
              'mode': args.mode, 'leaves': leaf_count,
              'coverage_chunks': len(coverage_modules), 'source_modules_sha256': hashes,
              'final_module': new+'.'+final, 'modules': modules}
    (out/'generation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['modules','source_modules_sha256']}))


if __name__ == '__main__':
    main()
