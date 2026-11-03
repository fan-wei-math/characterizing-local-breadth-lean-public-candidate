"""Fail closed on source/checker bytes, import omissions and dependency pins."""
from pathlib import Path
import hashlib,json,subprocess,sys,re,tomllib
from lean_comment_projection import projection,self_test
BASE=Path(__file__).resolve().parents[1]
ROOT=BASE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def audit():
 manifest=BASE/'manifests/SOURCE-SHA256SUMS'
 expected={}
 for line in manifest.read_text().splitlines():
  h,name=line.split('  ',1);p=ROOT/name
  assert p.is_file() and sha(p)==h, 'SOURCE_MANIFEST_MISMATCH '+name
  expected[name]=h
 for folder in ['lean','verification','scripts','manifests']:
  for p in (BASE/folder).rglob('*'):
   if not p.is_file() or '.lake' in p.parts or '__pycache__' in p.parts:continue
   name=p.relative_to(ROOT).as_posix()
   if p==manifest:continue
   assert name in expected,'UNMANIFESTED_SOURCE '+name
 provenance=json.loads((BASE/'manifests/SOURCE-PROVENANCE.json').read_text())['files']
 comment_baseline=json.loads((BASE/'manifests/COMMENT-PROJECTION-BASELINES.json').read_text())['files']
 assert len(comment_baseline)==133 and len({f['path'] for f in comment_baseline})==133
 baseline={f['path']:f for f in comment_baseline};self_test()
 for f in provenance:
  path=ROOT/f['released_path']
  assert sha(path)==f['released_sha256'], f['released_path']
  assert f['bytes_equal'] == (f['released_sha256']==f['original_sha256']), f['released_path']
  if f['category']=='mathematical_source':
   b=baseline[f['released_path']]
   assert f['outside_comments_equal'] is b['outside_comments_equal'] is True
   assert f['original_sha256']==b['original_sha256']
   assert f['released_sha256']==b['candidate_sha256']
   assert hashlib.sha256(projection(path.read_text())).hexdigest()==b['noncomment_projection_sha256']==f['noncomment_projection_sha256'], f['released_path']
   assert path.read_text().count('\n')==b['newline_count'], f['released_path']
  else:
   assert f['bytes_equal'] is True and f['released_sha256']==f['original_sha256'], f['released_path']
 modules=json.loads((BASE/'manifests/ALL-MODULES.json').read_text())['modules']
 assert len(modules)==133 and len(set(modules))==133
 for module in modules:
  p=BASE/'lean'/Path(*module.split('.')).with_suffix('.lean');assert p.exists(),module
  text=p.read_text()
  for line in text.splitlines():
   if line.startswith('import '):
    for imp in line[7:].split():
     if imp.startswith(('BanachDensity1D','BanachDensityHD')):assert imp in modules,('MISSING_IMPORT',module,imp)
 cfg=tomllib.loads((BASE/'lean/lakefile.toml').read_text());lock=json.loads((BASE/'lean/lake-manifest.json').read_text())
 assert cfg['require']==[{'name':'mathlib','scope':'leanprover-community','rev':'56a005855ea17e0b0958f73ec801ae140b0a1679'}]
 assert len(lock['packages'])==9
 for pkg in lock['packages']:
  assert pkg['type']=='git' and re.fullmatch('[0-9a-f]{40}',pkg['rev'])
  assert re.fullmatch(r'https://github.com/(leanprover-community|leanprover)/[A-Za-z0-9_-]+',pkg['url']),pkg
 assert (BASE/'lean/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
 theorems=json.loads((BASE/'manifests/THEOREM-MAP.json').read_text())['rows'];defs=json.loads((BASE/'manifests/DEFINITION-MAP.json').read_text())['rows']
 assert len(theorems)==65 and len(defs)==14
 assert next(x for x in theorems if x['number']=='1.6')['declarations']==['BanachDensity1D.Oct31.finite_point_rank_all']
 print(json.dumps({'status':'PASS','manifest_files':len(expected),'original_provenance_files':len(provenance),'byte_identical_original_files':sum(f['bytes_equal'] for f in provenance),'comment_sanitized_files':sum(not f['bytes_equal'] for f in provenance),'unchanged_noncomment_mathematical_files':len(comment_baseline),'mathematical_source_files':sum(f['category']=='mathematical_source' for f in provenance),'all_modules':len(modules),'theorem_rows':len(theorems),'definition_rows':len(defs),'external_packages':len(lock['packages'])}))
if __name__=='__main__':audit()
