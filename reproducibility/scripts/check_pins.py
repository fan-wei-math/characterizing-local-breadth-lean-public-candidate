from pathlib import Path
import json,subprocess,hashlib
BASE=Path(__file__).resolve().parents[1];LEAN=BASE/'lean'
lock=json.loads((LEAN/'lake-manifest.json').read_text());rows=[]
for p in lock['packages']:
 name=p['name'].strip('«»');d=LEAN/'.lake/packages'/name
 h=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()
 assert h==p['rev'],(name,h,p['rev'])
 changes=subprocess.check_output(['git','status','--porcelain=v1','--untracked-files=no'],cwd=d,text=True)
 assert not changes,(name,changes)
 rows.append({'name':name,'url':p['url'],'sha':h})
version=subprocess.check_output(['lake','env','lean','--version'],cwd=LEAN,text=True).strip()
assert 'version 4.35.0' in version,version
math=json.loads((LEAN/'.lake/packages/mathlib/lake-manifest.json').read_text())
locked={p['name']:p for p in lock['packages']}
for p in math['packages']:
 assert p['name'] in locked and p['rev']==locked[p['name']]['rev'] and p['url']==locked[p['name']]['url'],p
print(json.dumps({'status':'PASS','lean':version,'packages':rows,'mathlib_transitive_manifest_matches':True,'release_lock_sha256':hashlib.sha256((LEAN/'lake-manifest.json').read_bytes()).hexdigest()}))
