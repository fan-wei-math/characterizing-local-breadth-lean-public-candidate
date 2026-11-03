from pathlib import Path
import json,sys
from fingerprint_algorithm import parse,closure_fps,check
base=Path(__file__).resolve().parents[1]
project,log=sys.argv[1:];record=next(p for p in json.loads((base/'manifests/FROZEN-BASELINES.json').read_text())['projects'] if p['project']==project)
current=closure_fps(parse(Path(log).read_text()));bad=check(record['fingerprints'],current)
assert not bad,bad
print(json.dumps({'status':'PASS','project':project,'approved':record['approved_count'],'drift':len(bad),'current_declarations':len(current),'baseline_sha256':record['baseline_file_sha256']}))
