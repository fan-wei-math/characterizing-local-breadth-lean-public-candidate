"""Portable one-command verification with separate raw, timed, fail-closed receipts."""
from pathlib import Path
import argparse,subprocess,os,sys,json,time,datetime,platform,resource,hashlib,signal
BASE=Path(__file__).resolve().parents[1];ROOT=BASE.parent;LEAN=BASE/'lean'
p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--fast',action='store_true');g.add_argument('--all',action='store_true');p.add_argument('--output',default=None);p.add_argument('--jobs',type=int,default=4);a=p.parse_args()
out=Path(a.output).resolve() if a.output else BASE/'.runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out.mkdir(parents=True,exist_ok=False)
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',GIT_TERMINAL_PROMPT='0',GIT_OPTIONAL_LOCKS='0')
# No dependence on a user's Git URL rewriting or private checkout credentials.
env['GIT_CONFIG_GLOBAL']=os.devnull
env['LEAN_NUM_THREADS']=str(a.jobs)
records=[]
def run(name,cmd,cwd=ROOT,timeout=3600):
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
 try:
  with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:
   proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
   try:status=proc.wait(timeout=timeout)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();status=124
 except OSError as e:
  (out/(name+'.stderr')).write_text(str(e));status=127
 row={'name':name,'command':list(cmd),'cwd':str(Path(cwd).relative_to(ROOT)) or '.',
      'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'elapsed_seconds':time.monotonic()-t,'timeout_seconds':timeout,'exit_code':status,
      'stdout':name+'.stdout','stderr':name+'.stderr','max_child_rss_native_units':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
 (out/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n');records.append(row)
 print(name+': exit '+str(status),flush=True)
 if status:raise RuntimeError(name+' failed; see raw output in '+str(out))
 return out/(name+'.stdout')
try:
 base_sha=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
 dirty=subprocess.check_output(['git','status','--porcelain=v1'],cwd=ROOT,text=True)
 identity={'git_head_at_start':base_sha,'tracked_worktree_status_at_start':dirty,'branch':subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip(),'platform':platform.platform(),'python':sys.version,'cpu_count':os.cpu_count(),'jobs':a.jobs,'mode':'all' if a.all else 'fast','new_project_build_before':(LEAN/'.lake/build').exists(),'pinned_external_cache_present_before':(LEAN/'.lake/packages/mathlib/.lake/build').exists(),'source_manifest_sha256':hashlib.sha256((BASE/'manifests/SOURCE-SHA256SUMS').read_bytes()).hexdigest(),'environment_overrides':{k:env[k] for k in ['PYTHONDONTWRITEBYTECODE','GIT_TERMINAL_PROMPT','GIT_OPTIONAL_LOCKS','GIT_CONFIG_GLOBAL','LEAN_NUM_THREADS']},'resource_units':'ru_maxrss is bytes on macOS and KiB on Linux; maximum among completed children, not a summed peak.','network':'Only public pinned dependencies/cache; no private source dependency.','cache_policy':'Pinned external Mathlib/dependency caches may be reused. Project .lake/build must be absent for release clean-build evidence; ordinary smoke rechecks may retain it.'}
 (out/'ENVIRONMENT.json').write_text(json.dumps(identity,indent=2)+'\n')
 run('source-integrity-before',['python3','reproducibility/scripts/audit_source_manifest.py'])
 run('confidentiality-before',['python3','reproducibility/scripts/scan_prohibited_files.py'])
 run('source-token-scan',['python3','reproducibility/scripts/check_source_tokens.py'])
 run('lean-version',['lake','env','lean','--version'],LEAN)
 if not (LEAN/'.lake/packages/mathlib/.lake/build').exists():run('public-dependency-cache',['lake','exe','cache','get'],LEAN,1800)
 run('dependency-pins-before',['python3','reproducibility/scripts/check_pins.py'])
 allmodules=json.loads((BASE/'manifests/ALL-MODULES.json').read_text())['modules']
 if a.all:
  for key,prefix in [('1d','BanachDensity1D'),('hd','BanachDensityHD')]:
   modules=[m for m in allmodules if m.startswith(prefix)]
   run('full-'+key+'-build',['lake','build',*modules],LEAN)
  run('standalone-bridge-build',['lake','build','TriangularSchedule'],LEAN)
  query=run('complete-paper-registry',['lake','env','lean','../verification/PaperRegistry.lean'],LEAN)
  run('registry-coverage',['python3','reproducibility/scripts/check_registry.py',os.path.relpath(query,ROOT)])
  content=run('elaborated-content-identity',['lake','env','lean','../verification/ContentIdentity.lean'],LEAN)
  run('elaborated-content-comparison',['python3','reproducibility/scripts/check_content_identity.py',os.path.relpath(content,ROOT)])
  run('all-module-transitive-axioms',['lake','env','lean','../verification/AllModuleAxiomsComplete.lean'],LEAN)
  for key,name in [('1d','1D'),('hd','HD')]:
   raw=run('frozen-'+key,['lake','env','lean','../verification/Frozen'+name+'.lean'],LEAN)
   run('frozen-'+key+'-comparison',['python3','reproducibility/scripts/check_fingerprints.py',key,os.path.relpath(raw,ROOT)])
  run('whole-project-kernel-replay',['lake','env','lean','../verification/ReplayComplete.lean'],LEAN,3600)
 else:
  run('smoke-build',['lake','build','BanachDensity1D','BanachDensityHD','BanachDensityHD.ExactStatements'],LEAN)
 assert hashlib.sha256((BASE/'manifests/SOURCE-SHA256SUMS').read_bytes()).hexdigest()==identity['source_manifest_sha256'], 'Source manifest changed during verification'
 run('dependency-pins-after',['python3','reproducibility/scripts/check_pins.py'])
 run('source-integrity-after',['python3','reproducibility/scripts/audit_source_manifest.py'])
 status='PASS'
except Exception as e:
 status='NOT VERIFIED';print(str(e),file=sys.stderr,flush=True)
finally:
 (out/'RESULT.json').write_text(json.dumps({'status':status,'mode':'all' if a.all else 'fast','checks':records,'evidence_directory_name':out.name},indent=2)+'\n')
print('RESULT: '+status,flush=True)
sys.exit(0 if status=='PASS' else 1)
