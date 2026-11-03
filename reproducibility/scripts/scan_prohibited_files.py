"""Fail closed on release files, PDF objects, and every reachable new Git commit.

No inherited-disclosure exception is permitted. Local build/venv caches are not
release files; a tracked file is always scanned, even under a cache directory.
PDF checks use both Poppler and a separately pinned object parser.
"""
from pathlib import Path
from io import BytesIO
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
from pypdf.generic import IndirectObject,DictionaryObject,ArrayObject,StreamObject,TextStringObject,ByteStringObject
ROOT=Path(__file__).resolve().parents[2]
PDFS={'reports/author/Verification-Report.pdf','reports/daniel-zhou/K-REPORT-Nov1.pdf'}
IGNORED={'.git','.lake','.runs','.venv','__pycache__'}
RULES={
 'personal_home_path':rb'/(?:Users|home)/[A-Za-z0-9_.-]+/',
 'private_temp_path':rb'/(?:private/)?(?:var/folders|tmp)/[A-Za-z0-9_.-]+/',
 'credential':rb'(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|-----BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY-----|AKIA[0-9A-Z]{16})',
 'email':rb'\b[A-Za-z0-9_.+-]+@[A-Za-z0-9.-]+\.(?:edu|com|org|net|io)\b',
 'manuscript_source':rb'\\(?:documentclass|begin\{document\})',
}
findings=[];seen=set();pdf_details=[]
def git(*args,binary=False):
 return subprocess.check_output(['git',*args],cwd=ROOT,text=not binary)
def check_bytes(label,data):
 # Include UTF-16 strings in binary files; do not print matched private data.
 views=[data]
 for encoding in ['utf-16-le','utf-16-be']:
  try:views.append(data.decode(encoding,errors='ignore').encode())
  except UnicodeError:pass
 for kind,pattern in RULES.items():
  for view in views:
   for m in re.finditer(pattern,view):
    value=m.group()
    if kind=='email' and re.fullmatch(rb'[0-9]+\+[A-Za-z0-9-]+@users\.noreply\.github\.com',value):continue
    # Hosted CI's generic runner home is public infrastructure provenance.
    if kind=='personal_home_path' and value==b'/home/runner/':continue
    findings.append({'kind':kind,'location':label,'matched_content':'withheld'});break
   else:continue
   break

def inspect_pdf(label,data):
 reader=PdfReader(BytesIO(data),strict=True)
 assert not reader.is_encrypted, 'ENCRYPTED_PDF '+label
 assert not reader.attachments,'PDF_ATTACHMENTS '+label
 proc=subprocess.run(['pdftotext','-','-'],input=data,capture_output=True)
 assert proc.returncode==0,'PDF_EXTRACTION_FAILED '+label
 check_bytes(label+':poppler-text',proc.stdout)
 visited=set();objects=0;streams=0
 forbidden={'/EmbeddedFiles','/EmbeddedFile','/JavaScript','/JS','/Launch','/AA','/RichMedia','/XFA'}
 def walk(obj):
  nonlocal objects,streams
  if isinstance(obj,IndirectObject):
   key=(obj.idnum,obj.generation)
   if key in visited:return
   visited.add(key);objects+=1;walk(obj.get_object());return
  if isinstance(obj,DictionaryObject):
   assert not (set(obj)&forbidden),'PDF_ACTIVE_OR_EMBEDDED_CONTENT '+label
   if '/OpenAction' in obj:
    # An internal page-view destination is not executable PDF content.
    dest=obj['/OpenAction']
    assert isinstance(dest,ArrayObject) and len(dest)==2 and isinstance(dest[0],IndirectObject) and dest[1]=='/Fit' and dest[0].get_object().get('/Type')=='/Page','PDF_UNSAFE_OPEN_ACTION '+label
   assert obj.get('/Subtype')!='/Image','UNREVIEWED_PDF_IMAGE '+label
   if isinstance(obj,StreamObject):streams+=1;check_bytes(label+':decoded-stream',obj.get_data())
   for k,v in obj.items():check_bytes(label+':object-key',str(k).encode());walk(v)
  elif isinstance(obj,(ArrayObject,list,tuple)):
   for v in obj:walk(v)
  elif isinstance(obj,(TextStringObject,str)):check_bytes(label+':object-string',str(obj).encode())
  elif isinstance(obj,(ByteStringObject,bytes)):check_bytes(label+':object-bytes',bytes(obj))
 # All xref entries, including non-page and currently unreferenced objects.
 for generation,entries in reader.xref.items():
  if generation==65535:continue
  for number in entries:
   if number:walk(IndirectObject(number,generation,reader))
 for number in reader.xref_objStm:walk(IndirectObject(number,0,reader))
 for page in reader.pages:check_bytes(label+':pypdf-text',(page.extract_text() or '').encode())
 pdf_details.append({'file':label,'pages':len(reader.pages),'objects':objects,'decoded_streams':streams,'attachments':0,'metadata_checked':True,'independent_text_extractors':2})

def inspect(path,data):
 key=(path,hashlib.sha256(data).hexdigest())
 if key in seen:return
 seen.add(key)
 parts=Path(path).parts;suffix=Path(path).suffix.lower()
 assert not any(x.lower() in {'paper','manuscript','.ds_store','.env'} for x in parts),'PROHIBITED_PATH '+path
 assert suffix not in {'.tex','.bib','.aux','.png','.jpg','.jpeg','.zip','.tar','.gz','.bundle','.olean','.ilean','.o','.a','.so','.dylib'},'PROHIBITED_FILE '+path
 allowed=path in {'.gitignore','README.md','.github/workflows/lean-reproducibility.yml'} or path.startswith(('reports/','reproducibility/')) and (suffix in {'.md','.py','.sh','.lean','.toml','.json','.yml','.yaml','.stdout','.stderr','.txt'} or path in {'reproducibility/lean/lean-toolchain','reproducibility/manifests/SOURCE-SHA256SUMS'} or path in PDFS)
 assert allowed,'NOT_ALLOWLISTED '+path
 check_bytes(path,data)
 if suffix=='.pdf':assert path in PDFS;inspect_pdf(path,data)

has_git=(ROOT/'.git').exists()
tracked=set(git('ls-files').splitlines()) if has_git else set()
for p in ROOT.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(ROOT);path=rel.as_posix()
 if any(x in IGNORED for x in rel.parts) and path not in tracked:continue
 assert not p.is_symlink(),'SYMLINK_FORBIDDEN '+path
 inspect(path,p.read_bytes())
commits=git('rev-list','--all').splitlines() if has_git else []
if has_git:
 assert (ROOT/'.git').is_dir(),'EXTERNAL_GIT_DIRECTORY'
 for file in ['objects/info/alternates','info/grafts','shallow']:
  assert not (ROOT/'.git'/file).exists(),'IMPORTED_HISTORY_MECHANISM '+file
 assert not git('for-each-ref','--format=%(refname)','refs/replace').strip(),'REPLACE_REFS_FORBIDDEN'
 for commit in commits:
  check_bytes('commit:'+commit,git('show','-s','--format=fuller',commit).encode())
  for field in ['%ae','%ce']:
   assert re.fullmatch(r'[0-9]+\+[A-Za-z0-9-]+@users\.noreply\.github\.com',git('show','-s','--format='+field,commit).strip()),'NON_NOREPLY_COMMIT_EMAIL '+commit
  for row in git('ls-tree','-r',commit).splitlines():
   meta,path=row.split('\t',1);mode,kind,blob=meta.split()
   assert mode in {'100644','100755'} and kind=='blob','SUBMODULE_OR_SYMLINK '+path
   inspect(path,git('cat-file','blob',blob,binary=True))
 for ref in git('for-each-ref','--format=%(refname)').splitlines():check_bytes('ref-name',ref.encode())
 for tag in git('for-each-ref','--format=%(refname)','refs/tags').splitlines():check_bytes('tag-object',git('cat-file','-p',tag,binary=True))
 for item in ROOT.rglob('.git'):
  assert item==ROOT/'.git' or '.lake' in item.parts,'NESTED_REPOSITORY'
assert not findings,json.dumps(findings)
print(json.dumps({'status':'PASS','file_findings':0,'inherited_disclosure_exceptions':0,'distinct_path_content_pairs':len(seen),'reachable_new_commits':len(commits),'pdf_checks':pdf_details,'scope':'All proposed release files and all reachable Git commit trees, metadata, refs and tags; PDF extracted text, raw bytes, metadata, all decoded object streams. Build caches and private operator logs are not release files.'}))
