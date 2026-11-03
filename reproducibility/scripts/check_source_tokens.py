"""Nested-comment/string-aware source audit; stronger axiom/replay checks separate."""
from pathlib import Path
import re,json
BASE=Path(__file__).resolve().parents[1]
def strip(s):
 out=list(s);i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):out[i:i+2]='  ';depth+=1;i+=2
   elif s.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
   else:
    if s[i]!='\n':out[i]=' '
    i+=1
  elif string:
   if s[i]=='\\' and i+1<len(s):out[i]=' ';out[i+1]=' ' if s[i+1]!='\n' else '\n';i+=2
   else:
    if s[i]=='"':string=False
    if s[i]!='\n':out[i]=' '
    i+=1
  elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i)
   if j<0:j=len(s)
   out[i:j]=' '*(j-i);i=j
  elif s[i]=='"':string=True;out[i]=' ';i+=1
  else:i+=1
 assert depth==0 and not string
 return ''.join(out)
files=[];hits=[]
for p in sorted((BASE/'lean').rglob('*.lean')):
 if '.lake' in p.parts:continue
 files.append(p);code=strip(p.read_text())
 for m in re.finditer(r"\b(sorry|admit|sorryAx|axiom|unsafe|opaque)\b",code):
  hits.append({'path':p.relative_to(BASE).as_posix(),'token':m.group(),'line':code.count('\n',0,m.start())+1})
assert not hits,hits
print(json.dumps({'status':'PASS','files':len(files),'prohibited_tokens':hits,'note':'Compiler-generated unsafe recursion artifacts are checked separately by kernel replay; checker diagnostic IO is not mathematical source.'}))
