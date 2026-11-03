"""Comment erasure for the fixed release grammar; fail closed on unsupported interpolation.

All literal text and every byte outside comments are retained. Newlines inside
comments are retained, so layout-sensitive Lean code and source line numbers
are also compared. This is stronger than merely comparing token spellings.
"""
import re

def comment_spans(s):
    spans=[];i=0
    while i<len(s):
        if s.startswith('/-',i):
            start=i;depth=1;i+=2
            while depth:
                assert i<len(s),'unterminated block comment'
                if s.startswith('/-',i):depth+=1;i+=2
                elif s.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            spans.append((start,i,'block'));continue
        if s.startswith('--',i):
            end=s.find('\n',i)
            if end<0:end=len(s)
            spans.append((i,end,'line'));i=end;continue
        if s[i]=='«':
            end=s.find('»',i+1);assert end>=0,'unterminated quoted identifier';i=end+1;continue
        if s[i]=='r' and (i==0 or not (s[i-1].isalnum() or s[i-1] in "_'")):
            m=re.match(r'r(#+)?"',s[i:])
            if m:
                closing='"'+(m.group(1) or '');end=s.find(closing,i+m.end());assert end>=0,'unterminated raw string';i=end+len(closing);continue
        if s[i]=='"':
            assert i==0 or s[i-1]!='!','unsupported interpolated string: require independent lexer extension before use'
            i+=1
            while True:
                assert i<len(s),'unterminated string'
                if s[i]=='\\':i+=2
                elif s[i]=='"':i+=1;break
                else:i+=1
            continue
        if s[i]=="'" and (i==0 or not (s[i-1].isalnum() or s[i-1] in "_'")):
            m=re.match(r"'(?:[^\\'\n]|\\(?:[\\'\"rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'",s[i:])
            if m:i+=m.end();continue
        i+=1
    return spans

def projection(s):
    out=[];start=0
    for a,b,_ in comment_spans(s):
        out.extend([s[start:a],' ','\n'*s[a:b].count('\n')]);start=b
    out.append(s[start:]);return ''.join(out).encode('utf-8')

def self_test():
    examples=[('def x := 1 /- nested /- metadata -/ comment -/ + 2 -- tail\n','def x := 1 /- safe -/ + 2 -- changed\n'),
              ('def x := "/- visible -- literal -/"\n','def x := "/- visible -- literal -/"\n'),
              ('def x := r#"/- literal -/"#\n','def x := r#"/- literal -/"#\n'),
              ("def x := '-' -- private\n","def x := '-' -- public\n"),
              ('def «/- name -/» := 1\n','def «/- name -/» := 1\n')]
    for before,after in examples:assert projection(before)==projection(after)
    for before,after in [('def x := 1 /- c -/','def x := 2 /- c -/'),('def x := "secret"','def x := "other"')]:assert projection(before)!=projection(after)
    try:projection('def x := s!"{f "/- not comment -/"}"')
    except AssertionError:pass
    else:raise AssertionError('unsupported grammar must fail closed')
