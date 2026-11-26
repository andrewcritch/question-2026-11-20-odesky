from pathlib import Path
import re
p=Path('answer.md');s=p.read_text()
s=s.replace('\t',r'\t').replace('\b',r'\b')
def fix_math(x):
    for macro in ['theta','mu','delta','eta','beta','alpha','sum','Sigma','sqrt','Theta','sigma','log','min']:
        x=re.sub(r'(?<![\\A-Za-z])'+macro+r'(?![A-Za-z])',lambda m:'\\'+m.group(),x)
    return '$'+x+'$'
def inline(text):
    out=[];i=0
    while i<len(text):
        if text[i]!='(':
            out.append(text[i]);i+=1;continue
        j=i+1;depth=1
        while j<len(text) and depth:
            depth+=(text[j]=='(')-(text[j]==')');j+=1
        if depth:
            out.append(text[i:]);break
        x=text[i+1:j-1]
        out.append(text[i:j] if x in ['1','2'] else fix_math(x));i=j
    return ''.join(out)
lines=[];display=False;code=False;tick=chr(96)
for line in s.splitlines():
    if line.lstrip().startswith(tick*3):
        code=not code;lines.append(line);continue
    if code:lines.append(line);continue
    if line.strip()==r'\[':
        display=True;lines.append(line);continue
    if display:
        if line.strip()==r'\]':display=False
        lines.append(line);continue
    pieces=re.split('('+tick+'[^'+tick+']*'+tick+')',line)
    lines.append(''.join(piece if i%2 else inline(piece) for i,piece in enumerate(pieces)))
p.write_text('\n'.join(lines)+'\n')
