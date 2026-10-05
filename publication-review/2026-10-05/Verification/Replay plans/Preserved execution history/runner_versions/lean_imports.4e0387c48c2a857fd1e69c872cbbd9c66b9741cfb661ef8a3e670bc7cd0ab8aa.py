"""Read header imports while ignoring nested Lean comments and string contents."""
from pathlib import Path
import re
def stripped(text):
 out=[];i=0;depth=0;line_comment=False;quoted=False
 while i<len(text):
  pair=text[i:i+2];c=text[i]
  if line_comment:
   if c=='\n':line_comment=False;out.append(c)
   else:out.append(' ')
   i+=1;continue
  if depth:
   if pair=='/-':depth+=1;out.extend('  ');i+=2;continue
   if pair=='-/':depth-=1;out.extend('  ');i+=2;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if quoted:
   if c=='\\':out.extend('  ');i+=2;continue
   if c=='"':quoted=False
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if pair=='--':line_comment=True;out.extend('  ');i+=2;continue
  if pair=='/-':depth=1;out.extend('  ');i+=2;continue
  if c=='"':quoted=True;out.append(' ');i+=1;continue
  out.append(c);i+=1
 return ''.join(out)
def read_imports(file):
 text=stripped(Path(file).read_text(encoding='utf8'))
 return [name.replace('«','').replace('»','')
  for line in text.splitlines() if re.match(r'^\s*(public\s+)?(meta\s+)?import\s',line)
  for name in re.sub(r'^\s*(public\s+)?(meta\s+)?import\s+','',line).split()]
