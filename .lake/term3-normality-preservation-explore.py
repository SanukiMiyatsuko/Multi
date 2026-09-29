from pathlib import Path
exec(Path(__file__).with_name('term3-normality-explore.py').read_text().split('\nns=[Z]')[0])
from itertools import product
levels=[[Z]]
for n in range(1,7):
 terms=[]
 for i in range(n):
  for j in range(n-i):
   for k in range(n-i-j):
    l=n-1-i-j-k
    for a,b,c,d in product(levels[i],levels[j],levels[k],levels[l]):
     s=P(a,b,c,d)
     if normal(s):terms.append(s)
 levels.append(terms)
 print('level',n,len(terms),flush=True)
ns=[Z]
for i in range(3):ns.append(P(d=ns[-1]))
checked=0
for layer in levels:
 for s in layer:
  values=[]
  for n,t in enumerate(ns):
   r=fund(s,t)
   if not normal(r):
    print('PRESERVATION FAILURE',show(s),'n',n,'result',show(r),flush=True)
    diagnose(r)
    raise SystemExit
   values.append(r)
  for n in range(3):
   if values[n]>values[n+1]:
    print('MONOTONICITY FAILURE',show(s),'n',n,flush=True)
    raise SystemExit
  checked+=1
print('PASS',checked,flush=True)
