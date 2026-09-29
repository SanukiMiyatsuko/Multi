from pathlib import Path
exec(Path(__file__).with_name('term3-explore.py').read_text().split('ns=[Z]')[0])

@lru_cache(None)
def higher_support(u,s):
 if not s:return ()
 a,b,c,d=s
 if u<=a:return (b,)+higher_support(u,a)+higher_support(u,b)+higher_support(u,d)
 return higher_support(u,d)
@lru_cache(None)
def lower_support(u,v,s):
 if not s:return ()
 a,b,c,d=s
 if (u,v)<=(a,b):return (b,c)+lower_support(u,v,a)+lower_support(u,v,b)+lower_support(u,v,c)+lower_support(u,v,d)
 return lower_support(u,v,d)
@lru_cache(None)
def normal(s):
 if not s:return True
 a,b,c,d=s
 return all(normal(x) for x in s) and all(x<b for x in higher_support(a,b)) and all(x<c for x in lower_support(a,b,c)) and (not d or P(*d[:3])<=P(a,b,c))
def diagnose(s):
 if not s:return
 a,b,c,d=s
 for x in s:
  if not normal(x):diagnose(x);return
 print('localfailure',show(s),flush=True)
 print('higher',list(map(show,higher_support(a,b))),flush=True)
 print('lower',list(map(show,lower_support(a,b,c))),flush=True)

ns=[Z]
for i in range(4):ns.append(P(d=ns[-1]))
ls=[Z]
for i in range(4):ls.append(P(ls[-1]))
todo=deque((P(c=l),(i,)) for i,l in enumerate(ls))
seen=set()
while todo and len(seen)<15000:
 s,path=todo.popleft()
 if s in seen:continue
 seen.add(s)
 if not normal(s):
  print('NORMALITY FAILURE',path,'size',sz(s),show(s),flush=True)
  diagnose(s)
  break
 if sz(s)>100 or len(path)>12:continue
 for n,t in enumerate(ns):
  r=fund(s,t)
  if s and not r<s:print('DESCENT FAILURE',path,n,show(s),show(r),flush=True);raise SystemExit
  todo.append((r,path+(n,)))
else:print('PASS',len(seen),'remaining',len(todo),flush=True)
print('visited',len(seen),flush=True)
