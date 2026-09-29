from pathlib import Path
exec(Path(__file__).with_name('term3-explore.py').read_text().split('ns=[Z]')[0])
f=lambda x:P(Z,x)
g=lambda x:P(x)
h=lambda x:P(c=x)
f1=lambda x:P(ONE,x)
q=g(ONE)
targets={}
r=q
for n in range(8):
 targets[h(r)]=n
 r=f(h(r))
ns=[Z]
for i in range(3):ns.append(P(d=ns[-1]))
root=h(f1(q))
todo=deque([(root,())])
seen=set()
found=set()
while todo and len(seen)<300000:
 s,path=todo.popleft()
 if s in seen:continue
 seen.add(s)
 if s in targets:
  n=targets[s];found.add(n)
  print('FOUND',n,path,flush=True)
 if len(found)==len(targets):break
 if sz(s)>40 or len(path)>30:continue
 for n,t in enumerate(ns):
  r=fund(s,t)
  todo.append((r,path+(n,)))
 if len(seen)%10000==0:print('visited',len(seen),'pending',len(todo),flush=True)
print('done',len(seen),'pending',len(todo),flush=True)
