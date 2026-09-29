from functools import lru_cache
from collections import deque
Z=()
def P(a=Z,b=Z,c=Z,d=Z):return(a,b,c,d)
ONE=P()
@lru_cache(None)
def dom(s):
 if not s:return (0,)
 a,b,c,d=s
 if d:return dom(d)
 dc=dom(c)
 if dc[0]==0:
  db=dom(b)
  if db[0]==0:
   da=dom(a)
   return (1,) if da[0]==0 else (3,a,Z) if da[0]==1 else da
  if db[0]==1:return(3,a,b)
  if db[0]==2:return db
  return (2,) if P(a,b)<P(db[1],db[2]) else db
 if dc[0] in (1,2):return(2,)
 return (2,) if P(a,b,c)<P(dc[1],dc[2]) else dc
def add(s,t):
 if not s:return t
 if not t:return s
 a,b,c,d=s
 return P(a,b,c,add(d,t))
def iterate(f,t):
 if not t:return Z
 return f(iterate(f,t[3]))
@lru_cache(None)
def fund(s,t):
 if not s:return Z
 a,b,c,d=s
 if d:return P(a,b,c,fund(d,t))
 dc=dom(c)
 if dc[0]==0:
  db=dom(b)
  if db[0]==0:
   da=dom(a)
   if da[0]==0:return Z
   if da[0]==1:return t
   return P(fund(a,t))
  if db[0]==1:return t
  if db[0]==2:return P(a,fund(b,t))
  if P(a,b)>=P(db[1],db[2]):return P(a,fund(b,t))
  l0,l1=db[1:]
  if dom(l1)[0]==1:F=lambda x:P(l0,fund(l1,Z),fund(b,x))
  else:F=lambda x:P(fund(l0,Z),fund(b,x))
  return P(a,fund(b,iterate(F,t)))
 if dc[0]==1:return iterate(lambda x:add(x,P(a,b,fund(c,Z))),t)
 if dc[0]==2:return P(a,b,fund(c,t))
 if P(a,b,c)>=P(dc[1],dc[2]):return P(a,b,fund(c,t))
 l0,l1=dc[1:]
 if dom(l1)[0]==1:F=lambda x:P(l0,fund(l1,Z),fund(c,x))
 else:F=lambda x:P(fund(l0,Z),fund(c,x))
 return P(a,b,fund(c,iterate(F,t)))
@lru_cache(None)
def enc(s):
 if not s:return Z
 a,b,c,d=s
 return((enc(a),enc(b),Z),enc(c),enc(d))
@lru_cache(None)
def G(u,s):
 if not s:return ()
 a,b,c=s
 if u<=a:return (b,)+G(u,a)+G(u,b)+G(u,c)
 return G(u,c)
@lru_cache(None)
def nf(s):
 if not s:return True
 a,b,c=s
 return nf(a) and nf(b) and nf(c) and all(x<b for x in G(a,b)) and (not c or (c[0],c[1],Z)<= (a,b,Z))
@lru_cache(None)
def sz(s):return 0 if not s else 1+sum(sz(a) for a in s)
def show(s):return '0' if not s else 'P('+','.join(map(show,s))+')'
ns=[Z]
for i in range(4):ns.append(P(d=ns[-1]))
ls=[Z]
for i in range(4):ls.append(P(ls[-1]))
todo=deque((P(c=l),(i,)) for i,l in enumerate(ls))
seen=set()
while todo and len(seen)<100000:
 s,path=todo.popleft()
 if s in seen:continue
 seen.add(s)
 if not nf(enc(s)):
  print('ENCODING FAILURE',path,'size',sz(s),show(s),flush=True)
  break
 if sz(s)>200 or len(path)>20:continue
 for n,t in enumerate(ns):
  r=fund(s,t)
  if s and not r<s:print('DESCENT FAILURE',path,n,show(s),show(r),flush=True);raise SystemExit
  todo.append((r,path+(n,)))
else:print('PASS',len(seen),'remaining',len(todo),flush=True)
print('visited',len(seen),flush=True)
