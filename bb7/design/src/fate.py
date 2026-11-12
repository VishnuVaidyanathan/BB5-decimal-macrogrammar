# Work out what each design does after its last observed door, using its measured gate map.
import sys
from collections import Counter
sys.setrecursionlimit(10000)
def fit(m, M):
    cls={}
    for c in range(m):
        qs=[q for q in range(3,15) if q%m==c]; v=[M[q] for q in qs]
        keep=[(q,x) for q,x in zip(qs,v) if x!='?']
        # drop unknown values only at the end of a class
        while v and v[-1]=='?': v=v[:-1]; qs=qs[:-1]
        if any(x=='?' for x in v): return None
        full=[M[q] for q in range(3,15) if q%m==c]
        if not v: cls[c]=('STUCK',); continue
        if all(x=='H' for x in full): cls[c]=('H',); continue
        if any(x=='H' for x in full): return None
        if any(x=='H' for x in v): return None
        if len(v)<3: return None
        d=[v[i+1]-v[i] for i in range(len(v)-1)]
        if all(x==d[0] for x in d):
            cls[c]=('lin',qs[0],v[0],d[0]); continue          # v = v0 + d*(q-q0)/m
        if d[0]==0 or (d[1]%d[0])!=0: return None
        r=d[1]//d[0]; k=v[1]-r*v[0]
        if r<2 or any(v[i+1]!=r*v[i]+k for i in range(len(v)-1)): return None
        cls[c]=('exp',qs[0],v[0],r,k)                           # v_{i+1} = r v_i + k
    return cls
def get_map(M):
    for m in (1,2,3,4):
        c=fit(m,M)
        if c: return m,c
    return None,None
def seq_mod(v0,r,k,n_mod_fn,Mod):
    # value of v_n mod Mod where n is given through n_mod_fn(period) (n assumed large) 
    seen={}; u=v0%Mod; i=0; seq=[]
    while u not in seen: seen[u]=i; seq.append(u); u=(r*u+k)%Mod; i+=1
    mu=seen[u]; lam=i-mu
    return mu,lam,seq
class Tower:   # value = v_n of class recurrence with n=(inner-q0)/m ; inner is int or Tower
    def __init__(s,q0,v0,r,k,m,inner): s.q0,s.v0,s.r,s.k,s.m,s.inner=q0,v0,r,k,m,inner
    def mod(s,Mod):
        mu,lam,seq=seq_mod(s.v0,s.r,s.k,None,Mod)
        inner_mod = s.inner % (s.m*lam) if isinstance(s.inner,int) else s.inner.mod(s.m*lam)
        n_mod=((inner_mod - s.q0)//s.m) % lam      # inner ≡ q0 (mod m)
        # n is huge (>= mu): pick representative >= mu
        n=n_mod
        while n<mu: n+=lam
        return seq[mu+((n-mu)%lam)]
def vmod(x,Mod): return x%Mod if isinstance(x,int) else x.mod(Mod)
def fate(m,cls,q):
    h=0; lin_steps=0; first_big=None
    for it in range(400):
        c=vmod(q,m); t=cls[c]
        if t[0]=='H': return ('HALT',h,first_big)
        if t[0]=='STUCK': return ('no return seen (likely forever)',h,first_big)
        if t[0]=='lin':
            _,q0,v0,d=t
            if not isinstance(q,int): 
                if d!=m: return ('lin-on-tower',h,first_big)
                # shift by (v0-q0): just changes class
                sh=v0-q0
                q=ShiftT(q,sh); lin_steps+=1
                if lin_steps>12: return ('FOREVER-linear',h,first_big)
                continue
            q=v0+d*(q-q0)//m; lin_steps+=1
            if lin_steps>300 or q>10**7: return ('FOREVER-linear',h,first_big)
            continue
        _,q0,v0,r,k=t
        h+=1
        if h>6: return ('FOREVER-or-tall',h,first_big)
        if isinstance(q,int) and (q-q0)//m<=4000:
            n=(q-q0)//m; v=v0
            for _ in range(n): v=r*v+k
            if first_big is None: first_big=len(str(v))
            q=v
        else:
            q=Tower(q0,v0,r,k,m,q)
        lin_steps=0
    return ('unclear',h,first_big)
class ShiftT:
    def __init__(s,base,sh): s.base,s.sh=base,sh
    def mod(s,Mod): return (vmod(s.base,Mod)+s.sh)%Mod
res=Counter(); best=[]
for f in sys.argv[1:]:
    for line in open(f):
        try:
            left,mp=line.split('| map:'); a=left.split(); st,tm=a[0],a[1]
            nq=int(a[4].split('=')[1].rstrip(':')); qs=[int(x) for x in a[5:]]
            M={3+i:(x if x in 'H?' else int(x)) for i,x in enumerate(mp.split())}
        except Exception: res['parse']+=1; continue
        if len(M)<12: continue
        if nq==0: res['no door reached in 1.5M steps']+=1; continue
        m,cls=get_map(M)
        if m is None: res['gate map not simple']+=1; continue
        if nq>len(qs): 
            res['door hit >40 times (slow linear)']+=1; continue
        try: out=fate(m,cls,qs[-1])
        except Exception as e: res['error']+=1; continue
        res[(out[0],out[1])]+=1
        if out[0]=='HALT' and out[1]>=1: best.append((out[1],out[2] or 0,st,tm,qs,m,cls))
print(res)
best.sort(key=lambda x:(-x[0],-x[1]))
for b in best[:400]: print('height',b[0],'digits of first big block',b[1],'start',b[2],b[3],'doors',b[4][-6:],'mod',b[5],b[6])
print(len(best),'predicted to halt after >=1 big restart')
