# Closure of the champion's transcript grammar, by shapes.
# Shape = (lower bound on P, list of (gap, counter)), counter in {1, 2, 'M'} where M = even and >= 4.
# Facts used (all follow from the rules): after the one restart P is always even; every counter except the
# final 1 is even; the rules only ask: gap, counter = 1 / 2 / more, P even or odd, and 3P+8-2j >= 6.
import sys
from collections import deque, Counter
CAP=200
def up(lb): return min(CAP,3*lb+6)
def step(lb,rest):
    (g,Z),tail=rest[0],rest[1:]; j=g//2
    if g%2: return 'OUT odd gap',[]
    if 3*lb+8-2*j<6 and lb<CAP: return 'OUT gap too wide: P>=%d j=%d'%(lb,j),[]
    if Z==1:
        return ('HALT j=%d'%j,[]) if not tail else ('OUT odd counter in the middle',[])
    if j==1 and Z=='M': return 'TRIPLES',[(up(lb),((2,2),)+tail)]
    new=((2,2),)*(j-2)+(((2,'M'),) if j>=2 else ())
    nlb=2 if j>=2 else min(CAP,3*lb+8-2*j)
    lab=('SWAP j=%d'%j) if j>=2 else 'TRIPLE'
    if Z==2:
        if not tail: return 'OUT last counter 2, nothing behind',[]
        return lab,[(nlb,new+((2+tail[0][0],tail[0][1]),)+tail[1:])]
    return lab,[(nlb,new+((2,'M'),)+tail),(nlb,new+((2,2),)+tail)]     # counter stays big, or is now down to 2
def explore(units,limit):
    start=(16,((4,2),)+((2,2),)*(units-1)+((2,1),))
    seen={start}; q=deque([start]); used=Counter(); outs=Counter(); halts=Counter(); maxj=0
    while q:
        lb,rest=q.popleft(); lab,nxt=step(lb,rest)
        if lab.startswith('OUT'): outs[lab]+=1; continue
        if lab.startswith('HALT'): halts[lab]+=1; continue
        if 'j=' in lab: maxj=max(maxj,int(lab.split('=')[1]))
        used[lab.split(' j')[0]]+=1
        for s in nxt:
            if s not in seen: seen.add(s); q.append(s)
        if len(seen)>limit: return None
    return len(seen),maxj,dict(halts),dict(outs)
print('units  shapes     widest gap j   halts reached         shapes with no rule')
for u in range(1,20):
    r=explore(u,2_500_000)
    if r is None: print('%3d    (more than 2,500,000 shapes - stopped)'%u); break
    print('%3d    %-9d  %-13d  %-20s  %s'%(u,r[0],r[1],r[2],r[3] if r[3] else 'none')); sys.stdout.flush()
