# Independent check of a gate: start at the door (solid block 1^Q, door state, given offset from right end),
# run until the door comes back (print new Q) or the machine stops at an empty wire / halt.
import sys
from t2 import parse
def door_map(tm, door, off, Q, lim=50_000_000):
    T=parse(tm); ds=ord(door[0])-65; dsym=int(door[1])
    tape=set(range(Q)); pos=Q-1+off; st=ds; t=0
    while t<lim:
        b=1 if pos in tape else 0
        if t>0 and st==ds and b==dsym and tape and pos==max(tape)+off and len(tape)==max(tape)-min(tape)+1:
            return ('door',len(tape),t)
        if (st,b) not in T or st==7: return ('stop','ABCDEFGZ'[st]+str(b),t,len(tape))
        w,m,nx=T[(st,b)]
        if w: tape.add(pos)
        else: tape.discard(pos)
        pos+=m; st=nx; t+=1
    return ('limit',)
if __name__=='__main__':
    tm,door,off=sys.argv[1],sys.argv[2],int(sys.argv[3])
    for Q in range(int(sys.argv[4]),int(sys.argv[5])+1): print(Q,door_map(tm,door,off,Q))
