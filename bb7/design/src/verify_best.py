# Checks for the best design found so far (run from a blank tape, start state G).
from t2 import parse
from door import door_map
from fractions import Fraction as F
TM="1RA1RB_1RD1LC_0LA0LC_1LE1LD_0LA1LF_---0LE_1LB---"; START='G'; DOOR=('E1',-1)
T=parse(TM)
# 1. from a blank tape: when is the tape one solid block with the head at the door?
tape={}; pos=0; st=ord(START)-65; t=0; doors=[]
ds=ord(DOOR[0][0])-65; dsym=int(DOOR[0][1])
while t<400000:
    b=tape.get(pos,0)
    if st==ds and b==dsym:
        ks=[k for k,v in tape.items() if v]
        if ks and pos==max(ks)+DOOR[1] and len(ks)==max(ks)-min(ks)+1 and (not doors or doors[-1][1]!=len(ks)): doors.append((t,len(ks)))
    if (st,b) not in T: print('stopped early',t); break
    w,m,nx=T[(st,b)]; tape[pos]=w; pos+=m; st=nx; t+=1
print('1. doors from blank (step, block):',doors)
# 2. even blocks halt
ev=[(Q,)+door_map(TM,DOOR[0],DOOR[1],Q) for Q in list(range(4,202,2))+[256,1024,2066,4096]]
assert all(r[1]=='stop' for r in ev)
print('2. every even block tested halts. wires:',sorted({r[2] for r in ev}))
print('   steps = Q-1 :',all(r[3]==r[0]-1 for r in ev),'  ones left = Q/2+1 :',all(r[4]==r[0]//2+1 for r in ev), ev[:3])
# 3. odd blocks restart
od=[(Q,)+door_map(TM,DOOR[0],DOOR[1],Q,lim=400_000_000) for Q in range(3,17,2)]
print('3. odd blocks:',[(r[0],r[2]) for r in od])
print('   new block = (17*3^n+1)/2, n=(Q-3)/2 :',all(r[2]==(17*3**((r[0]-3)//2)+1)//2 for r in od))
def solve(A,b):
    n=len(A); M=[[F(x) for x in row]+[F(y)] for row,y in zip(A,b)]
    for i in range(n):
        p=next(r for r in range(i,n) if M[r][i]!=0); M[i],M[p]=M[p],M[i]
        M[i]=[x/M[i][i] for x in M[i]]
        for r in range(n):
            if r!=i: M[r]=[x-M[r][i]*y for x,y in zip(M[r],M[i])]
    return [M[i][n] for i in range(n)]
basis=lambda n:[9**n,3**n,n*3**n,n,1]
ns=[(r[0]-3)//2 for r in od]; stp=[r[3] for r in od]
co=solve([basis(n) for n in ns[:5]],stp[:5])
print('   steps = a*9^n + b*3^n + c*n*3^n + d*n + e with',[str(c) for c in co],' fits the other points:',all(sum(c*x for c,x in zip(co,basis(n)))==s for n,s in zip(ns,stp)))
Tn=lambda n: sum(c*x for c,x in zip(co,basis(n)))
# 4. the chain 13 -> 2066 -> halt, run in full, against the formulas
Q=13; r1=od[5]; assert r1[0]==13
pred=Tn(5)+r1[2]-1
tape=set(range(13)); pos=12+DOOR[1]; st=ds; t=0
while True:
    b=1 if pos in tape else 0
    if (st,b) not in T: break
    w,m,nx=T[(st,b)]
    (tape.add if w else tape.discard)(pos); pos+=m; st=nx; t+=1
print('4. full run from block 13: halts at',t,' predicted',pred,' ones',len(tape),' predicted',r1[2]//2+1)
# 5. the real run: blank -> 11 -> 689 -> big -> halt
t689=[d for d in doors if d[1]==689][0][0]
n=(689-3)//2; big=(17*3**n+1)//2
total=t689+Tn(n)+big-1
print('5. block after the restart from 689:',big)
print('   it is even:',big%2==0)
print('   predicted halting step:',total)
print('   digits:',len(str(total)),'  ones left:',big//2+1,' digits:',len(str(big//2+1)))
