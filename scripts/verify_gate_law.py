"""Independent check of BB5 layer data, the ones law, and the gate law.
Machine: 1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA  (Marxen-Buntrock)
Digit = 2*state_index + symbol read.  Everything below is read from the
trace itself, not from the paper's table."""
import re
from array import array
T={('A',0):(1,1,'B'),('A',1):(1,-1,'C'),('B',0):(1,1,'C'),('B',1):(1,1,'B'),
   ('C',0):(1,1,'D'),('C',1):(0,-1,'E'),('D',0):(1,-1,'A'),('D',1):(1,-1,'D'),
   ('E',0):(1,1,'Z'),('E',1):(0,-1,'A')}
I={'A':0,'B':1,'C':2,'D':3,'E':4}
tape=bytearray(40000);pos=20000;st='A';ones=0
tr=bytearray();on=array('I')
while st!='Z':
    s=tape[pos];tr.append(48+2*I[st]+s);on.append(ones)
    w,d,n=T[(st,s)];ones+=w-s;tape[pos]=w;pos+=d;st=n
final=ones;t=tr.decode()
print('steps',len(t),'final ones',final)

blocks=[(m.start(),m.end(),(m.end()-m.start())//3) for m in re.finditer(r'(?:159)+',t)]
# keep only real oscillator blocks (the paper's): those followed by a gate or the halt
layers=[]
for k,(a,b,M) in enumerate(blocks):
    nxt=t[b:b+8]
    g=1 if nxt.startswith('02477776') else 2 if nxt.startswith('14776') else None
    halt=t[b:].startswith('158') and b+3==len(t)
    if g or halt: layers.append(dict(start=a,end=b,M=M,g=g if g else 'HALT'))
print('layers found',len(layers))

ok_all=True
for n,L in enumerate(layers):
    before=on[L['start']]; after=on[L['end']] if L['end']<len(on) else final
    L['before'],L['after']=before,after
    if L['g']!='HALT':
        seg=t[L['end']:layers[n+1]['start']]
        rungs=[(len(a),len(b)) for a,b in re.findall(r'4(7+)60(3+)2',seg)]
        L['rungs']=len(rungs); L['K']=rungs[-1][0]
        L['coupling']=all(b==a+1 for a,b in rungs[:-1]) and rungs[-1][1]==rungs[-1][0]+2

print(f"{'L':>2} {'M':>5} {'gate':>4} {'before':>6} {'3M+g':>6} {'after':>6} {'M+g':>6} {'K+2':>6} {'mod3':>4} {'next':>4} {'mine':>4} {'paper':>5} {'Mnext':>6} {'rec':>4} {'rungs':>5} {'B=A+1/+2':>8}")
for n,L in enumerate(layers):
    g=L['g']; gv=3 if g=='HALT' else g
    line=f"{n+1:>2} {L['M']:>5} {str(g):>4} {L['before']:>6} {3*L['M']+gv:>6} {L['after']:>6} {L['M']+gv:>6}"
    if g!='HALT':
        r=(L['K']+2)%3; nx=layers[n+1]['g']
        mine={0:1,1:2,2:'HALT'}[r]; paper={1:1,2:2}.get(r,'?')
        rec=(L['K']+2)//3+1
        line+=f" {L['K']+2:>6} {r:>4} {str(nx):>4} {('ok' if mine==nx else 'NO'):>4} {('ok' if paper==nx else 'NO'):>5} {rec:>6} {('ok' if rec==layers[n+1]['M'] else 'NO'):>4} {L['rungs']:>5} {str(L['coupling']):>8}"
    print(line)
# note: last layer's "after" includes the final 158 and the halt step
