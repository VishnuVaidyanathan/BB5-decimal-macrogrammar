"""Checks for the halting induction (see bb7_halting_induction.tex).

The ladder functions:
    G_1(P) = 3P + 6
    G_j(P) = G_{j-1} applied (3P + 8 - 2j)/2 times to p_{j-1}          (j >= 2)
    p_1 = 2,   p_k = G_{k-1}(p_{k-1})
Consume lemma A_j:  (P | (2j, Z), (g, X), T)  ->  (G_j^(Z/2)(P) | (g + 2j, X), T)   for even P, even Z.

Test 1: A_j against the exact rule simulator, for every small case that can be computed.
Test 2: the whole chain against the real machine, for small tapes (1 unit).
Test 3: the two numbers of the real run that we can still write down.
"""
import sys
sys.set_int_max_str_digits(0)
def G(j,P,limit=10**6):
    if j==1: return 3*P+6
    n=(3*P+8-2*j)//2
    assert n>=3 and n<=limit, 'too big'
    x=p(j-1)
    for _ in range(n): x=G(j-1,x,limit)
    return x
_p={1:2}
def p(k):
    if k not in _p: _p[k]=G(k-1,p(k-1))
    return _p[k]
# exact rule simulator (the same rules as bb7_grammar.move, with runs of triplings done at once)
def run_rules(P,rest,stop_len=None,maxmoves=10**6):
    steps=0; moves=0
    while True:
        if stop_len is not None and len(rest)==stop_len and moves>0 and rest[0][1]==stop_X: return P,rest,steps
        (g,Z),tail=rest[0],rest[1:]; j=g//2; m=3*P+3-2*j
        assert g%2==0 and m>=1, 'outside the rules'
        if Z==1:
            assert not tail and P%2==0, 'outside the rules'
            return 'HALT',P,j
        moves+=1; assert moves<maxmoves
        N=3*P+8-2*j
        new=[(2,2)]*(j-2)+([(2,N)] if j>=2 else [])
        if Z>2: new+=[(2,Z-2)]+tail
        else:
            assert tail, 'outside the rules'
            new+=[(2+tail[0][0],tail[0][1])]+tail[1:]
        P,rest=(2 if j>=2 else N),new
def consume(j,P,Z):
    """run (P | (2j,Z), (2,1)) with the rules until the marker (.,1) is the only counter left"""
    rest=[(2*j,Z),(2,1)]; moves=0
    while not (len(rest)==1 and rest[0][1]==1):
        (g,Zc),tail=rest[0],rest[1:]; jj=g//2; assert 3*P+3-2*jj>=1
        N=3*P+8-2*jj; new=[(2,2)]*(jj-2)+([(2,N)] if jj>=2 else [])
        if Zc>2: new+=[(2,Zc-2)]+tail
        else: new+=[(2+tail[0][0],tail[0][1])]+tail[1:]
        P,rest=(2 if jj>=2 else N),new; moves+=1
        if moves>3*10**5: return None
    return P,rest[0][0]
print('Test 1: consume lemma A_j against the rules')
n=0
for j,P,Z in [(1,2,2),(1,2,8),(1,16,6),(1,40,20),(2,2,2),(2,4,2),(2,16,2),(2,2,4),(2,4,4),(2,6,2)]:
    r=consume(j,P,Z); want=P
    for _ in range(Z//2): want=G(j,want)
    ok=(r==(want,2+2*j)); n+=ok
    print('   j=%d P=%-3d Z=%-3d : rules give P with %d digits, gap %d ; formula agrees: %s'%(j,P,Z,len(str(r[0])),r[1],ok))
print('  ',n,'of 10 agree')

print('Test 2: one unit, against the real machine   tape = 1 0 [G] 0 1^P 0000 11 00 1')
import bb7_grammar as g, subprocess, os
exe='/tmp/run_tape'
if not os.path.exists(exe): subprocess.run(['gcc','-O2','-o',exe,os.path.join(os.path.dirname(os.path.abspath(__file__)),'run_tape.c')],check=True)
def wlen(P,j): return 3*P*P+27*P+44+2*j+(2*j-1)*(6*P+14-2*j)
def hlen(P,j):                      # length of the halt word, by the same pieces as bb7_grammar.H
    m=3*P+3-2*j
    head=9+sum(2*(3*i+1)+7 for i in range(1,P+1))+4+(3*P+4)+sum(3+k+4+k+1 for k in range(3*P+2,3*P+3-2*j,-1))
    return head+3+m+(2*(m+1)+7)+4+(m+5)+sum(3+k+4+k+1 for k in range(m+3,-1,-1))+9+10*((m+3)//2)+6
assert all(wlen(P,j)==len(g.W(P,j)) and hlen(P,j)==len(g.H(P,j)) for P in (2,4,12,40) for j in (1,2,3,5) if 3*P+3-2*j>=1)
for P0 in (2,4):
    t,ones=map(int,subprocess.run([exe,str(P0),'1'],capture_output=True,text=True).stdout.split())
    Pend=G(2,P0); N=3*P0+4
    pred=wlen(P0,2); x=2
    for _ in range(N//2): pred+=wlen(x,1); x=3*x+6
    pred+=hlen(x,3)
    print('   P0=%d : machine halts at step %d ; predicted %d ; final P = G_2(P0) = %d : %s'%(P0,t,pred,Pend,(t==pred and x==Pend)))

print('Test 3: the real run')
Q1=G(2,16); print('   Q1 = G_2(16) =',Q1,'  (macro run: 12709329141642)',Q1==12709329141642)
print('   counter made by the second unit = 3*Q1 + 2 =',3*Q1+2,'  (macro run: 38127987424928)',3*Q1+2==38127987424928)
print('   p_2 =',p(2),'  p_3 = 5*3^20 - 3 :',p(3)==5*3**20-3)
