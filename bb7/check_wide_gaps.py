"""Check the move word W(P,j) and the halt word H(P,j) against the machine, digit for digit,
for every gap width j = 1..21 (the run with 19 units needs gaps up to j = 21)."""
import bb7_grammar as g
tm="1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB"
T={}
for s,part in enumerate(tm.split('_')):
    for b in (0,1):
        p=part[b*3:b*3+3]; T[(s,b)]=(int(p[0]),1 if p[1]=='R' else -1, 7 if p[2]=='Z' else ord(p[2])-65)
D="0123456789abcd"
def transcript(P,j,Z,rest,n):
    cells=[1,0,0]+[1]*P+[0]*(2*j)+[1]*Z+rest
    tape={i:c for i,c in enumerate(cells)}; pos=2; st=6; out=[]
    for _ in range(n):
        if st==7: break
        b=tape.get(pos,0); out.append(D[2*st+b]); w,m,nx=T[(st,b)]; tape[pos]=w; pos+=m; st=nx
    return ''.join(out), st
okW=okH=0
for j in range(1,22):
    for P in (42,44,60):
        w=g.W(P,j); t,_=transcript(P,j,4,[0,0,1,1],len(w)); okW+=(t==w)
        h=g.H(P,j); t,st=transcript(P,j,1,[],len(h)+5); okH+=(t==h and st==7)
print('move words: %d of 63 match'%okW); print('halt words: %d of 63 match'%okH)
