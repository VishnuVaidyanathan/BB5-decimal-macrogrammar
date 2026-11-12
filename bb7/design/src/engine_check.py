import sys
tm=sys.argv[1]; n=int(sys.argv[2]); g=int(sys.argv[3]); rounds=int(sys.argv[4])
T={}
for s,part in enumerate(tm.split('_')):
    for b in (0,1):
        p=part[b*3:b*3+3]
        if p!='---': T[(s,b)]=(int(p[0]),1 if p[1]=='R' else -1, ord(p[2])-65)
P=2; tape=set(range(n))|set(range(n+g,n+g+P)); pos=0; st=0; out=[]; t=0; used=set()
while len(out)<rounds and t<50_000_000:
    k=(st,1 if pos in tape else 0)
    if k not in T: out.append('UNDEF %s%d'%('ABCDEFG'[k[0]],k[1])); break
    used.add(k)
    w,m,nx=T[k]
    if w: tape.add(pos)
    else: tape.discard(pos)
    pos+=m; st=nx; t+=1
    if st==0 and tape:
        lo=min(tape); hi=max(tape); Q=len(tape)-n
        if Q>P and pos==(lo if n else lo-g) and hi-pos+1==n+g+Q and all((pos+i) in tape for i in range(n)) and all((pos+n+i) not in tape for i in range(g)):
            out.append((t,Q)); P=Q
print(tm,out,'wires used',len(used))
