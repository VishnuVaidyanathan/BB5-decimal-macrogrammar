import sys
def parse(tm):
    T={}
    for s,part in enumerate(tm.split('_')):
        for b in (0,1):
            p=part[b*3:b*3+3]
            if p!='---': T[(s,b)]=(int(p[0]),1 if p[1]=='R' else -1, 7 if p[2]=='Z' else ord(p[2])-65)
    return T
def run(tm,tapestr,st=0,N=200,show=True,stop=None):
    # tapestr like "[]0011" : [] marks head
    T=parse(tm); pos=tapestr.index('['); s=tapestr.replace('[','').replace(']','')
    tape={i:int(c) for i,c in enumerate(s)}
    def fmt():
        ks=[k for k,v in tape.items() if v]+[pos]; lo,hi=min(ks),max(ks)
        return ''.join(('[%s]'%'ABCDEFGZ'[st] if i==pos else '')+str(tape.get(i,0)) for i in range(lo,hi+1))
    for t in range(N):
        if show: print(t,fmt())
        k=(st,tape.get(pos,0))
        if k not in T or st==7: print('STOP at',t,'ABCDEFGZ'[st],k[1],fmt()); return
        w,m,nx=T[k]; tape[pos]=w; pos+=m; st=nx
    print('END',fmt())
if __name__=='__main__':
    run(sys.argv[1],sys.argv[2],N=int(sys.argv[3]))
