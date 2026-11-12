// Engines: partial tables that take  E(P) = [A] 1^n 0^g 1^P  (head on leftmost cell of the shape, blank elsewhere)
// back to E(Q) with Q = k*P + c, k >= 2.  Lazy (TNF) search, <= MAXW wires, <= MAXS states.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int MAXW=8, MAXS=6, G=2, N0=1, PART=0, PARTS=1;
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw=0, nstates=1;
long nodes=0, found=0, top=0;
#define TS 1024
int ust,usym;
int runtest(int P){
  static unsigned char t[TS]; memset(t,0,TS);
  int base=500; for(int i=0;i<N0;i++)t[base+i]=1; for(int i=0;i<P;i++)t[base+N0+G+i]=1;
  int lo=base-200, hi=base+200; int pos=base, st=0; int ones=N0+P;
  int lim=3000; int l1=base+(N0?0:G), r1=base+N0+G+P-1;
  for(int s=0;s<lim;s++){
    int b=t[pos]; if(!def[st][b]){ust=st;usym=b;return -2;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi) return -1;
    if(ones==0) return -1;
    while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
    if(st==0 && ones>N0+P && pos==(N0? l1 : l1-G)){
      int Q=ones-N0; int ok=(r1-pos+1==N0+G+Q);
      if(ok){ for(int i=0;i<N0&&ok;i++) if(!t[pos+i]) ok=0; for(int i=0;i<G&&ok;i++) if(t[pos+N0+i]) ok=0; }
      if(ok) return Q;
    }
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<MAXS;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(int depth){
  nodes++;
  int r[3]; int us=-1,ub=-1; int i;
  for(i=0;i<3;i++){ r[i]=runtest(2+i); if(r[i]==-1) return; if(r[i]==-2){us=ust;ub=usym;break;} }
  if(i==3){ int d=r[1]-r[0]; if(d==r[2]-r[1] && d>=2){ char buf[80]; name(buf); found++; printf("ENG n=%d g=%d k=%d c=%d wires=%d states=%d %s\n",N0,G,d,r[0]-2*d,nw,nstates,buf);} return; }
  if(nw>=MAXW) return;
  int s=us,b=ub; def[s][b]=1; nw++;
  int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<MAXS; nx++){
    if(nx==ns0) nstates=ns0+1; else nstates=ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){
      if(depth==1){ top++; if(top%PARTS!=PART) continue; }
      W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(depth+1); }
  }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ MAXW=atoi(argv[1]); MAXS=atoi(argv[2]); N0=atoi(argv[3]); G=atoi(argv[4]); if(argc>6){PART=atoi(argv[5]);PARTS=atoi(argv[6]);}
  dfs(0); fprintf(stderr,"W=%d S=%d n=%d g=%d nodes=%ld found=%ld\n",MAXW,MAXS,N0,G,nodes,found); }
