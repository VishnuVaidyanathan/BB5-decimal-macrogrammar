// Phase A: enumerate "Build cores": partial tables (<=MAXW wires, <=MAXS states, TNF order)
// that turn  1^n 0^g 1^P  (head on leftmost 1, state A) into one solid block of ones,
// with ones gained per old one = k >= 1.5, checked for P = 4, 6, 8.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int MAXW=9, MAXS=6, G=2, N0=3;
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw=0, nstates=1;
long nodes=0, found=0;
#define TS 512
// run test with given P. returns: -1 reject, -2 undefined wire (ust,usym set), else ones count at acceptance
int ust,usym;
int runtest(int P){
  static unsigned char t[TS]; memset(t,0,TS);
  int base=200; for(int i=0;i<N0;i++)t[base+i]=1; for(int i=0;i<P;i++)t[base+N0+G+i]=1;
  int lo=base-3*P-12, hi=base+N0+G+4*P+12; int pos=base, st=0; int ones=N0+P;
  int lim=200+40*P*P+200*P;
  int l1=base, r1=base+N0+G+P-1; // bounds of nonzero region (loose, maintained)
  for(int s=0;s<lim;s++){
    int b=t[pos]; if(!def[st][b]){ust=st;usym=b;return -2;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi) return -1;
    if(ones==0) return -1;
    while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
    if(ones==r1-l1+1 && ones>=N0+2*P) return ones;
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<MAXS;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){
  nodes++;
  int r4=runtest(4); int us=ust,ub=usym; int r6=-3,r8=-3;
  if(r4==-1) return;
  if(r4>=0){ r6=runtest(6); us=ust;ub=usym; if(r6==-1) return;
    if(r6>=0){ r8=runtest(8); us=ust;ub=usym; if(r8==-1) return;
      if(r8>=0){ if(r6-r4==r8-r6 && r6-r4>=4){ char buf[80]; name(buf); found++; printf("CORE g=%d n=%d k2=%d c=%d wires=%d states=%d %s\n",G,N0,r6-r4,r4,nw,nstates,buf);} return; } } }
  if(nw>=MAXW) return;
  int s=us,b=ub; def[s][b]=1; nw++;
  int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<MAXS; nx++){
    if(nx==ns0) nstates=ns0+1; else nstates=ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); }
  }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ MAXW=atoi(argv[1]); MAXS=atoi(argv[2]); G=atoi(argv[3]); N0=atoi(argv[4]);
  dfs(); fprintf(stderr,"W=%d S=%d g=%d n=%d nodes=%ld found=%ld\n",MAXW,MAXS,G,N0,nodes,found); }
