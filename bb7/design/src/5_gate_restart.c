// Gate + Restart search on a fixed Engine+Fuel table.
// Start at the door: tape 1^Q, head one cell right of the block, door state reading 0.
// Lazily add <= ADD wires. For each Q in a small set the run must either come back to the door
// with a bigger block Q' (restart) or stop at an undefined wire (possible halt).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int ADD=3, MAXS=7; int DS=4, DSYM=0, OFF=1; const char*TAG="";
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw=0, nstates, nw0;
long nodes=0, found=0;
#define TS 16384
int ust,usym; long usteps;
long runtest(int Q,long lim){   // returns Q' >0 on return to door, -1 reject, -2 undefined
  static unsigned char t[TS]; memset(t,0,TS);
  int base=8000; for(int i=0;i<Q;i++)t[base+i]=1; int l1=base,r1=base+Q-1; int ones=Q;
  int lo=base-7000, hi=base+7000; int pos=r1+OFF, st=DS;
  for(long s=0;s<lim;s++){
    int b=t[pos];
    if(s>0 && st==DS && b==DSYM){ while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--; if(pos==r1+OFF && ones==r1-l1+1) return ones; }
    if(!def[st][b]){ ust=st;usym=b;usteps=s; return -2; }
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi||ones==0) return -1;
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<7;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
int QMIN=3,QMAX=14;
void dfs(void){
  nodes++;
  long res[32]; int us=-1,ub=-1; int nret=0, nund=0, hs=-1,hb=-1, multi=0;
  for(int Q=QMIN;Q<=QMAX;Q++){
    long r=runtest(Q, Q<=5?200000:6000000);
    if(r==-1) return;
    res[Q]=r;
    if(r==-2){ if(us<0){us=ust;ub=usym;} if(hs<0){hs=ust;hb=usym;} else if(hs!=ust||hb!=usym) multi=1; nund++; res[Q]=-(1000+ust*2+usym); }
    else nret++;
    if(Q==5 && nret==0 && nw-nw0>=ADD) return;
  }
  if(nw>nw0 && nret>=3 && !multi){
    long first=0,last=0,fq=0,lq=0; int mono=1; long prev=0;
    for(int Q=QMIN;Q<=QMAX;Q++) if(res[Q]>0){ if(!first){first=res[Q];fq=Q;} if(res[Q]<=prev) mono=0; prev=res[Q]; last=res[Q]; lq=Q; }
    if(last>=20*lq && last>=6*first){ char buf[80]; name(buf); found++;
      printf("GATE add=%d wires=%d states=%d halts=%d haltwire=%c%d mono=%d res:",nw-nw0,nw,nstates,nund,hs<0?'-':'A'+hs,hb<0?0:hb,mono);
      for(int Q=QMIN;Q<=QMAX;Q++){ if(res[Q]>0) printf(" %ld",res[Q]); else printf(" H"); } printf("  %s %s\n",TAG,buf); fflush(stdout); }
  }
  if(us<0 || nw-nw0>=ADD) return;
  int s=us,b=ub; def[s][b]=1; nw++;
  int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<MAXS; nx++){
    if(nx==ns0) nstates=ns0+1; else nstates=ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); }
  }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ ADD=atoi(argv[1]); const char*tm=argv[2]; DS=argv[3][0]-'A'; DSYM=argv[3][1]-'0'; if(argc>4) OFF=atoi(argv[4]); if(argc>5) TAG=argv[5];
  int mx=0; for(int s=0;s<7;s++)for(int b=0;b<2;b++){ if(strlen(tm)<(size_t)(s*7+b*3+3)) continue; const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; nw++; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A'; if(s>mx)mx=s; if(X[s][b]>mx)mx=X[s][b];}
  nstates=mx+1; nw0=nw; dfs(); fprintf(stderr,"ADD=%d nodes=%ld found=%ld\n",ADD,nodes,found); }
