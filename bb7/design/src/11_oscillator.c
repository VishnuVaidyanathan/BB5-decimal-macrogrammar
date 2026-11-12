// Oscillator search. Seed: up-stroke + down-stroke.  Add <= ADD wires so that after the block has been taken
// apart (down), a solid block at least twice the first top appears (up again).  Tape: [A] 0^g 1^P.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int ADD=2, G; long LIM=60000;
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw, nw0, nstates;
long nodes=0, found=0; char seed[64];
#define TS 4096
int ust,usym; int rQ,rPieces,rTop2;
int runtest(int P){
  static unsigned char t[TS]; memset(t,0,TS);
  int base=2000; for(int i=0;i<P;i++)t[base+G+i]=1;
  int lo=base-1800, hi=base+1800; int pos=base, st=0; int ones=P; int Q=0; int l1=base+G,r1=base+G+P-1; int pieces1=0;
  for(long s=0;s<LIM;s++){
    int b=t[pos]; if(!def[st][b]){ust=st;usym=b;return -2;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi||ones==0) return -1;
    if((s&15)==0){ while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
      int solid=(ones==r1-l1+1);
      if(!pieces1){ if(solid && ones>=2*P && ones>Q) Q=ones;
        if(Q && !solid && ones>=Q/2 && ones<=Q+3){ int pieces=0,mx=0,c=0; for(int i=l1;i<=r1+1;i++){ if(i<=r1&&t[i])c++; else { if(c){pieces++; if(c>mx)mx=c;} c=0; } }
          if(mx<=3 && pieces*3>=Q) pieces1=pieces; } }
      else if(ones>=2*Q){ int mx=0,c=0; for(int i=l1;i<=r1+1;i++){ if(i<=r1&&t[i])c++; else { if(c>mx)mx=c; c=0; } }
        if(mx>=2*Q){ rQ=Q; rPieces=pieces1; rTop2=mx; return 1; } } }
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<7;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){
  nodes++;
  int r=runtest(3); if(r==-1) return;
  if(r==1){ int q3=rQ,p3=rPieces,t3=rTop2; int r4=runtest(4); if(r4==-1) return;
    if(r4==1){ char buf[64]; name(buf); found++; printf("OSC g=%d wires=%d P3:top=%d pieces=%d top2=%d P4:top=%d pieces=%d top2=%d %s\n",G,nw,q3,p3,t3,rQ,rPieces,rTop2,buf); fflush(stdout); return; } }
  if(nw-nw0>=ADD) return;
  int s=ust,b=usym; def[s][b]=1; nw++; int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<7; nx++){ nstates=(nx==ns0)?ns0+1:ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); } }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ ADD=atoi(argv[1]); int part=atoi(argv[2]),parts=atoi(argv[3]); int maxw=atoi(argv[4]); char line[256]; long n=0;
  while(fgets(line,256,stdin)){ if((n++)%parts!=part) continue; if(sscanf(line,"%d %s",&G,seed)!=2) continue;
    memset(def,0,sizeof def); nw=0; int mx=0;
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){ const char*c=seed+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; nw++; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A'; if(s>mx)mx=s; if(X[s][b]>mx)mx=X[s][b];}
    if(nw>maxw) continue; nstates=mx+1; nw0=nw; dfs(); }
  fprintf(stderr,"ADD=%d nodes=%ld found=%ld\n",ADD,nodes,found); }
