// For "start table doorState doorSym doorOff": (1) run from blank, list the door events (block sizes Q);
// (2) measure the gate map from the door for Q=3..11.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<22)
static unsigned char t[TS];
int W[7][2],D[7][2],X[7][2],def[7][2]; int DS,DSYM,OFF;
// mode 0: from blank (start st0); mode 1: from door with Q. Fills qs[], returns count; *end: 0 run,1 halt,2 edge
int run(int mode,int st0,int Q,long LIM,long*qs,int maxq,int*end,long*steps){
  int base=TS/2; int lo=base,hi=base,pos=base,st=st0; long ones=0; int l1=base,r1=base; int nq=0;
  if(mode){ for(int i=0;i<Q;i++)t[base+i]=1; ones=Q; r1=base+Q-1; hi=r1+2; pos=r1+OFF; st=DS; }
  long s; *end=0;
  for(s=0;s<LIM;s++){ int b=t[pos];
    if(st==DS&&b==DSYM&&ones>0&&(s>0||!mode)){ while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
      if(pos==r1+OFF&&ones==r1-l1+1){ if(nq<maxq)qs[nq]=ones; nq++; if(mode)break; } }
    if(!def[st][b]){*end=1;break;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1||ones==1)l1=pos; if(pos>r1||ones==1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>TS-8){*end=2;break;} }
  *steps=s; memset(t+lo-2,0,hi-lo+5); return nq;
}
int main(int argc,char**argv){ long LIM=atol(argv[1]); int part=atoi(argv[2]),parts=atoi(argv[3]); char line[160]; long n=0; char sc,dsc; char tm[64]; int dsym,off;
  while(fgets(line,160,stdin)){ if((n++)%parts!=part) continue; if(sscanf(line,"%c %s %c %d %d",&sc,tm,&dsc,&dsym,&off)!=5) continue;
    memset(def,0,sizeof def); DS=dsc-'A'; DSYM=dsym; OFF=off;
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
    if(LIM==0){ int anyH=0; for(int Q=3;Q<=10;Q++){ long q1[2]; int e; long st; int k=run(1,0,Q,20000,q1,1,&e,&st); if(!k&&e==1) anyH=1; } if(anyH) fputs(line,stdout); continue; }
    long qs[40]; int end; long steps; int nq=run(0,sc-'A',0,LIM,qs,40,&end,&steps);
    printf("%c %s %c%d %d doors=%d:",sc,tm,dsc,dsym,off,nq); for(int i=(nq>40?0:0);i<nq&&i<40;i++) printf(" %ld",qs[i]);
    printf(" | map:");
    for(int Q=3;Q<=14;Q++){ long q1[2]; int e; long st; int k=run(1,0,Q,Q<=8?300000:3000000,q1,1,&e,&st); if(k) printf(" %ld",q1[0]); else printf(" %s",e==1?"H":"?"); }
    printf("\n"); } }
