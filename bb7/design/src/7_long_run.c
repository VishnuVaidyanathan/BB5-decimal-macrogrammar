// Run "start table" lines from a blank tape for LIM steps. Print HALT (steps, ones) or RUN (width, ones).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<22)
static unsigned char t[TS];
int main(int argc,char**argv){ long LIM=atol(argv[1]); int part=atoi(argv[2]),parts=atoi(argv[3]); char line[128]; long n=0; char sc; char tm[64];
  int W[7][2],D[7][2],X[7][2],def[7][2];
  while(fgets(line,128,stdin)){ if((n++)%parts!=part) continue; if(sscanf(line,"%c %s",&sc,tm)!=2) continue;
    memset(def,0,sizeof def);
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
    int lo=TS/2,hi=TS/2,pos=TS/2,st=sc-'A'; long s; long ones=0; int halted=0,edge=0;
    for(s=0;s<LIM;s++){ int b=t[pos]; if(!def[st][b]){halted=1;break;}
      int w=W[st][b]; ones+=w-b; t[pos]=w; pos+=D[st][b]; st=X[st][b];
      if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>TS-8){edge=1;break;} }
    if(halted) printf("HALT steps=%ld ones=%ld wire=%c%d %c %s\n",s,ones,'A'+st,t[pos],sc,tm);
    else printf("%s width=%d ones=%ld %c %s\n",edge?"EDGE":"RUN",hi-lo+1,ones,sc,tm);
    memset(t+lo-2,0,hi-lo+5);
  } }
