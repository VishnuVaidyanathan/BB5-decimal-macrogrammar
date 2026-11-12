// From a blank tape: when is each wire first used?  Input lines "S TABLE".  Prints wires not used within LIM.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<22)
static unsigned char t[TS];
int main(int argc,char**argv){ long LIM=atol(argv[1]); char line[128]; char sc; char tm[64];
  int W[7][2],D[7][2],X[7][2],def[7][2];
  while(fgets(line,128,stdin)){ if(sscanf(line,"%c %s",&sc,tm)!=2) continue; memset(def,0,sizeof def);
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
    long first[7][2]; long cnt[7][2]; memset(cnt,0,sizeof cnt); for(int i=0;i<7;i++)first[i][0]=first[i][1]=-1;
    int lo=TS/2,hi=TS/2,pos=TS/2,st=sc-'A'; long s; long ones=0; int end=0;
    for(s=0;s<LIM;s++){ int b=t[pos]; if(!def[st][b]){end=1;break;} if(first[st][b]<0)first[st][b]=s; cnt[st][b]++;
      int w=W[st][b]; ones+=w-b; t[pos]=w; pos+=D[st][b]; st=X[st][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>TS-8){end=2;break;} }
    int nb=0; for(int i=lo;i<=hi;i++) if(t[i]&&(i==lo||!t[i-1])) nb++;
    printf("%s ones=%ld blocks=%d unused:",end==1?"HALT":end==2?"EDGE":"RUN",ones,nb);
    for(int i=0;i<7;i++)for(int b=0;b<2;b++) if(def[i][b]&&first[i][b]<0) printf(" %c%d",'A'+i,b);
    printf(" | late:"); for(int i=0;i<7;i++)for(int b=0;b<2;b++) if(first[i][b]>=1000) printf(" %c%d@%ld(x%ld)",'A'+i,b,first[i][b],cnt[i][b]);
    printf(" | %c %s\n",sc,tm); memset(t+lo-2,0,hi-lo+5); } }
