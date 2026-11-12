// Ladder check. Tape: [A] 0^g 1^1 0^(2a) 1^z . Run until the head goes 3 cells past the first tape's right end
// (all counters used) or the machine stops, or LIM. Print ones at that moment for z=1,2,3.
// input lines: g a TABLE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<22)
static unsigned char t[TS];
int main(int argc,char**argv){ long LIM=atol(argv[1]); char line[200]; int g,a; char tm[64];
  int W[7][2],D[7][2],X[7][2],def[7][2];
  while(fgets(line,200,stdin)){ if(sscanf(line,"%d %d %s",&g,&a,tm)!=3) continue; memset(def,0,sizeof def);
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
    printf("%s g%d a%d :",tm,g,a);
    for(int z=1;z<=3;z++){ int base=TS/2; int p=base+g; t[p++]=1; p+=2*a; for(int i=0;i<z;i++)t[p++]=1; int end=p+2; long ones=1+z;
      int pos=base,st=0,lo=base,hi=p; long s; const char*why="LIMIT";
      for(s=0;s<LIM;s++){ int b=t[pos]; if(!def[st][b]){why="STOP";break;} int w=W[st][b]; ones+=w-b; t[pos]=w; pos+=D[st][b]; st=X[st][b];
        if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos>end){why="PAST";break;} if(pos<8){why="EDGE";break;} }
      printf("  z=%d %s ones=%ld steps=%ld",z,why,ones,s); memset(t+lo-2,0,hi-lo+5); }
    printf("\n"); } }
