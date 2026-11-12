// Run a table from the tape [A] 0^g 1^P 0^a 1^z1 0^a 1^z2 0^a 1^z3 ... and report how it ends.
// usage: ladder TABLE g a LIM P z1 [z2 ...]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<24)
static unsigned char t[TS];
int main(int argc,char**argv){ const char*tm=argv[1]; int g=atoi(argv[2]),a=atoi(argv[3]); long LIM=atol(argv[4]);
  int W[7][2],D[7][2],X[7][2],def[7][2]; memset(def,0,sizeof def);
  for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
  int base=TS/2; int p=base+g; long ones=0;
  for(int k=5;k<argc;k++){ int n=atoi(argv[k]); if(k>5) p+=a; for(int i=0;i<n;i++){t[p++]=1;ones++;} }
  int pos=base,st=0; long s; int halted=0; int lo=base,hi=p;
  for(s=0;s<LIM;s++){ int b=t[pos]; if(!def[st][b]){halted=1;break;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; pos+=D[st][b]; st=X[st][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>TS-8)break; }
  // describe the tape
  char buf[400]; int k=0; int i=lo; int nb=0;
  while(i<=hi&&nb<14){ int j=i; while(j<=hi&&t[j]==t[i])j++; k+=snprintf(buf+k,400-k,"%s%d^%d ",(i<=pos&&pos<j)?"[*]":"",t[i],j-i); i=j; nb++; }
  printf("%s steps=%ld ones=%ld state=%c | %s\n",halted?"HALT":"RUN",s,ones,'A'+st,buf); }
