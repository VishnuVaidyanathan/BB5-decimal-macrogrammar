// From blank: at two times (T1, T2) record the largest block and the number of small pieces (<=3 cells).
// Print machines where small pieces exist at T1 (>=MINU), the largest block grew, and the pieces got fewer ("eating").
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<21)
static unsigned char t[TS];
int main(int argc,char**argv){ long T1=atol(argv[1]),T2=atol(argv[2]); int MINU=atoi(argv[3]); int part=atoi(argv[4]),parts=atoi(argv[5]); char line[128]; char sc; char tm[64]; long n=0;
  int W[7][2],D[7][2],X[7][2],def[7][2];
  while(fgets(line,128,stdin)){ if((n++)%parts!=part) continue; if(sscanf(line,"%c %s",&sc,tm)!=2) continue; memset(def,0,sizeof def);
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
    int lo=TS/2,hi=TS/2,pos=TS/2,st=sc-'A'; long s; int end=0; int u1=0,m1=0,u2=0,m2=0;
    for(s=0;s<T2;s++){
      if(s==T1){ int c=0; for(int i=lo;i<=hi+1;i++){ if(i<=hi&&t[i])c++; else { if(c){ if(c<=3)u1++; if(c>m1)m1=c; } c=0; } } if(u1<MINU||m1<20){end=3;break;} }
      int b=t[pos]; if(!def[st][b]){end=1;break;} int w=W[st][b]; t[pos]=w; pos+=D[st][b]; st=X[st][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>TS-8){end=2;break;} }
    if(end==1) printf("HALT steps=%ld %c %s\n",s,sc,tm);
    else if(end==0){ int c=0; for(int i=lo;i<=hi+1;i++){ if(i<=hi&&t[i])c++; else { if(c){ if(c<=3)u2++; if(c>m2)m2=c; } c=0; } }
      if(u2<u1 && m2>m1) printf("EAT units %d->%d big %d->%d %c %s\n",u1,u2,m1,m2,sc,tm); }
    memset(t+lo-2,0,hi-lo+5); } }
