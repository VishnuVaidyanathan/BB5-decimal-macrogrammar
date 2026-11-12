// Print the tape (as block sizes and gaps) every time the machine is in the "clean" position:
// a chosen state, with the head exactly g cells left of the leftmost 1.
// usage: canon TABLE startState cleanState g LIM maxlines
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<24)
static unsigned char t[TS];
int main(int argc,char**argv){ const char*tm=argv[1]; int st=argv[2][0]-'A', cs=argv[3][0]-'A', g=atoi(argv[4]); long LIM=atol(argv[5]); int maxl=atoi(argv[6]);
  int W[7][2],D[7][2],X[7][2],def[7][2]; memset(def,0,sizeof def);
  for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
  int pos=TS/2; int l1=pos,r1=pos; long ones=0; if(getenv("TAPE")){ const char*z=getenv("TAPE"); for(int i=0;z[i];i++){ t[pos+i]=z[i]-48; if(t[pos+i]){ if(!ones)l1=pos+i; r1=pos+i; ones++; } } } int lines=0; long s; char last[600]="";
  for(s=0;s<LIM;s++){ int b=t[pos];
    if(st==cs && ones>0){ while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
      if(pos==l1-g){ char buf[600]; int k=0; int i=l1; int nb=0;
        while(i<=r1&&nb<40&&k<560){ int j=i; while(j<=r1&&t[j]==t[i])j++; if(t[i]) k+=snprintf(buf+k,600-k,"%d ",j-i); else k+=snprintf(buf+k,600-k,"(%d) ",j-i); i=j; nb++; }
        if(strcmp(buf,last)){ printf("%12ld  %s\n",s,buf); strcpy(last,buf); if(++lines>=maxl) return 0; } } }
    if(!def[st][b]){ printf("HALT at step %ld, ones=%ld\n",s,ones); return 0; }
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1||ones==1)l1=pos; if(pos>r1||ones==1)r1=pos; }
    pos+=D[st][b]; st=X[st][b]; if(pos<8||pos>TS-8){printf("EDGE\n");return 0;} }
  printf("still running at %ld, ones=%ld\n",s,ones); }
