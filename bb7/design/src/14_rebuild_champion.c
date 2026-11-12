// Rebuild the champion from the oscillator reading.
// Given: the 9 up-stroke wires only.  Contract for the rest (down + bottom):
//   start on a solid block 1^Q with blank tape around it (state B on its leftmost 1).
//   The block must be taken apart and packed into units "11 00": at some time the tape holds
//   at least Q/2-3 units in a row, with no more ones than Q+4.   Checked for Q = 12 and 16.
// Lazily fill the empty wires (28 choices each, any of the 7 states), at most ADD of them.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int ADD=4; int W[7][2], D[7][2], X[7][2], def[7][2]; int nw, nw0; long nodes=0, found=0;
#define TS 1024
int ust,usym;
int runtest(int Q){
  static unsigned char t[TS]; memset(t,0,TS); int base=500; for(int i=0;i<Q;i++)t[base+i]=1;
  int pos=base, st=1, ones=Q, lo=base-250, hi=base+250;
  for(int s=0;s<40*Q*Q+2000;s++){
    int b=t[pos]; if(!def[st][b]){ust=st;usym=b;return -2;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi||ones==0||ones>Q+4) return -1;
    if((s&7)==0){ int best=0,run=0; for(int i=lo;i<hi-4;i++){ if(!t[i-1]&&t[i]&&t[i+1]&&!t[i+2]&&!t[i+3]){ run++; i+=3; if(run>best)best=run; } else run=0; }
      if(best>=Q/2-3) return 1; }
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<7;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){ nodes++;
  int r=runtest(12); if(r==-1) return;
  if(r==1){ r=runtest(16); if(r==-1) return; if(r==1){ char buf[64]; name(buf); found++; printf("%d wires added: %s\n",nw-nw0,buf); return; } }
  if(nw-nw0>=ADD) return;
  int s=ust,b=usym; def[s][b]=1; nw++;
  for(int nx=0;nx<7;nx++) for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); }
  def[s][b]=0; nw--; }
int main(int argc,char**argv){ ADD=atoi(argv[1]); const char*tm=argv[2]; nw=0;
  for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; nw++; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
  nw0=nw; dfs(); fprintf(stderr,"tables tried: %ld   passing: %ld\n",nodes,found); }
