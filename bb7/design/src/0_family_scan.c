// Family: the champion's Build loop is kept (base 3); the other five wires are free.
// Fixed: A0=1RB B0=1RC B1=1RB C0=0RD D0=0LE D1=0LD E0=0LF E1=1LE F0=1RA
// Free : C1 F1 A1 G0 G1  -> one of them is the halt, the other four take any of 28 values.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<15)
static unsigned char tape[TS];
static int W[14], D[14], NX[14];
static const int freew[5] = {5, 11, 1, 12, 13};
static void setw(int k,int w,int d,int n){W[k]=w;D[k]=d;NX[k]=n;}
static void name(char*buf){
  for(int s=0;s<7;s++){ for(int x=0;x<2;x++){int k=2*s+x;
      if(NX[k]<0){*buf++='1';*buf++='R';*buf++='Z';} else {*buf++='0'+W[k];*buf++=D[k]>0?'R':'L';*buf++='A'+NX[k];}}
    if(s<6)*buf++='_';}
  *buf=0;
}
int main(int argc,char**argv){
  long N=atol(argv[1]); int part=atoi(argv[2]), parts=atoi(argv[3]);
  long sig_hi=N/1000; if(sig_hi<60) sig_hi=60;
  long nh=0,ne=0,nt=0,na=0,nc=0,idx=0; char buf[64];
  for(int h=0;h<5;h++)
   for(int v=0;v<28*28*28*28;v++,idx++){
    if(idx%parts!=part) continue;
    setw(0,1,1,1);setw(2,1,1,2);setw(3,1,1,1);setw(4,0,1,3);setw(6,0,-1,4);setw(7,0,-1,3);setw(8,0,-1,5);setw(9,1,-1,4);setw(10,1,1,0);
    int vv=v;
    for(int f=0;f<5;f++){int k=freew[f];
      if(f==h){setw(k,1,1,-1);continue;}
      int c=vv%28;vv/=28; setw(k,c&1,(c>>1)&1?1:-1,c>>2);}
    int p=TS/2,s=0,lo=p,hi=p; long cnt[14]={0},last[14]={0}; long k; int out=0;
    for(k=0;k<N;k++){
      int key=2*s+tape[p]; cnt[key]++; last[key]=k;
      if(NX[key]<0){out=1;k++;break;}
      tape[p]=W[key]; p+=D[key]; s=NX[key];
      if(p<lo){lo=p; if(p<2){out=2;break;}} else if(p>hi){hi=p; if(p>TS-3){out=2;break;}}
    }
    int ones=0; for(int i=lo;i<=hi;i++) ones+=tape[i];
    memset(tape+lo,0,hi-lo+1);
    if(out==1){ nh++; if(k>=2000){name(buf);printf("H %ld %d %s\n",k,ones,buf);} }
    else if(out==2) ne++;
    else if(hi-lo<64) nt++;
    else { na++;
      int sig=0; for(int i=0;i<14;i++) if(cnt[i]>=6 && cnt[i]<=sig_hi && last[i]>N/20) sig=1;
      if(sig){nc++; name(buf); printf("C %d %s\n",hi-lo,buf);} else if(argc>4){name(buf);printf("A %d %s\n",hi-lo,buf);} }
   }
  fprintf(stderr,"part %d: halt %ld, ran off %ld, tiny %ld, alive %ld (with rare-event sign %ld)\n",part,nh,ne,nt,na,nc);
  return 0;
}
