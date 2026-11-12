// Check the "oscillator" reading of the claimed BB(7) champion on its real run from a blank tape.
// A "look" = state D reading a cell right after B0, C0 (the head is at the right end of the working block).
//   D reads 1 -> predicted UP   : by the next look the working block has gained 3
//   D reads 0 -> predicted DOWN : by the next look the working block has lost 1, and one more 1 sits in the trail on its left
// The working block = the solid run of ones that ends at the cell B just wrote (two cells left of D).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TS (1<<24)
static unsigned char t[TS];
int main(int argc,char**argv){ long N=atol(argv[1]); const char*tm="1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB";
  int W[7][2],D[7][2],X[7][2];
  for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]=='Z'?7:c[2]-'A';}
  int pos=TS/2,st=0; int d1=-1,d2=-1; long s;
  long nlook[2]={0,0}; long ok[2]={0,0}; long bad_turn[2]={0,0}, bad_other[2]={0,0};
  long hist[2][9]; memset(hist,0,sizeof hist);
  int havePrev=0, prevSym=0; long prevL=0, prevTrail=0; long prevStep=0; int g0between=0; long nG0=0,nG1=0; int shown=0;
  long lo=pos,hi=pos;
  for(s=0;s<N&&st!=7;s++){ int b=t[pos]; int dig=2*st+b;
    if(st==6){ if(b==0){nG0++; g0between=1;} else nG1++; }
    if(st==3 && d1==4 && d2==2){            // a look
      long e=pos-2; long L=0; while(t[e-L])L++;           // working block
      long q=e-L; long trail=0; while(q>=lo){ trail+=t[q]; q--; }   // ones left of the working block
      if(havePrev){ long dL=L-prevL; int p=prevSym; nlook[p]++;
        int good = p ? (dL==3) : (dL==-1 && trail==prevTrail+1);
        if(good) ok[p]++; else { if(g0between) bad_turn[p]++; else { bad_other[p]++; if(shown<12){shown++; printf("  odd case at step %ld: D read %d, block %ld -> %ld, trail %ld -> %ld\n",prevStep,p,prevL,L,prevTrail,trail);} } }
        int h=dL+4; if(h<0)h=0; if(h>8)h=8; hist[p][h]++; }
      havePrev=1; prevSym=b; prevL=L; prevTrail=trail; prevStep=s; g0between=0; }
    d2=d1; d1=dig;
    t[pos]=W[st][b]; pos+=D[st][b]; st=X[st][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
  printf("steps run: %ld\n",s);
  for(int p=1;p>=0;p--){ printf("\nD read %d (%s): %ld looks\n",p,p?"predicted UP, block +3":"predicted DOWN, block -1 and trail +1",nlook[p]);
    printf("   exactly as predicted : %ld\n   different, with a bottom turn (G reads 0) in between : %ld\n   different, no turn in between : %ld\n",ok[p],bad_turn[p],bad_other[p]);
    printf("   change of block size  (<=-4,-3,-2,-1,0,+1,+2,+3,>=+4): "); for(int i=0;i<9;i++)printf("%ld ",hist[p][i]); printf("\n"); }
  printf("\nG reads 1 (inside a down line): %ld times.  G reads 0 (bottom / turn): %ld times\n",nG1,nG0);
}
