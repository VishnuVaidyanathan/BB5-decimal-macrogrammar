/* Run the claimed BB(7) champion from the clean tape  1 0 [G] 0 1^P 0000 (11 00)^u 1  and print the halting step.
   usage: run_tape P u */
#include <stdio.h>
#include <stdlib.h>
#define TS (1<<24)
static unsigned char t[TS];
int main(int argc,char**argv){ long P=atol(argv[1]); int u=atoi(argv[2]); const char*tm="1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB";
  int W[7][2],D[7][2],X[7][2];
  for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=tm+s*7+b*3; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]=='Z'?7:c[2]-'A';}
  long base=TS/4; long q=base; t[q++]=1; t[q++]=0; long head=q; t[q++]=0; for(long i=0;i<P;i++)t[q++]=1; q+=4; for(int i=0;i<u;i++){t[q++]=1;t[q++]=1;q+=2;} t[q++]=1;
  long pos=head; int st=6; unsigned long long s=0;
  while(st!=7){ int b=t[pos]; t[pos]=W[st][b]; pos+=D[st][b]; st=X[st][b]; s++; if(pos<8||pos>TS-8){printf("EDGE\n");return 1;} }
  long ones=0; for(long i=0;i<TS;i++)ones+=t[i]; printf("%llu %ld\n",s,ones); }
