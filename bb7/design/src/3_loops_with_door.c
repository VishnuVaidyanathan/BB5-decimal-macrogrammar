// Cores with an exhaustion door: [A] 0^g 1^P  (blank elsewhere) -> solid block 1^(kP+c), and exactly then
// the machine reaches an undefined wire (the door). Same door for P=3,5,7; k>=2.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int MAXW=7, MAXS=6, G=1;
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw=0, nstates=1;
long nodes=0, found=0;
#define TS 1024
int ust,usym,dOnes,dOffL,dOffR,dSolid;
int runtest(int P){
  static unsigned char t[TS]; memset(t,0,TS);
  int base=500; for(int i=0;i<P;i++)t[base+G+i]=1;
  int lo=base-150, hi=base+150; int pos=base, st=0; int ones=P; int l1=base+G, r1=base+G+P-1;
  for(int s=0;s<2500;s++){
    int b=t[pos];
    if(!def[st][b]){ ust=st;usym=b; while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
      dOnes=ones; dSolid=(ones==r1-l1+1); dOffL=pos-l1; dOffR=pos-r1; return -2; }
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi||ones==0) return -1;
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<MAXS;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){
  nodes++;
  int r=runtest(3); if(r==-1) return;
  int us=ust,ub=usym;
  if(dSolid && dOnes>=6){ int o3=dOnes,l3=dOffL,r3=dOffR;
    int ra=runtest(5); if(ra==-2&&ust==us&&usym==ub&&dSolid){ int o5=dOnes,l5=dOffL,r5=dOffR;
      int rb=runtest(7); if(rb==-2&&ust==us&&usym==ub&&dSolid){ int o7=dOnes;
        if(o5-o3==o7-o5 && o5-o3>=4 && (l3==l5&&l5==dOffL || r3==r5&&r5==dOffR)){ char buf[80]; name(buf); found++;
          printf("CORED g=%d k2=%d c3=%d door=%c%d %s=%d wires=%d states=%d %s\n",G,o5-o3,o3,'A'+us,ub,(l3==l5&&l5==dOffL)?"offL":"offR",(l3==l5&&l5==dOffL)?l3:r3,nw,nstates,buf); } } }
    ust=us;usym=ub;
  }
  if(nw>=MAXW) return;
  int s=us,b=ub; def[s][b]=1; nw++;
  int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<MAXS; nx++){
    if(nx==ns0) nstates=ns0+1; else nstates=ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); }
  }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ MAXW=atoi(argv[1]); MAXS=atoi(argv[2]); G=atoi(argv[3]);
  dfs(); fprintf(stderr,"W=%d S=%d g=%d nodes=%ld found=%ld\n",MAXW,MAXS,G,nodes,found); }
