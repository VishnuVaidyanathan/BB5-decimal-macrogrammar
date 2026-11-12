// Fuel part search on door-cores.
// Tape: [A] 0^g 1^P 0^s U^z .  Lazily add <= ADD wires.  Accept when the run with z=2 ends at an undefined wire
// with the tape one solid block, and the same door is reached for z=0,1,3 with the block growing >=2x per unit.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int ADD=3, MAXS=7, G;
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw=0, nstates, nw0;
long nodes=0, found=0;
#define TS 8192
const char*US[]={"1","10","100","110","1100","1110","1000","101"}; int NU=8;
int S_, UI; int ust,usym,dOnes,dSolid,dOffR,dOffL; char core[80];
int runtest(int P,int z,int lim){
  static unsigned char t[TS]; memset(t,0,TS);
  int base=4000; int p=base+G; for(int i=0;i<P;i++)t[p++]=1; int r1=p-1; int ones=P;
  if(z){ p+=S_; for(int k=0;k<z;k++) for(const char*c=US[UI];*c;c++){ t[p]=*c-'0'; if(t[p]){ones++; r1=p;} p++; } }
  int lo=base-3500, hi=base+3500; int pos=base, st=0; int l1=base+G;
  for(int s=0;s<lim;s++){
    int b=t[pos];
    if(!def[st][b]){ ust=st;usym=b; while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
      dOnes=ones; dSolid=(ones==r1-l1+1); dOffR=pos-r1; dOffL=pos-l1; return -2; }
    int w=W[st][b]; ones+=w-b; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi||ones==0) return -1;
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<7;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){
  nodes++;
  int P=2; int r=runtest(P,2,8000); if(r==-1) return;
  int us=ust,ub=usym;
  if(dSolid && dOnes>=6*P && nw>nw0){ int f2=dOnes, oR=dOffR;
    int f[4]; int ok=1; f[2]=f2;
    for(int z=0;z<4&&ok;z++){ if(z==2)continue; int rr=runtest(P,z,400000); if(rr!=-2||ust!=us||usym!=ub||!dSolid) ok=0; f[z]=dOnes; }
    if(ok && f[1]>=2*f[0] && f[2]>=2*f[1] && f[3]>=2*f[2]){ char buf[80]; name(buf); found++;
      printf("FUELDOOR g=%d s=%d U=%s add=%d wires=%d states=%d door=%c%d offR=%d ones(z=0..3)=%d,%d,%d,%d %s  core=%s\n",G,S_,US[UI],nw-nw0,nw,nstates,'A'+us,ub,oR,f[0],f[1],f[2],f[3],buf,core); fflush(stdout); }
    ust=us;usym=ub;
  }
  if(nw-nw0>=ADD) return;
  int s=us,b=ub; def[s][b]=1; nw++;
  int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<MAXS; nx++){
    if(nx==ns0) nstates=ns0+1; else nstates=ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); }
  }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ ADD=atoi(argv[1]); char line[256];
  while(fgets(line,256,stdin)){ char *p=strstr(line,"g="); if(!p) continue; G=atoi(p+2);
    char*q=strrchr(line,' '); if(!q) continue; strcpy(core,q+1); core[strcspn(core,"\n")]=0;
    memset(def,0,sizeof def); nw=0; int mx=0;
    for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*c=core+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; nw++; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A'; if(s>mx)mx=s; if(X[s][b]>mx)mx=X[s][b];}
    nstates=mx+1; nw0=nw;
    for(S_=1;S_<=3;S_++) for(UI=0;UI<NU;UI++) dfs();
  }
  fprintf(stderr,"ADD=%d nodes=%ld found=%ld\n",ADD,nodes,found); }
