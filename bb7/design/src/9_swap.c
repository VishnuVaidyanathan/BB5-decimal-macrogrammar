// Swap search.  Seeds: Engine+Fuel machines whose fuel is a solid counter block:
//    [A] 0^g 1^P 0^a 1^Z   ->   [A] 0^g 1^(kP+c) 0^a 1^(Z-1)          (triple; already true for the seed)
// Wanted, with a DOUBLE gap:
//    [A] 0^g 1^P 0^(2a) 1^Z ->  [A] 0^g 1^s 0^a 1^N 0^a 1^(Z-d)       (swap: N grows with P, s small, d = 1 or 2)
// Lazily add <= ADD wires.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int ADD=4, G, A_;
int W[7][2], D[7][2], X[7][2], def[7][2]; int nw, nw0, nstates;
long nodes=0, found=0; char seed[64];
#define TS 2048
int ust,usym; int rs,rN,rZ;
int runtest(int P,int Z){     // 1 accept (rs,rN,rZ set), -1 reject, -2 undefined
  static unsigned char t[TS]; memset(t,0,TS);
  int base=1000; int p=base+G; for(int i=0;i<P;i++)t[p++]=1; p+=2*A_; for(int i=0;i<Z;i++)t[p++]=1;
  int l1=base+G, r1=p-1; int lo=base-400, hi=base+400; int pos=base, st=0;
  for(int s=0;s<6000;s++){
    int b=t[pos]; if(!def[st][b]){ust=st;usym=b;return -2;}
    int w=W[st][b]; t[pos]=w; if(w){ if(pos<l1)l1=pos; if(pos>r1)r1=pos; }
    pos+=D[st][b]; st=X[st][b];
    if(pos<lo||pos>hi) return -1;
    while(l1<r1&&!t[l1])l1++; while(r1>l1&&!t[r1])r1--;
    if(st==0 && pos==l1-G && t[l1]){
      // parse blocks from l1
      int q=l1; int blk[4],gap[4]; int nb=0;
      while(q<=r1 && nb<4){ int c=0; while(q<=r1&&t[q]){c++;q++;} blk[nb]=c; int z=0; while(q<=r1&&!t[q]){z++;q++;} gap[nb]=z; nb++; }
      if(q<=r1) continue;
      if(nb==3 && gap[0]==A_ && gap[1]==A_ && blk[0]<=3 && blk[1]>=2*P && (blk[2]==Z-1||blk[2]==Z-2)){ rs=blk[0]; rN=blk[1]; rZ=blk[2]; return 1; }
    }
  }
  return -1;
}
void name(char*buf){int k=0; for(int s=0;s<7;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){
  nodes++;
  int r=runtest(2,5); if(r==-1) return;
  if(r==1){ int s2=rs,n2=rN,z2=rZ;
    int r3=runtest(3,5); if(r3==-1) return;
    if(r3==1){ int n3=rN, s3=rs, z3=rZ;
      int r4=runtest(4,6); if(r4==-1) return;
      if(r4==1){ if(s2==s3&&s3==rs && z2==z3 && rZ==z2+1 && n3-n2==rN-n3 && n3-n2>=2){ char buf[64]; name(buf); found++;
          printf("SWAP g=%d a=%d add=%d wires=%d s=%d N(2,3,4)=%d,%d,%d d=%d %s seed=%s\n",G,A_,nw-nw0,nw,s2,n2,n3,rN,5-z2,buf,seed); fflush(stdout);} return; } } }
  if(nw-nw0>=ADD) return;
  int s=ust,b=usym; def[s][b]=1; nw++; int ns0=nstates;
  for(int nx=0; nx<=ns0 && nx<7; nx++){ nstates=(nx==ns0)?ns0+1:ns0;
    for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[s][b]=w;D[s][b]=d;X[s][b]=nx; dfs(); } }
  nstates=ns0; def[s][b]=0; nw--;
}
int main(int argc,char**argv){ ADD=atoi(argv[1]); char line[256]; char a3[32],a4[32],a5[32];
  while(fgets(line,256,stdin)){ if(sscanf(line,"%d %d %s %s %s %s",&G,&A_,a3,a4,a5,seed)!=6) continue;
    memset(def,0,sizeof def); nw=0; int mx=0;
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){ if(strlen(seed)<(size_t)(s*7+b*3+3)) continue; const char*c=seed+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; nw++; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A'; if(s>mx)mx=s; if(X[s][b]>mx)mx=X[s][b];}
    nstates=mx+1; nw0=nw; dfs(); }
  fprintf(stderr,"ADD=%d nodes=%ld found=%ld\n",ADD,nodes,found); }
