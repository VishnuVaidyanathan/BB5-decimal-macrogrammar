// Boot search: every candidate is run FROM A BLANK TAPE.
// Input: partial tables (one per line). For each table and each start state (A..G), run from blank.
// At an empty wire: count it as a halt, and (if budget left) also try the 28 ways to fill it.
// Output: HALT lines (steps >= MINH) and RUN lines (still running at the limit, tape not tiny).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int ADD=1; long LIM=100000, MINH=300;
int W[7][2], D[7][2], X[7][2], def[7][2]; int added=0;
#define TS (1<<16)
static unsigned char t[TS];
long nodes=0,nh=0,nr=0; int START; char base[64];
void name(char*buf){int k=0; for(int s=0;s<7;s++){ for(int b=0;b<2;b++){ if(def[s][b]){buf[k++]='0'+W[s][b];buf[k++]=D[s][b]>0?'R':'L';buf[k++]='A'+X[s][b];} else {buf[k++]='-';buf[k++]='-';buf[k++]='-';} } buf[k++]='_';} buf[k-1]=0;}
void dfs(void){
  nodes++;
  int lo=TS/2,hi=TS/2,pos=TS/2,st=START; long s; int ones=0; int us=-1,ub=-1;
  memset(t,0,TS);
  for(s=0;s<LIM;s++){
    int b=t[pos]; if(!def[st][b]){us=st;ub=b;break;}
    int w=W[st][b]; ones+=w-b; t[pos]=w; pos+=D[st][b]; st=X[st][b];
    if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>TS-8){ return; }
  }
  char buf[64];
  if(us<0){ if(hi-lo>=60 && ones>=30){ name(buf); nr++; printf("RUN start=%c width=%d ones=%d %s\n",'A'+START,hi-lo+1,ones,buf);} return; }
  if(s>=MINH){ name(buf); nh++; printf("HALT start=%c steps=%ld ones=%d wire=%c%d %s\n",'A'+START,s,ones,'A'+us,ub,buf); }
  if(added>=ADD) return;
  def[us][ub]=1; added++;
  for(int nx=0;nx<7;nx++) for(int w=0;w<2;w++) for(int d=-1;d<=1;d+=2){ W[us][ub]=w;D[us][ub]=d;X[us][ub]=nx; dfs(); }
  def[us][ub]=0; added--;
}
int main(int argc,char**argv){ ADD=atoi(argv[1]); LIM=atol(argv[2]); int part=atoi(argv[3]),parts=atoi(argv[4]); char line[128]; long n=0;
  while(fgets(line,128,stdin)){ if((n++)%parts!=part) continue; if(strlen(line)<48) continue;
    memset(def,0,sizeof def);
    for(int s=0;s<7;s++)for(int b=0;b<2;b++){const char*c=line+s*7+b*3; if(c[0]=='-')continue; def[s][b]=1; W[s][b]=c[0]-'0'; D[s][b]=c[1]=='R'?1:-1; X[s][b]=c[2]-'A';}
    for(START=0;START<7;START++){ added=0; dfs(); } }
  fprintf(stderr,"nodes=%ld halts>=%ld: %ld running: %ld\n",nodes,MINH,nh,nr); }
