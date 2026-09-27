#define main isearch_main
#include "isearch.c"
#undef main
static unsigned long long rs=1234567ULL; static unsigned long long rnd(){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static int pickd(const mask_t *rows,int r,int C,int *orb,int *gok){
  int deg[MAXC]; long long inv[MAXR]; int lab[NMAX]; degrees(rows,r,C,deg); long long mn=-1;
  for(int a=0;a<r;a++){ inv[a]=row_inv(rows[a],deg); if(mn<0||inv[a]<mn) mn=inv[a]; }
  run_nauty(rows,r,C,inv,deg,lab,orb); int d=-1; for(int p=0;p<r+C;p++){int v=lab[p]; if(v<r&&inv[v]==mn) d=v;}
  /* check generators are automorphisms of the set system */
  *gok=1; for(size_t g=0;g<NGENS;g++){ int *pm=GENS+g*NMAX; for(int a=0;a<r;a++){ mask_t im=0,x=rows[a]; while(x){int c=lowbit(x); x&=~mbit(c); im|=mbit(pm[r+c]-r);} if(pm[a]>=r || rows[pm[a]]!=im) *gok=0; } }
  return d; }
int main(){ int bad=0,badg=0,ties=0;
 for(int t=0;t<3000;t++){ K=4; int r=2+(int)(rnd()%10);
   /* symmetric-ish: disjoint union of copies of a small random block, shifted by offsets up to >64 */
   int base=2+(int)(rnd()%4); int bc=K+(int)(rnd()%4); mask_t blk[8]; for(int a=0;a<base;a++){ mask_t S; do{S=0; while(popc(S)<K) S|=mbit((int)(rnd()%bc));}while(0); blk[a]=S; }
   int copies=r/base; if(copies<1) copies=1; if(copies*bc>120) copies=120/bc; r=0; mask_t rows[64];
   for(int c=0;c<copies;c++) for(int a=0;a<base;a++){ mask_t S=0,x=blk[a]; while(x){int q=lowbit(x); x&=~mbit(q); S|=mbit(q+c*bc);} int dup=0; for(int b=0;b<r;b++) if(rows[b]==S) dup=1; if(!dup) rows[r++]=S; }
   int C=copies*bc; int orb[NMAX],orb2[NMAX],gok,gok2; int d=pickd(rows,r,C,orb,&gok);
   int pr[64],pc[MAXC]; for(int i=0;i<r;i++) pr[i]=i; for(int i=0;i<C;i++) pc[i]=i;
   for(int i=r-1;i>0;i--){int j=rnd()%(i+1),tt=pr[i];pr[i]=pr[j];pr[j]=tt;} for(int i=C-1;i>0;i--){int j=rnd()%(i+1),tt=pc[i];pc[i]=pc[j];pc[j]=tt;}
   mask_t rows2[64]; for(int a=0;a<r;a++){ mask_t im=0,x=rows[a]; while(x){int c=lowbit(x); x&=~mbit(c); im|=mbit(pc[c]);} rows2[pr[a]]=im; }
   int d2=pickd(rows2,r,C,orb2,&gok2); if(orb2[d2]!=orb2[pr[d]]) bad++; if(!gok||!gok2) badg++;
   int cnt=0; for(int a=0;a<r;a++) if(orb[a]==orb[d]) cnt++; if(cnt>1) ties++; }
 printf("canon-invariance failures=%d bad generators=%d (cases with nontrivial orbit of d: %d)\n",bad,badg,ties); }
