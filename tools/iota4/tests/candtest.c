#define main isearch_main
#include "isearch.c"
#undef main
static unsigned long long rs=88172645463325252ULL; static unsigned long long rnd(){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static int cmpm(const void*a,const void*b){ mask_t x=*(const mask_t*)a,y=*(const mask_t*)b; return x<y?-1:x>y; }
int main(){ int fails=0, tests=0; long long tot=0;
 for(int t=0;t<300;t++){ K=3+(int)(rnd()%2); INTER=(int)(rnd()%2); int C=K+(int)(rnd()%(t<150?20:110-K)); if(C>120) C=120; COLCAP=C+(int)(rnd()%(K+1));
   int r=1+(int)(rnd()%(INTER?5:3)); mask_t rows[8];
   /* random rows, ensure every column 0..C-1 used not required for candidate test */
   for(int a=0;a<r;a++){ mask_t S=0; while(popc(S)<K) S|=mbit((int)(rnd()%C)); rows[a]=S; }
   cvec out={0}; candidates(rows,r,C,&out); qsort(out.v,out.n,sizeof(mask_t),cmpm);
   /* brute force: K-subsets of [0, C+K) with fresh part = prefix block */
   cvec bf={0}; int n=C+K; int idx[8]; for(int i=0;i<K;i++) idx[i]=i;
   for(;;){ mask_t S=0; int nf=0,ok=1; for(int i=0;i<K;i++){ S|=mbit(idx[i]); if(idx[i]>=C) nf++; }
     for(int j=0;j<nf;j++) if(!(S&mbit(C+j))) ok=0; if(C+nf>COLCAP) ok=0;
     if(ok && INTER){ for(int a=0;a<r;a++) if(!(rows[a]&S)) ok=0; }
     if(ok && valid_new(rows,r,S)) cpush(&bf,S);
     int i=K-1; while(i>=0 && idx[i]==n-K+i) i--; if(i<0) break; idx[i]++; for(int j=i+1;j<K;j++) idx[j]=idx[j-1]+1; }
   qsort(bf.v,bf.n,sizeof(mask_t),cmpm); tests++; tot+=bf.n;
   if(bf.n!=out.n || memcmp(bf.v,out.v,bf.n*sizeof(mask_t))){ fails++; printf("FAIL t=%d K=%d I=%d C=%d cap=%d r=%d gen=%zu bf=%zu\n",t,K,INTER,C,COLCAP,r,out.n,bf.n); }
   free(out.v); free(bf.v); }
 printf("tests=%d fails=%d total candidates=%lld\n",tests,fails,tot); return 0; }
