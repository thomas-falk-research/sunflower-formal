/* brute-force class counts, no nauty.
   mode P: bf P k inter n maxr  -- families of k-subsets of [n], up to S_n, via min image over all n! perms
   mode R: bf R k inter maxr    -- families (any #points), canonical = min Venn-region count vector over all row perms */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int K, INTER;
/* sets as uint64 point masks */
static int valid_new(const uint64_t *rows, int r, uint64_t S){
  for(int a=0;a<r;a++){ if(rows[a]==S) return 0; if(INTER && !(rows[a]&S)) return 0; }
  for(int a=0;a<r;a++) for(int b=a+1;b<r;b++){ uint64_t ab=rows[a]&rows[b]; if(ab==(rows[a]&S) && ab==(rows[b]&S)) return 0; }
  return 1;
}
/* ---------- hash set of byte keys ---------- */
typedef struct { unsigned char *keys; char *used; size_t cap, n; int klen; } hset;
static uint64_t hh(const unsigned char *k,int l){ uint64_t h=1469598103934665603ULL; for(int i=0;i<l;i++){h^=k[i]; h*=1099511628211ULL;} return h; }
static void hinit(hset *h,int klen){ h->klen=klen; h->cap=1024; h->n=0; h->keys=calloc(h->cap,klen); h->used=calloc(h->cap,1); }
static int hadd(hset *h,const unsigned char *k); 
static void hgrow(hset *h){ hset g; g.klen=h->klen; g.cap=h->cap*2; g.n=0; g.keys=calloc(g.cap,g.klen); g.used=calloc(g.cap,1);
  for(size_t i=0;i<h->cap;i++) if(h->used[i]) hadd(&g,h->keys+i*h->klen); free(h->keys); free(h->used); *h=g; }
static int hadd(hset *h,const unsigned char *k){ if(2*(h->n+1)>h->cap) hgrow(h);
  size_t i=hh(k,h->klen)&(h->cap-1); while(h->used[i]){ if(!memcmp(h->keys+i*h->klen,k,h->klen)) return 0; i=(i+1)&(h->cap-1);} 
  h->used[i]=1; memcpy(h->keys+i*h->klen,k,h->klen); h->n++; return 1; }

/* ================= mode P ================= */
static int NP, NS, NPERM; static uint64_t SETS[256]; static int *PT; /* PT[p*NS+s] image set index */
static int sidx(uint64_t m){ for(int i=0;i<NS;i++) if(SETS[i]==m) return i; return -1; }
static u128 canonP(u128 fam){ u128 best=~(u128)0; int idx[256],c=0; for(int s=0;s<NS;s++) if((fam>>s)&1) idx[c++]=s;
  for(int p=0;p<NPERM;p++){ u128 im=0; const int *t=PT+p*NS; for(int i=0;i<c;i++) im|=(u128)1<<t[idx[i]]; if(im<best) best=im; } return best; }
static void modeP(int n,int maxr){
  NP=n; NS=0; for(uint64_t m=0;m<(1ULL<<n);m++) if(__builtin_popcountll(m)==K) SETS[NS++]=m;
  if(NS>128){fprintf(stderr,"too many sets\n");exit(1);}
  NPERM=1; for(int i=2;i<=n;i++) NPERM*=i; PT=malloc(sizeof(int)*NPERM*NS);
  int perm[16]; for(int i=0;i<n;i++) perm[i]=i;
  for(int p=0;p<NPERM;p++){ for(int s=0;s<NS;s++){ uint64_t im=0,x=SETS[s]; while(x){int c=__builtin_ctzll(x); x&=x-1; im|=1ULL<<perm[c];} PT[p*NS+s]=sidx(im);} 
    /* next permutation */ int i=n-2; while(i>=0&&perm[i]>perm[i+1]) i--; if(i<0) break; int j=n-1; while(perm[j]<perm[i]) j--; int t=perm[i];perm[i]=perm[j];perm[j]=t; for(int a=i+1,b=n-1;a<b;a++,b--){t=perm[a];perm[a]=perm[b];perm[b]=t;} }
  u128 *cur=malloc(sizeof(u128)); cur[0]=0; size_t ncur=1; printf("P k=%d inter=%d n=%d: 1",K,INTER,n);
  for(int r=1;r<=maxr;r++){ hset h; hinit(&h,16);
    for(size_t q=0;q<ncur;q++){ uint64_t rows[64]; int rr=0; for(int s=0;s<NS;s++) if((cur[q]>>s)&1) rows[rr++]=SETS[s];
      for(int s=0;s<NS;s++){ if((cur[q]>>s)&1) continue; if(!valid_new(rows,rr,SETS[s])) continue; u128 c=canonP(cur[q]|((u128)1<<s)); hadd(&h,(unsigned char*)&c);} }
    free(cur); ncur=h.n; cur=malloc(sizeof(u128)*(ncur+1)); size_t k2=0; for(size_t i=0;i<h.cap;i++) if(h.used[i]) memcpy(&cur[k2++],h.keys+i*16,16);
    free(h.keys); free(h.used); printf(" %zu",ncur); fflush(stdout); if(!ncur) break; }
  printf("\n");
}
/* ================= mode R ================= */
static int R_; static int PERMS[40320][8]; static int NPR;
static void canonR(const uint64_t *rows,int r,unsigned char *out){ /* out: 2^r bytes */
  int np=0; uint64_t all=0; for(int a=0;a<r;a++) all|=rows[a];
  int pat[64]; while(all){int c=__builtin_ctzll(all); all&=all-1; int p=0; for(int a=0;a<r;a++) if((rows[a]>>c)&1) p|=1<<a; pat[np++]=p;}
  int L=1<<r; unsigned char best[256], cur[256]; int have=0;
  for(int q=0;q<NPR;q++){ memset(cur,0,L); for(int i=0;i<np;i++){ int p=pat[i],im=0; for(int a=0;a<r;a++) if((p>>a)&1) im|=1<<PERMS[q][a]; cur[im]++; }
    if(!have||memcmp(cur,best,L)<0){memcpy(best,cur,L);have=1;} }
  memcpy(out,best,L);
}
static void genperms(int r){ int perm[8]; for(int i=0;i<r;i++) perm[i]=i; NPR=0;
  for(;;){ memcpy(PERMS[NPR++],perm,sizeof perm); int i=r-2; while(i>=0&&perm[i]>perm[i+1]) i--; if(i<0) break; int j=r-1; while(perm[j]<perm[i]) j--; int t=perm[i];perm[i]=perm[j];perm[j]=t; for(int a=i+1,b=r-1;a<b;a++,b--){t=perm[a];perm[a]=perm[b];perm[b]=t;} } }
/* decode region vector to explicit rows */
static int decodeR(const unsigned char *v,int r,uint64_t *rows){ int c=0; for(int a=0;a<r;a++) rows[a]=0; for(int p=1;p<(1<<r);p++) for(int t=0;t<v[p];t++){ for(int a=0;a<r;a++) if((p>>a)&1) rows[a]|=1ULL<<c; c++; } return c; }
static uint64_t *XR; static int XC; static hset *XH; static int XREM;
static void extR(uint64_t S,int size,int from,const uint64_t *rows,int r,int C){
  if(size==K){ if(valid_new(rows,r,S)){ uint64_t nr[8]; memcpy(nr,rows,r*8); nr[r]=S; unsigned char key[256]; canonR(nr,r+1,key); hadd(XH,key);} return; }
  { uint64_t T=S; for(int t=0;t<K-size;t++) T|=1ULL<<(C+t); if(valid_new(rows,r,T)){ uint64_t nr[8]; memcpy(nr,rows,r*8); nr[r]=T; unsigned char key[256]; canonR(nr,r+1,key); hadd(XH,key);} }
  for(int c=from;c<C;c++) extR(S|(1ULL<<c),size+1,c+1,rows,r,C);
}
static void modeR(int maxr){
  unsigned char *cur=calloc(1,1); size_t ncur=1; int L=1; printf("R k=%d inter=%d: 1",K,INTER);
  for(int r=1;r<=maxr;r++){ genperms(r); int L2=1<<r; hset h; hinit(&h,L2); XH=&h;
    for(size_t q=0;q<ncur;q++){ uint64_t rows[8]; int C=decodeR(cur+q*L,r-1,rows); extR(0,0,0,rows,r-1,C); }
    free(cur); ncur=h.n; L=L2; cur=malloc(ncur*L+1); size_t k2=0; for(size_t i=0;i<h.cap;i++) if(h.used[i]) memcpy(cur+(k2++)*L,h.keys+i*L,L);
    free(h.keys); free(h.used); printf(" %zu",ncur); fflush(stdout); }
  printf("\n");
}
int main(int argc,char**argv){ K=atoi(argv[2]); INTER=atoi(argv[3]);
  if(argv[1][0]=='P') modeP(atoi(argv[4]),atoi(argv[5])); else modeR(atoi(argv[4])); return 0; }
