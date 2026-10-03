/* stdin: N, then N lines "mask flag" (flag 1 = fixed member).
   stdout: one line per 3-sunflower triple, listing its non-fixed indices;
   "ERR" if all three are fixed. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(void){ int N; if(scanf("%d",&N)!=1) return 2; uint64_t *m=malloc(N*8); int *f=malloc(N*4);
 for(int i=0;i<N;i++){ unsigned long long x; if(scanf("%llu %d",&x,&f[i])!=2) return 2; m[i]=x; }
 for(int a=0;a<N;a++) for(int b=a+1;b<N;b++){ uint64_t ab=m[a]&m[b];
  for(int c=b+1;c<N;c++){ if((m[a]&m[c])!=ab || (m[b]&m[c])!=ab) continue;
   if(f[a]&&f[b]&&f[c]){ printf("ERR\n"); continue; }
   if(!f[a]) printf("%d ",a); if(!f[b]) printf("%d ",b); if(!f[c]) printf("%d ",c); printf("\n"); } }
 return 0; }
