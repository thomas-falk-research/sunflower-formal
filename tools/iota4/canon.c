/* Canonical form of a 4-uniform family: the bipartite incidence graph
   (points | members) with the two sides as colour classes, canonically
   labelled by nauty; prints one canonical adjacency string per input line.
   Input lines: "... BIG r C h1 h2 ... hr" (hex 128-bit rows) or plain hex rows. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nauty.h"
static int cmpint(const void*a,const void*b){return (*(int*)a)-(*(int*)b);}
int main(void){
  static char line[1<<16];
  while(fgets(line,sizeof line,stdin)){
    char *p=strstr(line,"BIG"); if(!p) continue;
    int r,C; if(sscanf(p,"BIG %d %d",&r,&C)!=2) continue;
    p=strchr(p,' '); p=strchr(p+1,' '); p=strchr(p+1,' ');
    unsigned long long hi[64],lo[64];
    for(int a=0;a<r;a++){ while(*p==' ')p++; char buf[40]; strncpy(buf,p,32); buf[32]=0; p+=32;
      char h[17],l[17]; strncpy(h,buf,16);h[16]=0; strncpy(l,buf+16,16);l[16]=0;
      hi[a]=strtoull(h,0,16); lo[a]=strtoull(l,0,16); }
    /* points used */
    int pts[128],np=0;
    for(int i=0;i<128;i++){ int used=0; for(int a=0;a<r;a++){ if(i<64? (lo[a]>>i)&1 : (hi[a]>>(i-64))&1) used=1; } if(used) pts[np++]=i; }
    int n=np+r;
    int m=SETWORDSNEEDED(n); graph *g=calloc((size_t)m*n,sizeof(graph)), *cg=calloc((size_t)m*n,sizeof(graph)); int *lab=malloc(n*sizeof(int)),*ptn=malloc(n*sizeof(int)),*orbits=malloc(n*sizeof(int));
    for(int a=0;a<r;a++) for(int j=0;j<np;j++){ int i=pts[j]; if(i<64? (lo[a]>>i)&1 : (hi[a]>>(i-64))&1){ ADDONEEDGE(g,j,np+a,m);} }
    for(int i=0;i<n;i++){lab[i]=i;ptn[i]=1;} ptn[np-1]=0; ptn[n-1]=0;
    DEFAULTOPTIONS_GRAPH(options); options.getcanon=TRUE; options.defaultptn=FALSE; statsblk stats;
    densenauty(g,lab,ptn,orbits,&options,&stats,m,n,cg);
    /* print canonical member rows as sorted point lists */
    printf("%d %d",np,r);
    for(int a=np;a<n;a++){ int row[8],k=0; for(int j=0;j<np;j++) if(ISELEMENT(GRAPHROW(cg,a,m),j)) row[k++]=j; qsort(row,k,sizeof(int),cmpint); printf(" ["); for(int t=0;t<k;t++) printf("%s%d",t?",":"",row[t]); printf("]"); }
    printf("\n"); free(g);free(cg);free(lab);free(ptn);free(orbits);
  }
  return 0;
}
