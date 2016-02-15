#undef debug

#include <stdio.h>
#include "cr.h"

extern int isequal();
extern sopen(), swrite(), sclose();

static strmax = 0, treemax = 0;
char *alloc();

struct VERT { int         dep;
                      int         *beg, *end;
                      struct VERT *son, *bro, *suf; };

struct VERT *tree, *bot, *top;

int *text;

/* #define HSIZE   15700 */
#define HSIZE   415700

struct CLIST { struct CLIST *conxt;
                       struct VERT  *point, *value;
                       int           which; };

struct CLIST *cospace, *cotop, *hvect[HSIZE];

CLEAR()
{ register int i;
  for (i = 0; i < HSIZE; hvect[i++] = 0);
  cotop = cospace;
}

struct VERT *FIND(p,c)
register struct VERT *p;
register OCC *c;
{ register unsigned int h;
  register struct CLIST *cp;

  h = ((unsigned)p)%HSIZE;
  h = (128*h + (int)(c ? c->linpt : 0))%HSIZE;
  cp = hvect[h];
  while (cp != 0)
    { if (cp->point == p && isequal(cp->which,c))
        return (cp->value);
      cp = cp->conxt;
    }
  return (0);
}

ENTER(p,c,q)
register struct VERT *p, *q;
register OCC *c;
{ register unsigned int h;
  register struct CLIST *cp;

  h = ((unsigned)p)%HSIZE;
  h = (128*h + (int)(c ? c->linpt : 0))%HSIZE;
  cp = hvect[h];
  while (cp != 0)
    { if (cp->point == p && isequal(cp->which,c)) break;
      cp = cp->conxt;
    }
  if (cp == 0)
    { cotop->point = p;
      cotop->which = (int)c;
      cotop->value = q;
      cotop->conxt = hvect[h];
      hvect[h] = cotop++;
    }
  else
    cp->value = q;
}

#define INEW(bg,ed,dp)  \
{ (--top)->beg=bg; top->end=ed; top->dep=dp; top->son = 0; }

#define LNEW(bg,ed,dp)  \
{ (++bot)->beg=bg; bot->end=ed; bot->dep=dp; bot->son = 0; }

struct VERT *MAKETREE()
{ register int *rsbg, *rsed, *scan;
  register struct VERT *nxt, *cloc, *head;
  int *txtend;
  struct VERT *root;

  tree   = (struct VERT *)alloc(sizeof(tree[0]) * treemax);
  cospace= (struct CLIST *)alloc(sizeof(cospace[0]) * treemax);
  txtend = text+strmax;
  bot    = tree-1;
  top    = tree+treemax-1;
  CLEAR();

  head = cloc = root = top;
  rsbg = rsed = text;

  LNEW(text,txtend,0);
  ENTER(head,*text,bot);
  head->son = 0;

  while (1)
    { if (cloc != root)
        cloc = cloc->suf;
      else
        { if (*rsbg++ == 0) break;
          rsed += (head == root);
        }
#ifdef debug
printf("rsbg=%d rsed=%d cloc=%d head=%d\n\n",
       rsbg-text,rsed-text,cloc-tree,head-tree);
fflush(stdout);
#endif
      while (rsbg - rsed < 0)
        { nxt = FIND(cloc,*rsbg);
          if (nxt == 0)
            { if (cloc == root)
                LNEW(rsbg,txtend,0)
              else
                LNEW(rsbg,txtend,cloc->dep+(cloc->end-cloc->beg))
              ENTER(cloc,*rsbg,bot);
              nxt = bot;
            }
          if (rsed - rsbg < nxt->end - nxt->beg)
            { INEW(nxt->beg,nxt->beg+(rsed-rsbg),nxt->dep);
              nxt->dep += (rsed-rsbg);
              nxt->beg  = top->end;
              ENTER(cloc,*(top->beg),top);
              ENTER(top,*(nxt->beg),nxt);
              head = head->suf = top;
              break;
            }
          rsbg += nxt->end - nxt->beg;
          cloc  = nxt;
        }
      if (rsbg - rsed >= 0)
        { head->suf = cloc;
          while (1)
            { nxt = FIND(cloc,*rsed);
              if (nxt == 0)
                { head = cloc;
                  break;
                }
              scan  = nxt->beg+1;
              rsed += 1;
              while (scan - nxt->end < 0 && isequal(*scan,*rsed))
                { scan += 1;
                  rsed += 1;
                }
              if (scan - nxt->end < 0)
                { INEW(nxt->beg,scan,nxt->dep);
                  nxt->dep += scan-nxt->beg;
                  nxt->beg  = scan;
                  ENTER(cloc,*(top->beg),top);
                  ENTER(top,*scan,nxt);
                  head = top;
                  break;
                }
              cloc = nxt;
              rsbg = rsed;
            }
        }
      LNEW(rsed,txtend,head->dep+(head->end-head->beg));
      ENTER(head,*rsed,bot);
    }
  return (root);
}

LINKTREE()
{ register struct CLIST *cp;
  register struct VERT *p, *q;

  for (cp = cospace; cp < cotop; cp++)
    { p = cp->point;
      q = cp->value;
      q->bro = p->son;
      p->son = q;
    }
}

#ifdef debug
DISPTREE(vrt,lev)
struct VERT *vrt;
int   lev;
{ int *c;
  printf("%*s(%5d) ",2*lev,"",vrt-tree);
  if (vrt->son == 0)
    { if (*vrt->beg == 0)
        printf("$");
      else
        printf("%d",*vrt->beg);
      printf(" [%d] <%d>\n",vrt->dep,(vrt->beg-vrt->dep)-text);
    }
  else
    { if (lev != 0)
        { printf("\"");
          for (c = vrt->beg; c < vrt->end; c++) printf("%d",*c);
          printf("\"<%d,%d> [%d] {%d}\n",
                 vrt->beg-text,vrt->end-text-1,vrt->dep,vrt->suf-tree);
        }
      else
        printf("*\n");
      for (vrt = vrt->son; vrt != 0; vrt = vrt->bro)
        DISPTREE(vrt,lev+1);
    }
}
#endif

int COUNT(p)
register struct VERT *p;
{ register struct VERT *q;
  register int cnt;
  if (p->son == 0) return (1);
  cnt = 0;
  for (q = p->son; q != 0; q = q->bro)
    cnt += COUNT(q);
  sopen(cnt,p->son->dep);
  TLIST(p);
  sclose();
  return (cnt);
}

TLIST(p)
register struct VERT *p;
{ register struct VERT *q;
  if (p->son == 0)
    swrite( (p->beg - p->dep) - text );
  else
    for (q = p->son; q != 0; q = q->bro)
      TLIST(q);
}

mktree(t, n)
register int *t;
int n;
{ register struct VERT *root, *q;

  strmax = n;
  treemax = strmax * 2;
  text = t;
  root = MAKETREE();
  LINKTREE();

  for (q = root->son; q != 0; q = q->bro)
    COUNT(q);
#ifdef debug
  DISPTREE(root,0);
#endif
free(tree);
free(cospace);
}
