/* cr.c -- compress assembly language */
#include <stdio.h>
#include <ctype.h>
/* #include <sys/param.h> */
#include "regexp/regexp.h"
#include "cr.h"

static dodesc();		/* process the description file		*/
static char *expand();		/* expand a pattern			*/
static lookop();		/* look up a description opcode		*/
static makesubrs();		/* make sequences into subroutines	*/
static morph();			/* find largest seq with internal jumps	*/
static openfrag();		/* a candidate cj sequence?		*/

/*  usage: cr pattfile flags < input > output */
/*  c = don't cross-jump */
/*  p = don't do pa */
/*  e = entocc, m = misc, p = pa, c = cj, f = freeocc, i = install */
/*  b = print out buffer after each optimization move */
/*  y = don't optimize, just flush data to front */
/*  t = output threaded code */
/*  z = do idiom analysis */
/*  number -- stop optimizing after n edits */

static char debug[128];
#define THREADED (debug['t'])       /* output threaded code */
#define ICOUNT  (debug['z'])        /* output sequences for idiom analysis */
#define LBSIZE  512 
#define OCCTOTEXT(occ) ((char *)(occ->linpt + 1))
#define LINTOTEXT(lin) ((char *)(lin + 1))

regexp *flushend,		/* define start of text */
    *flushbeg,			/* start data segment */
    *endmark,			/* pattern matches an END pseudo-op if any */
    *retpatt,			/* regexp matching return instruction */
    *labpatt,			/* label match pattern */
    *equatepatt;		/* label equating pattern (currently unused) */

char *jumpfmt = "JUMP %s",	/* jump output format */
    *callfmt /* = "CALL %s" */,	/* call output format */
    *entseq[2],			/* stmts to insert at entry */
    *labfmt = "%l:",		/* label output format */
    *flushfmt,			/* start text segment output format */
    *labgfmt = "l%d:",		/* generated label format */
    *endstmt,			/* the end statement if any encountered */ 
    *exitseq[2],		/* stmts to insert at exit */
    *equatefmt = "EQUATE  \1,\2";	    /* output format for equates */

int eatblanks;		/* eat leading spaces, turn whitespace into space */
int nonest;		/* don't nest generated calls */
int subcost[2] = {1},	/* cost of a subroutine (normal/nested) */
    callcost[2] = {1};	/* cost of a call to a subroutine */

static ncallpatts = 0;
static regexp *callpatts[64];	/* call patterns */
static njumps = 0;		/* jump operations */
static regexp *jumps[64];
static nujumps = 0;		/* unconditional jump ops */
static regexp *ujumps[64];
static nbads = 0;
static regexp *badlist[64];	/* list of un-subroutinizable instructions */
static nflushlines = 0;
static regexp *flushlines[64];    /* patterns matching lines to flush through */

char *index();
char *spellop();

static int noccs = 0, nlins = 0;
static char linbf[LBSIZE];		/* line buffer */
static char labf[10];			/* label buffer */
static int seqlen = 0;
static int limit = 9999999;		/* limit # of edits */
static int nextlab = 1;
static flushmode;			/* reading data */
static OCC *last1;

/*  This is a vector of occurrence pointers to the non-labels in the file.
 *  It's passed to the pos-tree stuff for matching.
 *  Terminated by a null entry.
 */
unsigned occsz = 0;                 /* # of lines in occlist */
OCC **occlist = 0;                  /* line # to occ pointer */

static LIN *heads[HASHSIZE];		/* hash buckets */

static OCC *occavail = 0;           /* free occ list */

/*  The instruction occurrence list head */
static OCC occhead = {0, 0, 0, &occhead, &occhead};

/*  The list head for undefined labels */
static OCC looselabs = {0, 0, 0, &looselabs, &looselabs};

static struct subseq seqhead = {&seqhead, &seqhead, &seqhead, &seqhead};
/*  stack ops   */
static nstackops = 0;
static struct regexp *stackops[32];	/* regex patterns for stackops */
static char *stackvals[32];

SUBSEQ *pqmax();
static SUBSEQ *subseq = 0;
static int nsubs = 0;

/*  List of equated lines; this is output at the end */ 
LIN *equatelist = 0;

char *alloc(siz)
    {
    char *calloc();
    char *r;
    r = calloc(1, siz);
    if (!r)
        {
        fprintf(stderr, "no memory noccs %d nlins %d\n", noccs, nlins);
        exit(0);
        }
    return r;
    }

/*  make a duplicate copy of this sequence */
SUBSEQ *dupseq(subseq)
    SUBSEQ *subseq;
    {
    int newsiz, i;
    char *p, *p2, *p1;
    SUBSEQ *newseq;
    p1 = (char *)subseq;
    newsiz = sizeof(SUBSEQ) + (subseq->nelts - 1) * sizeof(subseq->ents[0]);
    p2 = p = alloc(newsiz);
    while (newsiz--) *p2++ = *p1++;
    newseq = (SUBSEQ *)p;
    for (i = 0; i < newseq->nelts; i++) newseq->ents[i].subseq = newseq;
    return newseq;
    }

/*  This program maintains three essential data structures:
 *  1) A list of lines in the buffer.  This list is doubly-linked
 *     in sequential order and identical lines are linked together.
 *
 *  2) A "symbol table" of all the different lines which have been
 *     encountered.  The text of the line is only stored once.
 *     The symbol table entry contains pointers to the first and
 *     last occurrences encountered, to aid in building the
 *     equivalence classes.
 *
 *  3) Descriptions of all of the sequences that have been found.
 *  
 */


/*  get input line */
getl(fil)
    FILE *fil;
    {
    char *p1;
    int c;
    p1 = linbf;

    /*  Read input line into linbf */
    do  {
        c = getc(fil);
        if (c == EOF) return 0;
        *(p1++) = c;
        if (p1 + 1 ==  linbf + sizeof(linbf))
            {
            fprintf(stderr, "linbf overflow\n");
            break;
            }
        } while (c != '\n');

    p1--;
    *p1 = 0;
    if (p1 - linbf != strlen(linbf)) printf("botch getl\n");
    return p1 - linbf;
    }

unsigned hash(lin)
    register char *lin;
    {
    register result;

    result = 0;
    for (;;)
        {
        if (!*lin) break;
        result = result * 97 + *lin++;
        }

    /* fix unsigned modulus bug on the ridge */
    if (result < 0)
        {
        result = -result;
        if (result < 0) result = 0;
        }

    result %= HASHSIZE;

    return result;
    }

/*  decide if this is an unconditional jump */
isujump(occ)
    OCC *occ;
    {
    return (occ->flags & FLGUJUMP);
    }

/*  Labels are always at the head of their eqchn's */
#define islabel(occ) ((occ)->label && (occ)->label->eqchn == (occ))
#define isret(occ) ((occ) && ((occ)->flags & FLGRET) != 0)
#define iscall(occ) (((occ)->flags & FLGCALL) != 0)
#define isxfer(occ) (((occ)->label) && (!islabel(occ)))

/*  call two things equal if they are equal instructions or
 *  they jump to the same label or equal distances
 */
isequal(occi, occj)
    OCC *occi, *occj;
    {
    int result;
    if (occi == occj) return 1;
    if (occi == 0 || occj == 0 || (occi->flags & FLGBAD)) return 0;
    result = (occi->linpt == occj->linpt &&
    (occi->label == occj->label || occi->relabel == occj->relabel)); 
    return result;
    }
    

ckrefs(occ)		/*  validate refchain for this label */
    OCC *occ;
    {
    OCC *next;
    int n;
    n = 0;
    for (next = (OCC *)(occ->label->refchn); next != occ; next = next->refchn)
        {
        if (!next) printf("ckrefs: %s not on refchn\n", spellop(occ));
        if (n++ > 10000) printf("ckrefs: %s refchn circular\n", spellop(occ));
        }
    }

/*  hash something & install it in the lines list if it's not already there */
LIN *install(bf)
    char *bf;
    {
    unsigned h;             /* the hash value */
    LIN *p;

    h = hash(bf);           /* get hash value */
    for (p = heads[h]; p; p = p->next)
        {
        if (!strcmp(LINTOTEXT(p), bf)) {
            if (debug['m']) printf("%s old\n", (char *)(p + 1));
            return p;
            }
        }

    /* Allocate new line for this */
    p = (LIN *)alloc(sizeof(LIN) + strlen(bf) + 1);

    strcpy((char *)(p + 1), bf);

    if (debug['m']) printf("new %s %d next %d\n",
         (char *)(p + 1), p, heads[h]);
    p->next = heads[h];
    heads[h] = p; 
    p->refchn = 0;
    p->usecount = 0;
    p->eqchn = 0;
    p->stackop = 0;
    p->regcomp = 0;

    nlins++;
    return p;
    }

/*  Allocate an occurrence. */
OCC *getocc()
    {
    OCC *occ;
    if (occavail == NULL)
        {
        int i;
        /*  Occs are allocated by the hundreds to save the overhead */
        occavail = (OCC *)alloc(100 * sizeof(OCC));
        for (i = 0; i < 100; i++)
            {
            occavail[i].seqprior = occavail + (i + 1);
            }
        occavail[99].seqprior = 0;
        }
    occ = occavail;
    occavail = occavail->seqprior;
    occ->ent.lineno = -1;
    occ->ent.parent = NULL;
    occ->linpt = occ->label = NULL;
    occ->relabel = (void *)NULL;
    occ->seqnext = occ->seqprior =
    occ->eqnext = occ->eqprior = occ->refchn = NULL;
    return occ;
    }

/*  link an occurrence onto the sequential list after pocc */
insertocc(pocc, occ)
    OCC *pocc, *occ;
    {
    if (!pocc || !occ)
        fprintf(stderr, "insertocc: null pointers\n");
    occ->seqnext = pocc->seqnext;       /* this' next is prior's next */
    occ->seqprior = pocc;               /* this' prior is prior */
    pocc->seqnext = occ;                /* prior's next is this */
    occ->seqnext->seqprior = occ;       /* this' next's prior is this */
    if (occ->seqnext == 0) fprintf(stderr, "insertocc: null seqnext\n");
    if (occ->seqprior == 0) fprintf(stderr, "insertocc: null seqprior\n");
    }

/*  remove this occurrence from the occurrence list */
OCC *outsertocc(occ)
    register OCC *occ;
    {
    register OCC *next, *prior;
    next = occ->seqnext;
    prior = occ->seqprior;
    next->seqprior = prior;
    prior->seqnext = next;
    return next;
    }

/*  Delete this occurrence from the buffer and return the next */
OCC *freeocc(occ)
    register OCC *occ;
    {
    register OCC *next;

    if (debug['f']) printf("freeocc %s\n", spellop(occ));

    /* search the refchn sequentially as it's not doubly-linked */
    if (isxfer(occ))
        {
        for (next = (OCC *)(occ->label);; next = next->refchn)
            {
            if (next->refchn == occ)
                {
                next->refchn = next->refchn->refchn;
                break;
                }
            if (next->refchn == NULL) break;
            }
        }

    if (occ->eqnext == occ) {
        /* Removing last list element? */
        occ->eqnext = occ->eqprior = NULL;
        }
    else {
        OCC *next = occ->eqnext, *prior = occ->eqprior;
        next->eqprior = prior;
        prior->eqnext = next;
        }

    /* Update lin's chain head if it pointed to occ */
    if (occ->linpt->eqchn == occ) {
        occ->linpt->eqchn = occ->eqnext;
        }

    /*  We don't put things back on the avail list.  It might make
     *  moved code adjacent when it shouldn't be.
     */
    next = outsertocc(occ);         /* delete from seqchn */    
    occ->flags |= FLGGONE;          /* signal death */
    return next;                    /* return next on seqchn */
    }

static char *newstr(s)
    char *s;
    {
    char *p;
    p = alloc(strlen(s) + 1);
    strcpy(p, s);
    return p;
    }

/*  Inspect the chain of occurrences for bogousities */
checkcirc(s)
    char *s;
    {
    OCC *occ;
    int n = 0;
    for (occ = occhead.seqnext; occ != &occhead; occ = occ->seqnext)
	{
	if (n++ > noccs + 4) printf("%s: seqchain circular!\n", s);
	if (occ->seqnext->seqprior != occ)
	    printf("%s: occ->seqnext->seqprior != occ!\n", s);
	if (occ->seqprior->seqnext != occ)
	    printf("%s: occ->seqprior->seqnext != occ!\n", s);
	}
    }

/*  Enter an occurrence of a line into the buffer to follow pocc */
OCC *entocc(linbf, pocc, fromline)
    OCC *pocc;              /* follows this occurrence */
    char *linbf;            /* the register transfer itself */
    {
    OCC *occ;               /* the occurrence of this line */
    LIN *lin;               /* the unique entry for this line */
    char *s, *t;
    struct regexp **p;
    int stackop = 0;

    /*	fix escapes */
    for (s = t = linbf;; s++)
	{
	if (*s == '\\')
	    {
	    s++;
	    if (*s == 'n') *t++ = '\n';
	    else if (*s == '\\') *t++ = '\\';
	    else *t++ = *s;
	    }
	else *t++ = *s;
	if (*s == 0) break;
	}

    /*  If this instruction is a transfer of control, we need to allocate
     *  an occurrence for the destination label also, and enter it if it's
     *  not already entered.
     */
    if (debug['e'])
        printf("entocc '%s' pocc %d from line %d\n", linbf, (int)pocc, fromline);

    occ = getocc();                 /* get an occurrence */

    /*  test for a label, zap colon */
    if (regexec(labpatt, linbf, 1)) {
	regsub(labpatt, "\\1", linbf);		/* just get the label */
	s = linbf;
        if (debug['e'])
            printf("a label '%s'\n", linbf);
        }

    else    {
        s = NULL;
        for (p = stackops; *p; p++)
            if (regexec(*p, linbf, 2))
                stackop = nval(expand(1, *p, stackvals[p - stackops]));

        if (regexec(retpatt, linbf, 3)) {
            occ->flags |= FLGRET;
	    if (debug['e'])
		printf("a return insn\n");
            goto classed;               /* rets aren't jumps or calls */
            }

        for (p = badlist; *p; p++)      /* mark instruction if bad */
            if (regexec(*p, linbf, 4)) {
                occ->flags |= FLGBAD;
		if (debug['e'])
		    printf("an unoptimizable insn\n");
                }

	if (anymatch(linbf, callpatts, ncallpatts) != -1) {
	    occ->flags |= FLGCALL;
            if (debug['e'])
               printf("a call insn\n");
            }

        for (p = jumps; *p; p++)
            {
            if (regexec(*p, linbf, 5))
                {
		char *ll;
                if (debug['e']) printf("jump %d ", p - jumps);
		ll = newstr(linbf);		/* make a copy */

		/*	extract label & install it */
                lin = install(expand(2, *p, "\\1"));       /* get the label */
		if (debug['e']) printf("to %s ", LINTOTEXT(lin));
                occ->refchn = lin->refchn;  /* link occ onto refchn */
                lin->refchn = occ;
                occ->label = lin;           /* point to it from  occ */
                ckrefs(occ);                /* validate refchn */

		/*	Turn the label part of the jump into \1 */
		strcpy((*p)->startp[1], "\\1");
		strcpy((*p)->startp[1] + 2, ll + ((*p)->endp[1] - linbf));

                for (p = ujumps; *p; p++)
                    if (regexec(*p, ll, 6))
                        {
                        if (debug['e']) printf("Unconditional ");
                        occ->flags |= FLGUJUMP;
                        break;
                        }
		free(ll);
                break;
                }
            }
        }
classed:
    lin = install(linbf);           /* install line in lines list */
    occ->linpt = lin;               /* point to our line from occurrence */
    insertocc(pocc, occ);           /* link occurrence onto sequential list */

    /*  Link occ into lin's equivalence chain */
    if (lin->eqchn == NULL) {
        occ->eqnext = occ->eqprior = lin->eqchn = occ;
        }
    else {
        occ->eqnext = lin->eqchn;
        occ->eqprior = lin->eqchn->eqprior;
        occ->eqnext->eqprior = occ->eqprior->eqnext = occ;
        lin->eqchn = occ;
        }

    lin->usecount++;                /* # of uses of this unique line */
    lin->stackop = stackop;

    /*  link label field to self if label.  this is how we tell. */
    if (s) occ->label = occ->linpt;

    noccs++;                        /* count an occurrence */
    if (debug['e']) printf("\n");
    return occ;
    }

/*  Insert a label in between this statement and its predeccessor, if
 *  there's not already one here.
 *  returns: the occ pointer to the label.
 *      labf contains the label sans colon.
 */
OCC *forcelabel(occ)
    OCC *occ;
    {
    if (islabel(occ->seqprior)) occ = occ->seqprior;
    if (islabel(occ))
        {
        if (debug['m']) printf("occ already has label %s\n", OCCTOTEXT(occ));
        strcpy(labf, OCCTOTEXT(occ));
        return occ;
        }
    else    {
        if (debug['m']) printf("new label l%d\n", nextlab);
        sprintf(labf, labgfmt, nextlab++);
        return entocc(labf, occ->seqprior, __LINE__);
        }
    }


/*  regenerate instruction with label for printing */
char *spellop(occ)
    register OCC *occ;
    {
    static char bf[64];

    if (isxfer(occ))
        {
        LIN *lin = occ->linpt;
        if (lin->regcomp == NULL) {
            lin->regcomp = regcomp(OCCTOTEXT(occ));
        }
	lin->regcomp->startp[1] = LINTOTEXT(occ->label);
	lin->regcomp->endp[1] = lin->regcomp->startp[1] + strlen(lin->regcomp->startp[1]);
	regsub(lin->regcomp, OCCTOTEXT(occ), bf);
	return bf;
        }
    else    if (islabel(occ)) sprintf(bf, labfmt, OCCTOTEXT(occ));
    else return OCCTOTEXT(occ);
    return bf;
    }

/*  skip over a label & return the instruction */   
OCC *thisop(occ)
    OCC *occ;
    {
    if (islabel(occ)) occ = occ->seqnext;
    if (occ == &occhead) occ = NULL;
    return occ;
    }

/*  return next op or NULL if this is the last one in the buffer */
OCC *nextop(occ)
    OCC *occ;
    {
    occ = occ->seqnext;
    if (occ == &occhead) return NULL;
    return thisop(occ);
    }


/*  occ points to a label.  equate adjacent labels & delete them */
/*  return a pointer to the sole remaining label */
OCC *equate(occ)
    OCC *occ;
    {
    char *s;
    OCC *loser, *fixocc;
    LIN *target, *p;
    static regexp *prog;
    if (!prog) prog = regcomp("abc");

recurse:
    if (islabel(occ->seqprior)) loser = occ->seqprior;
    else if (islabel(occ->seqnext)) loser = occ->seqnext;
    else return occ;

    /*  for each reference on this chain of references */
    target = occ->linpt;                /* jump target label */
    fixocc = loser->label->refchn;      /* point to 1st jump */
    while (fixocc)
        {
        if (debug['m']) printf("fixing %s ", spellop(fixocc));
        fixocc->label = target;         /* fix this jump */
        if (debug['m']) printf("to %s\n", spellop(fixocc));
        if (fixocc->refchn == NULL)     /* if no more to fix */
            {
            fixocc->refchn = target->refchn;    /* join chains */
            target->refchn = loser->label->refchn;
            ckrefs(target->refchn);     /* validate new refchn */
            break;
            }
        else    fixocc = fixocc->refchn;
        }

    /*  generate an equate for the loser.  We use pattern expansion
     *  so as to be able to generate the labels in either order.
     */
    prog->startp[1] = OCCTOTEXT(loser);
    prog->endp[1] = prog->startp[1] + strlen(prog->startp[1]);
    prog->startp[2] = OCCTOTEXT(occ);
    prog->endp[2] = prog->startp[2] + strlen(prog->startp[2]);
    s = expand(3, prog, equatefmt);

    p = (LIN *)alloc(sizeof(LIN) + strlen(s) + 1);
    strcpy((char *)(p + 1), s);
    p->next = equatelist;
    equatelist = p;

    /*  remove the losing label from the program buffer */
    outsertocc(loser);

    /*  and equate it to the target */
    goto recurse;
    }


/*  evaluate the savings for this sequence
 *  problems with getting a good evaluation:
 *  As I only get one copy of the sequence back, I can't tell where
 *  the labels are in all the sequences.  Hence some or all of the
 *  sequences may be invalid.  For purposes of costing, I assume that
 *  labels don't matter.  This could result in compressing things that
 *  shouldn't be.
 * 
 *  reduced by dividing by the number of elements in the parent,
 *  and my parent will be declared "nested" and may need re-evaluation.
 *  If this embeds other sequences my length is reduced by
 *  the total length of the sequences embedded minus the
 *  call overhead, and I'm declared "nested".
 *
 *  If subcost[1] is defined, we need to charge extra if a) this subroutine
 *  contains calls, b) this subroutine will be called from a subroutine
 *  which does not currently contain calls.
 */
eval(subseq)
    register SUBSEQ *subseq;
    {
    register struct ent *parent, *parent2;
    int result;
    int first, last, s1;
    register int n, l;
    struct ent *ents;
    int i;

    /*  Check to see if we're inside an existing definition */
    ents = subseq->ents;
    n = 500;            /* fudge 'cause we use integer arithmetic */ 

    /*  Count number of elements adjusting for elements that would
     *  be eliminated due to us being contained in defs that we're already
     *  doing
     */
    for (s1 = 0; s1 < subseq->nelts; s1++)
        {
        i = ents[s1].lineno;                    /* first line # in element */
        parent = &(occlist[i]->ent);            /* point to instruction */
        if ((THREADED || nonest) && parent->parent) return -1;
        if (debug['v']) printf("eval from %d nelts %d parent %d\n",
            i, subseq->nelts, parent);

        while (1)
            { 
            parent2 = parent->parent;           /* container of container */
            if (!parent2 || parent2->subseq->seqlen > subseq->seqlen)
                {
                n += 1000 / (parent2 ? parent2->subseq->effnelts : 1); 
                break;
                }
            parent = parent2;
            }
        }

    n /= 1000;

    /*  Count length adjusting for sequences contained in us */
    first = ents[0].lineno;
    last = first + subseq->seqlen - 1;
    l = 0;
    for (i = first; i <= last;)
        {
	if (iscall(occlist[i])) subseq->nested = 1;
        parent = &(occlist[i]->ent);            /* point to instruction */
        if (debug['v']) printf("eval length from %d to %d parent %d\n",
            first, last, parent);
        while (1)
            { 
            parent2 = parent->parent;           /* container of container */
            if (!parent2 || parent2->subseq->seqlen > subseq->seqlen)
                {
                /*  Parent2 contains us, we contain parent */
                if (parent == &(occlist[i]->ent)) {
                    if (debug['v']) printf("%d won't start anything\n", i);
                    if (occlist[i]->relabel != 1) l++;
                    i++;
                    }
                else {
                    if (debug['v'])
                        printf("%d will start seq from %d to %d\n",
                            i, parent->lineno,
                            parent->lineno + parent->subseq->seqlen - 1);
                    if (THREADED || nonest) return -1;
                    i = parent->lineno + parent->subseq->seqlen;
                    l += callcost[parent->subseq->nested];    /* charge call */
                    }

                break;
                }
            parent = parent2;
            }
        }

    subseq->efflen = l;
    subseq->effnelts = n;
    result = (n - !(THREADED || ICOUNT)) * (l - callcost[subseq->nested]);
    if (debug['v']) printf("eval: n %d adjusted %d l %d adjusted %d val %d\n",
        subseq->nelts, n, subseq->seqlen, l, result);
    subseq->val = result;
    return result;
    }


/*  Take delivery of one of a bunch of subroutines from the suffix algorithm */
sopen(nelts, len)
    int nelts, len;
    {
    nsubs = 0;
    subseq = 
        (SUBSEQ *)alloc(sizeof(SUBSEQ) + (nelts - 1) * sizeof(subseq->ents[0]));
    subseq->nelts = nelts;
    subseq->seqlen = len;
    }

/*  this called once for each subroutine optimized */
swrite(p)
    int p;
    {
    subseq->ents[nsubs].subseq = subseq;    /* each elt points to subseq */
    subseq->ents[nsubs++].lineno = p;
    }

/*  Used to qsort the elements in a sequence by first line number */
compar(s1, s2)
    struct ent *s1, *s2;
    {
    return s1->lineno - s2->lineno;
    }

/*  sclose() */
sclose()
    {
    int val, j, i, k;
    OCC *occ;

    qsort(subseq->ents, subseq->nelts, sizeof(subseq->ents[0]), compar);

    /*  Divide sequences containing weird instructions */
    for (i = 0; i < subseq->seqlen; i++)
        {
        occ = occlist[subseq->ents[0].lineno + i];
        for (j = 0; j < nbads; j++)
            {
            if (regexec(badlist[j], spellop(occ), 7))
                {       
                /*  construct a sequence representing the front of
                 *  this sequence, before the bad instruction
                 */
                SUBSEQ *newseq;
                newseq = dupseq(subseq);
                newseq->seqlen = i;
                val = eval(newseq);
                if (val > 0) pqinsert(newseq, val);
                else free(newseq);

                /*  Make the current sequence represent the end of
                 *  itself, after the bad instruction
                 */
                subseq->seqlen -= i + 1;
                for (k = 0; k < subseq->nelts; k++)
                    subseq->ents[k].lineno += i + 1;
                break;
                }
            }
        }

    val = eval(subseq);
    if (val > 0) pqinsert(subseq, val);
    else free(subseq);
    }

/*  Do cross-jumping */
static void docj(subseq)
    SUBSEQ *subseq;
    {
    int j, writelt;
    int s2;
    struct ent *ents;
    OCC *last2, *first2, *first1;

    if (debug['j']) debseq(subseq, "docj");

    writelt = 0;
    ents = subseq->ents;

    /*  Remove lost sequences from the vector */
    for (s2 = 0; s2 < subseq->nelts; s2++)
	{
	for (j = 0; j < subseq->seqlen; j++)
	    if (occlist[ents[s2].lineno + j]->flags & FLGGONE)
		{
		delent(subseq, s2);
		s2--;
		break;
		}
	}

    /*  Did all elements get deleted? */
    if (subseq->nelts <= 1) {
        return;
        }

    /*  Use an element that ends in jmp .+1 if there is one */
    for (s2 = 0; s2 < subseq->nelts; s2++)
        {
        if (occlist[ents[s2].lineno + subseq->seqlen - 1]->relabel == 1)
            {
            writelt = s2;
            break;
            }
        }

    first1 = occlist[ents[writelt].lineno];     /* first */

    /*  perform cj on these sequences */
    for (s2 = 0; s2 < subseq->nelts; s2++)
        {
        if (s2 != writelt)
            {
            OCC *occ1;

            /*  get last instruction of next sequence */
            first2 = occlist[ents[s2].lineno];
            last2 = occlist[ents[s2].lineno + subseq->seqlen - 1]; 

            /*  Sequences of identical statements ending in
             *  jumps to the same label are changed.  One of
             *  the sequences is replaced by a jump into the
             *  other sequence.  Labels are unionized.
             */
            forcelabel(first1);                 /* insert label in first */
            sprintf(linbf, jumpfmt, labf);      /* build jump in buffer */ 
            if (debug['j']) printf("inserting %s into sequence 2\n", linbf);
            last2 = entocc(linbf, last2, __LINE__);       /* put in first */

            /*  remove the instructions in sequence 2 and
             *  shuffle the labels into sequence 1.
             */
            occ1 = first1;
            while (first2 != last2)
                {
                OCC *occ;

                /*      if it's a label, insert in first */
                /*      & then equate it to whatever's there */
                if (islabel(first2))
                    {
                    if (debug['j'])
                        printf("moving %s from seq 2 to 1\n", spellop(first2));
                    occ = outsertocc(first2);
                    insertocc(occ1->seqprior, first2);
                    equate(occ1->seqprior);
                    first2 = occ;       /* point to next occ2 */
                    }
                else {
                    if (debug['j'])
                        printf("removing %s from seq 2\n", spellop(first2));
                    first2 = freeocc(first2);
                    /*  skip over labels in sequence 1 */
                    occ1 = nextop(occ1);
                    }
                }
            }
        }
    }

/*  dump seq for statistical analysis */
dumpseq(subseq, elt)
    int elt;
    SUBSEQ *subseq;
    {
    struct ent *ents;
    OCC *occ, *last1, *first1;
    int dolabel = 0;
    ents = subseq->ents;
    last1 = occlist[ents[elt].lineno + subseq->seqlen - 1];  /* last */
    first1 = occlist[ents[elt].lineno];             /* first */
    printf("l %d n %d %d v %d r %d\n",
            subseq->seqlen, subseq->nelts, subseq->effnelts,
            (subseq->seqlen-1)*(subseq->effnelts-1)-2,
            subseq->nelts*subseq->seqlen, spellop(last1));

    for (occ = first1;; occ = occ->seqnext)
        {
        if (!isxfer(occ) || occ->relabel != 1)
            {
            printf("%s\n", spellop(occ));
            if (isxfer(occ) &&
                occ->label->eqchn->ent.lineno == ents[elt].lineno+subseq->seqlen)
                    dolabel = 1;
            }
        if (occ == last1) break;
        }

    /*  print the final label if referenced within the sequence */
    if (dolabel) printf("%s\n", spellop(occ->seqnext));
    printf("\n");
    }

debseq(subseq,msg)
    SUBSEQ *subseq;
    char *msg;
    {
    OCC *occ, *last1, *first1;
    struct ent *ents;
    int i;
    int dolabel = 0;
    if (debug['q'])
        {
        printf("%s: len %d nelts %d val %d ",
            msg,subseq->seqlen, subseq->nelts, subseq->val);
        ents = subseq->ents;
        last1 = occlist[ents[0].lineno + subseq->seqlen - 1];   /* last */
        first1 = occlist[ents[0].lineno];                       /* first */
        for (occ = first1;; occ = occ->seqnext)
            {
            printf("%s ", spellop(occ));
            if (isxfer(occ) &&
                occ->label->eqchn->ent.lineno == ents[0].lineno+subseq->seqlen)
                    dolabel = 1;
            if (occ == last1) break;
            }

        /*  print the final label if referenced within the sequence */
        if (dolabel) printf("%s ", spellop(occ->seqnext));
        printf("\nstarting at: ");
        for (i = 0; i < subseq->nelts; i++) printf("%d ", ents[i].lineno);
        printf("\n");
        }
    }

/*  Commit to writing this sequence */
/*  Insert it on score- and size-ordered queues, and into the
 *  container tree.
 */
insertseq(subseq)
    SUBSEQ *subseq;
    {
    int i, j;
    OCC *occ;
    SUBSEQ *sub;

    /*  insert on the score-ordered queue */
    subseq->worse = &seqhead;           /* nothing's worse than we are */
    subseq->better = seqhead.better;
    seqhead.better = subseq;            /* except for the header */
    subseq->better->worse = subseq;

    /*  insert on the size-ordered queue */
    for (sub = seqhead.bigger;; sub = sub->bigger)
        {
        if (sub->bigger->seqlen < sub->seqlen && sub->bigger != &seqhead)
            printf("insertseq: can't happen\n");

        if (subseq->seqlen < sub->seqlen || sub == &seqhead)
            {
            subseq->bigger = sub;
            subseq->smaller = sub->smaller;
            sub->smaller = subseq;
            subseq->smaller->bigger = subseq;
            break;
            }
        }

    /*  Insert into the container tree. Occurrences and elements of sequences
     *  contain pointers to the sequence elements that contain them
     */
    for (i = 0; i < subseq->nelts; i++)
        {
        struct ent *parent, *parent2;
        if (debug['i']) {
            printf("insert seq %d elt %d from %d to %d ",
                subseq, i, subseq->ents[i].lineno,
                subseq->ents[i].lineno + subseq->seqlen - 1);
            printf("len %d effl %d n %d effn %d val %d\n",
                subseq->seqlen, subseq->efflen, subseq->nelts,
                subseq->effnelts, subseq->val);
            }

        /*  for each instruction in this element */
        for (j = subseq->ents[i].lineno;
            j < subseq->ents[i].lineno + subseq->seqlen;)       
            {
            occ = occlist[j];
            parent = &(occ->ent);       /* get addr of our container ptr */
            while (1)
                {
                parent2 = parent->parent;       /* point to its container */
                if (!parent2 || parent2->subseq->seqlen > subseq->seqlen)
                    {
                    /*  parent2 will enclose us, we enclose parent */
		    if (parent2) parent2->subseq->nested = 1;
                    parent->parent = &(subseq->ents[i]);
                    subseq->ents[i].parent = parent2;

                    if (debug['i'])
                        {
                        if (!parent2) printf("not contained by anything\n");
                        else printf("contained by seq from %d to %d\n",
                            parent2->lineno,
                            parent2->lineno + parent2->subseq->seqlen - 1);

                        if (parent == &(occ->ent))
                            printf("contains instruction at %d\n", j);
                        else printf("contains seq from %d to %d\n",
                            parent->lineno,
                            parent->lineno + parent->subseq->seqlen - 1);
                        }

                    /*  advance instruction counter past the thing that
                     *  we enclose
                     */
                    if (parent == &(occ->ent)) j++;
                    else {
			j = parent->lineno + parent->subseq->seqlen;
			subseq->nested = 1;
			}
                    break;
                    }
                parent = parent2;
                }
            }
        }
    }

reevaluate(subseq)		/* re-evaluate this sequence to see	*/
    register SUBSEQ *subseq;	/* if it's still possibly worthwhile	*/
    {
    int val;
    val = eval(subseq);
    if (val > 0) pqinsert(subseq, val);
    else free(subseq);
    }   

decap(subseq, newlen)		/* discard the beginning of a sequence	*/
    SUBSEQ *subseq;
    int newlen;
    {
    int s2;
    struct ent *ents;
    ents = subseq->ents;
    for (s2 = 0; s2 < subseq->nelts; s2++)
        ents[s2].lineno += subseq->seqlen - newlen;
    subseq->seqlen = newlen;
    reevaluate(subseq);
    }

delent(subseq, s1)		/*  Discard one element of a sequence */
    SUBSEQ *subseq;
    int s1;
    {
    int i;
    subseq->nelts--;
    for (i = s1; i < subseq->nelts; i++)
        subseq->ents[i] = subseq->ents[i + 1];
    }

/*  This called after all the sequences have been found.  The idea here
 *  is that we repeatedly pick off the highest-valued node.  We examine
 *  it to see if it's value has decreased (it can't increase).  It can
 *  decrease due to internal overlap or external overlap, or because
 *  we have to carve out a properly nesting subsequence, or because 
 *  we have to carve out a sequence which satisfies morph.
 *  If we can do the sequence as is, we go ahead and do it.  Otherwise
 *  we carve it up, re-evaluate it, and insert it back into the
 *  priority queue (assuming its value is still > 0).
 */
doseqs()
    {
    int s1, s2;
    int val, shorter, newval;
    struct ent *ents;
    SUBSEQ *newseq;         /* new subsequences */

getnext:
    /*  get next sequence and it's value */
    while ((subseq = pqmax(&val)) && limit > 0)
        {
        if (debug['d'])
            printf("len %d i %d val %d\n", subseq->seqlen, subseq->nelts, val);

        if (debug['d']) debseq(subseq, "trying");
        ents = subseq->ents;
        shorter = 0;

        newval = eval(subseq);
        if (newval < val)
            {
            /*  value has dropped due to external forces */
            if (newval <= 0) free(subseq);
            else pqinsert(subseq, newval);
            goto getnext;
            }

        /*  Check to see if this definition overlaps a committed definition
         *  (external overlap).
         */
        for (s1 = 0; s1 < subseq->nelts; s1++)  /* for each frag */
            {
            struct ent *lpar, *rpar, *lkid, *rkid;
            int first, last;

            first = ents[s1].lineno;
            last = ents[s1].lineno + subseq->seqlen - 1;

            /*  get immediate container and containee of first instruction */
            rkid = &(occlist[last]->ent);       /* point to instruction */
            while (1) { 
                rpar = rkid->parent;            /* container of container */
                if (!rpar || rpar->subseq->seqlen >= subseq->seqlen) break;
                rkid = rpar;
                }

            /*  similarly for last instruction */
            lkid = &(occlist[first]->ent);      /* point to instruction */
            while (1) { 
                lpar = lkid->parent;            /* container of container */
                if (!lpar || lpar->subseq->seqlen >= subseq->seqlen) break;
                lkid = lpar;
                }

            /*  reject if overlaps improperly */
            if (rpar != lpar || lkid->lineno < first ||
                rkid->subseq && rkid->lineno + rkid->subseq->seqlen - 1 > last)
                {
                if (debug['d']) printf("reject for external overlap\n");
                delent(subseq, s1);
                shorter = 1;
                s1--;
                }

            /*  reject redundant sequences outright */
            else if (rpar && (rpar->lineno == first &&
                rpar->lineno + rpar->subseq->seqlen - 1 == last ||
                rpar->subseq->nelts == subseq->nelts))
                {
                if (debug['d']) printf("redundant seq rejected\n");
                free(subseq);
                goto getnext;
                }
            }

        if (debug['d']) printf("no external overlap\n");

        /*  Inspect sequence for "internal" overlaps.  For example
	 *  xyxyx contains two xyx's but they overlap.
	 */
        for (s1 = 0; s1 < subseq->nelts - 1;)
            {
            if (ents[s1].lineno + subseq->seqlen > ents[s1 + 1].lineno)
                {
                /*  Commented out code to shorten length
                if (subseq->seqlen >= 1 && !shorter) {
                    SUBSEQ *newseq;
                    newseq = dupseq(subseq);
                    newseq->seqlen = ents[s1 + 1].lineno - ents[s1].lineno;
                    reevaluate(newseq);
                    }
                */

                /*  There's an overlap here.  Carve out an offending
                 *  element.
                 */
                if (debug['d'])
                    printf("overlap between s%d and s%d\n", s1, s1 + 1);
                delent(subseq, s1 + 1);
                shorter = 1;
                }
            else s1++;
            }

        if (debug['d']) printf("no internal overlap\n");

        if (shorter) {
            reevaluate(subseq);
            goto getnext;
            }

        /*  compare each sequence & ensure that jumps are 
         *  relatively or absolutely equal 
         */
        for (s1 = 1; s1 < subseq->nelts; s1++)
            {
            OCC *occ;
            int i;
            for (i = 0; i < subseq->seqlen; i++)
                {
                occ = occlist[ents[s1].lineno + i];
                if (isxfer(occ) &&
                    occ->relabel != occlist[ents[0].lineno + i]->relabel &&
                    occ->label != occlist[ents[0].lineno + i]->label)
                    {
                    /*  lose one sequence and re-evaluate */
                    if (debug['d']) printf("non-corr reljumps\n");
                    delent(subseq, s1);
                    reevaluate(subseq);
                    goto getnext;
                    }
                }
            }

        if (debug['d']) printf("reljmps correspond\n");

        if (openfrag(subseq))
            {
            int last, first, i;
            OCC *occ;

            /*  back up the end to the last unconditional jump or return */
            if (subseq->seqlen > 0 &&
                (!isujump(occ = occlist[ents[0].lineno + subseq->seqlen - 1])) &&
                !isret(occ))
                {  
                subseq->seqlen--;
                if (debug['j']) debseq(subseq, "shortening openfrag");
                reevaluate(subseq);
                goto getnext;
                }

            /*  Check for relatively-matched jumps out of the sequence */
            /*  Jumps out of the sequence must match absolutely */
            first = ents[0].lineno;
            last = first + subseq->seqlen - 1;
            for (i = 0; i < subseq->seqlen; i++)
                {
                occ = occlist[ents[0].lineno + i];
                if (isxfer(occ) && !iscall(occ))
                    {
                    int lineno;
                    if (debug['j']) printf("\ttransfers \n");

                    if (occ->label->eqchn == NULL) {
                        printf("occ->label->eqchn == null!\n");
                        printf("%s\n", spellop(occ));
                        printf("Probably a jump to an undefined label\n");
                        exit(-1);
                        }

                    lineno = occ->label->eqchn->ent.lineno; /* lineno */

                    if ((lineno > last || lineno < first) &&
                        occlist[ents[0].lineno + i]->relabel ==
                                occlist[ents[1].lineno + i]->relabel)
                        {
                        /*  kill relatively-matching jumps out of the seq */
                        if (debug['j']) printf("kill outside relatives\n");
                        subseq->seqlen = i - first;
                        reevaluate(subseq);
                        goto getnext;
                        }
                    }
                }
            }
        else {
            /*  The sequence was originally evaluated assuming we would
             *  be doing CJ cause that pays better.  If we must do PA
             *  we must now re-evaluate things & possibly not do the
             *  mung.  If we have already re-evaluated the sequence for
             *  PA then we are all set.
             */
            int newval;
            if (debug['d']) printf("closed fragment\n");
            newval = eval(subseq);              /* re-evaluate */
            if (newval == val && !ICOUNT && !THREADED)  /* value supplied was for CJ */
                {
                val -= callcost[0] + subcost[subseq->nested];
                if (val > 0) pqinsert(subseq, val);
                else free(subseq);
                goto getnext;
                }

            /*  check for proper stack nesting */
            if (debug['d'])
                printf("ents[0].lineno %d subseq %d subseq->seqlen %d\n",
                    ents[0].lineno, subseq, subseq->seqlen);

            seqlen = nests(ents[0].lineno, ents[0].lineno + subseq->seqlen - 1);
            if (seqlen != subseq->seqlen)
                {
                if (debug['d']) printf("nesting shortened us to %d\n", seqlen);

                /*  re-insert shortened sequence */
                newseq = dupseq(subseq);
                decap(subseq, seqlen);                  /* throw away head */
                newseq->seqlen -= seqlen + !seqlen;     /* keep head */
                while (newseq->seqlen > 0 &&
                    nests(ents[0].lineno,
                        ents[0].lineno + newseq->seqlen - 1) == 0)
                    newseq->seqlen--; 

                reevaluate(newseq);
                goto getnext;
                }

            /*  check for jumps into the fragment */
            for (s2 = 0; s2 < subseq->nelts; s2++)
                {
                seqlen = morph(ents[s2].lineno,
                    ents[s2].lineno + subseq->seqlen - 1);

                if (seqlen != subseq->seqlen)
                    {
                    if (debug['d']) printf("morph shortened to %d\n", seqlen);
                    newseq = dupseq(subseq);            /* duplicate */
                    decap(subseq, seqlen);              /* throw away head */
                    newseq->seqlen -= seqlen + !seqlen; /* keep head */
                    reevaluate(newseq);
                    goto getnext;
                    }
                }

            if (debug['d']) printf("morph passed\n");
            }

        /*  enter this sequence on the list of committed subroutines */
        insertseq(subseq);
        if (debug['d']) debseq(subseq, "inserting");
        limit--;
        }

    for (newseq = seqhead.worse; newseq != &seqhead; newseq = newseq->worse)
        {
        if (debug['d']) debseq(newseq, "remaining");
        }
    }

/*  Make the committed sequences into subroutines */
static makesubrs()
    {
    /*  get the longest sequence */
    /*  turn it into a subroutine by:
     *      1) forcing a label at its start
     *      2) if closed, forcing a return at its end
     *          this may involve moving it to the end of the buffer
     *      3) changing other occurrences into calls
     *
     *  Also handle nested calls where they need special handling.
     */
    int i, s1, writelt, elt;
    SUBSEQ *subseq;
    OCC *first, *last, *callpoint, *entry;
    struct ent *ents;


    /*  for each sequence from largest to smallest */
    for (subseq = seqhead.smaller; subseq != &seqhead; subseq = subseq->smaller)
        {
        ents = subseq->ents;

        /*  subseq points to the thing we are going to do next.
         *  Our next job is to find a good place to write this
         *  If this is an open fragment we try to find a copy
         *  ending in jmp .+1.  If it's closed we try to find
         *  a copy that's followed by a return.  Otherwise we
         *  have to move closed fragments to the end of the
         *  program and turn every use into a call.
         */
        writelt = elt = -1;
        if (openfrag(subseq))
            {
            if (!debug['c']) docj(subseq);
            }
        else if (!debug['p']) {
            int j;
            /*  Search for an element that's followed by a return */
            for (i = 0; i < subseq->nelts; i++) {
                j = subseq->ents[i].lineno;
                if ((occlist[j]->flags & FLGGONE) == 0)
                    {
                    entry = first = occlist[j];
                    elt = i;
                    if (!entseq[subseq->nested] && isret(nextop(occlist[j +
                        subseq->seqlen - 1]))) 
                        {
                        writelt = elt;
                        break;
                        }
                    }
                }

            /*  If we couldn't find any in-place candidates */
            if (writelt == -1)
                {
                /*  move any seq to end of the program and insert a return */
                writelt = elt;
                if (elt == -1) {
                    continue;               /* Every member of this seq has been deleted */
                    }
                if (ICOUNT) dumpseq(subseq, elt);
                first = occlist[ents[elt].lineno];
                last = occlist[ents[elt].lineno + subseq->seqlen - 1];
                callpoint = first->seqprior;            /* remember where */

                /*  clip this sequence from the buffer */
                first->seqprior->seqnext = last->seqnext;
                last->seqnext->seqprior = first->seqprior;

                if (debug['u']) printf("moving last to beginning of program\n");

                /*  and insert it at the end of the program */
                last->seqnext = &occhead;
                first->seqprior = occhead.seqprior;
                occhead.seqprior = last;
                first->seqprior->seqnext = first;
                
                /*  insert exit sequence after the last instruction */
                if (debug['u']) printf("return inserted\n");
                entocc(exitseq[subseq->nested], last, __LINE__);

		/*  insert entry code if needed */
		entry = first;
		if (entseq[subseq->nested]) {
		    if (debug['u']) printf("inserting entry code\n");
		    entocc(entseq[subseq->nested], first->seqprior, __LINE__);
		    entry = first->seqprior;
		    }

                /*  check for jumps to end of sequence and
                 *  replace them by jumps to the return op.
                 */
                for (i = 0; i < subseq->seqlen; i++)
                    {
                    OCC *occ;
                    occ = occlist[ents[elt].lineno + i]; /* point to occ */
                    if (isxfer(occ) && occ->label->eqchn &&
                        occ->label->eqchn->ent.lineno ==
                                ents[elt].lineno+subseq->seqlen)
                        {
                        OCC *newocc;
                        char *occtext;
                        regexp **p;

                        /*  this is a transfer off the end of the fragment
                         *  insert a label in front of the return and
                         *  jump to that label instead.
                         */
                        forcelabel(last->seqnext);
                        occtext = spellop(occ);     /* spell it */
                        if (debug['u'])
			    printf("'%s' transfer off end\n", occtext);

                        /*  find the jump pattern matched, build an instruction
                         *  using that pattern and the new label
                         */
                        for (p = jumps; *p; p++)
                            {
                            if (regexec(*p, occtext, 8))
                                {
                                char bf[512];
				if (debug['u'])
				printf("matched %d bras %d brae %d occ %d\n",
				    p - jumps, (*p)->startp[1], (*p)->endp[1],
				    occtext);
                                strncpy(bf, occtext, (*p)->startp[1] - occtext);
				bf[(*p)->startp[1] - occtext] = 0;
                                strcat(bf, labf);
                                strcat(bf, (*p)->endp[1]);
                                newocc = entocc(bf, occ, __LINE__);
				newocc->relabel = occ->relabel;
                                freeocc(occ);       /* remove old */
				occlist[ents[elt].lineno + i] = newocc;
				goto jok;
				}
			    }
                        /*      op was a jump but didn't match any pattern */
                        printf("fixjumps: can't happen\n");
                        }
jok:		    ;

		    /*  Check for jumps to the beginning of the sequence and
		     *  change them to point to the new label.  The old one
		     *  didn't get moved.
		     */
		    if (isxfer(occ) && occ->label->eqchn &&
			occ->label->eqchn->ent.lineno == ents[elt].lineno)
			{
			OCC *newocc;
			char *occtext;
			regexp **p;

			/*  This is a transfer to the beginning of the
			 *  fragment.  Jump to the point following the
			 *  entry sequence.
			 */
			occtext = spellop(occ);     /* spell it */
			if (debug['u']) printf("%s jumps to beginning\n", occtext);
			forcelabel(first);

			/*  find the jump pattern matched, build an instruction
			 *  using that pattern and the new label
			 */
			for (p = jumps; *p; p++)
			    {
			    if (regexec(*p, occtext, 9))
				{
				char bf[512];
				strncpy(bf, occtext, (*p)->startp[1] - occtext);
				bf[(*p)->startp[1] - occtext] = 0;
				strcat(bf, labf);
				strcat(bf, (*p)->endp[1]);
				newocc = entocc(bf, occ, __LINE__);
				newocc->relabel = occ->relabel;
				freeocc(occ);       /* remove old */
				occlist[ents[elt].lineno + i] = newocc;
				goto bjok;
				}
			    }
			/*      op was a jump but didn't match any pattern */
			printf("fixjumps: can't happen\n");
			}
    bjok:		;
                    }

                /*  insert a label at the beginning of the fragment */
                forcelabel(entry);
		sprintf(linbf, callfmt, labf);
		entocc(linbf, callpoint, __LINE__);               /* insert call */
                }

	    subseq->val = writelt;			/* abuse me */

            /*  Now rewrite the bodies as calls */
            for (s1 = 0; s1 < subseq->nelts; s1++)
                {
                OCC *occ, *nextocc;
                if (s1 != writelt &&
                    (!(occlist[ents[s1].lineno]->flags & FLGGONE)))
                    {
                    forcelabel(entry);

                    /*  point to next occ beyond this fragment */
                    nextocc =
                        occlist[ents[s1].lineno + subseq->seqlen - 1]->seqnext;
                    /*  delete everything up to there */

                    for (occ = occlist[ents[s1].lineno]; occ != nextocc;
                        occ = freeocc(occ))
                        ;

                    /*  If this body is followed by a return, just jump to
                     *  the beginning of the subroutine.  This effectively
                     *  eliminates tail recursion.
                     */
                    if (isret(occ)) {
                        occ = freeocc(occ);
                        sprintf(linbf, jumpfmt, labf);
                        }
                    else sprintf(linbf, callfmt, labf);

                    entocc(linbf, occ->seqprior, __LINE__);
                    if (debug['u'])
                        printf("inserting call at line %d\n", occ->ent.lineno);
                    }
                }

            if (debug['b'])
                {
                printf("after pa move: <><><><><><><><><><><><><><><><><>\n");
                dumpbuf();
                }
            }
        }
    }


/*  "callcost" needs to precede "call" in this list cuz the matcher
 *  ignores extra stuff following a keyword, so as to accept
 *  "labels" or "label"
 */ 
static char *opnames[] = {
    " ",        "balance",      "ujump",        "callcost",     "callfmt",
    "return",   "cjump",        "flushend",     "flushbegin",   "flushfmt",
    "label",    "newlabel",     "jumpfmt",      "equatefmt",	"???",
    "call",     "subcost",      "badlist",      "flush",        "eatblanks",
    "endmark",	"labfmt",	"entry",	"nonest",	"equate",
    "nestreturn","nestentry",	"nestcallcost",	"nestsubcost",
    };

static lookop()
    {
    int i;
    for (i = 0; i < sizeof(opnames) / sizeof(opnames[0]); i++)
        if (!strncmp(linbf + 2, opnames[i], strlen(opnames[i]))) return i;
    fprintf(stderr, "bad descr line '%s'\n", linbf);
    exit(0);
    /* NOTREACHED */
    }

static dodesc(ac, av)
    unsigned ac;
    char **av;
    {
    FILE *descrfil;

    /*  read description file   */
    if (ac < 2)
        {
        fprintf(stderr, "cr descrfil\n");
        exit(1);
        }
    else    {
        descrfil = fopen(av[1], "r");
        if (!descrfil)
            {
            fprintf(stderr, "can't open %s\n", av[1]);
            exit(1);
            }
        }

    while (getl(descrfil))
        {
        char *p;
        static dstate;
        if (!strncmp(linbf, "%%", 2)) dstate = lookop();
        else {
            switch(dstate)
                {
                case 0: break;  /* comment */
                case 1:
                    p = index(linbf, ';');
                    if (!p) fprintf(stderr, "semicolon expected in stackop\n");
                    else *p = 0;
                    if (nstackops == sizeof(stackops) / sizeof(stackops[0]))
                        fprintf(stderr, "stackops table full\n");
                    else {
                        stackops[nstackops] = regcomp(linbf);
                        stackvals[nstackops] = newstr(p+1);
                        nstackops++;
                        }
                    break;

                /*      unconditional jumps */
                case 2:
                    if (nujumps == sizeof(ujumps) / sizeof(ujumps[0]))
                        fprintf(stderr, "ujumps table full\n");
                    else ujumps[nujumps++] = regcomp(linbf);
                    break;

                case 3:
		    /*	cost of a call statement */
                    callcost[0] = atoi(linbf);
                    break;
                    
                case 4:
		    /* format to use in construction of call statements */
		    /* suitable for use in printf */
                    callfmt = newstr(linbf); break;

                case 5:		/* %%return */
                    exitseq[0] = newstr(linbf);
                    retpatt = regcomp(exitseq[0]);
                    break;

                case 6:
                    if (njumps == sizeof(jumps) / sizeof(jumps[0]))
                        fprintf(stderr, "jumps table full\n");
                    else {
                        jumps[njumps] = regcomp(linbf);
                        njumps++;
                        }
                    break;

                case 7:
                    flushend = regcomp(linbf);
                    break;

                case 8:
                    flushbeg = regcomp(linbf);
                    break;

                case 9:
                    flushfmt = newstr(linbf);
                    break;

                case 10:
		    /*	pattern to match existing label */
		    /*	must contain \(xyz\) somewhere */
                    labpatt = regcomp(linbf);
                    break;

                case 11: /* format of new labels */
                    labgfmt = newstr(linbf);
                    break;

                case 12:
                    jumpfmt = newstr(linbf);
                    break;

                case 13:
                    equatefmt = newstr(linbf);
		    /* fprintf(stderr, "equatefmt %s\n", equatefmt); */
                    break;

                case 15:
                    if (ncallpatts == sizeof(callpatts) / sizeof(callpatts[0]))
                        fprintf(stderr, "callpatts table full\n");
                    else callpatts[ncallpatts++] = regcomp(linbf);
                    break;

                case 16:
                    subcost[0] = atoi(linbf); break;

                case 17:
                    if (nbads == sizeof(badlist) / sizeof(badlist[0]))
                        fprintf(stderr, "badlist full\n");
                    else badlist[nbads++] = regcomp(linbf); break;

                case 18:
                    if (nflushlines == sizeof(flushlines) / sizeof(flushlines[0]))
                        fprintf(stderr, "flushlines full\n");
                    else {
                        flushlines[nflushlines] = regcomp(linbf);
                        if (debug['o']) printf("global name %s\n",
                            flushlines[nflushlines]);
                        nflushlines++;
                        }
                    break;

                case 19:
                    eatblanks++;
                    if (debug['o']) printf("eating blanks");
                    break;

                case 20:
                    /* this gets stuck at end of program */
                    endmark = regcomp(linbf); break;

		case 21:
		    /* format to use in construction of new labels */
		    /* suitable for use in printf(labfmt, labeltext) */
                    labfmt = newstr(linbf); break;

		case 22:	/* %%entry */
                    entseq[0] = newstr(linbf); break;

		case 23:
		    nonest++; break;

		case 24:
		    equatepatt = regcomp(linbf); break;

		case 25:
		    /* nested exit sequence */
		    exitseq[1] = newstr(linbf); break;

		case 26:	/* %%nestentry */
		    entseq[1] = newstr(linbf); break;

		case 27:
		    callcost[1] = atoi(linbf); break;

		case 28:
		    subcost[1] = atoi(linbf); break;

                default:
                    fprintf(stderr, "bad description line %s\n", linbf);
                    break;
                }
            }
        }
    if (exitseq[1] == 0)
       exitseq[1] = exitseq[0];
    if (callcost[1] == 0)
       callcost[1] = callcost[0];
    if (subcost[1] == 0)
       subcost[1] = subcost[0];
    if (entseq[1] == 0)
       entseq[1] = entseq[0];
    }

/*  Find the longest sequence ending at last which contains only
 *  internal jumps
 */
static morph(first, last)
    int first, last;
    {
    int i;
    char *s;
    OCC *occ, *ptr1;

    if (debug['m']) printf("morph first %d last %d\n", first, last);

redo:for (i = last; i >= first; i--)
        {
        occ = occlist[i];       /* get occurrence pointer */
        s = spellop(occ);       /* get spelling of this occurrence */
        if (debug['m']) printf("morph: trying %d %s\n", i, s);

        /*  if this is a label make sure refs to it are internal */
        if (i != last && islabel(occ->seqnext))
            {
            occ = occ->seqnext;     /* get the label pointer */
            if (debug['m']) printf("\tsequence 1 is a label\n");

            /*  for each reference to this label */
            for (ptr1 = occ->label->refchn; ptr1; ptr1 = ptr1->refchn)
                {
                if (debug['m'])
                    printf("referenced from line %d\n", ptr1->ent.lineno);

                if (ptr1->ent.lineno > last || ptr1->ent.lineno < first)
                    {
                    if (debug['m']) printf("\t\twith external references\n");
carve:              first = i + 1;
                    goto redo;
                    }
                }
            if (debug['m']) printf("\t\twith no external references\n");
            }

        /*  check for transfers out of the fragment */
        else if (isxfer(occ) && !iscall(occ))
            {
            int lineno;
            if (debug['m']) printf("\ttransfers \n");
            lineno = occ->label->eqchn->ent.lineno; /* label's lineno */
            if (lineno > last + 1 || lineno < first) goto carve; 
            }
        }
    return last - first + 1;
    }

/*  determine if the given sequence contains ret or absolute
 *  matching jumps
 */
static openfrag(subseq)
    SUBSEQ *subseq;
    {
    int first1, last1;
    int i1, i2, s1;
    OCC *occ;
    struct ent *ents;

    ents = subseq->ents;
    first1 = ents[0].lineno;                        /* first */
    last1 = ents[0].lineno + subseq->seqlen - 1;   /* last */

    for (i1 = last1; i1 >= first1; i1--)
        {
        occ = occlist[i1];      /* get occurrence pointer */

        if (isret(occ)) return 1;       /* contains ret; is open */
        if (isxfer(occ) && !iscall(occ))
            {
            for (s1 = 1; s1 < subseq->nelts; s1++)
                {
                i2 = i1 - first1 + ents[s1].lineno;
                /* if contains absolute jumps */
                if (occ->label == occlist[i2]->label) return 1;
                }
            }
        }
    return 0;                   /* no absolute jumps or rets; closed */
    }

/*              cj                                  pa
 *  outside jumps can dive into sequence    they can't
 *  inside jumps can jump out of sequence   they can't
 *  labels which are morphic wrt jumps      see above; you can't
 *  in the sequence can be equated for      jump into the sequence
 *  purposes of jumps outside the sequence
 *
 *  labels at head of first instruction     labels behind last instiructo
 *  can be equated                          can be equated, too
 *  we don't need to check stack            we need to
 *  label at the end of a sequence can be   can't do this
 *  cross-jumped against a jump to label
 *  sequence must end in returns, jmps, or  sequence cannot contain return 
 *  jump & label                            it can end in (internal) jump
 *                                          or label referenced internally
 *                                          and externally.
 *  sequence must end in unconditional jump
 */


/*  Expand output buffer, given current bracket bindings */
static char *expand(from, prog, bf)
    int from;                           /* debugging line */
    struct regexp *prog;		/* the regular expression */
    register char *bf;			/* pattern to expand */
    {
    static char lbf[MAXLINE];
    if (debug['x']) printf("expand from %d %s = ", from, bf);
    regsub(prog, bf, lbf);
    if (debug['x']) printf(" = %s\n", lbf);
    return lbf;
    }

nval(string)
    char *string;
    {
    int val;
    sscanf(string, (*string == '0' || *string == '-' && *(string + 1) == '0') ?
        "%o" : "%d", &val);
    return val;
    }

/*  return the length of the longest stack-nested subsequence which
 *  ends at last
 */
nests(first, last)
    int first, last;
    {
    int i;
    int lastbal;
    int stacklev;
    OCC *occ;

    if (THREADED) return last - first + 1;

    lastbal = last + 1;         /* last balancing location */
    stacklev = 0;               /* current stack level */
    for (i = last; i >= first; i--)
        {
	int v;			/* value to use for balance debug */
        occ = occlist[i];       /* get occurrence pointer */

	/*  calculate indentation */
	v = stacklev;		/* assume use of old value */
        stacklev += occ->linpt->stackop;
	if (stacklev < v)  v = stacklev;	/* use new value */

	if (debug['n']) printf("%3d %*s%s\n", -v, -v, "", spellop(occ));

        /*  remember if we're balanced */
        if (stacklev == 0) lastbal = i;
        else if (stacklev > 0) break;
        }
    return last - lastbal + 1;
    }

/*  construct the vector of occurrence pointers used by suffix tree alg */
static mkvec()
    {
    occlist = (OCC **)alloc((noccs + 1) * sizeof(occlist[0]));
    occsz = 0;
    for (last1 = occhead.seqnext; last1 != &occhead; last1 = last1->seqnext) 
        {
        last1->ent.lineno = occsz;      /* save index into occlist */
        if (!islabel(last1)) 
            {
            occlist[occsz] = last1;
            occsz++;
            last1->relabel = 0;         /* relative jump displacement */
            }
        }
    occlist[occsz] = 0;

    /*  set relabel fields to the relative jump displacement */
    for (last1 = occhead.seqprior; last1 != &occhead; last1 = last1->seqprior)
        {
        static absurd = 999999;
        if (isxfer(last1))
            {
            if (last1->label->eqchn == NULL) last1->relabel = absurd++;
            else last1->relabel =
                nextop(last1->label->eqchn)->ent.lineno - last1->ent.lineno;
            }
        }
    }

dumpbuf()
    {
    OCC *last1;

    /*  Output result file */
    for (last1 = occhead.seqnext; last1 != &occhead; last1 = last1->seqnext)
        {
        /* Skip relative jumps to .+1 */
        if (!isujump(last1) || last1->relabel != 1)
	    {
            printf("%s\n", spellop(last1));
	    }
        }
    if (endstmt) printf("%s\n", endstmt);
    }

anymatch(actual, patterns, npatts)	/* does actual match any of	*/
    char *actual;			/* the patterns?		*/
    regexp **patterns;
    int npatts;
    {
    int i;
    for (i = 0; i < npatts; i++)
        if (regexec(patterns[i], actual, 10)) return i;
    return -1;
    }

main(ac, av)
    unsigned ac;
    char **av;
    {
    LIN *lin;
    int   linecount = 0;

    if (ac > 2)
        {
        char *p;
        for (p = av[2]; *p; p++)
            {
            if ('0' <= *p && *p <= '9')
                {
                limit = atoi(p);
                fprintf(stderr, "limit to %d edits\n", limit);
                break;
                }
            debug[*p]++;            /* set debug flags */
            }
        }

    dodesc(ac, av);     /* read the machine description file */
    if (ICOUNT || THREADED) subcost[0] = callcost[0] = 0;

    /*  Read the assembly file.  To save space we pass through lines
     *  which will not be optimized.  This is:  everything in data
     *  segment and constants in text segment, and externs (public)
     *  declarations.  We insert jumps in front of labels, and insert
     *  non-labels into the occlist for gene to match against.
     */
    for (;;) {
        char *p, *s, *d;
        char newbf[512];

        if (!getl(stdin)) {
           printf("%d lines\n", linecount);
           break;
           }

        linecount++;
        p = linbf;

        /*  lose leading whitespace & fold intervening */
        if (eatblanks)
            {
            /*  strip out leading blanks from the line */
            while (*p == ' ' || *p == '\t') p++;
            s = p;                      /* source from stripped old buffer */
            d = p = newbf;              /* destination is new buffer */
nq:         while (*s != ' ' && *s != '\t')
                {
                *d++ = *s;              /* copy non-blank */
                if (*s == 0) goto done; /* done? */
                s++;                    /* next input char */
                }
            *d++ = ' ';                 /* add blank to output */
            while (*s == ' ' || *s == '\t') s++;
            goto nq;
            }

        /*  test for end of flush mode markers */
done:   if (regexec(flushend, p, 11)) {
            flushmode = 0;
            if (!ICOUNT) printf("%s\n", p);
            }

        /*  test for beginning of flush mode marker */
        else if (regexec(flushbeg, p, 12)) {
            flushmode = 1;
            if (!ICOUNT) printf("%s\n", p);
            }

        /*  flush the line itself if we are in flush mode
         *  (cause it might have blanks that were folded out)
         */
        else if (flushmode || anymatch(p, flushlines, nflushlines) != -1) 
            {
            if (!ICOUNT) printf("%s\n", linbf); 
            }

        /*  Remember if we see an END card */
        else if (endmark && regexec(endmark, p, 13))
            {
            endstmt = newstr(p);
            }

        else entocc(p, occhead.seqprior, __LINE__);    /* enter the line */
        }

    /*  Mark beginning of unflushed stuff */
    if (!ICOUNT && flushfmt) printf("%s\n", flushfmt);

    if (!debug['y'])
        {   
        /*  equate out adjacent labels & insert jump lx in front of lx:
         *  to unify cross-jumping case
         */
        for (last1 = occhead.seqprior;
            last1 != &occhead; last1 = last1->seqprior)
            {
            char bf[40];
            if (islabel(last1))
                {
                last1 = equate(last1);          /* delete adjacent labels */
                sprintf(bf, jumpfmt, OCCTOTEXT(last1)); /* make jump to this */
                entocc(bf, last1->seqprior, __LINE__);    /* insert in front */
                }
            }

        mkvec();                    /* make the vector of line pointers */
        if (ICOUNT || THREADED)     /* collect statistics */
            {
            int i;
            /*  make entries for singletons */
            for (i = 0; i < occsz; i++)
                {
                if (occlist[i]->linpt->usecount == 1)
                    {
                    sopen(1, 1);        /* make one occurrence of length one */
                    swrite(i);
                    sclose();
                    }
                }
            }
        mktree(occlist, noccs + 1); /* construct the postree and prioritize */
        doseqs();                   /* figure out the sequences */
        makesubrs();                /* construct subroutines */
        }

    if (!ICOUNT) dumpbuf();
    else {
        OCC *last1;
        for (last1 = occhead.seqnext; last1 != &occhead; last1 = last1->seqnext)
            {
            last1->linpt->effcount++;
            }

        for (last1 = occhead.seqnext; last1 != &occhead;
            last1 = last1->seqnext)
            {
            int count;
            if ((!isujump(last1) || last1->relabel != 1) && !iscall(last1) &&
                !islabel(last1) &&
                (last1->linpt->usecount == 1 || last1->linpt->effcount == 1))
                {
                count = last1->linpt->effcount;
                printf("l 1 n %d %d v %d r %d\n%s\n\n",
                        last1->linpt->usecount, count,
                        -2, last1->linpt->usecount, spellop(last1));
                }
            }
        }

    for (lin = equatelist; lin; lin = lin->next)
        {
        if (!ICOUNT) printf("%s\n", LINTOTEXT(lin));
        }
    }
