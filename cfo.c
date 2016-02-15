/* an older version of cr.c */

#include <stdio.h>
#include <ctype.h>
#include <sys/param.h>

#define max(a,b) ((a) > (b) ? (a) : (b))

static char debug = 0;

#define	NO		0
#define	YES		1
#define	FOREVER	for(;;)
#define	LBSIZE	128	
#define	TEXT		char
#define	RETOP	"rts pc"
#define	CALLOP	"jsr pc,"
#define	TEXTNAME	".text"
#define	DATANAME	".data"
#define	GLOBAL	".globl"
#define	FLDSEPS	" "			/* field separator */
#define	UJUMP	"jbr"
#define	MINPA	4 
#define	MINCJ	2			/* minimum cross-jumping match */
#define	OCCTOTEXT(occ) ((TEXT *)(occ->lin + 1))
#define	LINTOTEXT(lin) ((TEXT *)(lin + 1))
char *index();
static unsigned noccs = 0, nlins = 0;
static char linbf[LBSIZE] = 0;			/* line buffer */
static char labf[10] = 0;				/* label buffer */
static unsigned linno = 0;
static int matchlen = 0;
static unsigned nextlab = 1;
static TEXT **bp = 0;
static TEXT *percent[10] = 0;

static TEXT *bad[] = {
	".word",
	NULL
	};

static char *alloc(siz)
	unsigned siz;
	{
	char *malloc();
	char *r;
	r = malloc(siz);
	if (!r)
		{
		fprintf(stderr, "no memory noccs %d nlins %d\n", noccs, nlins);
		exit(NO);
		}
	return r;
	}

static int arg = 1;				/* argument counter for command line */

#define HASHSIZE 255			/* # of hash buckets */

/*	This program maintains two essential data structures:
 *	1) A list of lines in the buffer.  This list is doubly-linked
 *	   in sequential order and identical lines are linked together.
 *
 *	2) A "symbol table" of all the different lines which have been
 *	   encountered.  The text of the line is only stored once.
 *	   The symbol table entry contains pointers to the first and
 *	   last occurrences encountered, to aid in building the
 *	   equivalence classes.
 *	
 *	It would probably be better to chain all jumps and calls of
 *	a label together with the label.
 *
 */

/*	Unique lines */
typedef struct Lin {
	struct Occ *eqchn;			/* equivalent occurrences chain */
	struct Occ *refchn;			/* chain of all references to this label */
	struct Lin *next;			/* hash chain links */
	} LIN;

static LIN *heads[HASHSIZE] = 0;	/* hash buckets */

/*	Occurrences of lines */
typedef struct Occ {
	struct Occ *eqchn;			/* equivalence chain */
	struct Occ *refchn;			/* next ref to this label */
	struct Occ *seqnext, *seqprior;	/* sequential chain */
	struct Lin *label;			/* points to label if a transfer */
	struct Lin *lin;			/* our line */
	} OCC;

static OCC *oc1ptr = 0, *oc2ptr = 0;

/*	Line pointers to some known instructions	*/
static LIN *tstspp = 0;			/* tst (sp)+ */
static LIN *cmpspp = 0;			/* cmp (sp)+,(sp)+ */
static LIN *retop = 0;			/* return */

/*	static LIN *popaf = 0;		af<=sp
static LIN *hlpsp = 0;			hl+sp
static LIN *hltosp = 0;			hl->sp
static LIN *exchg = 0;			hl<>*sp
*/

static OCC *occavail = 0;		/* free occ list */

/*	The instruction occurrence list head */
static OCC occhead = {0, 0 , &occhead, &occhead};

/*	The list head for undefined labels */
static OCC looselabs = {0, 0, &looselabs, &looselabs};

getl(fil)
	FILE *fil;
	{
	char *p1;
	int c;
	p1 = linbf;

	/*	Read input line into linbf */
	do	{
		c = getc(fil);
		if (c == EOF)
			{
			return 0;
			}
		*(p1++) = c;
		if (p1 + 1 ==  linbf + sizeof(linbf))
			{
			printf("linbf overflow\n");
			break;
			}
		} while (c != '\n');

	p1--;
	*p1 = 0;
	if (p1 - linbf != strlen(linbf)) printf("botch getl\n");
	return p1 - linbf;
	}

unsigned hash(lin)
	TEXT *lin;
	{
	unsigned result;

	result = 0;
	while (*lin)
		{
		result = (result >> 1) ^ *lin++ ^ ((result & 1) << 15);
		}
	result %= HASHSIZE;

	/*	if (stats) collct[result]++;		 count collisions */
	return result;
	}

/*	Things that transfer control to labels */
static TEXT *jumps[] = {
	"jlt ", "jbr ", "jne ", "jeq ", "jge ", "jgt ",
	"jle ", "jpl ", "jmi ", "jhi ", "jsr pc,", "jmp ", NULL
	};

/*	decide if this instruction is a (possibly conditional) jump */
char isjump(occ)
	register OCC *occ;
	{
	register TEXT **p;
	if (occ == &occhead) return NO;
	for (p = &(jumps[0]); *p; p++) 
		if (!strcmp(OCCTOTEXT(occ), *p)) return YES;
	return NO;
	}

/*	decide if this is an unconditional jump */
char isujump(occ)
	OCC *occ;
	{
	if (occ == &occhead) return NO;
	return (!strcmp(OCCTOTEXT(occ), "jbr ") ||
		!strcmp(OCCTOTEXT(occ), "jmp "));
	}

#define islabel(occ) ((occ)->label->eqchn == (occ))
#define isret(occ) ((occ)->lin == retop)

/*	return the label occurrence pointed to by a xfer */
OCC *findlabel(occ)
	OCC *occ;
	{
	return occ->label->eqchn;
	}

/*	Decide if this is transfers control to a label via call or jump */
isxfer(occ)
	OCC	*occ;
	{
	return ((occ->label != NULL) && (!islabel(occ)));
	}

/*	decide if this is a call */
iscall(occ)
	OCC *occ;
	{
	return (!strcmp(OCCTOTEXT(occ), CALLOP));
	}

TEXT *spellop();

/*	validate refchain for this label */
ckrefs(occ)
	OCC *occ;
	{
	OCC *next;
	int	n;
	n = 0;
	for (next = (OCC *)(occ->label->refchn);
		next != occ; next = next->refchn)
		{
		if (!next) printf("ckrefs: %s not on refchn\n", spellop(occ));
		if (n++ > 10000)
				printf("ckrefs: %s refchn circular\n", spellop(occ));
		}
	}

/*	hash something & install it in the lines list if it's not already there */
LIN *install(bf)
	TEXT *bf;
	{
	unsigned h;			/* the hash value */
	LIN *p;

	h = hash(bf);			/* get hash value */
	for (p = heads[h]; p; p = p->next)
		{
		if (!strcmp(LINTOTEXT(p), bf))
			{
			/* if (debug)
			 * printf("%d: %s old\n", ++linno, (TEXT *)(p + 1)); */
			return p;
			}
		}

	/* Allocate new line for this */
	p = (LIN *)alloc(sizeof(LIN) + strlen(bf) + 1);

	strcpy((TEXT *)(p + 1), bf);

	/* if (debug) printf("%d: %s new\n", ++linno, (TEXT *)(p + 1)); */
	p->next = heads[h];
	heads[h] = p; 
	p->refchn = 0;
	p->eqchn = 0;
	nlins++;
	return p;
	}

/*	allocate an occurrence */
OCC *getocc()
	{
	OCC *occ;
	if (occavail == NULL)
		{
		char i;
		/*	Occs are allocated by the hundreds to save the overhead */
		occavail = (OCC *)alloc(100 * sizeof(OCC));
		for (i = 0; i < 99; i++)
			{
			occavail[i].seqnext = occavail + (i + 1);
			}
		occavail[99].seqnext = 0;
		}
	occ = occavail;
	occavail = occavail->seqnext;
	occ->lin = occ->label = NULL;
	occ->seqnext = occ->eqchn = occ->seqprior = occ->refchn = NULL;
	return occ;
	}

/*	link an occurrence onto the sequential list after pocc */
insertocc(pocc, occ)
	OCC *pocc, *occ;
	{
	occ->seqnext = pocc->seqnext;		/* this' next is prior's next */
	occ->seqprior = pocc;			/* this' prior is prior */
	pocc->seqnext = occ;			/* prior's next is this */
	occ->seqnext->seqprior = occ;		/* this' next's prior is this */
	}

/*	remove this occurrence from the seqlist */
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


/*	delete this occurrence from the buffer and return the next */
OCC *freeocc(occ)
	register OCC *occ;
	{
	register OCC *next, *prior;

	/* search the eqchn sequentially as it's not doubly-linked */
	/*	if (debug) printf("freeocc %s\n", spellop(occ)); */
	for (next = (OCC *)(occ->lin); next->eqchn != occ; next = next->eqchn)
		;
	next->eqchn = next->eqchn->eqchn;	/* delete from eqchn */

	/* search the refchn sequentially as it's not doubly-linked */
	if (debug) printf("freeocc %s\n", spellop(occ));
	if (isxfer(occ))
		{
		for (next = (OCC *)(occ->label);
			next->refchn != occ; next = next->refchn)
			;
		next->refchn = next->refchn->refchn;
		}

	next = outsertocc(occ);			/* delete from seqchn */	
	occ->seqnext = occavail; 		/* free this onto avail chain */
	occavail = occ;
	return next;					/* return next on seqchn */
	}

/*	Enter an occurrence of a line into the buffer to follow pocc */
OCC *entocc(linbf, pocc)
	OCC *pocc;			/* follows this occurrence */
	TEXT *linbf;			/* the register transfer itself */
	{
	OCC *occ;				/* the occurrence of this line */
	LIN *lin;				/* the unique entry for this line */
	TEXT *s;
	TEXT **p;

	/*	If this instruction is a transfer of control, we need to allocate
	 *	an occurrence for the destination label also, and enter it if it's
	 *	not already entered.
	 */
	/*
	if (debug) printf("entocc: linbf %s pocc %d\n", linbf, (int)pocc);
	*/
	occ = getocc();					/* get an occurrence */

	/*	test for a label, zap colon */
	s = index(linbf, ':');
	if (s && *(s + 1) == 0)
		{
		/*	if (debug) printf("a label\n");	*/
		*s = 0;
		}
	else	{
		s = NULL;

		for (p = &jumps[0]; *p; p++)
			{
			if (!strncmp(linbf, *p, strlen(*p)))
				{
				TEXT *ss;
				/*	if (debug) printf("a jump "); */
				ss = linbf + strlen(*p);		/* point to label */
				lin = install(ss);			/* put label in lines list */
				*ss = 0;					/* zap the label */
				occ->refchn = lin->refchn;	/* link occ onto refchn */
				lin->refchn = occ;
				occ->label = lin;			/* point to it from  occ */
				ckrefs(occ);				/* validate refchn */
				}
			}
		}

	lin = install(linbf);		/* install line in lines list */
	occ->lin = lin;			/* point to our line from occurrence */
	insertocc(pocc, occ);		/* link occurrence onto sequential list */
	occ->eqchn = lin->eqchn;		/* link occ onto eqchn off line */
	lin->eqchn = occ;

	/*	test for some special instructions */
	if (!strcmp(linbf, "tst (sp)+")) tstspp = occ->lin;
	if (!strcmp(linbf, "cmp (sp)+,(sp)+")) cmpspp = occ->lin;
	if (!strcmp(linbf, RETOP)) retop = occ->lin;

	/*	link label field to self if label.  this is how we tell. */
	if (s)
		{
		occ->label = occ->lin;
		}

	noccs++;					/* count an occurrence */
	return occ;
	}


/*	Insert a label in between this statement and it predeccessor, if
 *	there's not already one here.
 *	returns: the occ pointer to the label.
 *		labf contains the label sans colon.
 */
OCC *forcelabel(occ)
	OCC *occ;
	{
	if (islabel(occ->seqprior))
		{
		occ = occ->seqprior;
		}
	if (islabel(occ))
		{
		/* if (debug)
			printf("occ already has label %s\n", OCCTOTEXT(occ)); */
		sprintf(labf, "%s", OCCTOTEXT(occ));
		return occ;
		}
	else	{
		sprintf(labf, ".l%d:", nextlab++);
		return entocc(labf, occ->seqprior);
		}
	}
static char datamode;			/* reading data */
static OCC *oc1, *oc2, *oc1end, *oc2end;
static OCC *oc1insert, *oc2insert;
static char lastbal, stacklev, eatingaf;
static char retstat, maxstat, labstat;	/* ret following matches */
static int i;

/*	regenerate instruction with label for printing */
TEXT *spellop(occ)
	OCC *occ;
	{
	static TEXT bf[64];
	if (isxfer(occ))
		{
		sprintf(bf, "%s%s", OCCTOTEXT(occ), LINTOTEXT(occ->label));
		}
	else	if (islabel(occ)) sprintf(bf, "%s:", OCCTOTEXT(occ));
	else sprintf(bf, "%s", OCCTOTEXT(occ));
	return bf;
	}

/*	Check out the match for feasibility
 *	oc1ct, oc2ct = first occurrence,
 *	linct = # of match instructions (ex labels)
 *
 *	oc1, oc2 = last occurrence
 *
 *	If both sequences end in ujumps (unconditional jumps) to the same label
 *	or return instructions then we perform cross-jumping immediately.
 *	Otherwise we figure out how much of the sequence is amenable to
 *	procedural abstraction (pa).
 */
examine(oc1ct, oc2ct, oc1, oc2)
	register OCC *oc1ct, *oc2ct, *oc1, *oc2;
	{
	int strikes = 0;
	while (strikes != 3)
		{
		if (!(strikes & 1)) printf("%-25s", spellop(oc1ct));
		else printf("%-25s", "");
		if (!(strikes & 2)) printf("%-25s\n", spellop(oc2ct));
		else printf("\n");
		if (oc1ct == oc1) strikes |= 1;
		if (oc2ct == oc2) strikes |= 2;
		oc1ct = oc1ct -> seqnext;
		oc2ct = oc2ct -> seqnext;
		}
	}

#define	DONE	0		/* we've returned the last pair */
#define	NEW	1		/* we've returned done indication */
#define	INPR	2		/* in progress */
#define	thisop(occ) ((islabel(occ)) ? (occ)->seqnext : (occ))

OCC *nextop(occ)
	OCC *occ;
	{
	occ = occ->seqnext;
	return thisop(occ);
	}

/*	skip labels & find prior instruction */
OCC *priorop(occ)
	OCC *occ;
	{
	do	{
		occ = occ->seqprior;
		if (occ == &occhead) return NULL;
		} while (islabel(occ));
	return occ;
	}

/*	run through each pair of instructions */
/*	start and stop indicate the first & last items to be processed */
priors(stop1, stop2, pptr1, pptr2, start1, start2, status)
	register OCC **pptr1, **pptr2;
	OCC *start1, *start2, *stop1, *stop2;
	int *status;
	{
	int nlabels;

	nlabels = 0;
	if (*status == DONE)
		{
		*status = NEW;
		return NO;
		}

	if (*status == NEW)
		{
		*pptr1 = start1;
		*pptr2 = start2;

		/*	if start precedes stop give up before we begin */
		if (stop1->seqprior == start1 || stop2->seqprior == start2)
			return NO;
		*status = INPR;
		}
	else	{
		/*	if we have an unmatched label on one side, defer
		 *	backing up the other pointer.
		 */
		if (islabel((*pptr1)->seqprior))
			{
			if (*pptr1 != stop1) *pptr1 = (*pptr1)->seqprior;
			nlabels++;
			}

		if (islabel((*pptr2)->seqprior))
			{
			if (*pptr2 != stop2) *pptr2 = (*pptr2)->seqprior;
			nlabels++;
			}

		if (nlabels == 0)
			{
			if (*pptr1 != stop1) *pptr1 = (*pptr1)->seqprior;
			if (*pptr2 != stop2) *pptr2 = (*pptr2)->seqprior;
			}

		/*
		if (!(nlabels & 1))
			{
			if ((*pptr1 == stop1) != (*pptr2 == stop2))
				{
				printf("priors: sync error\n");
				examine(*pptr1, *pptr2, start1, start2);
				}
			}
		*/
		}

	if (*pptr1 == stop1 && *pptr2 == stop2) *status = DONE;
	return YES;
	}

/*	occ points to a label.  equate adjacent labels & delete them */
OCC *equate(occ)
	OCC *occ;
	{
	OCC *loser, *fixocc;
	LIN *target;
recurse:
	if (islabel(occ->seqprior))
		{
		loser = occ->seqprior;
		}
	else if (islabel(occ->seqnext))
		{
		loser = occ->seqnext;
		}
	else return occ;

	/*	for each reference on this chain of references */
	target = occ->lin;					/* jump target label */
	fixocc = loser->label->refchn;		/* point to 1st jump */
	while (fixocc)
		{
		/*	if (debug) printf("fixing %s ", spellop(fixocc));	*/
		fixocc->label = target;			/* fix this jump */
		/*	if (debug) printf("to %s\n", spellop(fixocc));	*/
		if (fixocc->refchn == NULL)		/* if no more to fix */
			{
			fixocc->refchn = target->refchn;	/* join chains */
			target->refchn = loser->label->refchn;
			ckrefs(target->refchn);		/* validate new refchn */
			break;
			}
		else	{
			fixocc = fixocc->refchn;
			}
		}

	/*	remove the now unused label */
	outsertocc(loser);

	/*	and equate it to the target */
	printf("%s=%s\n", OCCTOTEXT(loser), OCCTOTEXT(occ));
	goto recurse;
	}

/*	Do cross-jumping for each statement in the program */
/*	Sequences of identical statements ending in jumps to the
 *	same label are changed.  One of the sequences is replaced
 *	by a jump into the other sequence.
 *	Chains of identical statements ending on one
 *	label and a jump to the label are handled similarly,
 *	the sequence without the label is always the truncated one.
 */
cj()
	{
	register OCC *oc1ct, *oc2ct;
	int	done;
	OCC *oc1p1, *oc2p1, *oc1p2, *oc2p2;
	register match1, match2;
	int	done1, done2;
	register OCC *nextoc2;
	register linct;
	register	maxlen;			/* len of longest common seq */
	int	matchlins;			/* # of lines matched + fudge for returns */
	int	maxlins;				/* max of all matchlins */
	OCC *oc1end, *oc2end;
	OCC *oc1label, *oc2label;
	OCC *maxoc1, *maxoc2, *maxoc1ct, *maxoc2ct;
	OCC *nextoc1;

	/*	run through the buffer backward */
	for (oc1 = occhead.seqprior; oc1 != &occhead; oc1 = oc1->seqprior)
		{
		if (islabel(oc1)) oc1 = equate(oc1);
		}

	/*	run through the buffer backward */
	for (oc1 = occhead.seqprior; oc1 != &occhead; oc1 = oc1->seqprior)
		{
		if (isujump(oc1) || isret(oc1))
			{
			/*	this is a branch or return */

			/*	examine all of the other branches to the same label */
			/*	if this is a return, examine all other returns */
			/*	also examine code above the label */
			/*	we will replace sequence at oc1 by a jump into oc2 */
			/*	Set up to do the label first.  */

			nextoc2 = oc1->lin->eqchn;	/* next is first match */
			if (!isret(oc1))
				{
				oc2 = findlabel(oc1);	/* but *this* is the label */
				if (oc2 != NULL)		/* if found */
					{
					/*	printf("doing label first\n");	*/
					goto start;		/* into middle of loop */
					}
				}

			/*	For each matching line.  Jumps don't need to match
			 *	labels, cause we allow for similar code to have labels
			 *	renamed.
			 */
			FOREVER	{
				oc2 = nextoc2;			/* go to next match */
				nextoc2 = oc2->eqchn;	/* rememember next */
				if (oc2 == 0) break;	/* done */
				if (oc1 == oc2) continue;
start:			oc2ct = oc2->seqprior;
				oc1ct = oc1->seqprior;
				done = NO;
				match1 = 1;
				match2 = 1;
				for(;;)
					{
					/*	Test for overlap, falling off the edge */
					if (oc1ct == oc2 || oc1ct == &occhead) done = YES;
					else if (islabel(oc1ct))
						{
						oc1ct = oc1ct->seqprior;
						match1++;
						continue;
						}

					if (oc2ct == oc1 || oc2ct == &occhead) done = YES;
					else if (islabel(oc2ct))
						{
						oc2ct = oc2ct->seqprior;
						match2++;
						continue;
						}

					/*	Test for equality */
					if (oc1ct->lin != oc2ct->lin || done)
						{
						break;		/* not equal and neither label */
						}

					/*	These two lines are ok for now. */
					oc1ct = oc1ct->seqprior;
					oc2ct = oc2ct->seqprior;
					match1++;
					match2++;
					}

				matchlen = max(match1, match2);

				/*	if this match is as good as minimum cross-jump
				 *	ocxct point to the failing instruction or the
				 *	beginning of the buffer or the overlapping
				 *	instruction
				 */
				if (matchlen >= MINCJ)
					{
					oc1ct = oc1ct->seqnext;
					oc2ct = oc2ct->seqnext;

					if (debug) {
						/*
						printf("cj: found match length %d\n", matchlen);
						examine(oc1ct, oc2ct, oc1, oc2);
						*/
						}

					/*	ocxct through ocx match */

					/*	find the longest sequence which will be
					 *	conformed when we rename labels.
					 */
					oc1ptr = oc1ct;
					oc2ptr = oc2ct;

					/*	If we are matching jump x and label x at the
					 *	end of the sequence, don't check these for
					 *	isomorphism cause labels are ignored during
					 *	such checks.
					 */
					if (islabel(oc1) || islabel(oc2))
						{
						matchlen = morph(&oc1ptr, &oc2ptr,
							oc1->seqprior, oc2->seqprior) + 1;
						}
					else	{
						matchlen = morph(&oc1ptr, &oc2ptr, oc1, oc2);
						}
					oc1ct = oc1ptr;
					oc2ct = oc2ptr;

					/*	If the sequence is still worthwhile... */
					/*	ocxct through ocx contain match */
					if (matchlen >= MINCJ)
						{
						OCC *destlab;			/* destination label */

						/*	Sequences of identical statements ending in
						 *	jumps to the same label are changed.  One of
						 *	the sequences is replaced by a jump into the
						 *	other sequence.  Labels are unionized.
						 */

						if (debug) {
							/*
							printf("about to cross-jump this:\n");
							examine(oc1ct, oc2ct, oc1, oc2);
							*/
							}

						/*	insert label in s2 */
						destlab = forcelabel(oc2ct);	/* label in 2nd */

						/*	insert jump from end of s1 to s2 */
						sprintf(linbf, "%s%s%s", UJUMP, FLDSEPS, labf);

						oc1 = entocc(linbf, oc1);	/* put in first */
						/*
						if (debug)
						printf("inserting %s into sequence 1\n", linbf);
						*/
						/*	now delete s1
						 *	oc1ct points to next label or instruction
						 *	oc2ct points to next instruction
						 */
						while (oc1ct != oc1)
							{
							OCC *occ;

							/*	if it's a label, insert in 2nd */
							/*	& then equate it to whatever's there */
							if (islabel(oc1ct))
								{
								/*
								if (debug)
								printf("moving %s from seq 1 to 2\n",
									spellop(oc1ct));
								*/
								occ = outsertocc(oc1ct);
								insertocc(oc2ct->seqprior, oc1ct);
								equate(oc2ct->seqprior);
								oc1ct = occ;	/* point to next occ1 */
								}
							else	{
								/*
								if (debug)
								printf("removing %s from seq 1\n",
									spellop(oc1ct));
								*/
								oc1ct = freeocc(oc1ct);

								/*	skip over labels in sequence 2 */
								oc2ct = nextop(oc2ct);
								}
							}

						/*	Back up oc1 one more place so that it'll
						 *	get branch chained.
						 */
						oc1 = oc1->seqnext;
						goto advance;
						}
					}
				}
			}

		if (!isret(oc1))
			{
			/*	For each line equivalent to the one being tested */
			oc2 = oc1->lin->eqchn;
			maxlen = 0;				/* longest seq length */
			maxlins = 0;
			while (oc2)
				{
				oc1ct = oc1;
				oc2ct = oc2;

				/*	find potential matches fast & dirty */
				for (linct = 0;; linct++ )
					{
					/*	break on overlap, end of buffer */
retest:				if (oc1ct == oc2 || oc2ct == oc1 ||
						oc1ct == &occhead || oc2ct == &occhead) break;

					/*	test for equality	*/
					if (oc1ct->lin != oc2ct->lin)
						{
						/*	not equal, ignore labels */
						if (islabel(oc1ct))
							{
							oc1ct = oc1ct->seqprior;
							goto retest;
							}
						else if (islabel(oc2ct))
							{
							oc2ct = oc2ct->seqprior;
							goto retest;
							}
						else break;
						}

					oc1ct = oc1ct->seqprior;
					oc2ct = oc2ct->seqprior;
					}

				/*	remember how long this is & add fudge for being
				 *	followed by a return statement.
				 */
				matchlins = linct;
				if (isret(nextop(oc2)) || isret(nextop(oc1))) matchlins++;

				/*	If this match is potentially useful, examine it.
				 *	Find longest suffix which is stack-disciplined,
				 *	does not jump out (except right past the end),
				 *	contains no jumps in, for which internal jumps
				 *	go to isomorphic labels
				 */
				if (matchlins >= MINPA && matchlins > maxlins)
					{
					oc1ct = thisop(oc1ct->seqnext); 
					oc2ct = thisop(oc2ct->seqnext);

					oc1end = oc1;
					oc2end = oc2;
					if (islabel(oc1->seqnext) && islabel(oc2->seqnext))
						{
						/*	include labels at end of match */
						oc1end = oc1->seqnext;
						oc2end = oc2->seqnext;
						}

					/* printf("pa: found match!\n");
					examine(oc1ct, oc2ct, oc1end, oc2end);
					 */

					/*	limit match to longest isomorph */
					oc1ptr = oc1ct;
					oc2ptr = oc2ct;
					matchlen = morph2(&oc1ptr, &oc2ptr, oc1end, oc2end);
					matchlen = nests(&oc1ptr, &oc2ptr, oc1end, oc2end);
					matchlins = matchlen;
					if (isret(nextop(oc2)) || isret(nextop(oc1)))
						matchlins++;
					/*
					printf("%d lines balanced\n", matchlen);
					*/
					oc1ct = oc1ptr;
					oc2ct = oc2ptr;

					/*	Remember best match, prefer if already has ret */
					if (matchlins > maxlins)
						{
						/*
						if (debug) printf("\tbest so far\n");
						*/
						maxlins = matchlins;
						maxlen = matchlen;
						maxoc1 = oc1end;
						maxoc2 = oc2end;
						maxoc1ct = oc1ct;
						maxoc2ct = oc2ct;
						}
					}

				/*	Go on to next match */
				oc2 = oc2->eqchn;
				}

			/*	maxoc2 points to the longest equal seq
			 *	& maxlins is its len
			 */
			if (maxlins >= MINPA)
				{
				/*	Found a match	*/
				matchlen = maxlen;
				oc1end = maxoc1;
				oc2end = maxoc2;
				oc1ct = maxoc1ct;
				oc2ct = maxoc2ct;

				if (debug)
					{
					printf("about to pa match %d\n", matchlen); 
					examine(oc1ct, oc2ct, oc1end, oc2end);
					}

				/*	Found good match.  Check for ret following either
				 */
				nextoc1 = oc1->seqnext;	/* where to restart */
				retstat = 0;
				if (isret(nextop(oc2end)))
					{
					OCC *oc3ct;
					if (debug) printf("ret follows oc2ct\n");
					if (debug) printf("interchanging oc1 and oc2\n");
					oc3ct = oc1ct;
					oc1ct = oc2ct;
					oc2ct = oc3ct;

					oc3ct = oc1end;
					oc1end = oc2end;
					oc2end = oc3ct;
					retstat = 1;
					}
				else if (isret(nextop(oc1end))) retstat = 1;

				/*	Remove sequence starting at oc2end */
				/*	which does not have a following ret */
				/*	keep the label in place */
				oc2label = NULL;
				if (islabel(oc2end))
					{
					oc2label = oc2end;
					oc2end = oc2end->seqprior;
					}

				oc1label = NULL;
				if (islabel(oc1end))
					{
					oc1label = oc1end;
					oc1end = oc1end->seqprior;
					}

				/*	remember where to put the call */
				oc2insert = oc2end->seqnext;

				/*	delete one copy */
				for(; oc2ct != oc2insert; oc2ct = freeocc(oc2ct))
					;

				oc1insert = oc1end->seqnext;

				/*	If oc1 is not followed by ret move it to
				 *	the beginning of the buffer and add a ret
				 */
				if (!retstat)
					{
					/*	in case the two sequences are adjacent
					 *	oc2insert might now equal oc1ct.
					 *	if this is the case we need to move it
					 *	backward.
					 */
					if (oc2insert == oc1ct) oc2insert = oc1ct->seqprior;

					/*	remove this sequence from buffer	*/
					oc1ct->seqprior->seqnext = oc1insert;
					oc1insert->seqprior = oc1ct->seqprior;

					if (debug) printf(
						"moving oc1 to beginning of program\n");

					oc1ct->seqprior = &occhead;
					oc1end->seqnext = occhead.seqnext;
					occhead.seqnext = oc1ct;
					oc1end->seqnext->seqprior = oc1end;
					entocc(RETOP, oc1end);
					}
				else	{
					if (debug) printf("oc1 already has ret\n");
					}

				/*	check for jumps to end of sequence and
				 *	replace them by jumps to the return op.
				 */

				/*	if oc1 is not preceded by a label, insert one */
				forcelabel(oc1ct);

				/*	insert call into oc2 */ 
				sprintf(linbf, "%s%s", CALLOP, labf);
				entocc(linbf, oc2insert->seqprior);

				/*	If oc1 was not followed by a ret insert call */
				if (!retstat)
					{
					sprintf(linbf, "%s%s", CALLOP, labf);
					entocc(linbf, oc1insert->seqprior);
					}

				oc1 = nextoc1;
				goto advance;
				}
			}
advance:
		;
		}
	}

main(ac, av)
	unsigned ac;
	TEXT **av;
	{
	TEXT *p;

	/*	Read the file.  To save space we pass through lines which will
	 *	not be optimized.  This is:  everything in data segment and
	 *	constants in text segment, and externs (public) declarations.
	 */
	FOREVER	{
		if (!getl(stdin)) break;
		if (!strcmp(TEXTNAME, linbf)) {
			datamode = NO;
			printf("%s\n", linbf);
			}
		else if (!strcmp(DATANAME, linbf)) {
			datamode = YES;
			printf("%s\n", linbf);
			}
		else if (datamode || !strncmp(GLOBAL, linbf, strlen(GLOBAL)))
			printf("%s\n", linbf);	
		else	{
			entocc(linbf, occhead.seqprior);	/* enter the line */
			}
		}

	printf("%s\n", TEXTNAME);

	cj();			/* do cross-jumping optimization */
	if (ac != 1) debug = 1;

	/*	Output result file */
	for (oc1 = occhead.seqnext; oc1 != &occhead; oc1 = oc1->seqnext)
		{
		printf("%s\n", spellop(oc1));
		}
	}

/*	determine if these two sequences are morphic up the names of labels.  
 */
morph(pfirst1, pfirst2, last1, last2)
	OCC **pfirst1, **pfirst2, *last1, *last2;
	{
	int done1, done2;
	OCC *this1, *this2, *first1, *first2;
	first1 = *pfirst1;
	first2 = *pfirst2;

redo:
	done1 = NEW;
	matchlen = 0;

	while (priors(first1, first2, &this1, &this2, last1, last2, &done1))
		{
		/*
		if (debug)
		printf("trying %s and %s\n", OCCTOTEXT(this1), OCCTOTEXT(this2));
		*/
		/*	ignore labels */
		if (islabel(this1) || islabel(this2))
			{
			/*
			if (debug) printf("\tignoring labels\n");
			*/
			continue;
			}

		/*	if these are transfers to different labels */	
		if (isxfer(this1) && this1->label != this2->label)
			{
			OCC *oc1, *oc2;
			/*
			if (debug) printf("\ttransfer to different labels\n");
			*/
			done2 = NEW;

			/*	search labels inside the sequence from first to last. */
			while (priors(first1, first2, &oc1, &oc2, last1, last2, &done2))
				{
				int s1has, s2has;

				s1has = (islabel(oc1) && (this1->label == oc1->label));
				s2has = (islabel(oc2) && (this2->label == oc2->label));

				if (s1has != s2has)
					{
					/*
					if (debug) printf("\t\t\tnot conformed\n");
					*/
					first1 = this1->seqnext;
					first2 = this2->seqnext;
					goto redo;
					}

				else if (s1has) goto conform;
				}

			/*
			if (debug) printf("\t\tlabels not found\n");
			*/
			first1 = thisop(this1)->seqnext;
			first2 = thisop(this2)->seqnext;
			goto redo;
			}

conform:	matchlen++;
		/*
		if (debug)
		printf("\tlabels conform!\n");
		*/
		}

	/*	save new values for first1 & first2 */	
	*pfirst1 = first1;
	*pfirst2 = first2;
	return matchlen;
	}

/*	determine if these two sequences are morphic up to names of labels. */
morph2(pfirst1, pfirst2, last1, last2)
	OCC **pfirst1, **pfirst2, *last1, *last2;
	{
	int done1, done2;
	OCC *this1, *this2, *first1, *first2;
	OCC *ptr1, *ptr2;
	first1 = *pfirst1;
	first2 = *pfirst2;

redo:
	done1 = NEW;
	matchlen = 0;

	while (priors(first1, first2, &this1, &this2, last1, last2, &done1))
		{
		/*
		if (debug) printf("trying %s and %s\n", OCCTOTEXT(this1), OCCTOTEXT(this2));
		*/
		/*	if this is a label make sure refs to it are internal */
		if (islabel(this1))
			{
			/*
			if (debug) printf("\tsequence 1 is a label\n");
			*/
			if (this1 == last1)
				{
				/*
				if (debug) printf("\t\tbut it's last in sequence\n");
				*/
				}
			else	{
				for (ptr1 = this1->label->refchn; ptr1;
					ptr1 = ptr1->refchn)
					{
					for (ptr2 = last1; ptr2 != first1->seqprior;
						ptr2 = ptr2->seqprior)
						{
						if (ptr2 == ptr1) goto got1;
						}
					/*
					if (debug) printf("\t\twith external references\n");
					*/
					first1 = thisop(this1);
					first2 = thisop(this2);
					goto redo;
got1:				;
					}
				/*
				if (debug) printf("\t\twith no external references\n");
				*/
				}
			}

		/*	if this is a label make sure refs to it are internal */
		if (islabel(this2))
			{
			/*
			if (debug) printf("\tsequence 1 is a label\n");
			*/
			if (this2 == last2)
				{
				/*
				if (debug) printf("\t\tbut it's last in sequence\n");
				*/
				}
			else	{
				for (ptr1 = this2->label->refchn; ptr1;
					ptr1 = ptr1->refchn)
					{
					for (ptr2 = last2; ptr2 != first2->seqprior;
						ptr2 = ptr2->seqprior)
						{
						if (ptr2 == ptr1) goto got2;
						}
					/*
					if (debug) printf("\t\twith external references\n");
					*/
					first1 = thisop(this1);
					first2 = thisop(this2);
					goto redo;
got2:				;
					}
				/*
				if (debug) printf("\t\twith no external references\n");
				*/
				}
			}

		/*	if these are calls to the same label, ignore them */
		if (iscall(this1))
			{
			if (this1->label != this2->label)
				{
				/*
				if (debug) printf("\tcalls to different labels\n");
				*/
				goto redoit;
				}
			else	{
				/*
				if (debug) printf("\tcalls ignored\n");
				*/
				}
			}

		/*	if these are transfers to different labels */	
		else if (isxfer(this1))
			{
			OCC *oc1, *oc2;
			/*
			if (debug) printf("\ttransfers \n");
			*/
			done2 = NEW;

			/*	search labels inside the sequence from first to last. */
			while (priors(first1, first2, &oc1, &oc2, last1, last2, &done2))
				{
				int s1has, s2has;

				s1has = (islabel(oc1) && (this1->label == oc1->label));
				s2has = (islabel(oc2) && (this2->label == oc2->label));

				if (s1has != s2has)
					{
					/*
					if (debug) printf("\t\t\tnot conformed\n");
					*/
					goto redoit;
					}

				else if (s1has) goto conform;
				}

			/*
			if (debug) printf("\t\tlabels not found\n");
			*/
redoit:		first1 = thisop(this1)->seqnext;
			first2 = thisop(this2)->seqnext;
			goto redo;
			}

conform:	matchlen++;
		/*
		if (debug) printf("\tlabels conform!\n");
		*/
		}

	/*	save new values for first1 & first2 */	
	*pfirst1 = first1;
	*pfirst2 = first2;
	return matchlen;
	}

/*				cj					pa
 *		outside jumps can dive into sequence		they can't
 *		inside jumps can jump out of sequence		they can't
 *		labels which are morphic wrt jumps		see above; you can't
 *		in the sequence can be equated for			jump into the sequence
 *		purposes of jumps outside the sequence
 *
 *		labels at head of first instruction	labels behind last instiructo
 *	can be equated						can be equated	
 *	we don't need to check stack			we need to
 *	label at the end of a sequence can be	can't do this
 *	cross-jumped against a jump to label
 *	sequence must end in returns, jmps, or	sequence cannot contain return 
 *	jump & label						it can end in (internal) jump
 *									or label referenced internally
 *									and externally.
 */

/*	stack ops	*/
static TEXT *stackops[] = {
	"movf %1,-(sp)",
	"mov %1,-(sp)",
	"add $%1,sp",
	"tst (sp)+",
	"cmp (sp)+,(sp)+",
	"mov %1,(sp)",
	"jsr pc,%1",
	NULL
	};

/*	amount pushed or popped
 *	on the 11 this also matches jsr against the mov rx,(sp) that
 *	flags the first parameter pushed
 */
static TEXT *stackvals[] = {"8", "2", "-%1", "-2", "-4", "9999", "-9999"};

/*	bound[i] points to a text string if i bound, else NULL */
static char *bound[10] = 0;
static int len[10] = 0;

/*	Expand output buffer */
char *expand(bf)
	register char *bf;
	{
	static char lbf[512];
	char *dp, *result;
	char c;
	/*
	if (debug) printf("expand %s = ", bf);
	*/
	dp = lbf;
	do	{
		c = *bf++;
		if (c == '%' && '0' <= *bf && *bf <= '9')
			{
			char *vp, c;
			c = *bf++ - '0';
			if (bound[c] == 0 || len[c] > 200)
				fprintf(stderr, "%%%d not bound\n", c);
			for (vp = bound[c]; vp < bound[c] + len[c];)
				{
				*dp++ = *vp++;
				}
			}
		else *dp++ = c;
		} while (c);

	/*
	if (debug) printf(" = %s\n", lbf);
	*/
	return lbf;
	}

/*	match a pattern & set bindings */
match(actual, formal)
	TEXT *actual, *formal;
	{
	int i;
	for (i = 0; i < 10; i++) bound[i] = 0;	/* break bindings */

	/*
	if (debug) printf("matching %s and %s\n", actual, formal);
	*/

	/*	For each char in this line */
	for (;;)
		{
		register char formc;
		register char *p3;
		char actc;

		formc = *formal++;		/* get next chars */
		actc = *actual++;

		/*	if this is a variable, define or check binding */
		if (formc == '%' && *formal >= '0' && *formal <= '9')
			{
			formc = *formal++ - '0';	/* var # */
			if (bound[formc])
				{
				/*	check	*/
				for (p3 = bound[formc]; p3 < bound[formc] + len[formc]; p3++)
					{
					if (*p3 != actc) return NO;
					actc = *actual++;
					}
				actual--;
				}
			else	{
				/*	define	*/
				bound[formc] = --actual;
				while (*actual != *formal && *actual) actual++;
				len[formc] = actual - bound[formc];
				}
			}
		else if (formc != actc) return NO;
		else if (formc == 0) return YES;
		}
	}

/*	convert string to number	*/
nval(string)
	TEXT *string;
	{
	int val;
	sscanf(string, "%d", &val);
	return val;
	}

/*	find the longest properly nesting subsequence ending with oc1 & oc2	*/
nests(oc1ct, oc2ct, oc1, oc2)
	OCC **oc1ct, **oc2ct, *oc1, *oc2;
	{
	OCC *lastbal1, *lastbal2;
	int	matchlen, lastlen;
	int stacklev;
	char **p;
	OCC *oc1p1, *oc2p1;
	int	done1;

	matchlen = stacklev = lastlen = 0;
	lastbal1 = lastbal2 = NULL;
	done1 = NEW;
	while (priors(*oc1ct, *oc2ct, &oc1p1, &oc2p1, oc1, oc2, &done1))
		{
		if (!islabel(oc1p1) && !islabel(oc2p1))
			{
			/*
			if (debug) printf("nests: trying %s and %s\n",
				spellop(oc1p1), spellop(oc2p1));
			*/
			for (p = stackops; *p; p++)
				{
				if (match(spellop(oc1p1), *p))
					{
					stacklev += nval(expand(stackvals[p - stackops]));
					/*
					if (debug) printf("\tnew stack %d\n", stacklev);
					*/
					break;
					}
				}
			matchlen++;			/* count a line */
			}

		/*	remember if we're balanced */
		if (stacklev == 0)
			{
			lastbal1 = oc1p1;
			lastbal2 = oc2p1;
			lastlen = matchlen;		/* remember match length */
			}

		else if (stacklev > 0)		/* unbalanced push going backward */
			{
			break;
			}
		}

	if (!lastbal1) return 0;
	*oc1ct = lastbal1;
	*oc2ct = lastbal2;
	return lastlen;
	}
