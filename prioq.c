/* prioq.c -- implementation of priority queue */

#include "cr.h"

/*  priority queue */
typedef struct entry
    {
    SUBSEQ *val;
    int prio;
    } ENTRY;

ENTRY *prioq;
static int nelts = 0, prioqsz = 0;

char *alloc();

/*  insert in val into queue in descending priority */
pqinsert(val, prio)
    SUBSEQ *val;
    {
    int i, j;
    if (nelts == prioqsz)
	{
	prioqsz += 100;
	if (nelts == 0) prioq = (ENTRY *)malloc(prioqsz * sizeof(ENTRY));
	else prioq = (ENTRY *)realloc(prioq, sizeof(ENTRY) * prioqsz);
	if (!prioq) { 
	    printf("no memory\n");
	    exit();
	    }
	}

    j = nelts;			/* # of the new entry */
    i = (nelts - 1) >> 1;	/* # of its parent */
    nelts++;
    while (i >= 0 && prioq[i].prio < prio)
	{
	prioq[j] = prioq[i];
	j = i;			/* remember this node */
	i = (i - 1) >> 1;	/* go to parent */
	}
    prioq[j].prio = prio;
    prioq[j].val = val;
    }

/*  return the value of the element of highest priority and remove
 *  the element from the heap
 *  nelts contains the number of elements in the heap
 *  parents are always bigger than their children; biggest is zeroth.
 */
SUBSEQ *pqmax(valp)
    int *valp;
    {
    ENTRY tmp;
    int kid, winner, parent;
    SUBSEQ *result;

getanother:
    if (nelts == 0) return 0;		/* queue empty? */
    result = prioq[0].val;		/* returning zeroth value */
    *valp = prioq[0].prio;		/* returning zeroth priority */
    parent = 0; 			/* current parent */
    kid = 1;				/* start at left kid of root */
    nelts--;				/* nelts = # of high element in tree */
    prioq[0] = prioq[nelts];		/* root holds old last element */

    /*	sink parent down to its level of incompetence */
    while (kid <= nelts)		/* while kid is inside array */
	{
	winner = parent;		/* assume parent will win */
	if (prioq[kid].prio > prioq[winner].prio)
	    winner = kid;		/* kid's ahead */
	if (kid < nelts && prioq[kid + 1].prio > prioq[winner].prio)
	    winner = kid + 1;		/* right kid wins */
	if (winner == parent) break;	/* sunk properly */
	tmp = prioq[winner];		/* move winner into parents slot */
	prioq[winner] = prioq[parent];	/* and parent into winner's */
	prioq[parent] = tmp;
	parent = winner;		/* parent's still possibly misplaced */
	kid = (winner << 1) + 1;
	}

    /*	The following eliminates any duplicates that may have got
     *	stuck in, by repeatedly discarding the entry that's about
     *	to be returned if it duplicates the entry at the front of
     *	the queue.
     */
    if (nelts == 0 || prioq[0].val->nelts != result->nelts ||
	prioq[0].val->seqlen != result->seqlen) return result;

    for (kid = 0; kid < result->nelts; kid++)
	if (prioq[0].val->ents[kid].lineno != result->ents[kid].lineno)
	    return result;
	
    goto getanother;
    }
