/* cr.h -- header file for cruncher */

#define MAXLINE 1024

#define HASHSIZE 10007		/* # of hash buckets */
#define FLGUJUMP	1	/* I'm an unconditional jump */
#define FLGGONE		2	/* I've been deleted */
#define	FLGRET		4	/* I'm a return instruction */
#define	FLGCALL		8	/* I'm a call instruction */
#define FLGBAD		16	/* I'm not optimizable */

struct ent {
    int lineno;			/* first line # of this element */
    struct subseq *subseq;	/* subsequence of which this is a member */
    struct ent *parent;		/* immediately enclosing element */
    };
    
/* occurrences of lines */
/*  if an occ is deleted from the sequential list (seqnext/seqprior)
 *  then eqnext points to equivalent in body and refchn points to the jsr instruction.
 */
typedef struct occ
    {
    struct occ *eqnext;		/* next occurrence of this same line */
    struct occ *eqprior;	/* prior occurrence of this same line */
    struct occ *refchn;		/* next occurrence of a ref to our label */
    struct occ *seqnext;	/* next occurrence of any line in the program */
    struct occ *seqprior;	/* prior */
    struct lin *label;		/* pointer to label line (jumps & labels) */
    struct lin *linpt;		/* pointer to master copy of line */
    int relabel;		/* jump displacement (jumps) */
    int flags;
    struct ent ent;		/* our first line # and enclosing sequence */
    } OCC;

/*  master copies of lines -- the actual characters of text follow
 *  this structure in memory.
 */
typedef struct lin
    {
    OCC *eqchn; 		/* first occurrence on occurrence list */
    OCC *refchn;		/* references to this label (if a label) */
    struct lin *next;		/* hash link */
    int usecount;		/* use count before optimization */
    int effcount;		/* after optimization */
    int stackop;		/* stack change */
    struct regexp *regcomp;		/* regular expression version */
    } LIN;


/*  List of sequences which are equal modulo gene */
typedef struct subseq {
    struct subseq *worse;	/* link of all committed sequences */
    struct subseq *better;	/* link to next better */
    struct subseq *smaller;	/* link to next smaller */
    struct subseq *bigger;	/* link to next longer */
    int nelts;			/* # of elements in the sequence */
    int seqlen;			/* length of the sequence */
    int effnelts;		/* # of nelts after collapse */
    int efflen;			/* length after collapse */
    int val;			/* value of this sequence */
    char nested;		/* 1 if this subseq contains calls */
    OCC *label;			/* the label at the head of this if any */
    struct ent ents[1];		/* vector of entries */
    } SUBSEQ;


