/***** mx_romotes : stl2tree.h *****/
/* Version 1.0				     */

/*Written by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS         */
/*Some of the code in this file was modified basing on S-TaLiRo*/
/*Software Written by Georgios Fainekos, ASU, U.S.A.           */

#include <stdio.h>
#include <string.h>
#include <time.h>

typedef struct Symbol
{/*Taken from S-TaLiRo Software*/
	char *name;
	ConvSet *set;
	struct Symbol *next;	/* linked list, symbol table */
	int index;
} Symbol;

typedef struct
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	int LTL;			/* Is this an LTL formula */
	int ConOnSamples;	/* Are the constraints on the actual time or the # of samples? */
	mwSize SysDim;      /* System dimension */
	mwSize nSamp;       /* Number of Samples */
	size_t nPred;       /* Number of Predicates */
	int nInp;	        /* Number of inputs to romotes_taliro */
	/*Following members are added by ZHONG Bingzhuo, on 17.09.2018*/
	double max_delay_s; /*Maximal delay in the signal*/
	double sample_f_s; /*frequency for verifying specification*/
    bool lipschitz_on; /*whether lipschitz deviation term is on*/
} ROMOTESParam;


#define NullSymbol (Symbol *)0

typedef struct queue
{/*Taken from S-TaLiRo Software*/
	int i;
    struct Node *first;     /*Recording the address of the first element in the queue*/
    struct Node *last;      /*Recording the address of the second element in the queue*/
}queue;

/*Structure defined for recording a number*/
typedef union
{/*Taken from S-TaLiRo Software*/
	struct {
		int inf;
	} num;
	struct {
		int inf;    /*If it is infinite, inf =1 or -1, and f_num equals to 0.0, otherwise, inf should be 0 and f_num should be the actual value*/
		double f_num;
	} numf; /*recording real number*/
	struct {
		int inf;
		int i_num;
	} numi; /*Recording integer number*/
} Number;

/*Recoding information of an interval*/
typedef struct
{/*Taken from S-TaLiRo Software*/
	Number lbd;     /*Number of lower bound value*/
	int l_closed;   /*If the lower bound of the interval is closed, it is 1. otherwise 0*/
	Number ubd;     /*Number of upper bound value*/
	int u_closed;   /*If the upper bound of the interval is closed, it is 1. otherwise 0*/
} Interval;

typedef struct Node
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	short ntyp;	            /* node type */
    int index;              /*The position in the array with name "subformula"*/
    int visited;            /*Used in deep first search, when the node has been visited, it is set to one*/
	Interval time;          /* Recording the time constraint when the node corresponds to a temporal operator  */
	struct Symbol *sym;     /* Recording the address of the symbol when the node corresponds to an atomic proposition*/
	struct Node	*lft;	    /* Recording the address of the node on left hand side */
	struct Node	*rgt;	    /* Recording the address of the node on right hand side */
	/*Following members are added by ZHONG Bingzhuo, on 17.09.2018*/
	struct Node *parent;    /*Recording the address of the parent node*/
	double *upperdata;      /*Recording the evolution of the upper bound*/
	double *u_timestamp;    /*Recording the evolution of the upper bound time stamp*/
	int num_upperdata;      /*Number of data point in the upper bound evolution*/
	double *lowerdata;      /*Recording the evolution of the lower bound*/
	int num_lowerdata;      /*Recording the evolution of the lower bound time stamp*/
	double *l_timestamp;    /*Number of data point in the lower bound evolution*/
	int singleton;          /*If no spatial deviation exits in the signal being monitored, set it to 1*/
} Node;


enum
{/*Taken from S-TaLiRo Software*/
	ALWAYS=257,
	AND,		/* 258 */
	EQUIV,		/* 259 */
	EVENTUALLY,	/* 260 */
	FALSE,		/* 261 */
	IMPLIES,	/* 262 */
	NOT,		/* 263 */
	OR,			/* 264 */
	PREDICATE,	/* 265 */
	TRUE,		/* 266 */
	U_OPER,		/* 267 */
	V_OPER,		/* 268 */
	NEXT,		/* 269 */
	VALUE,		/* 270 */
	WEAKNEXT,	/* 271 */
	U_MOD,		/* 272 */
	V_MOD,		/* 273 */
	POSITIVE_POLAR = 1,
	NEGATIVE_POLAR = -1,
	MIXED_POLAR = 0,
	UNDEFINED_POLAR = 2,
	PRED = 1,
	PAR = 2,
	PREDPAR = 3
};

typedef Node	*Nodeptr;
#define YYSTYPE	 Nodeptr
#define Nhash	255

typedef struct PMap
/*Taken from S-TaLiRo Software*/{
	char *str;
	ConvSet set;
	bool true_pred;
} PMap;

typedef struct
{/*Taken from S-TaLiRo Software*/
	int *pindex;
	size_t total;
	int used;
}PredList;


typedef struct
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	Number zero;                    /*Number zero in monitoring*/
	Number inf;                     /*Number infinite in monitoring*/
	Interval zero2inf;              /*Interval [0, +inf] in monitoring*/
	Interval emptyInter;            /*Interval (0, 0) in monitoring*/
	Interval TimeCon;               /*Temporarily saving the time constraint of the operator being read at this moment*/
	YYSTYPE	tl_yylval;              /*Temporarily saving the operator being read at this moment*/
	int	tl_errs;                    /*Used when there is error*/
	FILE *tl_out;                   /*Address of the file to which the result would be exported*/
	char	yytext[2048];           /*Buffer for reading new character*/
	Symbol *symtab[Nhash+1];        /*Table for the list of symbol*/
	PMap *predMap;                  /*Address of the predicate map*/
	PredList pList;                 /*Using for whether the predicate contains a parameter, currently not used in RoMoTeS*/
	bool lbd;                       /*supplementary variable used in reading information of time constraint*/
	int type_temp;                  /*Temporarily recording the type of the operator being read at this moment*/
	/*Following members are added by ZHONG Bingzhuo, on 17.09.2018*/
	ROMOTESParam romotes_param;     /*Parameters required for RoMoTeS*/
} Miscellaneous;

/*Functions for generating formula tree*/
Node	*dupnode(Node *);
Node	*getnode(Node *);
Node	*push_negation(Node *, Miscellaneous *, int *, char *, int *);
Node	*switchNotTempOper(Node *n, int ntyp, Miscellaneous *, int *cnt, char *uform, int *tl_yychar);
Node	*tl_nn(int, Node *, Node *, Miscellaneous *);
Symbol	*tl_lookup(char *, Miscellaneous *miscell);
void	tl_clearlookup(char *, Miscellaneous *miscell);
void	releasenode(int, Node *);
Symbol	*getsym(Symbol *);
char	*emalloc(size_t);
int	tl_Getchar(int *cnt, size_t hasuform, char *uform);
void	tl_UnGetchar(int *cnt);
Node	*tl_parse(int *cnt, size_t hasuform, char *uform, Miscellaneous *miscell, int *);
int	tl_yylex(int *cnt, size_t hasuform, char *uform, Miscellaneous *miscell, int *tl_yychar);

/*Functions for generating error information */
void	fatal(char *, char *, int *, char *, int *, Miscellaneous *);
void	tl_yyerror(char *s1, int *cnt, char *uform, int *, Miscellaneous *);
void	tl_explain(int);
void	Fatal(char *, char *, int *, char *, int *, Miscellaneous *);
static void	non_fatal(char *, char *, int *, char *, int *, Miscellaneous *);
void	fatal(char *, char *, int *, char *, int *, Miscellaneous *);
void	dump(Node *, Miscellaneous *);
Symbol	*DoDump(Node *, char *, Miscellaneous *miscell);
void put_uform(char *uform, Miscellaneous *);
void tl_exit(int i);

#define ZN	(Node *)0
#define ZS	(Symbol *)0
#define ZD  (double *)0
#define NullSet (ConvSet *)0

#define True	tl_nn(TRUE,  ZN, ZN, miscell)
#define False	tl_nn(FALSE, ZN, ZN, miscell)
#define Not(a)	push_negation(tl_nn(NOT, a, ZN, miscell), miscell, cnt, uform, tl_yychar)


#define Debug(x)	{ if (0) printf(x); }
#define Debug2(x,y)	{ if (tl_verbose) printf(x,y); }
#define Dump(x)		{ if (0) dump(x, miscell); }
#define Explain(x)	{ if (tl_verbose) tl_explain(x); }

#define Assert(x, y)	{ if (!(x)) { tl_explain(y); \
			  Fatal(": assertion failed\n",(char *)0, cnt, uform, tl_yychar, miscell); } }
#define min(a,b)    (((a) < (b)) ? (a) : (b))
#define max(a, b)  (((a) > (b)) ? (a) : (b))
#define dmin(a, b)  (((a) < (b)) ? (a) : (b))


/*Data type and Functions for simplifying the formula, currently are not used, remains to be studied */
typedef struct Cache {
	Node *before;
	Node *after;
	int same;
	struct Cache *nxt;
} Cache;

int implies(Node *a, Node *b, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell);
Node *bin_simpler(Node *ptr, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar);
Node	*Canonical(Node *, Miscellaneous *, int *, char *, int *);
Node	*canonical(Node *, Miscellaneous *, int *, char *, int *);
Node	*cached(Node *, Miscellaneous *, int *, char *, int *);
Node	*in_cache(Node *, int *, char *, int *, Miscellaneous *);
Node	*right_linked(Node *);
int	anywhere(int, Node *, Node *, int *, char *, int *, Miscellaneous *);
int	isequal(Node *, Node *, int *, char *, int *, Miscellaneous *);
void	cache_stats(void);

#define rewrite(n)	canonical(right_linked(n), miscell, cnt, uform, tl_yychar)
