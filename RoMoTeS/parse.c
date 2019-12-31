/***** mx_romotes : parse.c *****/

/* Version 1.0				     */

/*Edited by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS*/

/*Following functions in this file  are developed bY ZHONG Bingzhuo
"tl_nn"
"getnode"
"push_negation"
"bin_minimal"

/*Following functions in this file are taken from S-TaLiRo Software Written by Georgios Fainekos  ASU, U.S.A.
"releasenode"
"dupnode"
"switchNotTempOper"
"tl_factor"
"tl_level"
"tl_formula"
"tl_parse"
*/

#include "mex.h"
#include "matrix.h"
#include "distances.h"
#include "stl2tree.h"


static Node	*tl_formula(int *, size_t, char *, Miscellaneous *, int *);
static Node	*tl_factor(int *, size_t, char *, Miscellaneous *, int *);
static Node	*tl_level(int,int *, size_t, char *, Miscellaneous *, int *);

/* It frees the memory for the node if all_levels=0
   It frees the memory for the tree if all_levels=1 */
void releasenode(int all_levels, Node *n)
{/*Taken from S-TaLiRo Software*/
	if (!n) return;

	if (all_levels)
	{	releasenode(1, n->lft);
		n->lft = ZN;
		releasenode(1, n->rgt);
		n->rgt = ZN;
	}
	mxFree((void *) n);
}

/*To create a node with type represented by "t"*/
Node *tl_nn(int t, Node *ll, Node *rl, Miscellaneous *miscell)
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	Node *n = (Node *) emalloc(sizeof(Node));

	n->ntyp = (short) t;
	n->sym = ZS;
	n->time = miscell->emptyInter;
	n->lft  = ll;
	n->rgt  = rl;
	/*Added by ZHONG Bingzhuo, on 17.09.2018*/
	n->parent = ZN;
	n->upperdata=ZD;
    n->lowerdata=ZD;
    n->u_timestamp=ZD;
    n->l_timestamp=ZD;
    n->num_upperdata=0;
    n->num_lowerdata=0;
    n->singleton=0;

	return n;
}

/*To obtain the node "p"*/
Node *getnode(Node *p)
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	Node *n;

	if (!p) return p;

	n =  (Node *) emalloc(sizeof(Node));
	n->ntyp = p->ntyp;
	n->time = p->time;
	n->sym  = p->sym;
	n->lft  = p->lft;
	n->rgt  = p->rgt;
	/*Added by ZHONG Bingzhuo, on 17.09.2018*/
	n->parent = p->parent;
	n->upperdata=p->upperdata;
	n->lowerdata=p->lowerdata;
	n->num_lowerdata=p->num_lowerdata;
	n->num_upperdata=p->num_upperdata;
    n->u_timestamp=p->u_timestamp;
    n->l_timestamp=p->l_timestamp;
    n->singleton=p->singleton=0;

	return n;
}

/*To duplicate a node*/
Node *dupnode(Node *n)
{/*Taken from S-TaLiRo Software*/
	Node *d;

	if (!n) return n;
	d = getnode(n);
	d->lft = dupnode(n->lft);
	d->rgt = dupnode(n->rgt);
	return d;
}

/*Function for revising negation operation*/
Node *push_negation(Node *n, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar)
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	Node *m;

	Assert(n->ntyp == NOT, n->ntyp);

	switch (n->lft->ntyp) {
	case TRUE: /*Not TRUE equals to FALSE*/
		releasenode(0, n->lft);
		n->lft = ZN;
		n->ntyp = FALSE;
		break;
	case FALSE: /*Not FALSE equals to TRUE*/
		releasenode(0, n->lft);
		n->lft = ZN;
		n->ntyp = TRUE;
		break;
	case NOT:   /*Double NOT means nothing*/
		m = n->lft->lft;
		releasenode(0, n->lft);
		n->lft = ZN;
		releasenode(0, n);
		n = m;
		break;
		/*Following conversions correspond to the rule for negation normal form*/
	case V_OPER:
		n = switchNotTempOper(n,U_OPER, miscell, cnt, uform, tl_yychar);
		break;
	case U_OPER:
		n = switchNotTempOper(n,V_OPER, miscell, cnt, uform, tl_yychar);
		break;
	case NEXT:
		n = switchNotTempOper(n,WEAKNEXT, miscell, cnt, uform, tl_yychar);
		break;
	case WEAKNEXT:
		n = switchNotTempOper(n,NEXT, miscell, cnt, uform, tl_yychar);
		break;
	case  AND:
		n = switchNotTempOper(n,OR, miscell, cnt, uform, tl_yychar);
		break;
	case  OR:
		n = switchNotTempOper(n,AND, miscell, cnt, uform, tl_yychar);
		break;
    case ALWAYS:
        n= switchNotTempOper(n,EVENTUALLY, miscell, cnt, uform, tl_yychar);
        break;
     case EVENTUALLY:
        n= switchNotTempOper(n,ALWAYS, miscell, cnt, uform, tl_yychar);
        break;
	}

	return n;
}

/*Function for revising negation operation of complicated operator*/
Node *switchNotTempOper(Node *n, int ntyp, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar)
{/*Taken from S-TaLiRo Software*/
	Node *m;

	m = n;
	n = n->lft;
	n->ntyp = ntyp;
	m->lft = n->lft;
	n->lft = push_negation(m, miscell, cnt, uform, tl_yychar);
	if (ntyp!=NEXT && ntyp!=WEAKNEXT)
	{
		n->rgt = Not(n->rgt);
	}
	return(n);
}

/*Function for converting implies, equivalent, UNTIL and RELEASE operator with time constraint*/
static Node *bin_minimal(Node *ptr, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar)
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	Node *a, *b,*c,*d,*e;
	Interval Timec;

	if (ptr)
	{
		switch (ptr->ntyp)
		{
			case IMPLIES:
				return tl_nn(OR, Not(ptr->lft), ptr->rgt, miscell);

			case EQUIV:
				a = tl_nn(AND,dupnode(ptr->lft),dupnode(ptr->rgt), miscell);
				b = tl_nn(AND,Not(ptr->lft),Not(ptr->rgt), miscell);
				return tl_nn(OR, a, b, miscell);

            case U_OPER:/*code for transforming until operator with bounded time constraint*/
                Timec=ptr->time;
                if(!(miscell->romotes_param.LTL||(Timec.lbd.numf.inf == 0 && Timec.lbd.numf.f_num == 0.0 && Timec.l_closed == 1 && Timec.ubd.numf.inf == 1)))
                {
                    a=dupnode(ptr->lft);
                    b=dupnode(ptr->rgt);
                    c=tl_nn(EVENTUALLY,True, dupnode(b), miscell);
                    c->time=Timec;
                    d=tl_nn(U_OPER,dupnode(a), dupnode(b), miscell);
                    d->time.lbd.numf.inf = 0;
                    d->time.lbd.numf.f_num = 0.0;
                    d->time.l_closed = 1;
                    d->time.ubd.numf.inf = 1;
                    e=tl_nn(ALWAYS, False, dupnode(d), miscell);
                    e->time.l_closed=Timec.l_closed;
                    e->time.lbd.numf.inf=0;
                    e->time.lbd.numf.f_num=0.0;
                    e->time.u_closed=Timec.u_closed;
                    e->time.ubd.numf.inf=0;
                    e->time.ubd.numf.f_num=Timec.lbd.numf.f_num;
                    ptr=tl_nn(AND,dupnode(c),dupnode(e), miscell);
                }

                case V_OPER:/*code for transforming REALEASE operator with bounded time constraint*/
                Timec=ptr->time;
                if(!(miscell->romotes_param.LTL||(Timec.lbd.numf.inf == 0 && Timec.lbd.numf.f_num == 0.0 && Timec.l_closed == 1 && Timec.ubd.numf.inf == 1)))
                {
                    a=dupnode(ptr->lft);
                    b=dupnode(ptr->rgt);
                    c=tl_nn(ALWAYS,False,dupnode(b), miscell);
                    c->time=Timec;
                    d=tl_nn(V_OPER,dupnode(a), dupnode(b), miscell);
                    d->time.lbd.numf.inf = 0;
                    d->time.lbd.numf.f_num = 0.0;
                    d->time.l_closed = 1;
                    d->time.ubd.numf.inf = 1;
                    e=tl_nn(EVENTUALLY, True, dupnode(d), miscell);
                    e->time.l_closed=Timec.l_closed;
                    e->time.lbd.numf.inf=0;
                    e->time.lbd.numf.f_num=0.0;
                    e->time.u_closed=Timec.u_closed;
                    e->time.ubd.numf.inf=0;
                    e->time.ubd.numf.f_num=Timec.lbd.numf.f_num;
                    ptr=tl_nn(OR,dupnode(c),dupnode(e), miscell);
                }


		}
	}
	return ptr;
}

/*Function for creating new node according to the currently read operator*/
static Node *tl_factor(int *cnt, size_t hasuform, char *uform, Miscellaneous *miscell, int *tl_yychar)
{/*Taken from S-TaLiRo Software*/
	Node *ptr = ZN;
	int tl_simp_log_p = 0;

	switch ((*tl_yychar))
	{
	case '(':
		ptr = tl_formula(cnt, hasuform, uform, miscell, tl_yychar);
		if ((*tl_yychar) != ')')
			tl_yyerror("expected ')'", cnt, uform, tl_yychar, miscell);
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		goto simpl;

	case NOT:
		ptr = miscell->tl_yylval;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		ptr->lft = tl_factor(cnt, hasuform, uform, miscell, tl_yychar);
		ptr = push_negation(ptr, miscell, cnt, uform, tl_yychar);
		goto simpl;

	case ALWAYS:
		ptr = tl_nn(ALWAYS, False, ZN, miscell);
		ptr->time = miscell->TimeCon;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		ptr->rgt = tl_factor(cnt, hasuform, uform, miscell, tl_yychar);
/*		if(tl_simp_log_p)
		{	/* must be modified! */
/*			if (ptr->ntyp == V_OPER)
			{
				if (ptr->lft->ntyp == FALSE)
					break;	/* [][]p = []p */
/*				ptr = ptr->rgt;	/* [] (p V q) = [] q */
/*			}
		}
*/		goto simpl;

	case NEXT:
		ptr = tl_nn(NEXT, ZN, ZN, miscell);
		ptr->time = miscell->TimeCon;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		ptr->lft = tl_factor(cnt, hasuform, uform, miscell, tl_yychar);
		goto simpl;

	case WEAKNEXT:
		ptr = tl_nn(WEAKNEXT, ZN, ZN, miscell);
		ptr->time = miscell->TimeCon;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		ptr->lft = tl_factor(cnt, hasuform, uform, miscell, tl_yychar);
		goto simpl;

	case EVENTUALLY:
		ptr = tl_nn(EVENTUALLY, True, ZN, miscell);
		ptr->time = miscell->TimeCon;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		ptr->rgt = tl_factor(cnt, hasuform, uform, miscell, tl_yychar);

/*	case U_OPER:
		ptr = tl_nn(U_OPER, ZN, ZN);
		ptr->time = miscell->TimeCon;
		(*tl_yychar) = tl_yylex();
		ptr->lft = tl_factor();
		goto simpl;
*/		goto simpl;

/*	case IMPLIES:
		ptr = tl_nn(OR, Not(ptr->lft), ptr->rgt);
		goto simpl;

/*	case EQUIV:
		a = tl_nn(AND,dupnode(ptr->lft),dupnode(ptr->rgt));
		b = tl_nn(AND,Not(ptr->lft),Not(ptr->rgt));
		ptr = tl_nn(OR, a, b); */

	simpl:
		if (tl_simp_log_p)
		  ptr = bin_simpler(ptr,miscell,cnt,uform, tl_yychar);
		break;

	case PREDICATE:
		ptr = miscell->tl_yylval;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		break;

	case TRUE:
	case FALSE:
		ptr = miscell->tl_yylval;
		(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
		break;
	}
	if (!ptr) tl_yyerror("expected predicate", cnt, uform, tl_yychar, miscell);
	return ptr;
}

/*Function for organizing the newly generated nodes into a tree structure*/
static Node *tl_level(int nr, int *cnt, size_t hasuform, char *uform, Miscellaneous *miscell, int *tl_yychar)
{/*Taken from S-TaLiRo Software*/
	int i; Node *ptr = ZN;
	Interval LocInter;
	int tl_simp_log_p = 0;
	static int	prec[2][4] = {
	{ U_OPER,  V_OPER, 0, 0},  /* left associative */
	{ OR, AND, IMPLIES, EQUIV, },	/* left associative */
};


	if (nr < 0)
		return tl_factor(cnt, hasuform, uform, miscell, tl_yychar);

	ptr = tl_level(nr-1, cnt, hasuform, uform, miscell, tl_yychar);
again:
	for (i = 0; i < 4; i++)
		if ((*tl_yychar) == prec[nr][i])
		{
			if (nr==0 && (i==0 || i==1))
				LocInter = miscell->TimeCon;
			(*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
			ptr = tl_nn(prec[nr][i],ptr,tl_level(nr-1, cnt, hasuform, uform, miscell, tl_yychar), miscell);
			if (nr==0 && (i==0 || i==1))
				ptr->time = LocInter;
			if(tl_simp_log_p)
				ptr = bin_simpler(ptr,miscell,cnt,uform, tl_yychar);
			else
				ptr = bin_minimal(ptr,miscell,cnt,uform, tl_yychar);
			goto again;
		}
	if (!ptr) tl_yyerror("syntax error", cnt, uform, tl_yychar, miscell);
	return ptr;
}

/*Function for reading the first word*/
static Node *
tl_formula(int *cnt, size_t hasuform, char *uform, Miscellaneous *miscell, int *tl_yychar)
{/*Taken from S-TaLiRo Software*/
    Node *tmpptr;
    (*tl_yychar) = tl_yylex(cnt, hasuform, uform, miscell, tl_yychar);
    tmpptr=tl_level(1, cnt, hasuform, uform, miscell, tl_yychar);
	return tmpptr;/* 2 precedence levels, 1 and 0 */
}

/*Function for starting the parsing procedure*/
Node *tl_parse(int *cnt, size_t hasuform, char *uform, Miscellaneous *miscell, int *tl_yychar)
{/*Taken from S-TaLiRo Software*/
	int tl_verbose_p = 0;
   Node *n = tl_formula(cnt, hasuform, uform, miscell, tl_yychar);
   if (tl_verbose_p)
	{	printf("formula: ");
		put_uform(uform, miscell);
		printf("\n");
	}
	return(n);
}

