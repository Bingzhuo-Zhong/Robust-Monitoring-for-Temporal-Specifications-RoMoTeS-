/***** mx_romotes : cache.c *****/
/* Version 1.0				     */

/*Edited by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS*/

/*All functions in this file are taken from S-TaLiRo Software Written by Georgios Fainekos  ASU, U.S.A*/

/*The functions in this file work for formula simplification, but they are not even called in RoMoTeS*/
/*considering that they are not even used in S-TaLiRo, although they are given, application of these*/
/*of these functions remain to be studied.*/


#include "mex.h"
#include "matrix.h"
#include "distances.h"
#include "stl2tree.h"

#define BUFF_LEN 4096

int implies(Node *a, Node *b, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
  return
    (isequal(a,b, cnt, uform, tl_yychar, miscell) ||
     b->ntyp == TRUE ||
     a->ntyp == FALSE ||
     (b->ntyp == AND && implies(a, b->lft, cnt, uform, tl_yychar, miscell) && implies(a, b->rgt, cnt, uform, tl_yychar, miscell)) ||
     (a->ntyp == OR && implies(a->lft, b, cnt, uform, tl_yychar, miscell) && implies(a->rgt, b, cnt, uform, tl_yychar, miscell)) ||
     (a->ntyp == AND && (implies(a->lft, b, cnt, uform, tl_yychar, miscell) || implies(a->rgt, b, cnt, uform, tl_yychar, miscell))) ||
     (b->ntyp == OR && (implies(a, b->lft, cnt, uform, tl_yychar, miscell) || implies(a, b->rgt, cnt, uform, tl_yychar, miscell))) ||
     (b->ntyp == U_OPER && implies(a, b->rgt, cnt, uform, tl_yychar, miscell)) ||
     (a->ntyp == V_OPER && implies(a->rgt, b, cnt, uform, tl_yychar, miscell)) ||
     (a->ntyp == U_OPER && implies(a->lft, b, cnt, uform, tl_yychar, miscell) && implies(a->rgt, b, cnt, uform, tl_yychar, miscell)) ||
     (b->ntyp == V_OPER && implies(a, b->lft, cnt, uform, tl_yychar, miscell) && implies(a, b->rgt, cnt, uform, tl_yychar, miscell)) ||
     ((a->ntyp == U_OPER || a->ntyp == V_OPER) && a->ntyp == b->ntyp &&
         implies(a->lft, b->lft, cnt, uform, tl_yychar, miscell) && implies(a->rgt, b->rgt, cnt, uform, tl_yychar, miscell)));
}

Node *bin_simpler(Node *ptr, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar)
{	Node *a, *b;

	if (ptr)
	switch (ptr->ntyp) {
	case U_OPER:
		if (ptr->rgt->ntyp == TRUE
		||  ptr->rgt->ntyp == FALSE
		||  ptr->lft->ntyp == FALSE)
		{	ptr = ptr->rgt;
			break;
		}
		if (implies(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell)) /* NEW */
		{	ptr = ptr->rgt;
		        break;
		}
		if (ptr->lft->ntyp == U_OPER
		&&  isequal(ptr->lft->lft, ptr->rgt, cnt, uform, tl_yychar, miscell))
		{	/* (p U q) U p = (q U p) */
			ptr->lft = ptr->lft->rgt;
			break;
		}
		if (ptr->rgt->ntyp == U_OPER
		&&  implies(ptr->lft, ptr->rgt->lft, cnt, uform, tl_yychar, miscell))
		{	/* NEW */
			ptr = ptr->rgt;
			break;
		}
		/* X p U X q == X (p U q) */
		if (ptr->rgt->ntyp == NEXT
		&&  ptr->lft->ntyp == NEXT)
		{	ptr = tl_nn(NEXT,
				tl_nn(U_OPER,
					ptr->lft->lft,
					ptr->rgt->lft, miscell), ZN, miscell);
		        break;
		}

		/* NEW : F X p == X F p */
		if (ptr->lft->ntyp == TRUE &&
		    ptr->rgt->ntyp == NEXT) {
		  ptr = tl_nn(NEXT, tl_nn(U_OPER, True, ptr->rgt->lft, miscell), ZN, miscell);
		  break;
		}

		/* NEW : F G F p == G F p */
		if (ptr->lft->ntyp == TRUE &&
		    ptr->rgt->ntyp == V_OPER &&
		    ptr->rgt->lft->ntyp == FALSE &&
		    ptr->rgt->rgt->ntyp == U_OPER &&
		    ptr->rgt->rgt->lft->ntyp == TRUE) {
		  ptr = ptr->rgt;
		  break;
		}

		/* NEW */
		if (ptr->lft->ntyp != TRUE &&
		    implies(push_negation(tl_nn(NOT, dupnode(ptr->rgt), ZN, miscell), miscell, cnt, uform, tl_yychar), ptr->lft, cnt, uform, tl_yychar, miscell))
		{       ptr->lft = True;
		        break;
		}
		break;
	case V_OPER:
		if (ptr->rgt->ntyp == FALSE
		||  ptr->rgt->ntyp == TRUE
		||  ptr->lft->ntyp == TRUE)
		{	ptr = ptr->rgt;
			break;
		}
		if (implies(ptr->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))
		{	/* p V p = p */
			ptr = ptr->rgt;
			break;
		}
		/* F V (p V q) == F V q */
		if (ptr->lft->ntyp == FALSE
		&&  ptr->rgt->ntyp == V_OPER)
		{	ptr->rgt = ptr->rgt->rgt;
			break;
		}
		/* NEW : G X p == X G p */
		if (ptr->lft->ntyp == FALSE &&
		    ptr->rgt->ntyp == NEXT) {
		  ptr = tl_nn(NEXT, tl_nn(V_OPER, False, ptr->rgt->lft, miscell), ZN, miscell);
		  break;
		}
		/* NEW : G F G p == F G p */
		if (ptr->lft->ntyp == FALSE &&
		    ptr->rgt->ntyp == U_OPER &&
		    ptr->rgt->lft->ntyp == TRUE &&
		    ptr->rgt->rgt->ntyp == V_OPER &&
		    ptr->rgt->rgt->lft->ntyp == FALSE) {
		  ptr = ptr->rgt;
		  break;
		}

		/* NEW */
		if (ptr->rgt->ntyp == V_OPER
		&&  implies(ptr->rgt->lft, ptr->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->rgt;
			break;
		}

		/* NEW */
		if (ptr->lft->ntyp != FALSE &&
		    implies(ptr->lft,
			    push_negation(tl_nn(NOT, dupnode(ptr->rgt), ZN, miscell), miscell, cnt, uform, tl_yychar), cnt, uform, tl_yychar, miscell))
		{       ptr->lft = False;
		        break;
		}
		break;
	case NEXT:
		/* NEW : X G F p == G F p */
		if (ptr->lft->ntyp == V_OPER &&
		    ptr->lft->lft->ntyp == FALSE &&
		    ptr->lft->rgt->ntyp == U_OPER &&
		    ptr->lft->rgt->lft->ntyp == TRUE) {
		  break;
		}
		/* NEW : X F G p == F G p */
		if (ptr->lft->ntyp == U_OPER &&
		    ptr->lft->lft->ntyp == TRUE &&
		    ptr->lft->rgt->ntyp == V_OPER &&
		    ptr->lft->rgt->lft->ntyp == FALSE) {
		  break;
		}
		break;
	case ALWAYS:
		/* NEW : [] G F p == G F p */
		if (ptr->rgt->ntyp == V_OPER &&
		    ptr->rgt->rgt->ntyp == FALSE &&
		    ptr->rgt->lft->ntyp == U_OPER &&
		    ptr->rgt->lft->rgt->ntyp == TRUE) {
		  ptr = ptr->rgt;
		  break;
		}
		/* NEW : [] F G p == F G p */
		if (ptr->rgt->ntyp == U_OPER &&
		    ptr->rgt->rgt->ntyp == TRUE &&
		    ptr->rgt->lft->ntyp == V_OPER &&
		    ptr->rgt->lft->rgt->ntyp == FALSE) {
		  ptr = ptr->rgt;
		  break;
		}
		break;

	case IMPLIES:
		if (implies(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell))
		  {	ptr = True;
			break;
		}
		ptr = tl_nn(OR, Not(ptr->lft), ptr->rgt, miscell);
		ptr = canonical(right_linked(ptr), miscell, cnt, uform, tl_yychar);
		break;
	case EQUIV:
		if (implies(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell) &&
		    implies(ptr->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))
		  {	ptr = True;
			break;
		}
		a = canonical(right_linked(tl_nn(AND,
			dupnode(ptr->lft),
			dupnode(ptr->rgt), miscell)), miscell, cnt, uform, tl_yychar);
		b = canonical(right_linked(tl_nn(AND,
			Not(ptr->lft),
			Not(ptr->rgt), miscell)), miscell, cnt, uform, tl_yychar);
		ptr = tl_nn(OR, a, b, miscell);
		ptr = canonical(right_linked(ptr), miscell, cnt, uform, tl_yychar);
		break;
	case AND:
		/* p && (q U p) = p */
		if (ptr->rgt->ntyp == U_OPER
		&&  isequal(ptr->rgt->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->lft;
			break;
		}
		if (ptr->lft->ntyp == U_OPER
		&&  isequal(ptr->lft->rgt, ptr->rgt, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->rgt;
			break;
		}

		/* p && (q V p) == q V p */
		if (ptr->rgt->ntyp == V_OPER
		&&  isequal(ptr->rgt->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->rgt;
			break;
		}
		if (ptr->lft->ntyp == V_OPER
		&&  isequal(ptr->lft->rgt, ptr->rgt, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->lft;
			break;
		}

		/* (p U q) && (r U q) = (p && r) U q*/
		if (ptr->rgt->ntyp == U_OPER
		&&  ptr->lft->ntyp == U_OPER
		&&  isequal(ptr->rgt->rgt, ptr->lft->rgt, cnt, uform, tl_yychar, miscell))
		{	ptr = tl_nn(U_OPER,
				tl_nn(AND, ptr->lft->lft, ptr->rgt->lft, miscell),
				ptr->lft->rgt, miscell);
			break;
		}

		/* (p V q) && (p V r) = p V (q && r) */
		if (ptr->rgt->ntyp == V_OPER
		&&  ptr->lft->ntyp == V_OPER
		&&  isequal(ptr->rgt->lft, ptr->lft->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = tl_nn(V_OPER,
				ptr->rgt->lft,
				tl_nn(AND, ptr->lft->rgt, ptr->rgt->rgt, miscell), miscell);
			break;
		}
		/* X p && X q == X (p && q) */
		if (ptr->rgt->ntyp == NEXT
		&&  ptr->lft->ntyp == NEXT)
		{	ptr = tl_nn(NEXT,
				tl_nn(AND,
					ptr->rgt->lft,
					ptr->lft->lft, miscell), ZN, miscell);
			break;
		}
		/* (p V q) && (r U q) == p V q */
		if (ptr->rgt->ntyp == U_OPER
		&&  ptr->lft->ntyp == V_OPER
		&&  isequal(ptr->lft->rgt, ptr->rgt->rgt, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->lft;
			break;
		}

		if (isequal(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell)	/* (p && p) == p */
		||  ptr->rgt->ntyp == FALSE	/* (p && F) == F */
		||  ptr->lft->ntyp == TRUE	/* (T && p) == p */
		||  implies(ptr->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))/* NEW */
		{	ptr = ptr->rgt;
			break;
		}
		if (ptr->rgt->ntyp == TRUE	/* (p && T) == p */
		||  ptr->lft->ntyp == FALSE	/* (F && p) == F */
		||  implies(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell))/* NEW */
		{	ptr = ptr->lft;
			break;
		}

		/* NEW : F G p && F G q == F G (p && q) */
		if (ptr->lft->ntyp == U_OPER &&
		    ptr->lft->lft->ntyp == TRUE &&
		    ptr->lft->rgt->ntyp == V_OPER &&
		    ptr->lft->rgt->lft->ntyp == FALSE &&
		    ptr->rgt->ntyp == U_OPER &&
		    ptr->rgt->lft->ntyp == TRUE &&
		    ptr->rgt->rgt->ntyp == V_OPER &&
		    ptr->rgt->rgt->lft->ntyp == FALSE)
		  {
		    ptr = tl_nn(U_OPER, True,
				tl_nn(V_OPER, False,
				      tl_nn(AND, ptr->lft->rgt->rgt,
					    ptr->rgt->rgt->rgt, miscell), miscell), miscell);
		    break;
		  }

		/* NEW */
		if (implies(ptr->lft,
			    push_negation(tl_nn(NOT, dupnode(ptr->rgt), ZN, miscell), miscell, cnt, uform, tl_yychar), cnt, uform, tl_yychar, miscell)
		 || implies(ptr->rgt,
			    push_negation(tl_nn(NOT, dupnode(ptr->lft), ZN, miscell), miscell, cnt, uform, tl_yychar), cnt, uform, tl_yychar, miscell))
		{       ptr = False;
		        break;
		}
		break;

	case OR:
		/* p || (q U p) == q U p */
		if (ptr->rgt->ntyp == U_OPER
		&&  isequal(ptr->rgt->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->rgt;
			break;
		}

		/* p || (q V p) == p */
		if (ptr->rgt->ntyp == V_OPER
		&&  isequal(ptr->rgt->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->lft;
			break;
		}

		/* (p U q) || (p U r) = p U (q || r) */
		if (ptr->rgt->ntyp == U_OPER
		&&  ptr->lft->ntyp == U_OPER
		&&  isequal(ptr->rgt->lft, ptr->lft->lft, cnt, uform, tl_yychar, miscell))
		{	ptr = tl_nn(U_OPER,
				ptr->rgt->lft,
				tl_nn(OR, ptr->lft->rgt, ptr->rgt->rgt, miscell), miscell);
			break;
		}

		if (isequal(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell)	/* (p || p) == p */
		||  ptr->rgt->ntyp == FALSE	/* (p || F) == p */
		||  ptr->lft->ntyp == TRUE	/* (T || p) == T */
		||  implies(ptr->rgt, ptr->lft, cnt, uform, tl_yychar, miscell))/* NEW */
		{	ptr = ptr->lft;
			break;
		}
		if (ptr->rgt->ntyp == TRUE	/* (p || T) == T */
		||  ptr->lft->ntyp == FALSE	/* (F || p) == p */
		||  implies(ptr->lft, ptr->rgt, cnt, uform, tl_yychar, miscell))/* NEW */
		{	ptr = ptr->rgt;
			break;
		}

		/* (p V q) || (r V q) = (p || r) V q */
		if (ptr->rgt->ntyp == V_OPER
		&&  ptr->lft->ntyp == V_OPER
		&&  isequal(ptr->lft->rgt, ptr->rgt->rgt, cnt, uform, tl_yychar, miscell))
		{	ptr = tl_nn(V_OPER,
				tl_nn(OR, ptr->lft->lft, ptr->rgt->lft, miscell),
				ptr->rgt->rgt, miscell);
			break;
		}

		/* (p V q) || (r U q) == r U q */
		if (ptr->rgt->ntyp == U_OPER
		&&  ptr->lft->ntyp == V_OPER
		&&  isequal(ptr->lft->rgt, ptr->rgt->rgt, cnt, uform, tl_yychar, miscell))
		{	ptr = ptr->rgt;
			break;
		}

		/* NEW : G F p || G F q == G F (p || q) */
		if (ptr->lft->ntyp == V_OPER &&
		    ptr->lft->lft->ntyp == FALSE &&
		    ptr->lft->rgt->ntyp == U_OPER &&
		    ptr->lft->rgt->lft->ntyp == TRUE &&
		    ptr->rgt->ntyp == V_OPER &&
		    ptr->rgt->lft->ntyp == FALSE &&
		    ptr->rgt->rgt->ntyp == U_OPER &&
		    ptr->rgt->rgt->lft->ntyp == TRUE)
		  {
		    ptr = tl_nn(V_OPER, False,
				tl_nn(U_OPER, True,
				      tl_nn(OR, ptr->lft->rgt->rgt,
					    ptr->rgt->rgt->rgt, miscell), miscell), miscell);
		    break;
		  }

		/* NEW */
		if (implies(push_negation(tl_nn(NOT, dupnode(ptr->rgt), ZN, miscell), miscell, cnt, uform, tl_yychar),
			    ptr->lft, cnt, uform, tl_yychar, miscell)
		 || implies(push_negation(tl_nn(NOT, dupnode(ptr->lft), ZN, miscell), miscell, cnt, uform, tl_yychar),
			    ptr->rgt, cnt, uform, tl_yychar, miscell))
		{       ptr = True;
		        break;
		}
		break;
	}
	return ptr;
}


Node *right_linked(Node *n)
{
	if (!n)
		return n;

	if (n->ntyp == AND || n->ntyp == OR)
		while (n->lft && n->lft->ntyp == n->ntyp)
		{
			Node *tmp = n->lft;
			n->lft = tmp->rgt;
			tmp->rgt = n;
			n = tmp;
		}

	n->lft = right_linked(n->lft);
	n->rgt = right_linked(n->rgt);

	return n;
}

/* assumes input is right_linked */
Node *canonical(Node *n, Miscellaneous *miscell, int *cnt, char *uform , int *tl_yychar)
{
	Node *m;

	if (!n)
		return n;

	if (m = in_cache(n, cnt, uform, tl_yychar, miscell))
		return m;

	n->rgt = canonical(n->rgt, miscell, cnt, uform, tl_yychar);
	n->lft = canonical(n->lft, miscell, cnt, uform, tl_yychar);

	return cached(n, miscell, cnt, uform, tl_yychar);
}


static void addcan(int tok, Node *n, Miscellaneous *miscell)
{	Node	*m, *prev = ZN;
	Node	**ptr;
	Node	*N;
	Symbol	*s, *t; int cmp;
	static char	dumpbuf[BUFF_LEN];
	static Node	*can = ZN;

	if (!n) return;

	if (n->ntyp == tok)
	{	addcan(tok, n->rgt, miscell);
		addcan(tok, n->lft, miscell);
		return;
	}
#if 0
	if ((tok == AND && n->ntyp == TRUE)
	||  (tok == OR  && n->ntyp == FALSE))
		return;
#endif
	N = dupnode(n);
	if (!can)
	{	can = N;
		return;
	}

	s = DoDump(N,dumpbuf, miscell);
	if (can->ntyp != tok)	/* only one element in list so far */
	{	ptr = &can;
		goto insert;
	}

	/* there are at least 2 elements in list */
	prev = ZN;
	for (m = can; m->ntyp == tok && m->rgt; prev = m, m = m->rgt)
	{	t = DoDump(m->lft,dumpbuf, miscell);
		cmp = strcmp(s->name, t->name);
		if (cmp == 0)	/* duplicate */
			return;
		if (cmp < 0)
		{	if (!prev)
			{	can = tl_nn(tok, N, can, miscell);
				return;
			} else
			{	ptr = &(prev->rgt);
				goto insert;
	}	}	}

	/* new entry goes at the end of the list */
	ptr = &(prev->rgt);
insert:
	t = DoDump(*ptr,dumpbuf, miscell);
	cmp = strcmp(s->name, t->name);
	if (cmp == 0)	/* duplicate */
		return;
	if (cmp < 0)
		*ptr = tl_nn(tok, N, *ptr, miscell);
	else
		*ptr = tl_nn(tok, *ptr, N, miscell);
}


static void
marknode(int tok, Node *m)
{
	if (m->ntyp != tok)
	{	releasenode(0, m->rgt);
		m->rgt = ZN;
	}
	m->ntyp = -1;
}

Node *Canonical(Node *n, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar)
{	Node *m, *p, *k1, *k2, *prev, *dflt = ZN;
	int tok;
	static Node	*can = ZN;


	if (!n) return n;

	tok = n->ntyp;
	if (tok != AND && tok != OR)
		return n;

	can = ZN;
	addcan(tok, n, miscell);
#if 1
	Debug("\nA0: "); Dump(can);
	Debug("\nA1: "); Dump(n); Debug("\n");
#endif
	releasenode(1, n);

	/* mark redundant nodes */
	if (tok == AND)
	{	for (m = can; m; m = (m->ntyp == AND) ? m->rgt : ZN)
		{	k1 = (m->ntyp == AND) ? m->lft : m;
			if (k1->ntyp == TRUE)
			{	marknode(AND, m);
				dflt = True;
				continue;
			}
			if (k1->ntyp == FALSE)
			{	releasenode(1, can);
				can = False;
				goto out;
		}	}
		for (m = can; m; m = (m->ntyp == AND) ? m->rgt : ZN)
		for (p = can; p; p = (p->ntyp == AND) ? p->rgt : ZN)
		{	if (p == m
			||  p->ntyp == -1
			||  m->ntyp == -1)
				continue;
			k1 = (m->ntyp == AND) ? m->lft : m;
			k2 = (p->ntyp == AND) ? p->lft : p;

			if (isequal(k1, k2, cnt, uform, tl_yychar, miscell))
			{	marknode(AND, p);
				continue;
			}
			if (anywhere(OR, k1, k2, cnt, uform, tl_yychar, miscell))
			{	marknode(AND, p);
				continue;
			}
			if (k2->ntyp == U_OPER
			&&  anywhere(AND, k2->rgt, can, cnt, uform, tl_yychar, miscell))
			{	marknode(AND, p);
				continue;
			}	/* q && (p U q) = q */
	}	}
	if (tok == OR)
	{	for (m = can; m; m = (m->ntyp == OR) ? m->rgt : ZN)
		{	k1 = (m->ntyp == OR) ? m->lft : m;
			if (k1->ntyp == FALSE)
			{	marknode(OR, m);
				dflt = False;
				continue;
			}
			if (k1->ntyp == TRUE)
			{	releasenode(1, can);
				can = True;
				goto out;
		}	}
		for (m = can; m; m = (m->ntyp == OR) ? m->rgt : ZN)
		for (p = can; p; p = (p->ntyp == OR) ? p->rgt : ZN)
		{	if (p == m
			||  p->ntyp == -1
			||  m->ntyp == -1)
				continue;
			k1 = (m->ntyp == OR) ? m->lft : m;
			k2 = (p->ntyp == OR) ? p->lft : p;

			if (isequal(k1, k2, cnt, uform, tl_yychar, miscell))
			{	marknode(OR, p);
				continue;
			}
			if (anywhere(AND, k1, k2, cnt, uform, tl_yychar, miscell))
			{	marknode(OR, p);
				continue;
			}
			if (k2->ntyp == V_OPER
			&&  k2->lft->ntyp == FALSE
			&&  anywhere(AND, k2->rgt, can, cnt, uform, tl_yychar, miscell))
			{	marknode(OR, p);
				continue;
			}	/* p || (F V p) = p */
	}	}
	for (m = can, prev = ZN; m; )	/* remove marked nodes */
	{	if (m->ntyp == -1)
		{	k2 = m->rgt;
			releasenode(0, m);
			if (!prev)
			{	m = can = can->rgt;
			} else
			{	m = prev->rgt = k2;
				/* if deleted the last node in a chain */
				if (!prev->rgt && prev->lft
				&&  (prev->ntyp == AND || prev->ntyp == OR))
				{	k1 = prev->lft;
					prev->ntyp = prev->lft->ntyp;
					prev->sym = prev->lft->sym;
					prev->rgt = prev->lft->rgt;
					prev->lft = prev->lft->lft;
					releasenode(0, k1);
				}
			}
			continue;
		}
		prev = m;
		m = m->rgt;
	}
out:
#if 1
	Debug("A2: "); Dump(can); Debug("\n");
#endif
	if (!can)
	{	if (!dflt)
			fatal("cannot happen, Canonical", (char *) 0, cnt, uform, tl_yychar, miscell);
		return dflt;
	}

	return can;
}


static int	ismatch(Node *, Node *);
int	sameform(Node *, Node *, int *cnt, char *uform, int *tl_yychar, Miscellaneous *);

void cache_dump(Miscellaneous *miscell)
{	Cache *d; int nr=0;
	static Cache	*stored = (Cache *) 0;

	printf("\nCACHE DUMP:\n");
	for (d = stored; d; d = d->nxt, nr++)
	{	if (d->same) continue;
		printf("B%3d: ", nr); dump(d->before, miscell); printf("\n");
		printf("A%3d: ", nr); dump(d->after, miscell); printf("\n");
	}
	printf("============\n");
}

Node *in_cache(Node *n, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	Cache *d; int nr=0;
	static Cache	*stored = (Cache *) 0;
	static unsigned long CacheHits;

	for (d = stored; d; d = d->nxt, nr++)
		if (isequal(d->before, n, cnt, uform, tl_yychar, miscell))
		{	CacheHits++;
			if (d->same && ismatch(n, d->before)) return n;
			return dupnode(d->after);
		}
	return ZN;
}

Node * cached(Node *n, Miscellaneous *miscell, int *cnt, char *uform, int *tl_yychar)
{	Cache *d;
	Node *m;
	static Cache	*stored = (Cache *) 0;
	static unsigned long Caches;


	if (!n) return n;
	if (m = in_cache(n, cnt, uform, tl_yychar, miscell))
		return m;

	Caches++;
	d = (Cache *) emalloc(sizeof(Cache));
	d->before = dupnode(n);
	d->after  = Canonical(n, miscell, cnt, uform, tl_yychar); /* n is released */

	if (ismatch(d->before, d->after))
	{	d->same = 1;
		releasenode(1, d->after);
		d->after = d->before;
	}
	d->nxt = stored;
	stored = d;
	return dupnode(d->after);
}

void cache_stats(void)
{
	static unsigned long Caches;
	static unsigned long CacheHits;

	printf("cache stores     : %9ld\n", Caches);
	printf("cache hits       : %9ld\n", CacheHits);
}

int one_lft(int ntyp, Node *x, Node *in, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!x)  return 1;
	if (!in) return 0;

	if (sameform(x, in, cnt, uform, tl_yychar, miscell))
		return 1;

	if (in->ntyp != ntyp)
		return 0;

	if (one_lft(ntyp, x, in->lft, cnt, uform, tl_yychar, miscell))
		return 1;

	return one_lft(ntyp, x, in->rgt, cnt, uform, tl_yychar, miscell);
}

int
all_lfts(int ntyp, Node *from, Node *in, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!from) return 1;

	if (from->ntyp != ntyp)
		return one_lft(ntyp, from, in, cnt, uform, tl_yychar, miscell);

	if (!one_lft(ntyp, from->lft, in, cnt, uform, tl_yychar, miscell))
		return 0;

	return all_lfts(ntyp, from->rgt, in, cnt, uform, tl_yychar, miscell);
}

int
sametrees(int ntyp, Node *a, Node *b, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{	/* toplevel is an AND or OR */
	/* both trees are right-linked, but the leafs */
	/* can be in different places in the two trees */

	if (!all_lfts(ntyp, a, b, cnt, uform, tl_yychar, miscell))
		return 0;

	return all_lfts(ntyp, b, a, cnt, uform, tl_yychar, miscell);
}

int	/* a better isequal() */
sameform(Node *a, Node *b, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!a && !b) return 1;
	if (!a || !b) return 0;
	if (a->ntyp != b->ntyp) return 0;

	if (a->sym
	&&  b->sym
	&&  strcmp(a->sym->name, b->sym->name) != 0)
		return 0;

	switch (a->ntyp) {
	case TRUE:
	case FALSE:
		return 1;
	case PREDICATE:
		if (!a->sym || !b->sym) fatal("sameform...", (char *) 0, cnt, uform, tl_yychar, miscell);
		return !strcmp(a->sym->name, b->sym->name);

	case NOT:
	case NEXT:
		return sameform(a->lft, b->lft, cnt, uform, tl_yychar, miscell);
	case U_OPER:
	case V_OPER:
		if (!sameform(a->lft, b->lft, cnt, uform, tl_yychar, miscell))
			return 0;
		if (!sameform(a->rgt, b->rgt, cnt, uform, tl_yychar, miscell))
			return 0;
		return 1;

	case AND:
	case OR:	/* the hard case */
		return sametrees(a->ntyp, a, b, cnt, uform, tl_yychar, miscell);

	default:
		printf("type: %d\n", a->ntyp);
		fatal("cannot happen, sameform", (char *) 0, cnt, uform, tl_yychar, miscell);
	}

	return 0;
}

int
isequal(Node *a, Node *b, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!a && !b)
		return 1;

	if (!a || !b)
	{	if (!a)
		{	if (b->ntyp == TRUE)
				return 1;
		} else
		{	if (a->ntyp == TRUE)
				return 1;
		}
		return 0;
	}
	if (a->ntyp != b->ntyp)
		return 0;

	if (a->sym
	&&  b->sym
	&&  strcmp(a->sym->name, b->sym->name) != 0)
		return 0;

	if (isequal(a->lft, b->lft, cnt, uform, tl_yychar, miscell)
	&&  isequal(a->rgt, b->rgt, cnt, uform, tl_yychar, miscell))
		return 1;

	return sameform(a, b, cnt, uform, tl_yychar, miscell);
}

static int
ismatch(Node *a, Node *b)
{
	if (!a && !b) return 1;
	if (!a || !b) return 0;
	if (a->ntyp != b->ntyp) return 0;

	if (a->sym
	&&  b->sym
	&&  strcmp(a->sym->name, b->sym->name) != 0)
		return 0;

	if (ismatch(a->lft, b->lft)
	&&  ismatch(a->rgt, b->rgt))
		return 1;

	return 0;
}

int
any_term(Node *srch, Node *in, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!in) return 0;

	if (in->ntyp == AND)
		return	any_term(srch, in->lft, cnt, uform, tl_yychar, miscell) ||
			any_term(srch, in->rgt, cnt, uform, tl_yychar, miscell);

	return isequal(in, srch, cnt, uform, tl_yychar, miscell);
}

int
any_and(Node *srch, Node *in, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!in) return 0;

	if (srch->ntyp == AND)
		return	any_and(srch->lft, in, cnt, uform, tl_yychar, miscell) &&
			any_and(srch->rgt, in, cnt, uform, tl_yychar, miscell);

	return any_term(srch, in, cnt, uform, tl_yychar, miscell);
}

int
any_lor(Node *srch, Node *in, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!in) return 0;

	if (in->ntyp == OR)
		return	any_lor(srch, in->lft, cnt, uform, tl_yychar, miscell) ||
			any_lor(srch, in->rgt, cnt, uform, tl_yychar, miscell);

	return isequal(in, srch, cnt, uform, tl_yychar, miscell);
}

int
anywhere(int tok, Node *srch, Node *in, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{
	if (!in) return 0;

	switch (tok) {
	case AND:	return any_and(srch, in, cnt, uform, tl_yychar, miscell);
	case  OR:	return any_lor(srch, in, cnt, uform, tl_yychar, miscell);
	case   0:	return any_term(srch, in, cnt, uform, tl_yychar, miscell);
	}
	fatal("cannot happen, anywhere", (char *) 0, cnt, uform, tl_yychar, miscell);
	return 0;
}
