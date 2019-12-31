/***** mx_romotes : mx_romotes.c *****/

/* Version 1.0				     */

/*Edited by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS*/

/*Following functions in this file are developed bY ZHONG Bingzhuo
"mexFunction"

/*Following functions in this file are taken from S-TaLiRo Software Written by Georgios Fainekos and  ASU, U.S.A.
"emalloc"
"tl_Getchar"
"tl_UnGetchar"
"sdump"
"DoDump"
"dump"
"tl_explain"
"non_fatal"
"tl_yyerror"
"Fatal"
"fatal"
"put_uform"
"tl_exit"
*/


#include <stdlib.h>
#include "mex.h"
#include "matrix.h"
#include "distances.h"
#include "stl2tree.h"
#include "param.h"


#define BUFF_LEN 4096

/*apply for space with size n*/
char * emalloc(size_t n)
{/*Taken from S-TaLiRo Software*/
	char *tmp;

	if (!(tmp = (char *) mxMalloc(n)))
        mexErrMsgTxt("mx_romotes: not enough memory!");
	memset(tmp, 0, n);
	return tmp;
}

/*Obtained the following char, move the pointer forward*/
int tl_Getchar(int *cnt, size_t hasuform, char *uform)
{/*Taken from S-TaLiRo Software*/
	if (*cnt < hasuform)
		return uform[(*cnt)++];
	(*cnt)++;
	return -1;
}

/*Move the pointer backward*/
void tl_UnGetchar(int *cnt)
{/*Taken from S-TaLiRo Software*/
	if (*cnt > 0) (*cnt)--;
}

#define Binop(a)		\
		fprintf(miscell->tl_out, "(");	\
		dump(n->lft, miscell);		\
		fprintf(miscell->tl_out, a);	\
		dump(n->rgt, miscell);		\
		fprintf(miscell->tl_out, ")")

static void sdump(Node *n, char	*dumpbuf)
{/*Taken from S-TaLiRo Software*/
	switch (n->ntyp) {
	case PREDICATE:	strcat(dumpbuf, n->sym->name);
			break;
	case U_OPER:	strcat(dumpbuf, "U");
			goto common2;
	case V_OPER:	strcat(dumpbuf, "V");
			goto common2;
	case OR:	strcat(dumpbuf, "|");
			goto common2;
	case AND:	strcat(dumpbuf, "&");
common2:		sdump(n->rgt,dumpbuf);
common1:		sdump(n->lft,dumpbuf);
			break;
	case NEXT:	strcat(dumpbuf, "X");
			goto common1;
	case NOT:	strcat(dumpbuf, "!");
			goto common1;
	case TRUE:	strcat(dumpbuf, "T");
			break;
	case FALSE:	strcat(dumpbuf, "F");
			break;
	default:	strcat(dumpbuf, "?");
			break;
	}
}

Symbol *DoDump(Node *n, char *dumpbuf, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
	if (!n) return ZS;

	if (n->ntyp == PREDICATE)
		return n->sym;

	dumpbuf[0] = '\0';
	sdump(n,dumpbuf);
	return tl_lookup(dumpbuf, miscell);
}

void dump(Node *n, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
	if (!n) return;

	switch(n->ntyp) {
	case OR:	Binop(" || "); break;
	case AND:	Binop(" && "); break;
	case U_OPER:	Binop(" U ");  break;
	case V_OPER:	Binop(" V ");  break;
	case NEXT:
		fprintf(miscell->tl_out, "X");
		fprintf(miscell->tl_out, " (");
		dump(n->lft, miscell);
		fprintf(miscell->tl_out, ")");
		break;
	case NOT:
		fprintf(miscell->tl_out, "!");
		fprintf(miscell->tl_out, " (");
		dump(n->lft, miscell);
		fprintf(miscell->tl_out, ")");
		break;
	case FALSE:
		fprintf(miscell->tl_out, "false");
		break;
	case TRUE:
		fprintf(miscell->tl_out, "true");
		break;
	case PREDICATE:
		fprintf(miscell->tl_out, "(%s)", n->sym->name);
		break;
	case -1:
		fprintf(miscell->tl_out, " D ");
		break;
	default:
		printf("Unknown token: ");
		tl_explain(n->ntyp);
		break;
	}
}

/*To print the type of the current node*/
void tl_explain(int n)
{/*Taken from S-TaLiRo Software*/
	switch (n) {
	case ALWAYS:	printf("[]"); break;
	case EVENTUALLY: printf("<>"); break;
	case IMPLIES:	printf("->"); break;
	case EQUIV:	printf("<->"); break;
	case PREDICATE:	printf("predicate"); break;
	case OR:	printf("||"); break;
	case AND:	printf("&&"); break;
	case NOT:	printf("!"); break;
	case U_OPER:	printf("U"); break;
	case V_OPER:	printf("V"); break;
	case NEXT:	printf("X"); break;
	case TRUE:	printf("true"); break;
	case FALSE:	printf("false"); break;
	case ';':	printf("end of formula"); break;
	default:	printf("%c", n); break;
	}
}

/* cluster of functions for reporting fatal errors */

static void non_fatal(char *s1, char *s2, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
	int i;

	printf("TaLiRo: ");
	if (s2)
		printf(s1, s2);
	else
		printf(s1);
	if ((*tl_yychar) != -1 && (*tl_yychar) != 0)
	{	printf(", saw '");
		tl_explain((*tl_yychar));
		printf("'");
	}
	printf("\nTaLiRo: %s\n---------", uform);
	for (i = 0; i < (*cnt); i++)
		printf("-");
	printf("^\n");
	fflush(stdout);
	(miscell->tl_errs)++;
}

void
tl_yyerror(char *s1, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
	Fatal(s1, (char *) 0, cnt, uform, tl_yychar, miscell);
}

void
Fatal(char *s1, char *s2, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
  non_fatal(s1, s2, cnt, uform, tl_yychar, miscell);
}

void fatal(char *s1, char *s2, int *cnt, char *uform, int *tl_yychar, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
        non_fatal(s1, s2, cnt, uform, tl_yychar, miscell);
}

void put_uform(char *uform, Miscellaneous *miscell)
{/*Taken from S-TaLiRo Software*/
	fprintf(miscell->tl_out, "%s", uform);
}

void tl_exit(int i)
{/*Taken from S-TaLiRo Software*/
	mexErrMsgTxt("mx_romotes: unexpected error, tl_exit executed.");
}

/* end of cluster of functions for reporting fatal errors */


/*Interface function with MATLAB*/
void mexFunction(int nlhs, mxArray *plhs[],int nrhs, const mxArray *prhs[])
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
    /* Variables needed to process the input */
	int status;
    mwSize buflen, pbuflen;
	size_t NElems;
	mwSize ndimA, ndimb, ndimG, ndim, pdim;
	const mwSize *dimsA, *dimsb, *dimsG, *dims, *pardims;
	mwIndex jstruct, iii, jjj, i1, j1, idx_j;
	mxArray *tmp,*tmp_cell;
	/* Variables needed for monitor */
	Node *node;
	double *XTrace, *TStamps,*tempdouble,*Upperb,*Lowerb;
	bool *tempbool;
	PMap *predMap;
	int ii,jj,kk,ll;
	int npred;

	static char	uform[BUFF_LEN];
	static size_t hasuform=0;
	static int *cnt;
	int temp = 0;
	Miscellaneous *miscell = (Miscellaneous *) emalloc(sizeof(Miscellaneous));
	int *tl_yychar = (int *) emalloc(sizeof(int));

	/*To initialize necessary parameters for romotes*/
	miscell->romotes_param.LTL = 1;
	miscell->romotes_param.ConOnSamples = 0;
	miscell->romotes_param.SysDim = 0;
	miscell->romotes_param.nSamp = 0;
	miscell->romotes_param.nPred = 0;
	miscell->romotes_param.nInp = nrhs;
	miscell->romotes_param.max_delay_s=0.0;
	miscell->romotes_param.sample_f_s=0.0;
	miscell->romotes_param.lipschitz_on=false;
	miscell->tl_errs = 0;
	miscell->type_temp = 0;

	/* Other initializations */
	npred = 0;

	/* Reset cnt to 0:
		cnt is the counter that points to the next symbol in the formula
		to be processed. This is a static variable and it retains its
		value between Matlab calls to mx_romotes. */
	cnt = &temp;

	/* Make sure the I/O are in the right form */
    if(!nrhs == 5)
		mexErrMsgTxt("mx_romotes: 5 inputs are required.");
    else if(!mxIsChar(prhs[0]))
      mexErrMsgTxt("mx_romotes: 1st input must be a string with TL formula.");
    else if(!mxIsStruct(prhs[1]))
      mexErrMsgTxt("mx_romotes: 2nd input must be a structure (predicate map).");
    else if(!mxIsDouble(prhs[2]))
      mexErrMsgTxt("mx_romotes: 3rd input must be a numerical array (State trace).");
    else if(!mxIsDouble(prhs[3]))
      mexErrMsgTxt("mx_romotes: 4th input must be a numerical array (Time stamps).");
    else if(!mxIsStruct(prhs[4]))
      mexErrMsgTxt("mx_romotes: 5th input must be a structure (ROMOTES parameter).");

	if(nlhs > 1)
		mexErrMsgTxt("Too many output arguments.");

	plhs[0] = mxCreateDoubleMatrix(1,1,mxREAL);

	/* Process inputs */

	/* Get the formula */
	ndim = mxGetNumberOfDimensions(prhs[0]);
	dims = mxGetDimensions(prhs[0]);
	buflen = dims[1]*sizeof(mxChar)+1;
	if (buflen >= BUFF_LEN)
	{
      mexPrintf("%s%d%s\n", "The formula must be less than ", BUFF_LEN," characters.");
      mexErrMsgTxt("mx_romotes: Formula too long.");
	}
	status = mxGetString(prhs[0], uform, buflen);
    hasuform = strlen(uform);
    for (iii=0; iii<hasuform; iii++)
	{
		if (uform[iii] == '\t' || uform[iii] == '\"' || uform[iii] == '\n')
			uform[iii] = ' ';
	}

	/* Get state trace */
	ndim = mxGetNumberOfDimensions(prhs[2]);
	if (ndim>2)
		mexErrMsgTxt("mx_romotes: The state trace is not in proper form!");
	dims = mxGetDimensions(prhs[2]);
	miscell->romotes_param.nSamp = dims[0];
	miscell->romotes_param.SysDim = dims[1];
	XTrace = mxGetPr(prhs[2]);

	/* Get time stamps */
    ndim = mxGetNumberOfDimensions(prhs[3]);
	if (ndim>2)
		mexErrMsgTxt("mx_romotes: The time stamp sequence is not in proper form!");
	dims = mxGetDimensions(prhs[3]);
	if (miscell->romotes_param.nSamp != dims[0])
		mexErrMsgTxt("mx_romotes: The lengths of the time stamp sequence and the state trace do not match!");
	TStamps = mxGetPr(prhs[3]);

	/* Get predicate map*/
    NElems = mxGetNumberOfElements(prhs[1]);
	miscell->romotes_param.nPred = NElems;
    if (NElems==0)
        mexErrMsgTxt("mx_romotes: the predicate map is empty!");
    predMap = (PMap *)emalloc(NElems*sizeof(PMap));
	miscell->predMap = (PMap *)emalloc(NElems*sizeof(PMap));

    miscell->pList.pindex=(int *)emalloc(NElems*sizeof(int));

    /* initial predicate list*/
	for(ll = 0; ll < NElems; ll++)
	{
		miscell->pList.pindex[ll] = -1;
	}

	for(jstruct = 0; jstruct < NElems; jstruct++)
	{
        /* Get predicate name */
        tmp = mxGetField(prhs[1], jstruct, "str");
		if(tmp == NULL)
		{
            mexPrintf("%s%d\n", "Predicate no ", jstruct+1);
            mexErrMsgTxt("mx_romotes: The above parameter must has 'str' field!");
		}
		else
		{
			npred++;
		}

        /* Get name of the predicate */
        ndim = mxGetNumberOfDimensions(tmp);
        dims = mxGetDimensions(tmp);
        buflen = dims[1]*sizeof(mxChar)+1;
        predMap[jstruct].str = (char *)emalloc(buflen);
        miscell->predMap[jstruct].str = (char *)emalloc(buflen);
        predMap[jstruct].set.idx = (int) jstruct;
        predMap[jstruct].true_pred = true;
        status = mxGetString(tmp, predMap[jstruct].str, buflen);
        status = mxGetString(tmp, miscell->predMap[jstruct].str, buflen);

        /* Get set */
        tmp = mxGetField(prhs[1], jstruct, "A");
        /* If A is empty, then we should have an interval */
        if(tmp == NULL) /* TODO */
        {
            tmp = mxGetField(prhs[1], jstruct, "Int");
            if(tmp == NULL) {
                mexPrintf("%s%s \n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: Both fields 'A' and 'Int' do not exist!");
            }
        }
        else if(mxIsEmpty(tmp))
        {
            predMap[jstruct].set.isSetRn = true;
            predMap[jstruct].set.ncon = 0;
        }
        else
        {
            predMap[jstruct].set.isSetRn = false;
            /* get A */
            ndimA = mxGetNumberOfDimensions(tmp);
            if (ndimA>2)
            {
                mexPrintf("%s%s \n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: The set constraints are not in proper form!");
            }
            dimsA = mxGetDimensions(tmp);
            if (miscell->romotes_param.SysDim != dimsA[1])
            {
                mexPrintf("%s%s \n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: The dimensions of the set constraints and the state trace do not match!");
            }
            predMap[jstruct].set.ncon = dimsA[0]; /* the number of constraints */
            if (predMap[jstruct].set.ncon>2 && miscell->romotes_param.SysDim==1)
            {
                mexPrintf("%s%s \n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: For 1D signals only up to two constraints per predicate are allowed!\n More than two are redundant!");
            }
            predMap[jstruct].set.A = (double **)emalloc(predMap[jstruct].set.ncon*sizeof(double*));
            for (iii=0; iii<predMap[jstruct].set.ncon; iii++)
            {
                predMap[jstruct].set.A[iii] = (double *)emalloc(miscell->romotes_param.SysDim*sizeof(double));
                for (jjj=0; jjj<miscell->romotes_param.SysDim; jjj++)
                    predMap[jstruct].set.A[iii][jjj] = (mxGetPr(tmp))[iii+jjj*predMap[jstruct].set.ncon];
            }

            /* get b */
            tmp = mxGetField(prhs[1], jstruct, "b");
            if(tmp == NULL)
            {
                mexPrintf("%s%s\n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: Field 'b' is empty!");
            }
            ndimb = mxGetNumberOfDimensions(tmp);
            if (ndimb>2)
            {
                mexPrintf("%s%s\n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: The set constraints are not in proper form!");
            }
            dimsb = mxGetDimensions(tmp);
            if (predMap[jstruct].set.ncon != dimsb[0])
            {
                mexPrintf("%s%s\n", "Predicate: ", predMap[jstruct].str);
                mexErrMsgTxt("mx_romotes: Above predicate: The number of constraints between A and b do not match!");
            }
            predMap[jstruct].set.b = mxGetPr(tmp);
            if (predMap[jstruct].set.ncon==2 && miscell->romotes_param.SysDim==1)
            {
                if ((predMap[jstruct].set.A[0][0]>0 && predMap[jstruct].set.A[1][0]>0) ||
                    (predMap[jstruct].set.A[0][0]<0 && predMap[jstruct].set.A[1][0]<0) ||
                    !((predMap[jstruct].set.A[0][0]<0 && (predMap[jstruct].set.A[0][0]/predMap[jstruct].set.b[0]<=predMap[jstruct].set.A[1][0]/predMap[jstruct].set.b[1])) ||
                        (predMap[jstruct].set.A[1][0]<0 && (predMap[jstruct].set.A[1][0]/predMap[jstruct].set.b[1]<=predMap[jstruct].set.A[0][0]/predMap[jstruct].set.b[0]))))
                {
                    mexPrintf("%s%s\n", "Predicate: ", predMap[jstruct].str);
                    mexErrMsgTxt("mx_romotes: Above predicate: The constraint is the empty set!");
                }
            }
        }
    }
    /*Get maximal delay in signal*/
    tmp= mxGetField(prhs[4], 0, "max_delay_s");
    if (!mxIsDouble(tmp))
    {
       mexErrMsgTxt("mx_romotes: max_delay_s must be a number!");
    }
    tempdouble =mxGetPr(tmp);
    miscell->romotes_param.max_delay_s=tempdouble[0];

    /*Get variable sample_f_s*/
    tmp=mxGetField(prhs[4], 0, "sample_f_s");
    if (!mxIsDouble(tmp))
    {
       mexErrMsgTxt("mx_romotes: max_delay_s must be a number!");
    }
    tempdouble = mxGetPr(tmp);
    miscell->romotes_param.sample_f_s=tempdouble[0];

    /*Get variable lipschitz_on*/
    tmp=mxGetField(prhs[4], 0, "lipschitz_on");
    if (!mxIsLogical(tmp))
    {
       mexErrMsgTxt("mx_romotes: max_delay_s must be a Boolean!");
    }
    tempbool = mxGetPr(tmp);
    miscell->romotes_param.lipschitz_on=tempbool[0];

    /*Get constant upper bound*/
    tmp=mxGetField(prhs[4], 0, "upper_const_dev");
    ndim = mxGetNumberOfDimensions(tmp);
	if (ndim>2)
		mexErrMsgTxt("mx_romotes: The constant upper bound is not in proper form!");
	dims = mxGetDimensions(tmp);
	if(!(miscell->romotes_param.SysDim==dims[1]))
        mexErrMsgTxt("mx_romotes: The dimension of upper bound and the dimension of state variables do not match!");
	Upperb = mxGetPr(tmp);

    /*Get constant lower bound*/
    tmp=mxGetField(prhs[4], 0, "lower_const_dev");
    ndim = mxGetNumberOfDimensions(tmp);
	if (ndim>2)
		mexErrMsgTxt("mx_romotes: The constant lower bound is not in proper form!");
	dims = mxGetDimensions(tmp);
	if(!(miscell->romotes_param.SysDim==dims[1]))
        mexErrMsgTxt("mx_romotes: The dimension of lower bound and the dimension of state variables do not match!");
	Lowerb = mxGetPr(tmp);


	miscell->tl_out = stdout; /* TODO: For parallel toolbox all global variables must be removed */

	/* set up some variables wrt to timing constraints */
	miscell->zero2inf.l_closed = 1;
	miscell->zero2inf.u_closed = 0;
	miscell->emptyInter.l_closed = 0;
	miscell->emptyInter.u_closed = 0;
	if (miscell->romotes_param.ConOnSamples)
	{
		miscell->zero.numi.inf = 0;
		miscell->zero.numi.i_num = 0;
		miscell->inf.numi.inf = 1;
		miscell->inf.numi.i_num = 0;
		miscell->zero2inf.lbd = miscell->zero;
		miscell->zero2inf.ubd = miscell->inf;
		miscell->emptyInter.lbd = miscell->zero;
		miscell->emptyInter.ubd = miscell->zero;
	}
	else
	{
		miscell->zero.numf.inf = 0;
		miscell->zero.numf.f_num = 0.0;
		miscell->inf.numf.inf = 1;
		miscell->inf.numf.f_num = 0.0;
		miscell->zero2inf.lbd = miscell->zero;
		miscell->zero2inf.ubd = miscell->inf;
		miscell->emptyInter.lbd = miscell->zero;
		miscell->emptyInter.ubd = miscell->zero;
	}

    /*Convert the formula into a parsing tree and return the address of the root node of the tree*/
	node = tl_parse(cnt,hasuform,uform, miscell, tl_yychar);

    /*Compute the evolution of robustness estimate interval regarding the parsing tree structure*/
    plhs[0]=Offlinemonitoring(node,predMap,XTrace,TStamps,&(miscell->romotes_param), miscell,Upperb,Lowerb);

	/* Clear up storage space reserved for RoMoTeS */
	for (iii=0; iii<miscell->romotes_param.nPred; iii++)
	{
		tl_clearlookup(predMap[iii].str, miscell);
		for (jjj=0;jjj<predMap[iii].set.ncon;jjj++)
			mxFree(predMap[iii].set.A[jjj]);
        mxFree(predMap[iii].str);
		mxFree(predMap[iii].set.A);
	}
	for (iii=0; iii<miscell->romotes_param.nPred; iii++)
	{
        mxFree(miscell->predMap[iii].str);
    }
    mxFree(miscell->pList.pindex);
    mxFree(miscell->predMap);
    mxFree(predMap);
	mxFree(miscell);
	mxFree(tl_yychar);
}


