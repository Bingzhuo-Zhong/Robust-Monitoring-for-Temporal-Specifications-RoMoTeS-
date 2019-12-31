/***** mx_romotes : distances.h *****/
/* Version 1.0				     */

/*Written by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS         */
/*Some of the code in this file was modified basing on S-TaLiRo*/
/*Software Written by Georgios Fainekos, ASU, U.S.A.           */

/* Convex set */
typedef struct
{/*Taken from S-TaLiRo Software*/
	int Dim;        /* false: 1D Interval, true: higher dimensional set*/
	int idx;        /* Predicate index in the predicate map*/
	int *proj;      /* the projected dimension in a higher dimensional space*/
	int nproj;      /* the number of projected components*/
	double *loc;    /* locations in the H.A.*/
	int nloc;       /* number of locations (0 implies any location)*/
	/* 2D set and higher */
	bool isSetRn; /* true means that the set is R^n (indicated by an empty A as input)*/
	int ncon;	    /* number of constraints*/
	double **A;     /* constraint : A*x<=b */
	double *b;      /*no content*/
	/* Interval {lb,ub} where { is [ or ( and } is ] or ) */
	double lb;	    /* lower bound*/
	double ub;      /* upper bound*/
	int lbcl;       /* if lbcl is 1 then [ otherwise, i.e., 0, (*/
	int ubcl;       /* if upcl is 1 then ] otherwise, i.e., 0, )*/
} ConvSet;

/*Containing information about the upper and lower bound of the deviation*/
typedef struct
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double upperb;
    double lowerb;
}Deviation;

/**/
typedef struct
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double x;
    double t;
}time_state;

/*Functions necessary for computing distance*/
Deviation SignedDistInterval(Deviation *mondata_pre, ConvSet *SS, int dim);
int isPointInConvSet(double *xx, ConvSet *SS, int dim);
double inner_prod(double *vec1, double *vec2, int dim);
double norm(double *vec, int dim);
void vec_scl(double *vec0, double scl, double *vec1, int dim);
void vec_add(double* vec0, double *vec1, double *vec2, int dim);


