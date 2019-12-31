/***** mx_romotes : param.h *****/
/* Version 1.0				     */

/*Written by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS         */
/*Some of the code in this file was modified basing on S-TaLiRo*/
/*Software Written by Georgios Fainekos, ASU, U.S.A.           */

/*Functions for dealing with the formula tree*/
int enqueue(struct queue *q, Node *phi);
int dequeue(struct queue *q);
void init_queue(struct queue *q);
int queue_empty_p(const struct queue *q);
int DepthFirstTraversal(struct queue *q, Node *root,Node *parent,Node *subformula[],int *qi);
mxArray *Offlinemonitoring(Node *phi, PMap *predMap, double *XTrace, double *TStamps, ROMOTESParam *param, Miscellaneous *miscell,double *Upperb,double *Lowerb);
void Monode(Node *subformula[], ROMOTESParam *p_par, int mmm,double *XTrace,double *TStamps,double *Upperb,double *Lowerb);

double fmin(double a, double b);
double fmax(double a, double b);
int fminb(double a, double b);
int fmaxb(double a, double b);

/* Timing constraints */
int e_le(Number num1, Number num2, ROMOTESParam *p_par);
int e_eq(Number num1, Number num2, ROMOTESParam *p_par);
int e_leq(Number num1, Number num2, ROMOTESParam *p_par);
int e_ge(Number num1, Number num2, ROMOTESParam *p_par);
int e_geq(Number num1, Number num2, ROMOTESParam *p_par);

