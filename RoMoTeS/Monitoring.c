 /***** mx_romotes : Monitoring.c *****/
/* Version 1.0				     */

/*Edited by ZHONG Bingzhuo, TUM, Germany, for RoMoTeS*/

/*Following functions in this file are developed bY ZHONG Bingzhuo
"search_time_point_u"
"search_time_point_l"
"compute_time_value"
"compute_signal_value"
"compute_intersection"
"trimming"
"compute_dev_poly"
"compute_predicate"
"Monode" ¡°fmaxb¡±
"fminb"*/

/*The following functions in this file are developed bY ZHONG Bingzhuo
"Offlinemonitoring"*/

/*Following functions in this file are taken from S-TaLiRo Software Written by Georgios Fainekos and Hengyi Yang ASU, U.S.A.
"imax"
"imin"
"enqueue"
"init_queue"
"queue_empty_p"
"DepthFirstTraversal"
"fmax"
"fmin"
"e_le"
"e_eq"
"e_leq"
"e_ge"
"e_geq"*/

#include <time.h>
#include "mex.h"
#include "matrix.h"
#include "distances.h"
#include "stl2tree.h"
#include "param.h"
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>

#define intMax32bit 2147483647

/*Searching the index of the time point which is the as large as possible and at the same time smaller than "time"*/
int search_time_point_u(Node *longer_node,double time)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    int original_num=longer_node->num_upperdata;
    int temp_start=0;
    int temp_end=original_num-1;
    int middle_point=0;
    int indicator=0;


    if(time>longer_node->u_timestamp[original_num-1])
    {/*if the time to be searched is  bigger than the largest time point in the node*/
        return(-1);
    }

    /*searching with Dichotomy*/
    while((temp_end-temp_start)!=1&&(indicator==0))
    {
        middle_point=(temp_start+temp_end)/2;
        if(longer_node->u_timestamp[middle_point]>time)
        {
            temp_end=middle_point;
        }
        else if (longer_node->u_timestamp[middle_point]<time)
        {
            temp_start=middle_point;
        }
        else
        {
            temp_start=middle_point;
            indicator=1;        /*the middle point is exactly the time point to be searched*/
        }
    }
    return(temp_start);
}


/*Searching the index of the time point which is the as large as possible and at the same time smaller than "time"*/
int search_time_point_l(Node *longer_node,double time)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    int original_num=longer_node->num_lowerdata;
    int temp_start=0;
    int temp_end=original_num-1;
    int middle_point=0;
    int indicator=0;


    if(time>longer_node->l_timestamp[original_num-1])
    {/*if the time to be searched is  bigger than the largest time point in the node*/

        return(-1);
    }

    /*searching with Dichotomy*/
    while((temp_end-temp_start)!=1&&(indicator==0))
    {
        middle_point=(temp_start+temp_end)/2;
        if(longer_node->l_timestamp[middle_point]>time)
        {
            temp_end=middle_point;
        }
        else if (longer_node->l_timestamp[middle_point]<time)
        {
            temp_start=middle_point;
        }
        else
        {
            temp_start=middle_point;
            indicator=1;        /*the middle point is exactly the time point to be searched*/
        }
    }
    return(temp_start);
}

/*Given the signal value, computing the corresponding time stamp*/
double compute_time_value(double x0,double t0, double x1, double t1,double x)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double k,b;
    k=(x0-x1)/(t0-t1);
    b=x0-k*t0;
    if(k==0)
    {
        return(t0);
    }
    return((x-b)/k);
}

/*Given points on both sides of a line and a concrete time,return the value at this time*/
double compute_signal_value(double x0,double t0, double x1, double t1,double t)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double k,b;
    k=(x0-x1)/(t0-t1);
    b=x0-k*t0;
    return(k*t+b);
}

/*To compute the intersection point of two lines*/
time_state compute_intersection(double x0,double t0,double x1,double t1,double y0,double yt0,double y1, double yt1)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double k1,b1,k2,b2;
    time_state outp;
    k1=(x0-x1)/(t0-t1);
    b1=x0-k1*t0;
    k2=(y0-y1)/(yt0-yt1);
    b2=y0-k2*yt0;
    outp.t=(b2-b1)/(k1-k2);
    outp.x=k1*outp.t+b1;
    return(outp);
}

/*If both the left node and right node are not empty and the signal in both sub-node do not has the same length, trimming the longer one*/
void trimming(Node *subformula)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    int temp_leftnum,temp_rightnum,temp_leftnum_l,temp_rightnum_l;
    int target_time;
    double o_value;
    double x0,t0,x1,t1;
    temp_leftnum=subformula->lft->num_upperdata;
    temp_rightnum=subformula->rgt->num_upperdata;
	temp_leftnum_l=subformula->lft->num_lowerdata;
	temp_rightnum_l=subformula->rgt->num_lowerdata;

	/*if the length of signal in both node is not equal, the longer signal needs to be trimmed*/
    if(subformula->lft->u_timestamp[temp_leftnum-1]!=subformula->rgt->u_timestamp[temp_rightnum-1])
    {
        if(subformula->lft->u_timestamp[temp_leftnum-1]>subformula->rgt->u_timestamp[temp_rightnum-1])
        {/*signal in left node is longer*/

            /*trimming the upper data*/
            target_time=search_time_point_u(subformula->lft,subformula->rgt->u_timestamp[temp_rightnum-1]);
            if (subformula->lft->u_timestamp[target_time]==subformula->rgt->u_timestamp[temp_rightnum-1])
            {
                subformula->lft->num_upperdata=target_time+1;
            }
            else
            {
                x0=subformula->lft->upperdata[target_time];
                t0=subformula->lft->u_timestamp[target_time];
                x1=subformula->lft->upperdata[target_time+1];
                t1=subformula->lft->u_timestamp[target_time+1];
                o_value=compute_signal_value(x0,t0,x1,t1,subformula->rgt->u_timestamp[temp_rightnum-1]);
                subformula->lft->upperdata[target_time+1]=o_value;
                subformula->lft->u_timestamp[target_time+1]=subformula->rgt->u_timestamp[temp_rightnum-1];
                subformula->lft->num_upperdata=target_time+2;
            }

            /*trimming the lower data*/
            target_time=search_time_point_l(subformula->lft,subformula->rgt->l_timestamp[temp_rightnum_l-1]);
            if (subformula->lft->l_timestamp[target_time]==subformula->rgt->l_timestamp[temp_rightnum_l-1])
            {
                subformula->lft->num_lowerdata=target_time+1;
            }
            else
            {
                x0=subformula->lft->lowerdata[target_time];
                t0=subformula->lft->l_timestamp[target_time];
                x1=subformula->lft->lowerdata[target_time+1];
                t1=subformula->lft->l_timestamp[target_time+1];
                o_value=compute_signal_value(x0,t0,x1,t1,subformula->rgt->l_timestamp[temp_rightnum_l-1]);
                subformula->lft->lowerdata[target_time+1]=o_value;
                subformula->lft->l_timestamp[target_time+1]=subformula->rgt->l_timestamp[temp_rightnum_l-1];
                subformula->lft->num_lowerdata=target_time+2;
            }
        }
        else /*otherwise, signal in right node is longer*/
        {
            /*trimming the upper data*/
            target_time=search_time_point_u(subformula->rgt,subformula->lft->u_timestamp[temp_leftnum-1]);
            if (subformula->rgt->u_timestamp[target_time]==subformula->lft->u_timestamp[temp_leftnum-1])
            {
                subformula->rgt->num_upperdata=target_time+1;
            }
            else
            {
                x0=subformula->rgt->upperdata[target_time];
                t0=subformula->rgt->u_timestamp[target_time];
                x1=subformula->rgt->upperdata[target_time+1];
                t1=subformula->rgt->u_timestamp[target_time+1];
                o_value=compute_signal_value(x0,t0,x1,t1,subformula->lft->u_timestamp[temp_leftnum-1]);
                subformula->rgt->upperdata[target_time+1]=o_value;
                subformula->rgt->u_timestamp[target_time+1]=subformula->lft->u_timestamp[temp_leftnum-1];
                subformula->rgt->num_upperdata=target_time+2;
            }

            /*trimming the lower data*/
            target_time=search_time_point_l(subformula->rgt,subformula->lft->l_timestamp[temp_leftnum_l-1]);
            if (subformula->rgt->l_timestamp[target_time]==subformula->lft->l_timestamp[temp_leftnum_l-1])
            {
                subformula->rgt->num_lowerdata=target_time+1;
            }
            else
            {
                x0=subformula->rgt->lowerdata[target_time];
                t0=subformula->rgt->l_timestamp[target_time];
                x1=subformula->rgt->lowerdata[target_time+1];
                t1=subformula->rgt->l_timestamp[target_time+1];
                o_value=compute_signal_value(x0,t0,x1,t1,subformula->lft->l_timestamp[temp_leftnum_l-1]);
                subformula->rgt->lowerdata[target_time+1]=o_value;
                subformula->rgt->l_timestamp[target_time+1]=subformula->lft->l_timestamp[temp_leftnum_l-1];
                subformula->rgt->num_lowerdata=target_time+2;
            }
        }
    }

}

/*return the bigger integer*/
int imax(int a, int b)
{/*Taken from S-TaLiRo Software*/
	return(((a) > (b)) ? (a) : (b));
}

/*return the smaller integer*/
int imin(int a, int b)
{/*Taken from S-TaLiRo Software*/
	return(((a) < (b)) ? (a) : (b));
}

/*Given the upper bound and lower bound in all dimensions and the current state, return the deviation polytope*/
void compute_dev_poly(double *cur_state,double time_current, double time_front, double time_back,ROMOTESParam *p_par,double *Upperb,double *Lowerb,Deviation *mondata_pre)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double *u_dev=(double *)emalloc(p_par->SysDim*sizeof(double));
    double *l_dev=(double *)emalloc(p_par->SysDim*sizeof(double));
    int i;
    if(p_par->lipschitz_on)
    {
         /*Lipschitz error on sampling point is 0, since information has not been lost at sampling point*/
        for(i=0;i< p_par->SysDim;i++)
        {
            u_dev[i]=Upperb[i];
            l_dev[i]=Lowerb[i];
        }
    }
    else
    {
        for(i=0;i< p_par->SysDim;i++)
        {
            u_dev[i]=Upperb[i];
            l_dev[i]=Lowerb[i];
        }
    }
    for(i=0;i< p_par->SysDim;i++)
    {
        mondata_pre[i].upperb=u_dev[i]+cur_state[i];
        mondata_pre[i].lowerb=cur_state[i]-l_dev[i];
    }
}

/*Compute deviation robustness without delay*/
void compute_predicate(Node *subformula[], ROMOTESParam *p_par, int mmm,double *XTrace,double *TStamps,double *Upperb,double *Lowerb)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
	Deviation *mondata_pre/*,*deviation_poly*/;
	Deviation tmp_interval;
	int i=0,j=0;
	double time_current=0;
	double time_front=0;
	double time_back=0;
	double *cur_state=(double *)emalloc(p_par->SysDim*sizeof(double));
	if (!subformula[mmm]->sym->set)
	{
		mexPrintf("%s%s\n", "Predicate: ", subformula[mmm]->sym->name);
		mexErrMsgTxt("mx_romotes: The set for the above predicate has not been defined!\n");
	}

	/*Reserve space for monitoring data*/
	mondata_pre = (Deviation *)emalloc(p_par->SysDim*sizeof(Deviation));
	subformula[mmm]->upperdata=(double *)emalloc(p_par->nSamp*sizeof(double));
	subformula[mmm]->u_timestamp=(double *)emalloc(p_par->nSamp*sizeof(double));
	subformula[mmm]->lowerdata=(double *)emalloc(p_par->nSamp*sizeof(double));
	subformula[mmm]->l_timestamp=(double *)emalloc(p_par->nSamp*sizeof(double));
    subformula[mmm]->num_upperdata=p_par->nSamp;
    subformula[mmm]->num_lowerdata=p_par->nSamp;
	for(i=0;i<p_par->nSamp;i++)
    {
        for(j = 0; j < p_par->SysDim; j++)			/* To obtain current states*/
		{
			cur_state[j] = XTrace[i+j*p_par->nSamp];
		}
		time_current=TStamps[i];                    /* To obtain current time stamp*/
		time_front=TStamps[i];
		if(i==(p_par->nSamp-1))
        {
            time_back=TStamps[i];
        }
        else
        {
            time_back=TStamps[i+1];
        }
        compute_dev_poly(cur_state,time_current,time_front,time_back,p_par,Upperb,Lowerb,mondata_pre);
        subformula[mmm]->u_timestamp[i]=time_current;
        subformula[mmm]->l_timestamp[i]=time_current;
        tmp_interval=SignedDistInterval(mondata_pre,subformula[mmm]->sym->set,p_par->SysDim); /*To compute the signed distance interval*/
        subformula[mmm]->upperdata[i]=tmp_interval.upperb;
        subformula[mmm]->lowerdata[i]=tmp_interval.lowerb;
    }
}

/* cluster of functions for DFS */
/*Enqueue function for parsing a tree for STL formula*/
int enqueue(struct queue *q, Node *phi)
{/*Taken from S-TaLiRo Software*/

    if (phi == NULL) {
        errno = ENOMEM;
        return 1;
    }
	if(phi->visited == 0){
		phi->visited = 0;
			if (q->first == NULL){
				q->first = q->last = dupnode(phi);
				q->first = q->last = phi;							/* point first and last in the queue to the phi passed if the queue is empty*/
			}
			else {
				q->last = dupnode(phi);								/* stuff the phi passed in the last of the queue if the queue is not empty*/
				q->last = phi;
			}
		phi->visited = 1;
    return 0;
	}
	return -1;
}

/*Dequeue function for parsing a tree for STL formula*/
int dequeue(struct queue *q)
{/*Taken from S-TaLiRo Software*/
	if (!q->first) {
        return 1;
    }
    if (q->first == q->last)							/* if the queue has only one element*/
        q->first = q->last = NULL;
    else
        q->first = dupnode(q->last);					/*  pop the first element out of the queue*/
		q->first = q->last;
    return 0;
}

/*Initializing the queue, namely setting the first and last element in the queue as empty*/
void init_queue(struct queue *q)
{/*Taken from S-TaLiRo Software*/
    q->first = q->last = NULL;
}

/*To judge whether the queue is empty*/
int queue_empty_p(const struct queue *q)
{/*Taken from S-TaLiRo Software*/
    return q->first == NULL;
}

/*Depth first traversal function for handling the tree of the formula*/
int DepthFirstTraversal(struct queue *q,Node *root,Node *parent,Node *subformula[],int *i)
{/*Taken from S-TaLiRo Software*/
	double infval = mxGetInf();
	Node *p = NULL;
	if (root == NULL) return 0;

	enqueue(q,root);									/* enqueue the root node*/

	while (!queue_empty_p(q)) {
		if(!q->first){
			p = NULL;
		}
		else{											/* set subformula index		*/
			if((*i)>199)
			{
				mexErrMsgTxt("mx_remotes: The formula is too big to be stored in tree sturcture!");/* error message when amount of subformulas exceeds subMax*/
			}
			else
			{
				p = dupnode(q->first);
				p = q->first;
				p->index = *i;
				p->parent=parent;
				subformula[*i] = dupnode(p);
				subformula[*i] = p;
				(*i)++;
			}
		}

		dequeue(q);
		if (p->lft != NULL)
			DepthFirstTraversal( q,p->lft,p,subformula,i);
		if (p->rgt != NULL)
			DepthFirstTraversal( q,p->rgt,p,subformula,i);

	}
	return (*i-1);
}

/* cluster of functions for DFS ends */

/*Function for computing */
mxArray *Offlinemonitoring(Node *phi, PMap *predMap, double *XTrace, double *TStamps, ROMOTESParam *p_par, Miscellaneous *miscell,double *Upperb,double *Lowerb)
{/*Modified from S-TaLiRo Software, developed on 17.09.2018, by ZHONG Bingzhuo*/
	mwIndex ii = 0;							/* used for mapping predicate and passing state vector*/
	mwIndex jj = 0;							/* used for passing state vector*/
	Symbol *tmpsym;
	double infval;
	double tmp_value=0.0;						/*	infinite value*/
	const char *fields[] = {"dl", "ds", "most_related_iteration", "most_related_predicate_index"};
	const char *resultfields[]={"u_bound","u_time","l_bound","l_time"};
    mxArray *tmp,*ub,*ut,*lb,*lt;
#define subMax 200							/*	biggest number of iterations the subformula could store*/
	Node *subformula[subMax];				/* subformula array as a cross-reference for the phi*/
	int iii=0;								/* used for check the index for subformula*/
	int jjj=0;								/* length-1 of the subformula array */
	int mmm=0;                              /* used for offline monitoring*/
	int *qi;
	int temp = 1;
	/* Initialize some variables for DFS */
	queue q;
	queue *Q = &q;
	init_queue(Q);							/*initial the queue*/
	qi = &temp;                             /*array subformula starts from 1*/
	/*----------------------------------*/
	infval = mxGetInf();                    /*get the infinity value*/

	/*-----DFS for formula--------------*/
	jjj = DepthFirstTraversal(Q,phi,ZN,subformula,qi);
    for(iii=1; iii<jjj; iii++)			/*	check the index for subformula*/
    {
        if(iii != subformula[iii]->index)
            mexErrMsgTxt("mx_romotes: Depth-First-Traversal failed, subformulas are not matched to right index!");
    }

	/* map each predicate to a set */
	for (ii=0;ii<p_par->nPred;ii++)
	{
		if(predMap[ii].true_pred)
		{
			tmpsym = tl_lookup(predMap[ii].str, miscell);
			tmpsym->set = &(predMap[ii].set);
		}
	}
    mmm=jjj;
    while(mmm>0)   /*go through all nodes,*/
    {
        Monode(subformula,p_par,mmm,XTrace,TStamps,Upperb,Lowerb);
        mmm--;
    }

	/*read result from the first node*/
	ub=mxCreateDoubleMatrix(1,subformula[1]->num_upperdata,mxREAL);
	ut=mxCreateDoubleMatrix(1,subformula[1]->num_upperdata,mxREAL);
    lb=mxCreateDoubleMatrix(1,subformula[1]->num_lowerdata,mxREAL);
	lt=mxCreateDoubleMatrix(1,subformula[1]->num_lowerdata,mxREAL);
	memcpy(mxGetPr(ub),subformula[1]->upperdata,subformula[1]->num_upperdata*sizeof(double));
	memcpy(mxGetPr(ut),subformula[1]->u_timestamp,subformula[1]->num_upperdata*sizeof(double));
	memcpy(mxGetPr(lb),subformula[1]->lowerdata,subformula[1]->num_lowerdata*sizeof(double));
	memcpy(mxGetPr(lt),subformula[1]->l_timestamp,subformula[1]->num_lowerdata*sizeof(double));

    /* Output the result */
	tmp = mxCreateStructMatrix(1, 1, 4, resultfields);
    mxSetField(tmp, 0, "u_bound", ub);
	mxSetField(tmp, 0, "u_time", ut);
	mxSetField(tmp, 0, "l_bound",lb);
	mxSetField(tmp, 0, "l_time", lt);
    return(tmp);
}


void Monode(Node *subformula[], ROMOTESParam *p_par, int mmm,double *XTrace,double *TStamps,double *Upperb,double *Lowerb)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    double max_time_delay=0;                /*locally save maximal delay time in signal*/
    int i,j,k;
    int child_id;                                                                                   /*for NOT operation*/
    double *tmp_u_data,*tmp_u_time,*tmp_l_data,*tmp_l_time;                                         /*for temporal space for AND and OR operation*/
    double temp_leftnum,temp_rightnum,temp_leftnum_l,temp_rightnum_l;                               /*for trimming data with different length*/
    int target_time;                                                                                /*for trimming data with different length*/
    int tmp_num_space,left_pointer,right_pointer,tmp_num_point;                                     /*for AND and OR operator*/
    int left_smaller,pre_left_smaller;                                                              /*used for finding whether there is intersection*/
    int left_bigger,pre_left_bigger;                                                                /*used for finding whether there is intersection*/
    double o_value,o_time;                                                                          /*supplementary variable for calculating timed state point*/
    double x0,t0,x1,t1,y0,yt0,y1,yt1;                                                               /*for calculating intersection point*/
    time_state tmp_result;                                                                          /*for saving result for intersection*/
    int tmp_pointer;                                                                                /*temporary pointer for ALWAYS, OR operation*/
    int num_buff,start_pointer,end_pointer,l_pos,u_pos,new_l_pos,new_u_pos;                         /*for creating and updating buffer for streaming algorithm*/
    double *upper_list,*lower_list,*upper_list_time,*lower_list_time;                               /*for streaming algorithm*/
    double tmp_upperb,tmp_lowerb,cur_time,tmp_small,tmp_big,lb_value,ub_value;                      /*variable for EVENTUALLY and ALWAYS operator*/
    int ptf,ptb;                                                                                    /*supplementary variables*/
    double ptf_num,ptb_num,zts;                                                                     /*for UNTIL and RELEASE operator*/
    double *tmp_rgt_eve,*tmp_rgt_eve_time,*tmp_rgt_and,*tmp_rgt_and_time,*tmp_lft,*tmp_lft_time;    /*for UNTIL and RELEASE operator*/
    int pointer_rgt1,tmp_rgt_pointer1;                                                              /*for UNTIL and RELEASE operator*/
    int num_sample_point,counter,searching_int_pointer_u,size_searching_int_u;                      /*supplementary variable for calculation when time delay exists*/
    int searching_int_pointer_l,size_searching_int_l;                                               /*supplementary variable for calculation when time delay exists*/
    int ptf_u,ptf_l,ptb_u,ptb_l;                                                                    /*supplementary variable for calculation when time delay exists*/
    double lb_delay,ub_delay,ptf_num_u,ptf_num_l,ptb_num_u,ptb_num_l,temp;                          /*for calculating result with delay*/
    double *searching_interval_u,*searching_interval_l;

    /*To obtain the value of time delay*/
    max_time_delay=p_par->max_delay_s;

    switch (subformula[mmm]->ntyp)
    {
			case TRUE:
			case FALSE:
			case VALUE:
				break;

            case U_OPER:
			    /*trimming data*/
			    trimming(subformula[mmm]);

			    if (p_par->LTL||(subformula[mmm]->time.lbd.numf.inf == 0 && subformula[mmm]->time.lbd.numf.f_num == 0.0 && subformula[mmm]->time.l_closed == 1 && subformula[mmm]->time.ubd.numf.inf == 1))
				{
                    /*reserve temporary space for data of upper bound*/
                    tmp_u_data=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));
                    tmp_u_time=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));

                    /*pointer for the temporary space, start from the back*/
                    tmp_pointer=subformula[mmm]->lft->num_upperdata-1;

                    tmp_lft=(double *)emalloc(2*sizeof(double));
                    tmp_lft_time=(double *)emalloc(2*sizeof(double));

                    for(i=tmp_pointer;i>=0;i--)
                    {
                        /*reserve space for data on the left, there are always two point for the signal in the left node*/
                        if(i==tmp_pointer)  /*if this is the last point in the signal sequence in the left node*/
                        {
                            /*compare the last signal on both sides and select the smaller one*/
                            tmp_u_data[i]=fmin(subformula[mmm]->lft->upperdata[i],subformula[mmm]->rgt->upperdata[subformula[mmm]->rgt->num_upperdata-1]);
                            tmp_u_time[i]=subformula[mmm]->lft->u_timestamp[i];
                        }
                        else
                        {
                           /*save the current value in the left node required for calculation this round*/
                            tmp_lft[0]=subformula[mmm]->lft->upperdata[i];
                            tmp_lft_time[0]=subformula[mmm]->lft->u_timestamp[i];

                            if(subformula[mmm]->lft->upperdata[i]>=subformula[mmm]->lft->upperdata[i+1]) /*if this is a monotone decreasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->upperdata[i+1];
                                tmp_lft_time[1]=subformula[mmm]->lft->u_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->upperdata[ptf];
                                t0=subformula[mmm]->rgt->u_timestamp[ptf];
                                x1=subformula[mmm]->rgt->upperdata[ptf+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->upperdata[ptb];
                                t0=subformula[mmm]->rgt->u_timestamp[ptb];
                                x1=subformula[mmm]->rgt->upperdata[ptb+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->upperdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->u_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->u_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*AND operation*/
                                /*for upper bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));
                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_smaller=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_smaller=0;         /*the value of left_smaller in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_smaller=left_smaller;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_smaller=fminb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*AND operation comes to the end*/

                                /*"Eventually operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]>zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_u_data[i]=fmax(zts,fmin(tmp_u_data[i+1],tmp_lft[1]));
                                tmp_u_time[i]=subformula[mmm]->lft->u_timestamp[i];
                                /*release the space reserve for this round so that it can be reused next in next round*/

                                /*mxFree(tmp_lft);
                                mxFree(tmp_lft_time);*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                            else    /*if this is a monotone increasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->upperdata[i];
                                tmp_lft_time[1]=subformula[mmm]->lft->u_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->upperdata[ptf];
                                t0=subformula[mmm]->rgt->u_timestamp[ptf];
                                x1=subformula[mmm]->rgt->upperdata[ptf+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->upperdata[ptb];
                                t0=subformula[mmm]->rgt->u_timestamp[ptb];
                                x1=subformula[mmm]->rgt->upperdata[ptb+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->upperdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->u_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->u_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*AND operation*/
                                /*for upper bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));

                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_smaller=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_smaller=0;         /*the value of left_smaller in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_smaller=left_smaller;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_smaller=fminb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*AND operation comes to the end*/


                                /*"Eventually operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]>zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_u_data[i]=fmax(zts,fmin(tmp_u_data[i+1],tmp_lft[1]));
                                tmp_u_time[i]=subformula[mmm]->lft->u_timestamp[i];

                                /*release the space reserve for this round so that it can be reused next in next round*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                        }
                    }

                    /*reserve space for the data for upper bound*/
                    subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));
                    subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));

                    /*save data*/
                    subformula[mmm]->num_upperdata=subformula[mmm]->lft->num_upperdata;
                    for(i=0;i<subformula[mmm]->num_upperdata;i++)
                    {
                        subformula[mmm]->upperdata[i]=tmp_u_data[i];
                        subformula[mmm]->u_timestamp[i]=tmp_u_time[i];
                    }


                    mxFree(tmp_lft);
                    mxFree(tmp_lft_time);

                     /*if both left and right node is a singleton node, the lower bound is not necessary be calculated again*/
                    if(subformula[mmm]->lft->singleton==1&&subformula[mmm]->rgt->singleton==1)
                    {
                        subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        subformula[mmm]->num_lowerdata= subformula[mmm]->num_upperdata;
                        for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                        {
                            subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                            subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                        }

                        /*release temporal space*/
                        mxFree(tmp_u_data);
                        mxFree(tmp_u_time);
                        break;
                    }

                     /*reserve temporary space for data of lower bound*/
                    tmp_l_data=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));
                    tmp_l_time=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));

                    /*pointer for the temporary space, start from the back*/
                    tmp_pointer=subformula[mmm]->lft->num_lowerdata-1;

                    tmp_lft=(double *)emalloc(2*sizeof(double));
                    tmp_lft_time=(double *)emalloc(2*sizeof(double));

                    for(i=tmp_pointer;i>=0;i--)
                    {
                        /*reserve space for data on the left, there are always two point for the signal in the left node*/
                        if(i==tmp_pointer)  /*if this is the last point in the signal sequence in the left node*/
                        {
                            /*compare the last signal on both sides and select the smaller one*/
                            tmp_l_data[i]=fmin(subformula[mmm]->lft->lowerdata[i],subformula[mmm]->rgt->lowerdata[subformula[mmm]->rgt->num_lowerdata-1]);
                            tmp_l_time[i]=subformula[mmm]->lft->l_timestamp[i];
                        }
                        else
                        {
                           /*save the current value in the left node required for calculation this round*/
                            tmp_lft[0]=subformula[mmm]->lft->lowerdata[i];
                            tmp_lft_time[0]=subformula[mmm]->lft->l_timestamp[i];

                            if(subformula[mmm]->lft->lowerdata[i]>=subformula[mmm]->lft->lowerdata[i+1]) /*if this is a monotone decreasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->lowerdata[i+1];
                                tmp_lft_time[1]=subformula[mmm]->lft->l_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->lowerdata[ptf];
                                t0=subformula[mmm]->rgt->l_timestamp[ptf];
                                x1=subformula[mmm]->rgt->lowerdata[ptf+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->lowerdata[ptb];
                                t0=subformula[mmm]->rgt->l_timestamp[ptb];
                                x1=subformula[mmm]->rgt->lowerdata[ptb+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->lowerdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->l_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->l_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*AND operation*/
                                /*for lower bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));
                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_smaller=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_smaller=0;         /*the value of left_smaller in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_smaller=left_smaller;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_smaller=fminb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*AND operation comes to the end*/

                                /*"Eventually operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]>zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_l_data[i]=fmax(zts,fmin(tmp_l_data[i+1],tmp_lft[1]));
                                tmp_l_time[i]=subformula[mmm]->lft->l_timestamp[i];
                                /*release the space reserve for this round so that it can be reused next in next round*/

                                /*mxFree(tmp_lft);
                                mxFree(tmp_lft_time);*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                            else    /*if this is a monotone increasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->lowerdata[i];
                                tmp_lft_time[1]=subformula[mmm]->lft->l_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->lowerdata[ptf];
                                t0=subformula[mmm]->rgt->l_timestamp[ptf];
                                x1=subformula[mmm]->rgt->lowerdata[ptf+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->lowerdata[ptb];
                                t0=subformula[mmm]->rgt->l_timestamp[ptb];
                                x1=subformula[mmm]->rgt->lowerdata[ptb+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->lowerdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->l_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->l_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*AND operation*/
                                /*for lower bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));

                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_smaller=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_smaller=0;         /*the value of left_smaller in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_smaller=left_smaller;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_smaller=fminb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_smaller=fminb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmin(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*AND operation comes to the end*/


                                /*"Eventually operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]>zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_l_data[i]=fmax(zts,fmin(tmp_l_data[i+1],tmp_lft[1]));
                                tmp_l_time[i]=subformula[mmm]->lft->l_timestamp[i];

                                /*release the space reserve for this round so that it can be reused next in next round*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                        }
                    }

                    /*reserve space for the data for lower bound*/
                    subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));

                    /*save data*/
                    subformula[mmm]->num_lowerdata=subformula[mmm]->lft->num_lowerdata;
                    for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                    {
                        subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                        subformula[mmm]->l_timestamp[i]=tmp_l_time[i];
                    }

                    /*release temporary space*/
                    mxFree(tmp_lft);
                    mxFree(tmp_lft_time);
                    mxFree(tmp_u_data);
                    mxFree(tmp_u_time);
                    mxFree(tmp_l_data);
                    mxFree(tmp_l_time);
				}

				break;

            case V_OPER:
                /*trimming data*/
			    trimming(subformula[mmm]);

			    if (p_par->LTL||(subformula[mmm]->time.lbd.numf.inf == 0 && subformula[mmm]->time.lbd.numf.f_num == 0.0 && subformula[mmm]->time.l_closed == 1 && subformula[mmm]->time.ubd.numf.inf == 1))
				{
                    /*reserve temporary space for data of upper bound*/
                    tmp_u_data=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));
                    tmp_u_time=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));

                    /*pointer for the temporary space, start from the back*/
                    tmp_pointer=subformula[mmm]->lft->num_upperdata-1;

                    tmp_lft=(double *)emalloc(2*sizeof(double));
                    tmp_lft_time=(double *)emalloc(2*sizeof(double));

                    for(i=tmp_pointer;i>=0;i--)
                    {
                        /*reserve space for data on the left, there are always two point for the signal in the left node*/
                        if(i==tmp_pointer)  /*if this is the last point in the signal sequence in the left node*/
                        {
                            /*compare the last signal on both sides and select the bigger one*/
                            tmp_u_data[i]=fmax(subformula[mmm]->lft->upperdata[i],subformula[mmm]->rgt->upperdata[subformula[mmm]->rgt->num_upperdata-1]);
                            tmp_u_time[i]=subformula[mmm]->lft->u_timestamp[i];
                        }
                        else
                        {
                           /*save the current value in the left node required for calculation this round*/
                            tmp_lft[0]=subformula[mmm]->lft->upperdata[i];
                            tmp_lft_time[0]=subformula[mmm]->lft->u_timestamp[i];

                            if(subformula[mmm]->lft->upperdata[i]<subformula[mmm]->lft->upperdata[i+1]) /*if this is a monotone increasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->upperdata[i+1];
                                tmp_lft_time[1]=subformula[mmm]->lft->u_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->upperdata[ptf];
                                t0=subformula[mmm]->rgt->u_timestamp[ptf];
                                x1=subformula[mmm]->rgt->upperdata[ptf+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->upperdata[ptb];
                                t0=subformula[mmm]->rgt->u_timestamp[ptb];
                                x1=subformula[mmm]->rgt->upperdata[ptb+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->upperdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->u_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->u_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*Or operation*/
                                /*for upper bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));
                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_bigger=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_bigger=0;         /*the value of left_bigger in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_bigger=left_bigger;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_bigger=fmaxb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*OR operation comes to the end*/

                                /*"Eventually operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]<zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_u_data[i]=fmin(zts,fmax(tmp_u_data[i+1],tmp_lft[1]));
                                tmp_u_time[i]=subformula[mmm]->lft->u_timestamp[i];
                                /*release the space reserve for this round so that it can be reused next in next round*/

                                /*mxFree(tmp_lft);
                                mxFree(tmp_lft_time);*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                            else    /*if this is a monotone decreasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->upperdata[i];
                                tmp_lft_time[1]=subformula[mmm]->lft->u_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->upperdata[ptf];
                                t0=subformula[mmm]->rgt->u_timestamp[ptf];
                                x1=subformula[mmm]->rgt->upperdata[ptf+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_u(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->upperdata[ptb];
                                t0=subformula[mmm]->rgt->u_timestamp[ptb];
                                x1=subformula[mmm]->rgt->upperdata[ptb+1];
                                t1=subformula[mmm]->rgt->u_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->upperdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->u_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->u_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*OR operation*/
                                /*for upper bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));

                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_bigger=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_bigger=0;         /*the value of left_bigger in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_bigger=left_bigger;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_bigger=fmaxb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*OR operation comes to the end*/


                                /*"ALWAYS operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]<zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_u_data[i]=fmin(zts,fmax(tmp_u_data[i+1],tmp_lft[1]));
                                tmp_u_time[i]=subformula[mmm]->lft->u_timestamp[i];

                                /*release the space reserve for this round so that it can be reused next in next round*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                        }
                    }

                    /*reserve space for the data for upper bound*/
                    subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));
                    subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->lft->num_upperdata*sizeof(double));

                    /*save data*/
                    subformula[mmm]->num_upperdata=subformula[mmm]->lft->num_upperdata;
                    for(i=0;i<subformula[mmm]->num_upperdata;i++)
                    {
                        subformula[mmm]->upperdata[i]=tmp_u_data[i];
                        subformula[mmm]->u_timestamp[i]=tmp_u_time[i];
                    }


                    mxFree(tmp_lft);
                    mxFree(tmp_lft_time);

                     /*if both left and right node is a singleton node, the lower bound is not necessary be calculated again*/
                    if(subformula[mmm]->lft->singleton==1&&subformula[mmm]->rgt->singleton==1)
                    {
                        subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        subformula[mmm]->num_lowerdata= subformula[mmm]->num_upperdata;
                        for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                        {
                            subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                            subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                        }

                        /*release temporal space*/
                        mxFree(tmp_u_data);
                        mxFree(tmp_u_time);
                        break;
                    }

                     /*reserve temporary space for data of lower bound*/
                    tmp_l_data=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));
                    tmp_l_time=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));

                    /*pointer for the temporary space, start from the back*/
                    tmp_pointer=subformula[mmm]->lft->num_lowerdata-1;

                    tmp_lft=(double *)emalloc(2*sizeof(double));
                    tmp_lft_time=(double *)emalloc(2*sizeof(double));

                    for(i=tmp_pointer;i>=0;i--)
                    {
                        /*reserve space for data on the left, there are always two point for the signal in the left node*/
                        if(i==tmp_pointer)  /*if this is the last point in the signal sequence in the left node*/
                        {
                            /*compare the last signal on both sides and select the bigger one*/
                            tmp_l_data[i]=fmax(subformula[mmm]->lft->lowerdata[i],subformula[mmm]->rgt->lowerdata[subformula[mmm]->rgt->num_lowerdata-1]);
                            tmp_l_time[i]=subformula[mmm]->lft->l_timestamp[i];
                        }
                        else
                        {
                           /*save the current value in the left node required for calculation this round*/
                            tmp_lft[0]=subformula[mmm]->lft->lowerdata[i];
                            tmp_lft_time[0]=subformula[mmm]->lft->l_timestamp[i];

                            if(subformula[mmm]->lft->lowerdata[i]<subformula[mmm]->lft->lowerdata[i+1]) /*if this is a monotone increasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->lowerdata[i+1];
                                tmp_lft_time[1]=subformula[mmm]->lft->l_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->lowerdata[ptf];
                                t0=subformula[mmm]->rgt->l_timestamp[ptf];
                                x1=subformula[mmm]->rgt->lowerdata[ptf+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->lowerdata[ptb];
                                t0=subformula[mmm]->rgt->l_timestamp[ptb];
                                x1=subformula[mmm]->rgt->lowerdata[ptb+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->lowerdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->l_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->l_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*OR operation*/
                                /*for lower bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));
                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_bigger=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_bigger=0;         /*the value of left_bigger in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_bigger=left_bigger;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_bigger=fmaxb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*OR operation comes to the end*/

                                /*"ALWAYS operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]<zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_l_data[i]=fmin(zts,fmax(tmp_l_data[i+1],tmp_lft[1]));
                                tmp_l_time[i]=subformula[mmm]->lft->l_timestamp[i];
                                /*release the space reserve for this round so that it can be reused next in next round*/

                                /*mxFree(tmp_lft);
                                mxFree(tmp_lft_time);*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                            else    /*if this is a monotone decreasing interval*/
                            {
                                tmp_lft[1]=subformula[mmm]->lft->lowerdata[i];
                                tmp_lft_time[1]=subformula[mmm]->lft->l_timestamp[i+1];

                                /*calculate the first turning point*/
                                ptf=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[0]);
                                x0=subformula[mmm]->rgt->lowerdata[ptf];
                                t0=subformula[mmm]->rgt->l_timestamp[ptf];
                                x1=subformula[mmm]->rgt->lowerdata[ptf+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptf+1];
                                ptf_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[0]);

                                ptb=search_time_point_l(subformula[mmm]->rgt,tmp_lft_time[1]);
                                x0=subformula[mmm]->rgt->lowerdata[ptb];
                                t0=subformula[mmm]->rgt->l_timestamp[ptb];
                                x1=subformula[mmm]->rgt->lowerdata[ptb+1];
                                t1=subformula[mmm]->rgt->l_timestamp[ptb+1];
                                ptb_num=compute_signal_value(x0,t0,x1,t1,tmp_lft_time[1]);

                                /*fill in the temporal buffer for EVENTUALLY operation*/
                                pointer_rgt1=2+ptb-ptf;
                                tmp_rgt_and=(double *)emalloc(pointer_rgt1*sizeof(double));
                                tmp_rgt_and_time=(double *)emalloc(pointer_rgt1*sizeof(double));

                                if(ptf==ptb) /*no addition point need to be added*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    tmp_rgt_and[1]=ptb_num;
                                    tmp_rgt_and_time[1]=tmp_lft_time[1];
                                }
                                else /*place additional points*/
                                {
                                    tmp_rgt_and[0]=ptf_num;
                                    tmp_rgt_and_time[0]=tmp_lft_time[0];
                                    for(j=1;j<=ptb-ptf;j++)
                                    {
                                        tmp_rgt_and[j]=subformula[mmm]->rgt->lowerdata[ptf+j];
                                        tmp_rgt_and_time[j]=subformula[mmm]->rgt->l_timestamp[ptf+j];
                                    }
                                    if(subformula[mmm]->rgt->l_timestamp[ptb]==tmp_lft_time[1])
                                    {
                                        j--;
                                        pointer_rgt1--;
                                    }
                                    tmp_rgt_and[j]=ptb_num;
                                    tmp_rgt_and_time[j]=tmp_lft_time[1];
                                }

                                /*AND operation*/
                                /*for lower bound*/

                                tmp_num_space=4*(2+pointer_rgt1);
                                tmp_rgt_eve=(double *)emalloc(tmp_num_space*sizeof(double));
                                tmp_rgt_eve_time=(double *)emalloc(tmp_num_space*sizeof(double));

                                /*initialize pointer*/
                                left_pointer=0;             /*for y(t)*/
                                right_pointer=0;            /*for y'(t)*/
                                tmp_num_point=0;            /*pointer for the temporary array*/
                                left_bigger=0;             /*when the point in left node is bigger, this variable equals to 1, 0 otherwise*/
                                pre_left_bigger=0;         /*the value of left_bigger in the last round*/

                                while(left_pointer<2||right_pointer<pointer_rgt1) /*at lest signal in one node has not yet been gone through*/
                                {
                                    if(left_pointer==0&&right_pointer==0)
                                    {/*if this is the first time point to be compared*/
                                        tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                        pre_left_bigger=left_bigger;
                                        left_pointer++;
                                        right_pointer++;
                                        tmp_num_point++;
                                    }
                                    else if(tmp_lft_time[left_pointer]==tmp_rgt_and_time[right_pointer])
                                    {/*all node has been gone through*/
                                        left_bigger=fmaxb(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_lft[left_pointer-1];
                                            t0=tmp_lft_time[left_pointer-1];
                                            x1=tmp_lft[left_pointer];
                                            t1=tmp_lft_time[left_pointer];
                                            y0=tmp_rgt_and[right_pointer-1];
                                            yt0=tmp_rgt_and_time[right_pointer-1];
                                            y1=tmp_rgt_and[right_pointer];
                                            yt1=tmp_rgt_and_time[right_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_lft[left_pointer],tmp_rgt_and[right_pointer]);
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*add 1 in both both left pointer and right pointer so that the can jump out of the current while loop*/
                                            left_pointer++;
                                            right_pointer++;
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                    else /*if the current time point in the right node is earlier that the one in the left node*/
                                    {
                                        x0=tmp_lft[left_pointer-1];
                                        t0=tmp_lft_time[left_pointer-1];
                                        x1=tmp_lft[left_pointer];
                                        t1=tmp_lft_time[left_pointer];
                                        o_value=compute_signal_value(x0,t0,x1,t1,tmp_rgt_and_time[right_pointer]);

                                        left_bigger=fmaxb(o_value,tmp_rgt_and[right_pointer]);

                                        /*checking whether there is an intersection*/
                                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                                        {
                                            /*compute the intersection*/
                                            x0=tmp_rgt_and[right_pointer-1];
                                            t0=tmp_rgt_and_time[right_pointer-1];
                                            x1=tmp_rgt_and[right_pointer];
                                            t1=tmp_rgt_and_time[right_pointer];
                                            y0=tmp_lft[left_pointer-1];
                                            yt0=tmp_lft_time[left_pointer-1];
                                            y1=tmp_lft[left_pointer];
                                            yt1=tmp_lft_time[left_pointer];
                                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                                            /*put the intersection in tmp data list*/
                                            tmp_rgt_eve[tmp_num_point]=tmp_result.x;
                                            tmp_rgt_eve_time[tmp_num_point]=tmp_result.t;
                                            tmp_num_point++;
                                        }

                                            tmp_rgt_eve[tmp_num_point]=fmax(tmp_rgt_and[right_pointer],o_value);
                                            tmp_rgt_eve[tmp_num_point]=tmp_rgt_and_time[right_pointer];

                                            /*operation on the pointer*/
                                            if(right_pointer<pointer_rgt1-1)
                                            {
                                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                            }
                                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                                    }
                                }   /*OR operation comes to the end*/


                                /*"ALWAYS operation", to pick up the largest element in tmp_rgt_eve*/
                                zts=tmp_rgt_eve[0];
                                for(j=0;j<tmp_num_point;j++)
                                {
                                    if(tmp_rgt_eve[j]<zts)
                                    {
                                        zts=tmp_rgt_eve[j];
                                    }
                                }

                                tmp_l_data[i]=fmin(zts,fmax(tmp_l_data[i+1],tmp_lft[1]));
                                tmp_l_time[i]=subformula[mmm]->lft->l_timestamp[i];

                                /*release the space reserve for this round so that it can be reused next in next round*/
                                mxFree(tmp_rgt_and);
                                mxFree(tmp_rgt_and_time);
                                mxFree(tmp_rgt_eve);
                                mxFree(tmp_rgt_eve_time);
                            }
                        }
                    }

                    /*reserve space for the data for lower bound*/
                    subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->lft->num_lowerdata*sizeof(double));

                    /*save data*/
                    subformula[mmm]->num_lowerdata=subformula[mmm]->lft->num_lowerdata;
                    for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                    {
                        subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                        subformula[mmm]->l_timestamp[i]=tmp_l_time[i];
                    }

                    /*release temporary space*/
                    mxFree(tmp_lft);
                    mxFree(tmp_lft_time);
                    mxFree(tmp_u_data);
                    mxFree(tmp_u_time);
                    mxFree(tmp_l_data);
                    mxFree(tmp_l_time);
				}

				break;

			case PREDICATE:
                compute_predicate(subformula,p_par,mmm,XTrace,TStamps,Upperb,Lowerb);
                /*Judge whether there this is a singleton evolution*/
                i=0;
                subformula[mmm]->singleton=1;
                while(i<subformula[mmm]->num_upperdata)
                {
                    if(subformula[mmm]->upperdata[i]!=subformula[mmm]->lowerdata[i])
                    {/*if one inequality is found, it show that this is not a singleton evolution*/
                        subformula[mmm]->singleton=0;
                        break;
                    }
                    i++;
                }

                /*when delay is bigger than 0, the result obtained above need to be revise based on Interval Semantic of STL with time delay*/
                if(max_time_delay>0)
                {
                    /*reserve space for temporary data array for upper and lower bound when delay is considered*/
                    num_sample_point=subformula[mmm]->u_timestamp[subformula[mmm]->num_upperdata-1]/p_par->sample_f_s+2;
                    tmp_u_data=(double *)emalloc(num_sample_point*sizeof(double));
                    tmp_l_data=(double *)emalloc(num_sample_point*sizeof(double));

                    counter=0;
                    while (true)
                    {
                        cur_time=counter*p_par->sample_f_s+subformula[mmm]->u_timestamp[0];
                        lb_delay=cur_time;
                        ub_delay=cur_time+max_time_delay;
                        if(ub_delay>subformula[mmm]->u_timestamp[subformula[mmm]->num_upperdata-1]||lb_delay>subformula[mmm]->u_timestamp[subformula[mmm]->num_upperdata-1])
                        {
                            break;
                        }

                        /*calculating temporary upper bound*/
                        ptf_u=search_time_point_u(subformula[mmm],lb_delay);
                        x0=subformula[mmm]->upperdata[ptf_u];
                        t0=subformula[mmm]->u_timestamp[ptf_u];
                        x1=subformula[mmm]->upperdata[ptf_u+1];
                        t1=subformula[mmm]->u_timestamp[ptf_u+1];
                        ptf_num_u=compute_signal_value(x0,t0,x1,t1,lb_delay);

                        ptb_u=search_time_point_u(subformula[mmm],ub_delay);
                        x0=subformula[mmm]->upperdata[ptb_u];
                        t0=subformula[mmm]->u_timestamp[ptb_u];
                        x1=subformula[mmm]->upperdata[ptb_u+1];
                        t1=subformula[mmm]->u_timestamp[ptb_u+1];
                        ptb_num_u=compute_signal_value(x0,t0,x1,t1,ub_delay);

                        /*defining searching interval for upper bound*/
                        size_searching_int_u=2+ptb_u-ptf_u;
                        searching_interval_u=(double *)emalloc(size_searching_int_u*sizeof(double));

                        /*Adding element in the searching interval for upper bound*/
                        if(ptf_u==ptb_u) /*no addition point need to be added*/
                        {
                            searching_interval_u[0]=ptf_num_u;
                            searching_interval_u[1]=ptb_num_u;
                        }
                        else /*place additional points*/
                        {
                            searching_interval_u[0]=ptf_num_u;
                            for(j=1;j<=ptb_u-ptf_u;j++)
                            {
                                searching_interval_u[j]=subformula[mmm]->upperdata[ptf_u+j];
                            }
                            searching_interval_u[j]=ptb_num_u;
                        }

                        /*calculating temporary lower bound*/
                        ptf_l=search_time_point_l(subformula[mmm],lb_delay);
                        x0=subformula[mmm]->lowerdata[ptf_l];
                        t0=subformula[mmm]->l_timestamp[ptf_l];
                        x1=subformula[mmm]->lowerdata[ptf_l+1];
                        t1=subformula[mmm]->l_timestamp[ptf_l+1];
                        ptf_num_l=compute_signal_value(x0,t0,x1,t1,lb_delay);

                        ptb_l=search_time_point_l(subformula[mmm],ub_delay);
                        x0=subformula[mmm]->lowerdata[ptb_l];
                        t0=subformula[mmm]->l_timestamp[ptb_l];
                        x1=subformula[mmm]->lowerdata[ptb_l+1];
                        t1=subformula[mmm]->l_timestamp[ptb_l+1];
                        ptb_num_l=compute_signal_value(x0,t0,x1,t1,ub_delay);

                        /*defining searching interval for upper bound*/
                        size_searching_int_l=2+ptb_l-ptf_l;
                        searching_interval_l=(double *)emalloc(size_searching_int_l*sizeof(double));

                        /*Adding element in the searching interval for upper bound*/
                        if(ptf_l==ptb_l) /*no addition point need to be added*/
                        {
                            searching_interval_l[0]=ptf_num_l;
                            searching_interval_l[1]=ptb_num_l;
                        }
                        else /*place additional points*/
                        {
                            searching_interval_l[0]=ptf_num_l;
                            for(j=1;j<=ptb_l-ptf_l;j++)
                            {
                                searching_interval_l[j]=subformula[mmm]->lowerdata[ptf_l+j];
                            }

                            if(fabs(subformula[mmm]->lowerdata[ptb_l]-ptb_num_l)<0.0001)
                            {
                                j--;
                                size_searching_int_l--;
                            }
                            searching_interval_l[j]=ptb_num_l;

                        }

                        /*Put data into temporary array for upper bound and lower bound*/
                        if(subformula[mmm]->parent==ZN||subformula[mmm]->parent->ntyp!=NOT)/*the parent node of the current node is not, then we need to find a maximal interval in the searching interval and then using negation operation*/
                        {
                            /*determine upper bound*/
                            temp=searching_interval_u[0];
                            for(j=0;j<size_searching_int_u;j++)
                            {
                                if(searching_interval_u[j]<temp)
                                {
                                    temp=searching_interval_u[j];
                                }
                            }
                            tmp_u_data[counter]=temp;

                            /*determine lower bound*/
                            temp=searching_interval_l[0];
                            for(j=0;j<size_searching_int_l;j++)
                            {
                                if(searching_interval_l[j]<temp)
                                {
                                    temp=searching_interval_l[j];
                                }
                            }
                            tmp_l_data[counter]=temp;
                        }
                        else
                        {
                            /*determine upper bound*/
                            temp=searching_interval_l[0];
                            for(j=0;j<size_searching_int_l;j++)
                            {
                                if(searching_interval_l[j]>temp)
                                {
                                    temp=searching_interval_l[j];
                                }
                            }

                            tmp_u_data[counter]=-temp;

                            /*determine lower bound*/
                            temp=searching_interval_u[0];
                            for(j=0;j<size_searching_int_u;j++)
                            {
                                if(searching_interval_u[j]>temp)
                                {
                                    temp=searching_interval_u[j];
                                }
                            }
                            tmp_l_data[counter]=-temp;
                        }
                        mxFree(searching_interval_u);
                        mxFree(searching_interval_l);
                        counter++;
                    }

                    /*revising data in the node*/
                    subformula[mmm]->num_upperdata=counter;
                    subformula[mmm]->num_lowerdata=counter;
                    subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                    subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                    subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));

                    for(i=0;i<counter;i++)
                    {
                        subformula[mmm]->upperdata[i]=tmp_u_data[i];
                        subformula[mmm]->u_timestamp[i]=i*p_par->sample_f_s;
                        subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                        subformula[mmm]->l_timestamp[i]=i*p_par->sample_f_s;
                    }

                    mxFree(tmp_u_data);
                    mxFree(tmp_l_data);
                }
				break;

			case NOT:
                if(!(max_time_delay>0))
                {
                    subformula[mmm]->num_upperdata=subformula[mmm]->lft->num_lowerdata;
                    subformula[mmm]->num_lowerdata=subformula[mmm]->lft->num_upperdata;

                    /*reserve space for monitoring data*/
                    subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                    subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                    subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));

                    child_id=subformula[mmm]->lft->index;

                    if(subformula[child_id]->singleton==1)
                    {
                        subformula[mmm]->singleton=1;
                    }

                    /*compute the upper bound of negation node, and move time stamp correspondingly*/
                    for(i=0;i<subformula[mmm]->num_upperdata;i++)
                    {
                        subformula[mmm]->upperdata[i]=-subformula[child_id]->lowerdata[i];
                        subformula[mmm]->u_timestamp[i]=subformula[child_id]->l_timestamp[i];
                    }

                    /*compute the lower bound of negation node, and move time stamp correspondingly*/
                    for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                    {
                        subformula[mmm]->lowerdata[i]=-subformula[child_id]->upperdata[i];
                        subformula[mmm]->l_timestamp[i]=subformula[child_id]->u_timestamp[i];
                    }
                }
                else    /*If there is time delay in the signal, nothing need to be changed,data can be directly moved from its child node*/
                {
                    subformula[mmm]->num_upperdata=subformula[mmm]->lft->num_upperdata;
                    subformula[mmm]->num_lowerdata=subformula[mmm]->lft->num_lowerdata;

                    /*reserve space for monitoring data*/
                    subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                    subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                    subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));

                    child_id=subformula[mmm]->lft->index;

                    if(subformula[child_id]->singleton==1)
                    {
                        subformula[mmm]->singleton=1;
                    }

                    /*directly copy the data of upper bound in the children node*/
                    for(i=0;i<subformula[mmm]->num_upperdata;i++)
                    {
                        subformula[mmm]->upperdata[i]=subformula[child_id]->upperdata[i];
                        subformula[mmm]->u_timestamp[i]=subformula[child_id]->u_timestamp[i];
                    }

                    /*directly copy the data of lower bound in the children node*/
                    for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                    {
                        subformula[mmm]->lowerdata[i]=subformula[child_id]->lowerdata[i];
                        subformula[mmm]->l_timestamp[i]=subformula[child_id]->l_timestamp[i];
                    }
                }
				break;


			case AND:
			    /*trimming data*/
                trimming(subformula[mmm]);

			    /*reserve maximal space for AND operation,see "Efficient Robust Monitoring for STL",Alexandre,2013*/
			    /*space for upper bound*/
			    tmp_num_space=4*(subformula[mmm]->lft->num_upperdata+subformula[mmm]->rgt->num_upperdata);
			    tmp_u_data=(double *)emalloc(tmp_num_space*sizeof(double));
			    tmp_u_time=(double *)emalloc(tmp_num_space*sizeof(double));

			    /*for upper bound*/
                /*initialize pointer*/
                left_pointer=0;
                right_pointer=0;
                tmp_num_point=0;
                left_smaller=0;
                pre_left_smaller=0;

                while(left_pointer<subformula[mmm]->lft->num_upperdata||right_pointer<subformula[mmm]->rgt->num_upperdata)
                {
                    if(left_pointer==0&&right_pointer==0)
                    {/*if this is the first time point to be compared*/
                        tmp_u_data[tmp_num_point]=fmin(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);
                        tmp_u_time[tmp_num_point]=subformula[mmm]->lft->u_timestamp[left_pointer];
                        left_smaller=fminb(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);
                        pre_left_smaller=left_smaller;
                        left_pointer++;
                        right_pointer++;
                        tmp_num_point++;
                    }
                    else if(subformula[mmm]->lft->u_timestamp[left_pointer]==subformula[mmm]->rgt->u_timestamp[right_pointer])
                    {
                        left_smaller=fminb(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->upperdata[left_pointer-1];
                            t0=subformula[mmm]->lft->u_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->upperdata[left_pointer];
                            t1=subformula[mmm]->lft->u_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->upperdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->u_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->upperdata[right_pointer];
                            yt1=subformula[mmm]->rgt->u_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_u_data[tmp_num_point]=tmp_result.x;
                            tmp_u_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_u_data[tmp_num_point]=fmin(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);
                            tmp_u_time[tmp_num_point]=subformula[mmm]->lft->u_timestamp[left_pointer];

                            if(left_pointer==(subformula[mmm]->lft->num_upperdata-1)&&right_pointer==(subformula[mmm]->rgt->num_upperdata-1))
                            { /*all data in both left and right node has already been gone through,increase both pointers so that it can exit the loop*/
                                left_pointer++;
                                right_pointer++;
                            }
                            else/*at least data in one node has not been gone through yet*/
                            {
                                if(left_pointer<subformula[mmm]->lft->num_upperdata-1)
                                {
                                    left_pointer++;/*if this is not the last time point in the left, move it forward*/
                                }

                                if(right_pointer<subformula[mmm]->rgt->num_upperdata-1)
                                {
                                    right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                }
                            }
                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else if (subformula[mmm]->lft->u_timestamp[left_pointer]<subformula[mmm]->rgt->u_timestamp[right_pointer])
                    {/*if the current time point in the left node is earlier that the one in the right node*/
                        o_value=compute_signal_value(subformula[mmm]->rgt->upperdata[right_pointer-1],subformula[mmm]->rgt->u_timestamp[right_pointer-1],subformula[mmm]->rgt->upperdata[right_pointer],subformula[mmm]->rgt->u_timestamp[right_pointer],subformula[mmm]->lft->u_timestamp[left_pointer]);
                        left_smaller=fminb(subformula[mmm]->lft->upperdata[left_pointer],o_value);

                        /*checking whether there is an intersection*/
                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->upperdata[left_pointer-1];
                            t0=subformula[mmm]->lft->u_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->upperdata[left_pointer];
                            t1=subformula[mmm]->lft->u_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->upperdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->u_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->upperdata[right_pointer];
                            yt1=subformula[mmm]->rgt->u_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_u_data[tmp_num_point]=tmp_result.x;
                            tmp_u_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_u_data[tmp_num_point]=fmin(subformula[mmm]->lft->upperdata[left_pointer],o_value);
                            tmp_u_time[tmp_num_point]=subformula[mmm]->lft->u_timestamp[left_pointer];

                            if(left_pointer<subformula[mmm]->lft->num_upperdata-1)
                            {
                                left_pointer++;/*if this is not the last time point in the left, move it forward*/
                            }
                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else /*if the current time point in the right node is earlier that the one in the left node*/
                    {
                        o_value=compute_signal_value(subformula[mmm]->lft->upperdata[left_pointer-1],subformula[mmm]->lft->u_timestamp[left_pointer-1],subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->lft->u_timestamp[left_pointer],subformula[mmm]->rgt->u_timestamp[right_pointer]);
                        left_smaller=fminb(o_value,subformula[mmm]->rgt->upperdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->rgt->upperdata[right_pointer-1];
                            t0=subformula[mmm]->rgt->u_timestamp[right_pointer-1];
                            x1=subformula[mmm]->rgt->upperdata[right_pointer];
                            t1=subformula[mmm]->rgt->u_timestamp[right_pointer];
                            y0=subformula[mmm]->lft->upperdata[left_pointer-1];
                            yt0=subformula[mmm]->lft->u_timestamp[left_pointer-1];
                            y1=subformula[mmm]->lft->upperdata[left_pointer];
                            yt1=subformula[mmm]->lft->u_timestamp[left_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_u_data[tmp_num_point]=tmp_result.x;
                            tmp_u_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_u_data[tmp_num_point]=fmin(subformula[mmm]->rgt->upperdata[right_pointer],o_value);
                            tmp_u_time[tmp_num_point]=subformula[mmm]->rgt->u_timestamp[right_pointer];

                            /*operation on the pointer*/
                            if(right_pointer<subformula[mmm]->rgt->num_upperdata-1)
                            {
                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                            }
                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                }

                /*reserve space for the data for upper bound*/
                subformula[mmm]->upperdata=(double *)emalloc(tmp_num_point*sizeof(double));
                subformula[mmm]->u_timestamp=(double *)emalloc(tmp_num_point*sizeof(double));

                /*save data*/
                subformula[mmm]->num_upperdata=tmp_num_point;
                for(i=0;i<subformula[mmm]->num_upperdata;i++)
                {
                    subformula[mmm]->upperdata[i]=tmp_u_data[i];
                    subformula[mmm]->u_timestamp[i]=tmp_u_time[i];
                }

                /*if both left and right node is a singleton node, the lower bound is not necessary be calculated again*/
                if(subformula[mmm]->lft->singleton==1&&subformula[mmm]->rgt->singleton==1)
                {
                    subformula[mmm]->lowerdata=(double *)emalloc(tmp_num_point*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(tmp_num_point*sizeof(double));
                    subformula[mmm]->num_lowerdata=tmp_num_point;
                    for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                    {
                        subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                        subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                    }

                    /*release temporal space*/
                    mxFree(tmp_u_data);
                    mxFree(tmp_u_time);
                    break;
                }

			    /*space for lower bound*/
			    tmp_num_space=4*(subformula[mmm]->lft->num_lowerdata+subformula[mmm]->rgt->num_lowerdata);
			    tmp_l_data=(double *)emalloc(tmp_num_space*sizeof(double));
			    tmp_l_time=(double *)emalloc(tmp_num_space*sizeof(double));

                /*for lower bound*/
                /*initialize pointer*/
                left_pointer=0;
                right_pointer=0;
                tmp_num_point=0;
                left_smaller=0;
                pre_left_smaller=0;

                while(left_pointer<subformula[mmm]->lft->num_lowerdata||right_pointer<subformula[mmm]->rgt->num_lowerdata)
                {
                    if(left_pointer==0&&right_pointer==0)
                    {/*if this is the first time point to be compared*/
                        tmp_l_data[tmp_num_point]=fmin(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);
                        tmp_l_time[tmp_num_point]=subformula[mmm]->lft->l_timestamp[left_pointer];
                        left_smaller=fminb(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);
                        pre_left_smaller=left_smaller;
                        left_pointer++;
                        right_pointer++;
                        tmp_num_point++;
                    }
                    else if(subformula[mmm]->lft->l_timestamp[left_pointer]==subformula[mmm]->rgt->l_timestamp[right_pointer])
                    {
                        left_smaller=fminb(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->lowerdata[left_pointer-1];
                            t0=subformula[mmm]->lft->l_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->lowerdata[left_pointer];
                            t1=subformula[mmm]->lft->l_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->lowerdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->l_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->lowerdata[right_pointer];
                            yt1=subformula[mmm]->rgt->l_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_l_data[tmp_num_point]=tmp_result.x;
                            tmp_l_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_l_data[tmp_num_point]=fmin(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);
                            tmp_l_time[tmp_num_point]=subformula[mmm]->lft->l_timestamp[left_pointer];

                            if(left_pointer==(subformula[mmm]->lft->num_lowerdata-1)&&right_pointer==(subformula[mmm]->rgt->num_lowerdata-1))
                            { /*all data in both left and right node has already been gone through,increase both pointers so that it can exit the loop*/
                                left_pointer++;
                                right_pointer++;
                            }
                            else/*at least data in one node has not been gone through yet*/
                            {
                                if(left_pointer<subformula[mmm]->lft->num_lowerdata-1)
                                {
                                    left_pointer++;/*if this is not the last time point in the left, move it forward*/
                                }

                                if(right_pointer<subformula[mmm]->rgt->num_lowerdata-1)
                                {
                                    right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                }
                            }
                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else if (subformula[mmm]->lft->l_timestamp[left_pointer]<subformula[mmm]->rgt->l_timestamp[right_pointer])
                    {/*if the current time point in the left node is earlier that the one in the right node*/
                        o_value=compute_signal_value(subformula[mmm]->rgt->lowerdata[right_pointer-1],subformula[mmm]->rgt->l_timestamp[right_pointer-1],subformula[mmm]->rgt->lowerdata[right_pointer],subformula[mmm]->rgt->l_timestamp[right_pointer],subformula[mmm]->lft->l_timestamp[left_pointer]);
                        left_smaller=fminb(subformula[mmm]->lft->lowerdata[left_pointer],o_value);

                        /*checking whether there is an intersection*/
                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->lowerdata[left_pointer-1];
                            t0=subformula[mmm]->lft->l_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->lowerdata[left_pointer];
                            t1=subformula[mmm]->lft->l_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->lowerdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->l_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->lowerdata[right_pointer];
                            yt1=subformula[mmm]->rgt->l_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_l_data[tmp_num_point]=tmp_result.x;
                            tmp_l_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_l_data[tmp_num_point]=fmin(subformula[mmm]->lft->lowerdata[left_pointer],o_value);
                            tmp_l_time[tmp_num_point]=subformula[mmm]->lft->l_timestamp[left_pointer];

                            if(left_pointer<subformula[mmm]->lft->num_lowerdata-1)
                            {
                                left_pointer++;/*if this is not the last time point in the left, move it forward*/
                            }
                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else /*if the current time point in the right node is earlier that the one in the left node*/
                    {
                        o_value=compute_signal_value(subformula[mmm]->lft->lowerdata[left_pointer-1],subformula[mmm]->lft->l_timestamp[left_pointer-1],subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->lft->l_timestamp[left_pointer],subformula[mmm]->rgt->l_timestamp[right_pointer]);
                        left_smaller=fminb(o_value,subformula[mmm]->rgt->lowerdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_smaller!=pre_left_smaller)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->rgt->lowerdata[right_pointer-1];
                            t0=subformula[mmm]->rgt->l_timestamp[right_pointer-1];
                            x1=subformula[mmm]->rgt->lowerdata[right_pointer];
                            t1=subformula[mmm]->rgt->l_timestamp[right_pointer];
                            y0=subformula[mmm]->lft->lowerdata[left_pointer-1];
                            yt0=subformula[mmm]->lft->l_timestamp[left_pointer-1];
                            y1=subformula[mmm]->lft->lowerdata[left_pointer];
                            yt1=subformula[mmm]->lft->l_timestamp[left_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_l_data[tmp_num_point]=tmp_result.x;
                            tmp_l_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_l_data[tmp_num_point]=fmin(subformula[mmm]->rgt->lowerdata[right_pointer],o_value);
                            tmp_l_time[tmp_num_point]=subformula[mmm]->rgt->l_timestamp[right_pointer];

                            /*operation on the pointer*/
                            if(right_pointer<subformula[mmm]->rgt->num_lowerdata-1)
                            {
                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                            }
                            pre_left_smaller=left_smaller;  /*save the left_smaller value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                }

                /*reserve space for the data for lower bound*/
                subformula[mmm]->lowerdata=(double *)emalloc(tmp_num_point*sizeof(double));
                subformula[mmm]->l_timestamp=(double *)emalloc(tmp_num_point*sizeof(double));

                /*save data*/
                subformula[mmm]->num_lowerdata=tmp_num_point;
                for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                {
                    subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                    subformula[mmm]->l_timestamp[i]=tmp_l_time[i];
                }

                /*release temporal space*/
                mxFree(tmp_u_data);
                mxFree(tmp_u_time);
                mxFree(tmp_l_data);
                mxFree(tmp_l_time);
				break;

			case OR:
                /*trimming data*/
                trimming(subformula[mmm]);

                /*reserve maximal space for OR operation,see "Efficient Robust Monitoring for STL",Alexandre,2013*/
			    /*space for upper bound*/
			    tmp_num_space=4*(subformula[mmm]->lft->num_upperdata+subformula[mmm]->rgt->num_upperdata);
			    tmp_u_data=(double *)emalloc(tmp_num_space*sizeof(double));
			    tmp_u_time=(double *)emalloc(tmp_num_space*sizeof(double));

			    /*for upper bound*/
                /*initialize pointer*/
                left_pointer=0;
                right_pointer=0;
                tmp_num_point=0;
                left_bigger=0;
                pre_left_bigger=0;

                while(left_pointer<subformula[mmm]->lft->num_upperdata||right_pointer<subformula[mmm]->rgt->num_upperdata)
                {
                    if(left_pointer==0&&right_pointer==0)
                    {/*if this is the first time point to be compared*/
                        tmp_u_data[tmp_num_point]=fmax(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);
                        tmp_u_time[tmp_num_point]=subformula[mmm]->lft->u_timestamp[left_pointer];
                        left_bigger=fmaxb(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);
                        pre_left_bigger=left_bigger;
                        left_pointer++;
                        right_pointer++;
                        tmp_num_point++;
                    }
                    else if(subformula[mmm]->lft->u_timestamp[left_pointer]==subformula[mmm]->rgt->u_timestamp[right_pointer])
                    {
                        left_bigger=fmaxb(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->upperdata[left_pointer-1];
                            t0=subformula[mmm]->lft->u_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->upperdata[left_pointer];
                            t1=subformula[mmm]->lft->u_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->upperdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->u_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->upperdata[right_pointer];
                            yt1=subformula[mmm]->rgt->u_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_u_data[tmp_num_point]=tmp_result.x;
                            tmp_u_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_u_data[tmp_num_point]=fmax(subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->rgt->upperdata[right_pointer]);
                            tmp_u_time[tmp_num_point]=subformula[mmm]->lft->u_timestamp[left_pointer];

                            if(left_pointer==(subformula[mmm]->lft->num_upperdata-1)&&right_pointer==(subformula[mmm]->rgt->num_upperdata-1))
                            { /*all data in both left and right node has already been gone through,increase both pointers so that it can exit the loop*/
                                left_pointer++;
                                right_pointer++;
                            }
                            else/*at least data in one node has not been gone through yet*/
                            {
                                if(left_pointer<subformula[mmm]->lft->num_upperdata-1)
                                {
                                    left_pointer++;/*if this is not the last time point in the left, move it forward*/
                                }

                                if(right_pointer<subformula[mmm]->rgt->num_upperdata-1)
                                {
                                    right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                }
                            }
                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else if (subformula[mmm]->lft->u_timestamp[left_pointer]<subformula[mmm]->rgt->u_timestamp[right_pointer])
                    {/*if the current time point in the left node is earlier that the one in the right node*/
                        o_value=compute_signal_value(subformula[mmm]->rgt->upperdata[right_pointer-1],subformula[mmm]->rgt->u_timestamp[right_pointer-1],subformula[mmm]->rgt->upperdata[right_pointer],subformula[mmm]->rgt->u_timestamp[right_pointer],subformula[mmm]->lft->u_timestamp[left_pointer]);
                        left_bigger=fmaxb(subformula[mmm]->lft->upperdata[left_pointer],o_value);

                        /*checking whether there is an intersection*/
                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->upperdata[left_pointer-1];
                            t0=subformula[mmm]->lft->u_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->upperdata[left_pointer];
                            t1=subformula[mmm]->lft->u_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->upperdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->u_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->upperdata[right_pointer];
                            yt1=subformula[mmm]->rgt->u_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_u_data[tmp_num_point]=tmp_result.x;
                            tmp_u_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_u_data[tmp_num_point]=fmax(subformula[mmm]->lft->upperdata[left_pointer],o_value);
                            tmp_u_time[tmp_num_point]=subformula[mmm]->lft->u_timestamp[left_pointer];

                            if(left_pointer<subformula[mmm]->lft->num_upperdata-1)
                            {
                                left_pointer++;/*if this is not the last time point in the left, move it forward*/
                            }
                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else /*if the current time point in the right node is earlier that the one in the left node*/
                    {
                        o_value=compute_signal_value(subformula[mmm]->lft->upperdata[left_pointer-1],subformula[mmm]->lft->u_timestamp[left_pointer-1],subformula[mmm]->lft->upperdata[left_pointer],subformula[mmm]->lft->u_timestamp[left_pointer],subformula[mmm]->rgt->u_timestamp[right_pointer]);
                        left_bigger=fmaxb(o_value,subformula[mmm]->rgt->upperdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->rgt->upperdata[right_pointer-1];
                            t0=subformula[mmm]->rgt->u_timestamp[right_pointer-1];
                            x1=subformula[mmm]->rgt->upperdata[right_pointer];
                            t1=subformula[mmm]->rgt->u_timestamp[right_pointer];
                            y0=subformula[mmm]->lft->upperdata[left_pointer-1];
                            yt0=subformula[mmm]->lft->u_timestamp[left_pointer-1];
                            y1=subformula[mmm]->lft->upperdata[left_pointer];
                            yt1=subformula[mmm]->lft->u_timestamp[left_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_u_data[tmp_num_point]=tmp_result.x;
                            tmp_u_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_u_data[tmp_num_point]=fmax(subformula[mmm]->rgt->upperdata[right_pointer],o_value);
                            tmp_u_time[tmp_num_point]=subformula[mmm]->rgt->u_timestamp[right_pointer];

                            /*operation on the pointer*/
                            if(right_pointer<subformula[mmm]->rgt->num_upperdata-1)
                            {
                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                            }
                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                }

                /*reserve space for the data for upper bound*/
                subformula[mmm]->upperdata=(double *)emalloc(tmp_num_point*sizeof(double));
                subformula[mmm]->u_timestamp=(double *)emalloc(tmp_num_point*sizeof(double));

                /*save data*/
                subformula[mmm]->num_upperdata=tmp_num_point;
                for(i=0;i<subformula[mmm]->num_upperdata;i++)
                {
                    subformula[mmm]->upperdata[i]=tmp_u_data[i];
                    subformula[mmm]->u_timestamp[i]=tmp_u_time[i];
                }

                /*if both left and right node is a singleton node, the lower bound is not necessary be calculated again*/
                if(subformula[mmm]->lft->singleton==1&&subformula[mmm]->rgt->singleton==1)
                {
                    subformula[mmm]->lowerdata=(double *)emalloc(tmp_num_point*sizeof(double));
                    subformula[mmm]->l_timestamp=(double *)emalloc(tmp_num_point*sizeof(double));
                    subformula[mmm]->num_lowerdata=tmp_num_point;
                    for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                    {
                        subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                        subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                    }

                    /*release temporal space*/
                    mxFree(tmp_u_data);
                    mxFree(tmp_u_time);
                    break;
                }

                /*space for lower bound*/
			    tmp_num_space=4*(subformula[mmm]->lft->num_lowerdata+subformula[mmm]->rgt->num_lowerdata);
			    tmp_l_data=(double *)emalloc(tmp_num_space*sizeof(double));
			    tmp_l_time=(double *)emalloc(tmp_num_space*sizeof(double));

                /*for lower bound*/
                /*initialize pointer*/
                left_pointer=0;
                right_pointer=0;
                tmp_num_point=0;
                left_bigger=0;
                pre_left_bigger=0;

                while(left_pointer<subformula[mmm]->lft->num_lowerdata||right_pointer<subformula[mmm]->rgt->num_lowerdata)
                {
                    if(left_pointer==0&&right_pointer==0)
                    {/*if this is the first time point to be compared*/
                        tmp_l_data[tmp_num_point]=fmax(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);
                        tmp_l_time[tmp_num_point]=subformula[mmm]->lft->l_timestamp[left_pointer];
                        left_bigger=fmaxb(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);
                        pre_left_bigger=left_bigger;
                        left_pointer++;
                        right_pointer++;
                        tmp_num_point++;
                    }
                    else if(subformula[mmm]->lft->l_timestamp[left_pointer]==subformula[mmm]->rgt->l_timestamp[right_pointer])
                    {
                        left_bigger=fmaxb(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->lowerdata[left_pointer-1];
                            t0=subformula[mmm]->lft->l_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->lowerdata[left_pointer];
                            t1=subformula[mmm]->lft->l_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->lowerdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->l_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->lowerdata[right_pointer];
                            yt1=subformula[mmm]->rgt->l_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_l_data[tmp_num_point]=tmp_result.x;
                            tmp_l_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_l_data[tmp_num_point]=fmax(subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->rgt->lowerdata[right_pointer]);
                            tmp_l_time[tmp_num_point]=subformula[mmm]->lft->l_timestamp[left_pointer];

                            if(left_pointer==(subformula[mmm]->lft->num_lowerdata-1)&&right_pointer==(subformula[mmm]->rgt->num_lowerdata-1))
                            { /*all data in both left and right node has already been gone through,increase both pointers so that it can exit the loop*/
                                left_pointer++;
                                right_pointer++;
                            }
                            else/*at least data in one node has not been gone through yet*/
                            {
                                if(left_pointer<subformula[mmm]->lft->num_lowerdata-1)
                                {
                                    left_pointer++;/*if this is not the last time point in the left, move it forward*/
                                }

                                if(right_pointer<subformula[mmm]->rgt->num_lowerdata-1)
                                {
                                    right_pointer++;/*if this is not the last time point in the right, move it forward*/
                                }
                            }
                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else if (subformula[mmm]->lft->l_timestamp[left_pointer]<subformula[mmm]->rgt->l_timestamp[right_pointer])
                    {/*if the current time point in the left node is earlier that the one in the right node*/
                        o_value=compute_signal_value(subformula[mmm]->rgt->lowerdata[right_pointer-1],subformula[mmm]->rgt->l_timestamp[right_pointer-1],subformula[mmm]->rgt->lowerdata[right_pointer],subformula[mmm]->rgt->l_timestamp[right_pointer],subformula[mmm]->lft->l_timestamp[left_pointer]);
                        left_bigger=fmaxb(subformula[mmm]->lft->lowerdata[left_pointer],o_value);

                        /*checking whether there is an intersection*/
                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->lft->lowerdata[left_pointer-1];
                            t0=subformula[mmm]->lft->l_timestamp[left_pointer-1];
                            x1=subformula[mmm]->lft->lowerdata[left_pointer];
                            t1=subformula[mmm]->lft->l_timestamp[left_pointer];
                            y0=subformula[mmm]->rgt->lowerdata[right_pointer-1];
                            yt0=subformula[mmm]->rgt->l_timestamp[right_pointer-1];
                            y1=subformula[mmm]->rgt->lowerdata[right_pointer];
                            yt1=subformula[mmm]->rgt->l_timestamp[right_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_l_data[tmp_num_point]=tmp_result.x;
                            tmp_l_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_l_data[tmp_num_point]=fmax(subformula[mmm]->lft->lowerdata[left_pointer],o_value);
                            tmp_l_time[tmp_num_point]=subformula[mmm]->lft->l_timestamp[left_pointer];

                            if(left_pointer<subformula[mmm]->lft->num_lowerdata-1)
                            {
                                left_pointer++;/*if this is not the last time point in the left, move it forward*/
                            }
                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                    else /*if the current time point in the right node is earlier that the one in the left node*/
                    {
                        o_value=compute_signal_value(subformula[mmm]->lft->lowerdata[left_pointer-1],subformula[mmm]->lft->l_timestamp[left_pointer-1],subformula[mmm]->lft->lowerdata[left_pointer],subformula[mmm]->lft->l_timestamp[left_pointer],subformula[mmm]->rgt->l_timestamp[right_pointer]);
                        left_bigger=fmaxb(o_value,subformula[mmm]->rgt->lowerdata[right_pointer]);

                        /*checking whether there is an intersection*/
                        if(left_bigger!=pre_left_bigger)/*indicate that there is an intersection*/
                        {
                            /*compute the intersection*/
                            x0=subformula[mmm]->rgt->lowerdata[right_pointer-1];
                            t0=subformula[mmm]->rgt->l_timestamp[right_pointer-1];
                            x1=subformula[mmm]->rgt->lowerdata[right_pointer];
                            t1=subformula[mmm]->rgt->l_timestamp[right_pointer];
                            y0=subformula[mmm]->lft->lowerdata[left_pointer-1];
                            yt0=subformula[mmm]->lft->l_timestamp[left_pointer-1];
                            y1=subformula[mmm]->lft->lowerdata[left_pointer];
                            yt1=subformula[mmm]->lft->l_timestamp[left_pointer];
                            tmp_result=compute_intersection(x0,t0,x1,t1,y0,yt0,y1,yt1);

                            /*put the intersection in tmp data list*/
                            tmp_l_data[tmp_num_point]=tmp_result.x;
                            tmp_l_time[tmp_num_point]=tmp_result.t;
                            tmp_num_point++;
                        }

                            tmp_l_data[tmp_num_point]=fmax(subformula[mmm]->rgt->lowerdata[right_pointer],o_value);
                            tmp_l_time[tmp_num_point]=subformula[mmm]->rgt->l_timestamp[right_pointer];

                            /*operation on the pointer*/
                            if(right_pointer<subformula[mmm]->rgt->num_lowerdata-1)
                            {
                                right_pointer++;/*if this is not the last time point in the right, move it forward*/
                            }
                            pre_left_bigger=left_bigger;  /*save the left_bigger value in this round*/
                            tmp_num_point++;/*move the pointer in the tmp data list forward*/
                    }
                }

                /*reserve space for the data for lower bound*/
                subformula[mmm]->lowerdata=(double *)emalloc(tmp_num_point*sizeof(double));
                subformula[mmm]->l_timestamp=(double *)emalloc(tmp_num_point*sizeof(double));

                /*save data*/
                subformula[mmm]->num_lowerdata=tmp_num_point;
                for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                {
                    subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                    subformula[mmm]->l_timestamp[i]=tmp_l_time[i];
                }

                /*release temporal space*/
                mxFree(tmp_u_data);
                mxFree(tmp_u_time);
                mxFree(tmp_l_data);
                mxFree(tmp_l_time);
				break;

				case ALWAYS:
				    if(p_par->LTL||(subformula[mmm]->time.lbd.numf.inf == 0 && subformula[mmm]->time.lbd.numf.f_num == 0.0 && subformula[mmm]->time.l_closed == 1 && subformula[mmm]->time.ubd.numf.inf == 1))
                    {
                        /*reserve maximal space for OR operation,see "Efficient Robust Monitoring for STL",Alexandre,2013*/
                        /*space for upper bound*/
                        tmp_num_space=2*subformula[mmm]->rgt->num_upperdata;
                        tmp_u_data=(double *)emalloc(tmp_num_space*sizeof(double));
                        tmp_u_time=(double *)emalloc(tmp_num_space*sizeof(double));

                        /*go through upper bound*/
                        tmp_pointer=tmp_num_space-1;
                        for(i=subformula[mmm]->rgt->num_upperdata-1;i>=0;i--)
                        {
                            if(i==subformula[mmm]->rgt->num_upperdata-1)    /*if it is currently the last time point*/
                            {
                                tmp_u_data[tmp_pointer]=subformula[mmm]->rgt->upperdata[i];
                                tmp_u_time[tmp_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                                tmp_pointer--;
                            }
                            else    /*when it is not the last time point*/
                            {
                                if(subformula[mmm]->rgt->upperdata[i]>=tmp_u_data[tmp_pointer+1])
                                {/*if the current signal is bigger than the previous, the robustness boundary do not need to be changed*/
                                    tmp_u_data[tmp_pointer]=tmp_u_data[tmp_pointer+1];
                                    tmp_u_time[tmp_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                                    tmp_pointer--;
                                }
                                else
                                {
                                        x0=subformula[mmm]->rgt->upperdata[i];
                                        t0=subformula[mmm]->rgt->u_timestamp[i];
                                        x1=subformula[mmm]->rgt->upperdata[i+1];
                                        t1=subformula[mmm]->rgt->u_timestamp[i+1];
                                        o_time=compute_time_value(x0,t0,x1,t1,tmp_u_data[tmp_pointer+1]);
                                        tmp_u_data[tmp_pointer]=tmp_u_data[tmp_pointer+1];
                                        tmp_u_time[tmp_pointer]=o_time;
                                        tmp_pointer--;
                                        tmp_u_data[tmp_pointer]=subformula[mmm]->rgt->upperdata[i];
                                        tmp_u_time[tmp_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                                        tmp_pointer--;

                                }
                            }
                        }
                        subformula[mmm]->upperdata=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));
                        subformula[mmm]->u_timestamp=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));

                        /*save data*/
                        subformula[mmm]->num_upperdata=tmp_num_space-1-tmp_pointer;
                        tmp_pointer++;
                        for(i=0;i<subformula[mmm]->num_upperdata;i++)
                        {
                            subformula[mmm]->upperdata[i]=tmp_u_data[tmp_pointer];
                            subformula[mmm]->u_timestamp[i]=tmp_u_time[tmp_pointer];
                            tmp_pointer++;
                        }

                        /*if right node is a singleton node, the lower bound is not necessary be calculated again*/
                        if(subformula[mmm]->rgt->singleton==1)
                        {
                            subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->num_lowerdata=subformula[mmm]->num_upperdata;
                            for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                            {
                                subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                                subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                            }

                            /*release temporal space*/
                            mxFree(tmp_u_data);
                            mxFree(tmp_u_time);
                            break;
                        }

                        /*space for lower bound*/
                        tmp_num_space=2*subformula[mmm]->rgt->num_lowerdata;
                        tmp_l_data=(double *)emalloc(tmp_num_space*sizeof(double));
                        tmp_l_time=(double *)emalloc(tmp_num_space*sizeof(double));

                        tmp_pointer=tmp_num_space-1;
                        for(i=subformula[mmm]->rgt->num_lowerdata-1;i>=0;i--)
                        {
                            if(i==subformula[mmm]->rgt->num_lowerdata-1)    /*if it is currently the last time point*/
                            {
                                tmp_l_data[tmp_pointer]=subformula[mmm]->rgt->lowerdata[i];
                                tmp_l_time[tmp_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                                tmp_pointer--;
                            }
                            else    /*when it is not the last time point*/
                            {
                                if(subformula[mmm]->rgt->lowerdata[i]>=tmp_l_data[tmp_pointer+1])
                                {/*if the current signal is bigger than the previous, the robustness boundary do not need to be changed*/
                                    tmp_l_data[tmp_pointer]=tmp_l_data[tmp_pointer+1];
                                    tmp_l_time[tmp_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                                    tmp_pointer--;
                                }
                                else
                                {
                                        x0=subformula[mmm]->rgt->lowerdata[i];
                                        t0=subformula[mmm]->rgt->l_timestamp[i];
                                        x1=subformula[mmm]->rgt->lowerdata[i+1];
                                        t1=subformula[mmm]->rgt->l_timestamp[i+1];
                                        o_time=compute_time_value(x0,t0,x1,t1,tmp_l_data[tmp_pointer+1]);
                                        tmp_l_data[tmp_pointer]=tmp_l_data[tmp_pointer+1];
                                        tmp_l_time[tmp_pointer]=o_time;
                                        tmp_pointer--;
                                        tmp_l_data[tmp_pointer]=subformula[mmm]->rgt->lowerdata[i];
                                        tmp_l_time[tmp_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                                        tmp_pointer--;
                                }
                            }
                        }
                        subformula[mmm]->lowerdata=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));
                        subformula[mmm]->l_timestamp=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));

                        /*save data*/
                        subformula[mmm]->num_lowerdata=tmp_num_space-1-tmp_pointer;
                        tmp_pointer++;
                        for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                        {
                            subformula[mmm]->lowerdata[i]=tmp_l_data[tmp_pointer];
                            subformula[mmm]->l_timestamp[i]=tmp_l_time[tmp_pointer];
                            tmp_pointer++;
                        }

                        mxFree(tmp_u_data);
                        mxFree(tmp_u_time);
                        mxFree(tmp_l_data);
                        mxFree(tmp_l_time);
                        break;
                    }
                    else if(subformula[mmm]->time.lbd.numf.inf == 0 && (subformula[mmm]->time.lbd.numf.f_num != 0 || subformula[mmm]->time.l_closed == 0) && subformula[mmm]->time.ubd.numf.inf == 1)
                    {

                        break;
                    }
                    else
                    {
                        /*calculation for the upper bound*/
                        num_buff=subformula[mmm]->rgt->num_upperdata;
                        upper_list=(double *)emalloc(num_buff*sizeof(double));
                        upper_list_time=(double *)emalloc(num_buff*sizeof(double));
                        tmp_u_data=(double *)emalloc(num_buff*sizeof(double));
                        tmp_u_time=(double *)emalloc(num_buff*sizeof(double));
                        start_pointer=0;
                        end_pointer=0;
                        tmp_pointer=0;      /*pointer for tmp_u_data and tmp_u_time*/
                        tmp_upperb=subformula[mmm]->time.ubd.numf.f_num;
                        tmp_lowerb=subformula[mmm]->time.lbd.numf.f_num;

                        /*calculating for the first time point*/
                        cur_time=subformula[mmm]->rgt->u_timestamp[tmp_pointer];


                        l_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                        u_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_upperb);

                        /*even the value for the first time point cannot be calculated*/
                        if(l_pos==-1||u_pos==-1)
                        {

                            subformula[mmm]->num_upperdata=0;
                            subformula[mmm]->num_lowerdata=0;
                            break;
                        }


                        /*calculate the value on the boundary*/
                        x0=subformula[mmm]->rgt->upperdata[l_pos];
                        t0=subformula[mmm]->rgt->u_timestamp[l_pos];
                        x1=subformula[mmm]->rgt->upperdata[l_pos+1];
                        t1=subformula[mmm]->rgt->u_timestamp[l_pos+1];
                        lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                        x0=subformula[mmm]->rgt->upperdata[u_pos];
                        t0=subformula[mmm]->rgt->u_timestamp[u_pos];
                        x1=subformula[mmm]->rgt->upperdata[u_pos+1];
                        t1=subformula[mmm]->rgt->u_timestamp[u_pos+1];
                        ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);


                        upper_list[start_pointer]=subformula[mmm]->rgt->upperdata[l_pos+1];
                        upper_list_time[start_pointer]=subformula[mmm]->rgt->u_timestamp[l_pos+1];
                        for(i=l_pos+1;i<=u_pos;i++)
                        {
                            while(upper_list[end_pointer]>=subformula[mmm]->rgt->upperdata[i]&&end_pointer>=start_pointer)
                            {   /*keep deleting elements until the last element in the list is smaller than the new element to be added*/
                                end_pointer--;
                            }
                            end_pointer++;
                            upper_list[end_pointer]=subformula[mmm]->rgt->upperdata[i]; /*add the new element*/
                            upper_list_time[end_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                        }

                        tmp_small=upper_list[start_pointer];
                        tmp_small=fmin(tmp_small,lb_value);
                        tmp_small=fmin(tmp_small,ub_value);
                        tmp_u_data[tmp_pointer]=tmp_small;
                        tmp_u_data[tmp_pointer]=upper_list[start_pointer];
                        tmp_u_time[tmp_pointer]=cur_time;
                        tmp_pointer++;

                        while(1)
                        {
                            cur_time=subformula[mmm]->rgt->u_timestamp[tmp_pointer];
                            new_l_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                            new_u_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_upperb);

                            if(new_l_pos==-1||new_u_pos==-1)
                            {/*currently there is no enough information for the calculating the value in current time point*/
                                subformula[mmm]->num_upperdata=0;
                                subformula[mmm]->num_lowerdata=0;
                                break;
                            }

                            /*calculate the value on the boundary*/
                            x0=subformula[mmm]->rgt->upperdata[new_l_pos];
                            t0=subformula[mmm]->rgt->u_timestamp[new_l_pos];
                            x1=subformula[mmm]->rgt->upperdata[new_l_pos+1];
                            t1=subformula[mmm]->rgt->u_timestamp[new_l_pos+1];
                            lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                            x0=subformula[mmm]->rgt->upperdata[new_u_pos];
                            t0=subformula[mmm]->rgt->u_timestamp[new_u_pos];
                            x1=subformula[mmm]->rgt->upperdata[new_u_pos+1];
                            t1=subformula[mmm]->rgt->u_timestamp[new_u_pos+1];
                            ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);

                            /*if the current first element is not in the time interval to be tested, remove it until the list is empty*/
                            while(upper_list_time[start_pointer]<cur_time+tmp_lowerb&&start_pointer<=end_pointer)
                            {
                                start_pointer++;
                            }

                            /*the list is empty now,put the current first time point in the list*/
                            if(start_pointer>end_pointer)
                            {
                                end_pointer++;
                                upper_list[start_pointer]=subformula[mmm]->rgt->upperdata[new_l_pos+1];
                                upper_list_time[start_pointer]=subformula[mmm]->rgt->u_timestamp[new_l_pos+1];
                            }

                            /*renew the list from the back*/
                            for(i=u_pos+1;i<=new_u_pos;i++)
                            {
                                while(upper_list[end_pointer]>=subformula[mmm]->rgt->upperdata[i]&&end_pointer>=start_pointer)
                                {   /*keep deleting elements until the last element in the list is smaller than the new element to be added*/
                                    end_pointer--;
                                }
                                end_pointer++;
                                upper_list[end_pointer]=subformula[mmm]->rgt->upperdata[i]; /*add the new element*/
                                upper_list_time[end_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                            }

                            /*compare the first element in the list and the value on the lower bound and upper bound of the time interval to be tested*/
                            tmp_small=upper_list[start_pointer];
                            tmp_small=fmin(tmp_small,lb_value);
                            tmp_small=fmin(tmp_small,ub_value);
                            tmp_u_data[tmp_pointer]=tmp_small;
                            tmp_u_time[tmp_pointer]=cur_time;

                            /*save the current lower pointer and upper pointer*/
                            l_pos=new_l_pos;
                            u_pos=new_u_pos;
                            tmp_pointer++;
                        }

                        /*record data*/
                        subformula[mmm]->num_upperdata=tmp_pointer;
                        subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        for(i=0;i<tmp_pointer;i++)
                        {
                            subformula[mmm]->upperdata[i]=tmp_u_data[i];
                            subformula[mmm]->u_timestamp[i]=tmp_u_time[i];
                        }

                        /*if right node is a singleton node, the lower bound is not necessary be calculated again*/
                        if(subformula[mmm]->rgt->singleton==1)
                        {
                            subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->num_lowerdata=subformula[mmm]->num_upperdata;
                            for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                            {
                                subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                                subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                            }

                            /*release temporal space*/
                            mxFree(tmp_u_data);
                            mxFree(tmp_u_time);
                            mxFree(upper_list);
                            mxFree(upper_list_time);
                            break;
                        }


                        /*calculation for the lower bound*/
                        num_buff=subformula[mmm]->rgt->num_lowerdata;
                        lower_list=(double *)emalloc(num_buff*sizeof(double));
                        lower_list_time=(double *)emalloc(num_buff*sizeof(double));
                        tmp_l_data=(double *)emalloc(num_buff*sizeof(double));
                        tmp_l_time=(double *)emalloc(num_buff*sizeof(double));
                        start_pointer=0;
                        end_pointer=0;
                        tmp_pointer=0;      /*pointer for tmp_l_data and tmp_l_time*/
                        tmp_upperb=subformula[mmm]->time.ubd.numf.f_num;
                        tmp_lowerb=subformula[mmm]->time.lbd.numf.f_num;

                        /*calculating for the first time point*/
                        cur_time=subformula[mmm]->rgt->l_timestamp[tmp_pointer];


                        l_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                        u_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_upperb);

                        /*even the value for the first time point cannot be calculated*/
                        if(l_pos==-1||u_pos==-1)
                        {
                            subformula[mmm]->num_lowerdata=0;
                            subformula[mmm]->num_lowerdata=0;
                            break;
                        }


                        /*calculate the value on the boundary*/
                        x0=subformula[mmm]->rgt->lowerdata[l_pos];
                        t0=subformula[mmm]->rgt->l_timestamp[l_pos];
                        x1=subformula[mmm]->rgt->lowerdata[l_pos+1];
                        t1=subformula[mmm]->rgt->l_timestamp[l_pos+1];
                        lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                        x0=subformula[mmm]->rgt->lowerdata[u_pos];
                        t0=subformula[mmm]->rgt->l_timestamp[u_pos];
                        x1=subformula[mmm]->rgt->lowerdata[u_pos+1];
                        t1=subformula[mmm]->rgt->l_timestamp[u_pos+1];
                        ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);


                        lower_list[start_pointer]=subformula[mmm]->rgt->lowerdata[l_pos+1];
                        lower_list_time[start_pointer]=subformula[mmm]->rgt->l_timestamp[l_pos+1];
                        for(i=l_pos+1;i<=u_pos;i++)
                        {
                            while(lower_list[end_pointer]>=subformula[mmm]->rgt->lowerdata[i]&&end_pointer>=start_pointer)
                            {   /*keep deleting elements until the last element in the list is smaller than the new element to be added*/
                                end_pointer--;
                            }
                            end_pointer++;
                            lower_list[end_pointer]=subformula[mmm]->rgt->lowerdata[i]; /*add the new element*/
                            lower_list_time[end_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                        }

                        tmp_small=lower_list[start_pointer];
                        tmp_small=fmin(tmp_small,lb_value);
                        tmp_small=fmin(tmp_small,ub_value);
                        tmp_l_data[tmp_pointer]=tmp_small;
                        tmp_l_data[tmp_pointer]=lower_list[start_pointer];
                        tmp_l_time[tmp_pointer]=cur_time;
                        tmp_pointer++;

                        while(1)
                        {
                            cur_time=subformula[mmm]->rgt->l_timestamp[tmp_pointer];
                            new_l_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                            new_u_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_upperb);

                            if(new_l_pos==-1||new_u_pos==-1)
                            {/*currently there is no enough information for the calculating the value in current time point*/
                                subformula[mmm]->num_lowerdata=0;
                                subformula[mmm]->num_lowerdata=0;
                                break;
                            }

                            /*calculate the value on the boundary*/
                            x0=subformula[mmm]->rgt->lowerdata[new_l_pos];
                            t0=subformula[mmm]->rgt->l_timestamp[new_l_pos];
                            x1=subformula[mmm]->rgt->lowerdata[new_l_pos+1];
                            t1=subformula[mmm]->rgt->l_timestamp[new_l_pos+1];
                            lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                            x0=subformula[mmm]->rgt->lowerdata[new_u_pos];
                            t0=subformula[mmm]->rgt->l_timestamp[new_u_pos];
                            x1=subformula[mmm]->rgt->lowerdata[new_u_pos+1];
                            t1=subformula[mmm]->rgt->l_timestamp[new_u_pos+1];
                            ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);

                            /*if the current first element is not in the time interval to be tested, remove it until the list is empty*/
                            while(lower_list_time[start_pointer]<cur_time+tmp_lowerb&&start_pointer<=end_pointer)
                            {
                                start_pointer++;
                            }

                            /*the list is empty now,put the current first time point in the list*/
                            if(start_pointer>end_pointer)
                            {
                                end_pointer++;
                                lower_list[start_pointer]=subformula[mmm]->rgt->lowerdata[new_l_pos+1];
                                lower_list_time[start_pointer]=subformula[mmm]->rgt->l_timestamp[new_l_pos+1];
                            }

                            /*renew the list from the back*/
                            for(i=u_pos+1;i<=new_u_pos;i++)
                            {
                                while(lower_list[end_pointer]>=subformula[mmm]->rgt->lowerdata[i]&&end_pointer>=start_pointer)
                                {   /*keep deleting elements until the last element in the list is smaller than the new element to be added*/
                                    end_pointer--;
                                }
                                end_pointer++;
                                lower_list[end_pointer]=subformula[mmm]->rgt->lowerdata[i]; /*add the new element*/
                                lower_list_time[end_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                            }

                            /*compare the first element in the list and the value on the lower bound and upper bound of the time interval to be tested*/
                            tmp_small=lower_list[start_pointer];
                            tmp_small=fmin(tmp_small,lb_value);
                            tmp_small=fmin(tmp_small,ub_value);
                            tmp_l_data[tmp_pointer]=tmp_small;
                            tmp_l_time[tmp_pointer]=cur_time;

                            /*save the current lower pointer and upper pointer*/
                            l_pos=new_l_pos;
                            u_pos=new_u_pos;
                            tmp_pointer++;
                        }

                        /*record data*/
                        subformula[mmm]->num_lowerdata=tmp_pointer;
                        subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                        subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                        for(i=0;i<tmp_pointer;i++)
                        {
                            subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                            subformula[mmm]->l_timestamp[i]=tmp_l_time[i];
                        }
                        mxFree(tmp_u_data);
                        mxFree(tmp_u_time);
                        mxFree(upper_list);
                        mxFree(upper_list_time);
                        mxFree(tmp_l_data);
                        mxFree(tmp_l_time);
                        mxFree(lower_list);
                        mxFree(lower_list_time);

                    }
                    break;


			case EVENTUALLY:
                    if(p_par->LTL||(subformula[mmm]->time.lbd.numf.inf == 0 && subformula[mmm]->time.lbd.numf.f_num == 0.0 && subformula[mmm]->time.l_closed == 1 && subformula[mmm]->time.ubd.numf.inf == 1))
                    {
                        /*reserve maximal space for OR operation,see "Efficient Robust Monitoring for STL",Alexandre,2013*/
                        /*space for upper bound*/
                        tmp_num_space=2*subformula[mmm]->rgt->num_upperdata;
                        tmp_u_data=(double *)emalloc(tmp_num_space*sizeof(double));
                        tmp_u_time=(double *)emalloc(tmp_num_space*sizeof(double));

                        /*go through upper bound*/
                        tmp_pointer=tmp_num_space-1;
                        for(i=subformula[mmm]->rgt->num_upperdata-1;i>=0;i--)
                        {
                            if(i==subformula[mmm]->rgt->num_upperdata-1)    /*if it is currently the last time point*/
                            {
                                tmp_u_data[tmp_pointer]=subformula[mmm]->rgt->upperdata[i];
                                tmp_u_time[tmp_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                                tmp_pointer--;
                            }
                            else    /*when it is not the last time point*/
                            {
                                if(subformula[mmm]->rgt->upperdata[i]<=tmp_u_data[tmp_pointer+1])
                                {/*if the current signal is bigger than the previous, the robustness boundary do not need to be changed*/
                                    tmp_u_data[tmp_pointer]=tmp_u_data[tmp_pointer+1];
                                    tmp_u_time[tmp_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                                    tmp_pointer--;
                                }
                                else
                                {
                                        x0=subformula[mmm]->rgt->upperdata[i];
                                        t0=subformula[mmm]->rgt->u_timestamp[i];
                                        x1=subformula[mmm]->rgt->upperdata[i+1];
                                        t1=subformula[mmm]->rgt->u_timestamp[i+1];
                                        o_time=compute_time_value(x0,t0,x1,t1,tmp_u_data[tmp_pointer+1]);
                                        tmp_u_data[tmp_pointer]=tmp_u_data[tmp_pointer+1];
                                        tmp_u_time[tmp_pointer]=o_time;
                                        tmp_pointer--;
                                        tmp_u_data[tmp_pointer]=subformula[mmm]->rgt->upperdata[i];
                                        tmp_u_time[tmp_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                                        tmp_pointer--;

                                }
                            }
                        }
                        subformula[mmm]->upperdata=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));
                        subformula[mmm]->u_timestamp=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));

                        /*save data*/
                        subformula[mmm]->num_upperdata=tmp_num_space-1-tmp_pointer;
                        tmp_pointer++;
                        for(i=0;i<subformula[mmm]->num_upperdata;i++)
                        {
                            subformula[mmm]->upperdata[i]=tmp_u_data[tmp_pointer];
                            subformula[mmm]->u_timestamp[i]=tmp_u_time[tmp_pointer];
                            tmp_pointer++;
                        }

                        /*if right node is a singleton node, the lower bound is not necessary be calculated again*/
                        if(subformula[mmm]->rgt->singleton==1)
                        {
                            subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->num_lowerdata=subformula[mmm]->num_upperdata;
                            for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                            {
                                subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                                subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                            }

                            /*release temporal space*/
                            mxFree(tmp_u_data);
                            mxFree(tmp_u_time);
                            break;
                        }

                        /*space for lower bound*/
                        tmp_num_space=2*subformula[mmm]->rgt->num_lowerdata;
                        tmp_l_data=(double *)emalloc(tmp_num_space*sizeof(double));
                        tmp_l_time=(double *)emalloc(tmp_num_space*sizeof(double));

                        tmp_pointer=tmp_num_space-1;
                        for(i=subformula[mmm]->rgt->num_lowerdata-1;i>=0;i--)
                        {
                            if(i==subformula[mmm]->rgt->num_lowerdata-1)    /*if it is currently the last time point*/
                            {
                                tmp_l_data[tmp_pointer]=subformula[mmm]->rgt->lowerdata[i];
                                tmp_l_time[tmp_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                                tmp_pointer--;
                            }
                            else    /*when it is not the last time point*/
                            {
                                if(subformula[mmm]->rgt->lowerdata[i]<=tmp_l_data[tmp_pointer+1])
                                {/*if the current signal is bigger than the previous, the robustness boundary do not need to be changed*/
                                    tmp_l_data[tmp_pointer]=tmp_l_data[tmp_pointer+1];
                                    tmp_l_time[tmp_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                                    tmp_pointer--;
                                }
                                else
                                {
                                        x0=subformula[mmm]->rgt->lowerdata[i];
                                        t0=subformula[mmm]->rgt->l_timestamp[i];
                                        x1=subformula[mmm]->rgt->lowerdata[i+1];
                                        t1=subformula[mmm]->rgt->l_timestamp[i+1];
                                        o_time=compute_time_value(x0,t0,x1,t1,tmp_l_data[tmp_pointer+1]);
                                        tmp_l_data[tmp_pointer]=tmp_l_data[tmp_pointer+1];
                                        tmp_l_time[tmp_pointer]=o_time;
                                        tmp_pointer--;
                                        tmp_l_data[tmp_pointer]=subformula[mmm]->rgt->lowerdata[i];
                                        tmp_l_time[tmp_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                                        tmp_pointer--;
                                }
                            }
                        }
                        subformula[mmm]->lowerdata=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));
                        subformula[mmm]->l_timestamp=(double *)emalloc((tmp_num_space-1-tmp_pointer)*sizeof(double));

                        /*save data*/
                        subformula[mmm]->num_lowerdata=tmp_num_space-1-tmp_pointer;
                        tmp_pointer++;
                        for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                        {
                            subformula[mmm]->lowerdata[i]=tmp_l_data[tmp_pointer];
                            subformula[mmm]->l_timestamp[i]=tmp_l_time[tmp_pointer];
                            tmp_pointer++;
                        }

                        mxFree(tmp_u_data);
                        mxFree(tmp_u_time);
                        mxFree(tmp_l_data);
                        mxFree(tmp_l_time);
                        break;
                    }
                    else if(subformula[mmm]->time.lbd.numf.inf == 0 && (subformula[mmm]->time.lbd.numf.f_num != 0 || subformula[mmm]->time.l_closed == 0) && subformula[mmm]->time.ubd.numf.inf == 1)
                    {
                        break;
                    }
                    else
                    {
                        /*calculation for the upper bound*/
                        num_buff=subformula[mmm]->rgt->num_upperdata;
                        upper_list=(double *)emalloc(num_buff*sizeof(double));
                        upper_list_time=(double *)emalloc(num_buff*sizeof(double));
                        tmp_u_data=(double *)emalloc(num_buff*sizeof(double));
                        tmp_u_time=(double *)emalloc(num_buff*sizeof(double));
                        start_pointer=0;
                        end_pointer=0;
                        tmp_pointer=0;      /*pointer for tmp_u_data and tmp_u_time*/
                        tmp_upperb=subformula[mmm]->time.ubd.numf.f_num;
                        tmp_lowerb=subformula[mmm]->time.lbd.numf.f_num;

                        /*calculating for the first time point*/
                        cur_time=subformula[mmm]->rgt->u_timestamp[tmp_pointer];


                        l_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                        u_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_upperb);

                        /*even the value for the first time point cannot be calculated*/
                        if(l_pos==-1||u_pos==-1)
                        {

                            subformula[mmm]->num_upperdata=0;
                            subformula[mmm]->num_lowerdata=0;
                            break;
                        }


                        /*calculate the value on the boundary*/
                        x0=subformula[mmm]->rgt->upperdata[l_pos];
                        t0=subformula[mmm]->rgt->u_timestamp[l_pos];
                        x1=subformula[mmm]->rgt->upperdata[l_pos+1];
                        t1=subformula[mmm]->rgt->u_timestamp[l_pos+1];
                        lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                        x0=subformula[mmm]->rgt->upperdata[u_pos];
                        t0=subformula[mmm]->rgt->u_timestamp[u_pos];
                        x1=subformula[mmm]->rgt->upperdata[u_pos+1];
                        t1=subformula[mmm]->rgt->u_timestamp[u_pos+1];
                        ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);


                        upper_list[start_pointer]=subformula[mmm]->rgt->upperdata[l_pos+1];
                        upper_list_time[start_pointer]=subformula[mmm]->rgt->u_timestamp[l_pos+1];
                        for(i=l_pos+1;i<=u_pos;i++)
                        {
                            while(upper_list[end_pointer]<=subformula[mmm]->rgt->upperdata[i]&&end_pointer>=start_pointer)
                            {   /*keep deleting elements until the last element in the list is bigger than the new element to be added*/
                                end_pointer--;
                            }
                            end_pointer++;
                            upper_list[end_pointer]=subformula[mmm]->rgt->upperdata[i]; /*add the new element*/
                            upper_list_time[end_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                        }

                        tmp_small=upper_list[start_pointer];
                        tmp_small=fmax(tmp_small,lb_value);
                        tmp_small=fmax(tmp_small,ub_value);
                        tmp_u_data[tmp_pointer]=tmp_small;
                        tmp_u_data[tmp_pointer]=upper_list[start_pointer];
                        tmp_u_time[tmp_pointer]=cur_time;
                        tmp_pointer++;

                        while(1)
                        {
                            cur_time=subformula[mmm]->rgt->u_timestamp[tmp_pointer];
                            new_l_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                            new_u_pos=search_time_point_u(subformula[mmm]->rgt,cur_time+tmp_upperb);

                            if(new_l_pos==-1||new_u_pos==-1)
                            {/*currently there is no enough information for the calculating the value in current time point*/
                                subformula[mmm]->num_upperdata=0;
                                subformula[mmm]->num_lowerdata=0;
                                break;
                            }

                            /*calculate the value on the boundary*/
                            x0=subformula[mmm]->rgt->upperdata[new_l_pos];
                            t0=subformula[mmm]->rgt->u_timestamp[new_l_pos];
                            x1=subformula[mmm]->rgt->upperdata[new_l_pos+1];
                            t1=subformula[mmm]->rgt->u_timestamp[new_l_pos+1];
                            lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                            x0=subformula[mmm]->rgt->upperdata[new_u_pos];
                            t0=subformula[mmm]->rgt->u_timestamp[new_u_pos];
                            x1=subformula[mmm]->rgt->upperdata[new_u_pos+1];
                            t1=subformula[mmm]->rgt->u_timestamp[new_u_pos+1];
                            ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);

                            /*if the current first element is not in the time interval to be tested, remove it until the list is empty*/
                            while(upper_list_time[start_pointer]<cur_time+tmp_lowerb&&start_pointer<=end_pointer)
                            {
                                start_pointer++;
                            }

                            /*the list is empty now,put the current first time point in the list*/
                            if(start_pointer>end_pointer)
                            {
                                end_pointer++;
                                upper_list[start_pointer]=subformula[mmm]->rgt->upperdata[new_l_pos+1];
                                upper_list_time[start_pointer]=subformula[mmm]->rgt->u_timestamp[new_l_pos+1];
                            }

                            /*renew the list from the back*/
                            for(i=u_pos+1;i<=new_u_pos;i++)
                            {
                                while(upper_list[end_pointer]<=subformula[mmm]->rgt->upperdata[i]&&end_pointer>=start_pointer)
                                {   /*keep deleting elements until the last element in the list is bigger than the new element to be added*/
                                    end_pointer--;
                                }
                                end_pointer++;
                                upper_list[end_pointer]=subformula[mmm]->rgt->upperdata[i]; /*add the new element*/
                                upper_list_time[end_pointer]=subformula[mmm]->rgt->u_timestamp[i];
                            }

                            /*compare the first element in the list and the value on the lower bound and upper bound of the time interval to be tested*/
                            tmp_small=upper_list[start_pointer];
                            tmp_small=fmax(tmp_small,lb_value);
                            tmp_small=fmax(tmp_small,ub_value);
                            tmp_u_data[tmp_pointer]=tmp_small;
                            tmp_u_time[tmp_pointer]=cur_time;

                            /*save the current lower pointer and upper pointer*/
                            l_pos=new_l_pos;
                            u_pos=new_u_pos;
                            tmp_pointer++;
                        }

                        /*record data*/
                        subformula[mmm]->num_upperdata=tmp_pointer;
                        subformula[mmm]->upperdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        subformula[mmm]->u_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                        for(i=0;i<tmp_pointer;i++)
                        {
                            subformula[mmm]->upperdata[i]=tmp_u_data[i];
                            subformula[mmm]->u_timestamp[i]=tmp_u_time[i];
                        }

                        /*if right node is a singleton node, the lower bound is not necessary be calculated again*/
                        if(subformula[mmm]->rgt->singleton==1)
                        {
                            subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_upperdata*sizeof(double));
                            subformula[mmm]->num_lowerdata=subformula[mmm]->num_upperdata;
                            for(i=0;i<subformula[mmm]->num_lowerdata;i++)
                            {
                                subformula[mmm]->lowerdata[i]=subformula[mmm]->upperdata[i];
                                subformula[mmm]->l_timestamp[i]=subformula[mmm]->u_timestamp[i];
                            }

                            /*release temporal space*/
                            mxFree(tmp_u_data);
                            mxFree(tmp_u_time);
                            mxFree(upper_list);
                            mxFree(upper_list_time);
                            break;
                        }

                        /*calculation for the lower bound*/
                        num_buff=subformula[mmm]->rgt->num_lowerdata;
                        lower_list=(double *)emalloc(num_buff*sizeof(double));
                        lower_list_time=(double *)emalloc(num_buff*sizeof(double));
                        tmp_l_data=(double *)emalloc(num_buff*sizeof(double));
                        tmp_l_time=(double *)emalloc(num_buff*sizeof(double));
                        start_pointer=0;
                        end_pointer=0;
                        tmp_pointer=0;      /*pointer for tmp_l_data and tmp_l_time*/
                        tmp_upperb=subformula[mmm]->time.ubd.numf.f_num;
                        tmp_lowerb=subformula[mmm]->time.lbd.numf.f_num;

                        /*calculating for the first time point*/
                        cur_time=subformula[mmm]->rgt->l_timestamp[tmp_pointer];


                        l_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                        u_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_upperb);

                        /*even the value for the first time point cannot be calculated*/
                        if(l_pos==-1||u_pos==-1)
                        {
                            subformula[mmm]->num_lowerdata=0;
                            subformula[mmm]->num_lowerdata=0;
                            break;
                        }


                        /*calculate the value on the boundary*/
                        x0=subformula[mmm]->rgt->lowerdata[l_pos];
                        t0=subformula[mmm]->rgt->l_timestamp[l_pos];
                        x1=subformula[mmm]->rgt->lowerdata[l_pos+1];
                        t1=subformula[mmm]->rgt->l_timestamp[l_pos+1];
                        lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                        x0=subformula[mmm]->rgt->lowerdata[u_pos];
                        t0=subformula[mmm]->rgt->l_timestamp[u_pos];
                        x1=subformula[mmm]->rgt->lowerdata[u_pos+1];
                        t1=subformula[mmm]->rgt->l_timestamp[u_pos+1];
                        ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);


                        lower_list[start_pointer]=subformula[mmm]->rgt->lowerdata[l_pos+1];
                        lower_list_time[start_pointer]=subformula[mmm]->rgt->l_timestamp[l_pos+1];
                        for(i=l_pos+1;i<=u_pos;i++)
                        {
                            while(lower_list[end_pointer]<=subformula[mmm]->rgt->lowerdata[i]&&end_pointer>=start_pointer)
                            {   /*keep deleting elements until the last element in the list is smaller than the new element to be added*/
                                end_pointer--;
                            }
                            end_pointer++;
                            lower_list[end_pointer]=subformula[mmm]->rgt->lowerdata[i]; /*add the new element*/
                            lower_list_time[end_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                        }

                        tmp_small=lower_list[start_pointer];
                        tmp_small=fmax(tmp_small,lb_value);
                        tmp_small=fmax(tmp_small,ub_value);
                        tmp_l_data[tmp_pointer]=tmp_small;
                        tmp_l_data[tmp_pointer]=lower_list[start_pointer];
                        tmp_l_time[tmp_pointer]=cur_time;
                        tmp_pointer++;

                        while(1)
                        {
                            cur_time=subformula[mmm]->rgt->l_timestamp[tmp_pointer];
                            new_l_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_lowerb);
                            new_u_pos=search_time_point_l(subformula[mmm]->rgt,cur_time+tmp_upperb);

                            if(new_l_pos==-1||new_u_pos==-1)
                            {/*currently there is no enough information for the calculating the value in current time point*/
                                subformula[mmm]->num_lowerdata=0;
                                subformula[mmm]->num_lowerdata=0;
                                break;
                            }

                            /*calculate the value on the boundary*/
                            x0=subformula[mmm]->rgt->lowerdata[new_l_pos];
                            t0=subformula[mmm]->rgt->l_timestamp[new_l_pos];
                            x1=subformula[mmm]->rgt->lowerdata[new_l_pos+1];
                            t1=subformula[mmm]->rgt->l_timestamp[new_l_pos+1];
                            lb_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_lowerb);
                            x0=subformula[mmm]->rgt->lowerdata[new_u_pos];
                            t0=subformula[mmm]->rgt->l_timestamp[new_u_pos];
                            x1=subformula[mmm]->rgt->lowerdata[new_u_pos+1];
                            t1=subformula[mmm]->rgt->l_timestamp[new_u_pos+1];
                            ub_value=compute_signal_value(x0,t0,x1,t1,cur_time+tmp_upperb);

                            /*if the current first element is not in the time interval to be tested, remove it until the list is empty*/
                            while(lower_list_time[start_pointer]<cur_time+tmp_lowerb&&start_pointer<=end_pointer)
                            {
                                start_pointer++;
                            }

                            /*the list is empty now,put the current first time point in the list*/
                            if(start_pointer>end_pointer)
                            {
                                end_pointer++;
                                lower_list[start_pointer]=subformula[mmm]->rgt->lowerdata[new_l_pos+1];
                                lower_list_time[start_pointer]=subformula[mmm]->rgt->l_timestamp[new_l_pos+1];
                            }

                            /*renew the list from the back*/
                            for(i=u_pos+1;i<=new_u_pos;i++)
                            {
                                while(lower_list[end_pointer]<=subformula[mmm]->rgt->lowerdata[i]&&end_pointer>=start_pointer)
                                {   /*keep deleting elements until the last element in the list is smaller than the new element to be added*/
                                    end_pointer--;
                                }
                                end_pointer++;
                                lower_list[end_pointer]=subformula[mmm]->rgt->lowerdata[i]; /*add the new element*/
                                lower_list_time[end_pointer]=subformula[mmm]->rgt->l_timestamp[i];
                            }

                            /*compare the first element in the list and the value on the lower bound and upper bound of the time interval to be tested*/
                            tmp_small=lower_list[start_pointer];
                            tmp_small=fmax(tmp_small,lb_value);
                            tmp_small=fmax(tmp_small,ub_value);
                            tmp_l_data[tmp_pointer]=tmp_small;
                            tmp_l_time[tmp_pointer]=cur_time;

                            /*save the current lower pointer and upper pointer*/
                            l_pos=new_l_pos;
                            u_pos=new_u_pos;
                            tmp_pointer++;
                        }

                        /*record data*/
                        subformula[mmm]->num_lowerdata=tmp_pointer;
                        subformula[mmm]->lowerdata=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                        subformula[mmm]->l_timestamp=(double *)emalloc(subformula[mmm]->num_lowerdata*sizeof(double));
                        for(i=0;i<tmp_pointer;i++)
                        {
                            subformula[mmm]->lowerdata[i]=tmp_l_data[i];
                            subformula[mmm]->l_timestamp[i]=tmp_l_time[i];
                        }
                        mxFree(tmp_u_data);
                        mxFree(tmp_u_time);
                        mxFree(upper_list);
                        mxFree(upper_list_time);
                        mxFree(tmp_l_data);
                        mxFree(tmp_l_time);
                        mxFree(lower_list);
                        mxFree(lower_list_time);

                    }
                    break;

			default:
				/*mexPrintf("%s%s\n", "Node: ", subformula[mmm]->ntyp);*/
                /*mexPrintf("%s%s\n", "Node: ", "WEAKNEXT");*/
				mexErrMsgTxt("mx_dp_taliro: Some operator in the formula are not supported!\n");
				break;
    }
}

/*Return the bigger number between a and b*/
double fmax(double a, double b)
{/*Taken from S-TaLiRo Software*/
	return(((a) > (b)) ? (a) : (b));
}

/*Return the smaller number between a and b*/
double fmin(double a, double b)
{/*Taken from S-TaLiRo Software*/
	return(((a) < (b)) ? (a) : (b));
}

/*To compare a and b, if a > b. return 1, other wise 0*/
int fmaxb(double a, double b)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
	if(a>b)
        return(1);
    return(0);

}

/*To compare a and b, if a < b. return 1, other wise 0*/
int fminb(double a, double b)
{/*Developed on 17.09.2018, by ZHONG Bingzhuo */
    if(a<b)
        return(1);
    return(0);
}

/* Define comparisons over the extended real line */
int e_le(Number num1, Number num2, ROMOTESParam *p_par)
{/*Taken from S-TaLiRo Software*/
	if ((num1.num.inf==-1 && num2.num.inf>-1) || (num1.num.inf<1 && num2.num.inf==1))
		return(1);
	else if (num1.num.inf==0 && num2.num.inf==0)
	{
		if (p_par->ConOnSamples)
			return (num1.numi.i_num < num2.numi.i_num);
		else
			return (num1.numf.f_num < num2.numf.f_num);
	}
	else
		return(0);
}

/* Note : depending on the application it might be advisable to define		*/
/* 		  approximate equality for comparing double precision numbers		*/
int e_eq(Number num1, Number num2, ROMOTESParam *p_par)
{/*Taken from S-TaLiRo Software*/
	if (p_par->ConOnSamples)
		return(num1.num.inf==num2.num.inf && num1.numi.i_num==num2.numi.i_num);
	else
		return(num1.num.inf==num2.num.inf && num1.numf.f_num==num2.numf.f_num);
}

int e_leq(Number num1, Number num2, ROMOTESParam *p_par)
{/*Taken from S-TaLiRo Software*/
	return(e_le(num1,num2,p_par) || e_eq(num1,num2,p_par));
}

int e_ge(Number num1, Number num2, ROMOTESParam *p_par)
{/*Taken from S-TaLiRo Software*/
	return(!e_leq(num1,num2,p_par));
}

int e_geq(Number num1, Number num2, ROMOTESParam *p_par)
{/*Taken from S-TaLiRo Software*/
	return(!e_le(num1,num2,p_par));
}
