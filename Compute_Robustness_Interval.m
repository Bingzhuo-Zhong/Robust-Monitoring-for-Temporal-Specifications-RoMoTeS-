function rob = Compute_Robustness_Interval(stlFormula,pred,STraj,T,Para)
% Checking input parameter before transferring them to 'mx_romotes'
% function
%
% Input:
%   stlFormula: the temporal logic formula
%Syntax: 
%       phi := p | (phi) | !phi | phi \/ phi | phi /\ phi |
%           | phi -> phi | phi <-> phi | 
%           | phi U_{a,b} phi | phi R_{a,b} phi | 
%           | <>_{a,b} phi | []_{a,b} phi
%        where:           
%            p     is a predicate. Its first character must be a lowercase 
%                  letter and it may contain numeric digits.
%                  Examples: 
%                         pred1, isGateOpen2  
%            !     is not 
%            \/    is 'or'
%            /\    is 'and'
%            ->    is 'implies'
%            <->   if 'if and only if'
%            {a,b} where { is [ or ( and } is ] or ) is for defining 
%                  open or closed timing bounds on the temporal 
%			       operators.
%          U_{a,b} is the UNTIL operator with time bounds {a,b}. If
%                  no time bounds are required, then use U.  
%          R_{a,b} is the RELEASE operator with time bounds {a,b}. If
%                  no time bounds are required, then use R.
%         <>_{a,b} is the EVENTUALLY operator with time bounds {a,b}. If 
%                  no timining constraints are required, then simply use 
%                  <>.  
%         []_{a,b} is the ALWAYS operator with time bounds {a,b}. If no 
%		  	       timining constraints are required, then simply use [].  
%
%   pred: The mapping of the predicates to their respective states.
%
%          Pred(i).str : the predicate name as a string 
%          Pred(i).A, Pred(i).b : a constraint of the form Ax<=b
% remarks:
%   If there are more than one signal to be monitored, but some of the
%   predecate is only related to one of the signal, you should write such a
%   predicate in a proper way to increase the calculation
%   Example: given v and s is signals to be monitored, predicate p indicates
%    v < 30, and q indicates s > 60, you should write the predicate in the
%   following way, so that compare-based method can still be used regarding
%   specification regarding one-dimensional signal to be monitored
%
%   Pred(1).str='p';
%   Pred(1).A=[1 0;0 0];
%   Pred(1).b=[30 0];
%   Pred(1).str='q';
%   Pred(1).A=[0 0;0 -1];
%   Pred(1).b=[0,-60];
% 
%   STraj: Sequence of signals being monitored
%   T:     Sequence of time for STraj
%   Para:  Romotes_options object.
%   
% Output:
%   rob: Evolution of the robustness estimate interval
%
%
%   Create by ZHONG Bingzhuo in September 17, 2018


if nargin==5
    if ~isa(Para,'romotes_options')
        error('RoMoTeS: the options must be an romotes_options object')
    else
        par.max_delay_s=Para.max_delay_s;
        par.sample_f_s=Para.sample_f_s;
        par.lipschitz_on=Para.lipschitz_on;
        par.upper_const_dev=Para.upper_const_dev;
        par.lower_const_dev=Para.lower_const_dev;
        rob=mx_romotes(stlFormula,pred,STraj,T,par);
    end
else
    error('RoMoTeS: Input is not in the right format.')
end


            