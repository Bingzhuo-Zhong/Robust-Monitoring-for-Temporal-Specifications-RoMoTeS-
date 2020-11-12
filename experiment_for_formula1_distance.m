% Experiment for specification 1 for offline monitoring
%% Information about specification formula, predicates, and run-time obtions 
stlFormula='p';
Pred(1).str='p';
Pred(1).A=[2, 0;-2, 0];
Pred(1).b=[2;2];
para=romotes_options();
max_delay=0;
signal.Data1=[-2.5 -2 0];
signal.Data2=[-2.5 -2 0];
signal.Time=[0 0.1 0.2];
if max_delay>0
   [STraj,T] = add_delay_to_signal(max_delay,signal);
else
    STraj=[signal.Data1;signal.Data2]';
    
    T=signal.Time';
end
para.max_delay_s=max_delay;
para.sample_f_s=0.1;                %calculation period when time delay exists in signal, master thesis, section 4.1.2
para.lipschitz_on=false;            %whether lipschitz error is considered
para.upper_const_dev=[2 2];             %Vector for upper bound deviation
para.lower_const_dev=[2 2];             %Vector for lower bound deviation

%% Run 1000 times to obtain the computational time
%test_time=1000;%define total testing times
%t=zeros(test_time,1);
%for i=1:1:test_time
%    tic;
    rob=Compute_Robustness_Interval(stlFormula,Pred,STraj,T,para);
%    t(i,1)=toc;
%end

%% Demonstration of the last result
plot(rob.u_time,rob.u_bound,'b')
hold on
plot(rob.l_time,rob.l_bound,'r')
hold on
const=zeros(length(rob.l_time),1);
plot(rob.l_time,const,'m')
title('Result of Robust Monitoring')
legend('upper bound of robustness interval','lower bound of robustness interval','0-line');