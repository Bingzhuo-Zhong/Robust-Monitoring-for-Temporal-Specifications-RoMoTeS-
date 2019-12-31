function [lbd,ubd] = SignedDisInterval(x,A,b)
%Function for calculating the robutsness estimate interval
% For details, please refer to Section 4.1.2 of the master thesis 
% "Robust Monitoring of Temporal Properties for Continuous Signals in Hybrid Systems"

    [noc,nos,nod] = size(A);

    if isempty(A)
        lbd = inf;
        ubd = inf;
        return
    end

    if nod~=1  
        error('The set must be convex');
    end
    for i=1:1:nos
       lb(i,1)=x(i).lowerb;
       ub(i,1)=x(i).upperb;
    end 
    if noc==1 %if there is only one constraint,simple optimization problem can be apply
        x0=zeros(nos,1);
        options=optimset('Largescale','off','Display','off');
        a_abs=norm(A(1,:));
        fun_l=@(x)(b-A(1,:)*x)/a_abs;
        [~,lbd] =fmincon(fun_l,x0,[],[],[],[],lb,ub,[],options);
        fun_u=@(x)-(b-A(1,:)*x)/a_abs;
        [~,tmp_ubd] = fmincon(fun_u,x0,[],[],[],[],lb,ub,[],options);
        ubd=-tmp_ubd;
    else %there is more than one constraint
        %generating vertices of the deviation polytope
        for i=0:1:2^nos-1
            b_code=dec2bin(i,nos);
            for j=1:1:nos
                indicator=b_code(j);
                if indicator=='0'
                    target_point(j,i+1)=lb(j,1);
                else
                    target_point(j,i+1)=ub(j,1);
                end            
            end
        end
        %start calculating huasdorff distance, which is related to the 
        %lower bound from the deviation polytope to the permissive polytope
        H=eye(nos,nos);
        x0=zeros(nos,1);
        options=optimset('Largescale','on','Display','off');
        for i=1:1:2^nos
            a=target_point(:,i);
            fun=@(x)x'*H*x-2*a'*x+a'*a;
            [~,result(i)]=fmincon(fun,x0,A,b,[],[],[],[],[],options);
        end
        lbd=max(result);
        if abs(lbd)>0.001
            %huasdorff distance is not zero, which indicates that there is 
            %point which is outside the permissive polytope
            
            lbd=-sqrt(lbd);%maximal point is outside, distance is negative

            %try to calculate the upper bound
            H=eye(2*nos,2*nos);
            for i=1:1:nos
                H(i,i+nos)=-1;
                H(i+nos,i)=-1;
            end
            M=2*nos+noc;
            N=nos*2;
            U=eye(nos,nos);
            L=-eye(nos,nos);
            A_cur=zeros(M,N);
            A_cur((2*nos+1):M,(nos+1):N)=A;
            A_cur(1:nos,1:nos)=U;
            A_cur((nos+1):(2*nos),1:nos)=L;
            b_cur(1:nos,1)=ub;
            b_cur((nos+1):(2*nos),1)=-lb;
            b_cur((2*nos+1):M,1)=b;
            x0=zeros(2*nos,1);
            fun=@(x)x'*H*x;
            options=optimset('Largescale','on','Display','off');
            [~,ubd]=fmincon(fun,x0,A_cur,b_cur,[],[],[],[],[],options);

            %if the lower bound is bigger than zero, the deviation polytope
            % and the observation map does not intersect
            
            if abs(ubd)>0.001  
                ubd=-sqrt(ubd);
            else
            %other wise, they intersect with each other
            order='fun=@(x)([';
            for i=1:1:noc
                cur_i=num2str(i);
                tmp_oder=strcat('-(b(',cur_i,')-A(',cur_i,',1:nos)*x)/norm(A(',cur_i,',1:nos))');
                order=strcat(order,tmp_oder);
                if i~=noc
                    order=strcat(order,';');
                end
            end
            order=strcat(order,']);');
            eval(order);
            x0=zeros(nos,1);
            options=optimset('Largescale','off','Display','off');
            [test,fval]=fminimax(fun,x0,[],[],[],[],lb,ub,[],options);
            ubd=max(fval);
            ubd=-ubd;
            end
        else
            %huasdorff distance is zero, which indicate that the deviation 
            %polytope totally lies in the permissive polytope calculating 
            %upper bound
            order='fun=@(x)([';
            for i=1:1:noc
                cur_i=num2str(i);
                tmp_oder=strcat('-(b(',cur_i,')-A(',cur_i,',1:nos)*x)/norm(A(',cur_i,',1:nos))');
                order=strcat(order,tmp_oder);
                if i~=noc
                    order=strcat(order,';');
                end
            end
            order=strcat(order,']);');
            eval(order);
            x0=zeros(nos,1);
            options=optimset('Largescale','off','Display','off');
            [test,fval]=fminimax(fun,x0,[],[],[],[],lb,ub,[],options);
            ubd=max(fval);
            ubd=-ubd;
            
            %calculating lower bound
            y0=zeros(nos,1);
            options=optimset('Largescale','off','Display','off');
            for i=1:1:noc
                fun=@(y)(b(i)-A(i,:)*y)/norm(A(i,:));
                [~,tmp_lbd(i)] = fmincon(fun,y0,[],[],[],[],lb,ub,[],options);
            end
            lbd=min(tmp_lbd);
        end
    end
end



