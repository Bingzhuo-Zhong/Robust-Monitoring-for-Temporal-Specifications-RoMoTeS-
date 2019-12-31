classdef romotes_options
% Parameters necessary for RoMoTeS

 properties
    max_delay_s;        %maximal delay in signal
    sample_f_s;         %frequency for verifying specification
    lipschitz_on;       %whether lipschitz deviation term is on
    upper_const_dev;    %constant part of upper deviation,vector
    lower_const_dev;    %constant part of lower deviation, vector
 end
 
 methods
         function obj = romotes_options(varargin)
            if nargin>0
                error('romotes_options: Please access directly the properties of the object.')
            end
            obj.max_delay_s=0;
            obj.sample_f_s=0.1;
            obj.lipschitz_on=false;
            obj.upper_const_dev=0;
            obj.lower_const_dev=0;
         end
 end
 
end
