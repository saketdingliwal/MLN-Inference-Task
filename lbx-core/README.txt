### README --- 

## Authors: Carlos Mencia, Alessandro Previti and Joao Marques-Silva
## Copyright (c) 2015

*** Overview:
LBX is a tool for the extraction of Minimal Correction Subsets (MCSes) 
of CNF formulas. It also allows for enumerating MCSes, as well as 
approximating MaxSAT by selective MCS enumeration. The input formulas 
can be specified in standard DIMACS CNF format (.cnf) or  weighted CNF 
format (.wcnf).


*** Tool usage:
For getting detailed information about LBX arguments run "./lbx -h".


*** MCS extraction:
LBX uses the Literal-Based eXtractor algorithm [1]. By default, LBX enumerates 
all  MCSes, so for extracting a single MCS, set the option '-num 1'


*** MCS enumeration:
By default, LBX enumerates all MCSes. This corresponds to setting
'-num 0'. Option '-num NNN' can be used to indicate how many MCSes are
to be computed.


*** MaxSAT approximation:
LBX can approximate (partial weighted) MaxSAT by applying a suite of techniques for
selective MCS enumeration [1]. For this purpose set the option '-mxapp'.


*** Additional options/features:
-T  TTT: specify timeout in seconds [default: -T 3600]
-st: output statistics
-nw: do not write MCSes
-wm: write models
-rcpu: report CPU time with MCSes

*** Note
LBX assumes that the input formula is unsatisfiable.


*** References:
[1] C. Mencia, A. Previti, J. Marques-Silva : Literal-Based MCS Extraction.
 IJCAI 2015.


*** Credits:
Developer and maintainer: Carlos Mencia
Contributors: Alessandro Previti and Joao-Marques Silva


### README ends here
