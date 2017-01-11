#Synthetic Topology in Homotopy Type Theory for probabilstic programming

Florian Faissole - Bas Spitters 

This work is based on HoTT and HoTTClasses. 

#Build 

You need the following dependencies: 
- IR branch of Coq: https://github.com/mattam82/coq/tree/IR
- HoTT branch with IR: https://github.com/SkySkimmer/HoTT/tree/with-IR must be present on your system, built with Coq with IR
- HoTTClasses: https://github.com/SkySkimmer/HoTTClasses

Install the dependencies and run the following commands:

- cd Valuations
- make

#Description of the project: 

1) Spaces: In this repository, we built the basic spaces we will reuse to build our theories.


- RoundedClosed.v: general construction of inhabited rounded up/down closed subset of a set. It permits to define the 
  lower and upper reals. 
  
  Rlow / RlowPos = Q -> Sier + inhabited + down-rounded + positivity (for RlowPos). 
  
  Operations on Rlow/RlowPos: 
  
    -- QRlow: cast of Q as a Rlow;
    
    -- RlPlus: sum of lower reals; 
    
    -- Rlmult_q: product of a lower real with a positive rational;
    
    -- Rlminus_q: substraction of a lower real and a positive rational; 
    
    -- Rljoin: join of two lower reals; 
    
    -- Rlmeet: meet of two lower reals; 
    
    -- Rllub: lub of a sequence/enumerable set of lower reals. 
    
- Opens.v: here we give a construction of the opens subspaces of a set A using the correspondance 
    O(A) <---> A --> S where S is the Sierpinski space. 
 
- Functions.v: here we give a construction of the positive functions from A to RlowPos.  
 
- Cpo.v: here we define the structure directed complete partial order to define lower bounds on 
 sets of a given type/set. 
  
2) Theories: In this repository, we build the two theories of Valuations and LowerIntegrals.


- Valuations.v: we define a valuation like a measure on the opens subsets of a set A
  ((A -> Sier) -> RlowPos) with: 
  
   -- monotonicity;
   
   -- modularity;
   
   -- definiteness;
   
   -- sub-probability.
  
- LowerIntegrals.v: we define a (lower) integral on the functions
  ((A -> RlowPos) -> RlowPos) with: 
   -- monotonicity;
   
   -- sigma-additivity;
   
   -- definiteness;
   
   -- sub-probability; 
   
   -- continuity.
  

3) Riesz: in this repository, we provide a constructive formal proof of the homeomorphism between the theories  
   of valuations and lower integrals. 

 - D_op.v: 
 
 - OpenFun.v: 
 
 - Simples.v:
 
 - Riesz.v: 
 
4) Probas: in this repository, we use our model to interpret computational calculus and simple probabilistic programs. 

 - Monad.v: 
 
 - Giry.v:
 
 - Programs.v: 
 
 






