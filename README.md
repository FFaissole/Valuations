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
    between Opens(A) and the continuous maps (A --> S) where S is the Sierpinski space (see the formalization 
    of the Sierpinski space as Partial Unit in the HoTTClasses developement). 
 
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

 - D_op.v: Here we build an operator (D_op : Q+ -> mf A -> OS A) such that ((D_op q f) x) iff f x > q. It permits to 
 build a basis of opens for a lower approximation of the function by characteristic functions of these opens. 
 
 - OpenFun.v: Here we build an operator (OpenFun : OS A -> mf A) which takes an open subset of A and return the 
 characteristic function of the open subset. It is built using the induction principal on partial types.  
 
 - Sum_p_r.v: Here we build the sum of the measures of the opens generated by the D_op operators in a rational subdivision 
 of the values of the function, as an approximation of the integral of a function.
 
 - Simples.v: Here we use the least upper bound of the sum_p_r objects and prove that it is actually a good candidate to be an integral with the good properties. 
 
 - Riesz.v: Here we provide the 4 main parts of the proof of the Riesz theorem: 
 
     -- Riesz1: I_mu is an integral; 
     
     -- Riesz2: mu_I is a valuation;
     
     -- Riesz_hom1: forall valuation nu, mu_I_nu = nu; 
     
     -- Riesz_hom2: forall integral J, I_mu_J = J.
 
4) Probas: in this repository, we use our model to interpret computational calculus and simple probabilistic programs. 

 - Monad.v: a simple definition of a Kleisli's triple in the HoTT's formalization of category theory.
 
 - Giry.v: here we give a construction of the probability monad, more particularely the two monadic operators unit and 
 bind of the monad of valuations. 
 
 - Programs.v: here we give: 
    
    -- An interpretation of simples probabilistic programs: abstraction, application, conditional; 
    
    -- A construction of simple programs: flip coin and random number. 
 
 






