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

1) Spaces: 
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
  
- Model.v: some axioms and results needed for synthetic topology.
- Monad.v: a little definition of a monad (Kleisli's approach) based on the HoTT's category theory.
- Valuations.v: formalization of open subsets and valuations (probability distributions but on open subsets). 
- LowerIntpos.v: integrable functions and lower integrals. 
- Riesz.v:

2) Theories: 
- Test






