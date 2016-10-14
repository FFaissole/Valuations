#Probabilstic programming in HoTT using synthetic topology

Florian Faissole - Bas Spitters 

This work is based on HoTT and HoTTClasses. 

#Build 

You need the following dependencies: 
- IR branch of Coq: https://github.com/mattam82/coq/tree/IR
- HoTT branch with IR: https://github.com/SkySkimmer/HoTT/tree/with-IR must be present on your system, built with Coq with IR
- HoTTClasses: https://github.com/SkySkimmer/HoTTClasses

#Description of the files: 

- Duilq.v: general construction of rounded up/down closed subset of a set, base of the lower and upper reals construction. 
- Models.v: some axioms and results needed for synthetic topology.
- Monads.v: a little definition of a monad (Kleisli's approach) based on the HoTT's category theory.
- Valuations.v: formalization of open subsets and valuations (probability distributions but on open subsets). 
- IntPos.v: integrable functions and lower integrals. 
- RieszTh.v: formalization of a constructive Riesz representation theorem.
- SimpleFunctions.v: definition of simple functions by Tarski's free monoid.





