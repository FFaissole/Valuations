# Synthetic Topology in Homotopy Type Theory for probabilstic programming

Florian Faissole - Bas Spitters 

This work is based on HoTT and HoTTClasses. 

# Build 

You need the following dependencies: 
- IR branch of Coq: https://github.com/mattam82/coq/tree/IR
- HoTT modified to compile with Coq IR: https://github.com/SkySkimmer/HoTT/tree/mz-8.7
- HoTTClasses: https://github.com/SkySkimmer/HoTTClasses 

Install the dependencies and run the following commands:

- cd Valuations/
- make

# Organization

The project is organized as it follows:

- Dominance.v: proof that the Sierpinski space is a dominance. 
- Cpo.v: formalization of w-cpo.
- wCpo\_compl.v: proof of the w-Cpo completion.
- Rlow.v: formalization of the lower reals. 
- Opens.v: open subspaces in synthetic topology.
- Functions.v: integrable functions. 
- Valuations.v: theory of valuations. 
- LowerIntegrals.v: theory of lower integrals. 
- D\_op.v: operator which takes a function and a rational 
and gives the open in which the function is bigger than the 
rational.
- OpenFun.v: characteristic functions of open subspaces.
- Riesz1.v: embedding of lower integrals into valuations.
- Giry.v: Giry monad on lower integrals.
- Interp.v: Interpretation of probabilistic languages.
- Flip.v: flip coin program. 
- Random.v: random number generator. 
- RandomWalk.v: random walk programm. 
- S\_compute\_tac.v: tactic for partial values.
- U01.v: valuation on [0,1] from an axiomatic integral.








