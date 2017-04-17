# Synthetic Topology in Homotopy Type Theory for probabilstic programming

Florian Faissole - Bas Spitters 

This work is based on HoTT and HoTTClasses. 

# Build 

You need the following dependencies: 
- IR branch of Coq: https://github.com/mattam82/coq/tree/IR
- HoTT branch with IR: https://github.com/SkySkimmer/HoTT/tree/with-IR must be present on your system, built with Coq with IR
- HoTTClasses: https://github.com/SkySkimmer/HoTTClasses

Install the dependencies and run the following commands:

- cd Valuations
- make

# Organization

The project is organized as it follows:

- Models/*: basic definitions of the axioms of synthetic topology and sanity checks to verify that the formalism in which we rely is suitable for our purpose: definition of dominance, the Sierpinski space is a dominance, definition of cpo, partial types are free w-Cpo completion, definition of compactness.

- Spaces/*: formalization of our basic spaces; RoundedClosed.v contains a formalization of rounded closed cuts and and more precisely of lower reals; Opens.v contains a formalization of the open subsets of a set in synthetic topology; Functions.v contains the formalization of integrable positive functions.

- Theories/*: formalization of the theories of valuations and integrals, with a construction of the valuation associated to an integral, and machinery to build an integral from a valuation, with a partial proof of a constructive Riesz's Theorem. 
    
- Probas/*.v: interpretation of probabilistic languages: Giry.v contains a formalization of the Giry monad on integrals; Interp.v contains the interpretation rules of the semantic of a Rml-like language; Flip.v, Random.v and RandomWalk.v are examples of mini probabilstic programs; S_compute_tac.v is a tactic to compute with partial types. 


 
 






