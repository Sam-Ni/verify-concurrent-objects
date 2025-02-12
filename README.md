# Compositional Verification of Concurrent Objects

## Overview

This project formalizes concurrent objects using labelled transition systems (lts).
An object is correct if its lts refines the specification of the object.
Particularly, the object is linearizable if the specification is atomic.

The goal is to show that 
1. bigger objects can be built from composing the lts of smaller concurrent objects with open modules (implementation of big objects);
2. the correctness of bigger objects can be derived from
  proving the correctness of composition of corresponding specification of smaller objects and open modules.

## Plan

1. Define the labelled transition system and its general theory.

    It has 3 parts:
    1. lts and composition (LTS.v, currently the definition of composition is not strong enough in the simulation proof);
    2. trace, refinement and simulation (Refinement.v, may define backward simulation in the future);
    3. preservation of refinement in composed lts (TODO, first need to improve the definition of composition).

2. Apply the theory in an example. 

    The example has three layers of objects:
    1. an atomic Register with CAS and Read (Register.v);
    2. a RegisterCounter (RegisterCounter.v), which is a composition of the Register in layer 1 and the implementation (DCounter.v) of the Counter;
    3. A timer or queue using the RegisterCounter (and Register) (TODO).

    The goal is to show that
    1. RegisterCounter is correct in the sense that it refines the specification of the atomic Counter (Counter.v);
    2. the composition of Counter and implementation of timer
    refines the specification of timer (TODO);
    3. by the general theorem in 1.iii, the composition of RegisterCounter and implementation of timer preserves the refinement in ii (TODO).
    
## Compilation

The files should compile with Coq v8.19.1 in Linux.

1. In the terminal, cd to '~/.../ 
  verify-concurrent-objects' root
  directory.

2. Use ```make``` to compile the project.