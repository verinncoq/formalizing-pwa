# Formalizing Piecewise Affine Activation Functions of Neural Networks in Coq

by [Andrei Aleksandrov](https://github.com/Zawuza) and [Kim Völlinger](https://github.com/KimVoellinger).

## Overview

The use of AI in safety-critical industries such as automotive and aerospace requires assurance that neural networks will behave according to standards and regulations in the specific industry. Ideally, we want to present concise and verifiable evidence about the safety of a particular AI system. Unfortunately, it is hard to do, so the research split into *explainability*, which focuses on providing a concise explanation of AI behavior and reasoning, and *verification*, which attempts to give strong verifiable guarantees on AI's behavior, but without the requirement to be easily understandable by a human. 

In this work, we accomplished the first step for implementation of AI verification algorithms in Coq. We encoded a model of feedforward neural networks and developed a verified conversion between NNs and piecewise-affine (PWA) functions with its correctness proof. The PWA function is an abstract representation that one can easily encode into automatic solvers (SMT and MILP), but we did not implement the encoding itself here.

To accomplish this, we developed the theory of PWA functions inside Coq. We created a constructive representation of PWA functions. Then, we did prove that PWA functions are closed under composition and concatenation. Finally, we developed a verified transformation between neural networks and PWA functions. 

To see more details, read the full text [here](https://arxiv.org/abs/2301.12893).

## Repository overview

```
│   README.md
│   .gitignore
│   LICENSE
│   _CoqProject
│   build.ps1            <---- Script to compile all files
│   matrix_extensions.v  <---- Extensions of Coquelicot   
│   neural_networks.v    <---- Neural network definition,
│                              verified transfortmation
│   neuron_functions.v   <---- Different layer types and activations
|   piecewise_affine.v   <---- PWA function definition + example
|   pwaf_operations.v    <---- Proofs about operations on PWA 
```

## Running instructions

This code was developed using Coq 8.15.2 and Coq Platform 2022.04.1.

Because we use Coq Platform, we expect Coquelicot library to be avaliable in Coq by default. Otherwise, you need to install [Coquelicot](http://coquelicot.saclay.inria.fr/html/Coquelicot.Coquelicot.html) from OPAM or any other source.

To use any Coq IDE (CoqIDE or VsCoq), first compile the files using `build.ps1` and then you can use any IDE to browse them: there is _CoqProject in the repository. 
