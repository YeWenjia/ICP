# Imperative Compositional Programming (Artifact)


## Introduction

1. **Proof** contains the Coq formalizations of the $\lambda_{im}$ and $F_{im}^+$ calculi.
2. **Code** contains the implementation of the CP compiler extended with support for imperative features.
   You can check <https://github.com/yzyzsun/CP-next> for the up-to-date version.

Both parts can either be evaluated in the pre-built Docker images (with all the dependencies installed) or built from scratch.

## Hardware Dependencies

The Docker images can run on any machine that supports the `linux/amd64` architecture. We verified that an M1 MacBook can also run the images via emulation.

## Getting Started

To get started, we recommend testing if you can pull and run the two Docker images, *or*, based on your own choice, build from scratch. Please follow the instructions in Option 1/2 below.

## Step-by-Step Instructions

### 1. Proof

#### (Option 1) Docker Image

You can pull and run the Docker image by the following command:
```
docker run -it wenjiaye/icp-oopsla24:v1 
```

Please jump to the confluence part to build the proofs.

#### (Option 2) Build from Scratch 

We describe how to build the proofs from scratch below:

1. Install Coq 8.10.2.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam-using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.10.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is properly installed (type `coqc` in the terminal and you should *not* see "command not found"), then install `Metalib`:
   1. `git clone https://github.com/plclub/metalib`
   2. `cd metalib/Metalib`
   3. Make sure the version is correct by `git checkout 597fd7d`
   4. `make install`

####  (Confluence) Build the Proofs

1. Enter `/home/Proof/IM` or `/home/Proof/FIM` directory.

2. Please make sure you have run the command `eval $(opam env)` if you installed Coq via opam.

3. Type `make` in the terminal to build and compile the proofs.

4. For `IM`, you should see something like the following:
```
$ cd /home/Proof/IM
$ make
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC Infrastructure.v
COQC Wellformedness.v
COQC SubtypingInversion.v
COQC Disjointness.v
COQC Value.v
COQC KeyProperties.v
COQC Deterministic.v
COQC IsomorphicSubtyping.v
COQC TypeSafety.v
```
estimated time: 1min.

For `FIM`, you should see something like the following:
```
$ cd /home/Proof/FIM
$ make
_CoqProject && coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC Infrastructure.v
COQC Wellformedness.v
COQC Value.v
COQC SubtypingInversion.v
COQC Disjointness.v
COQC KeyProperties.v
COQC Deterministic.v
COQC IsomorphicSubtyping.v
COQC TypeSafety.v
```
estimated time: 10min.


### 2. Code

#### (Option 1) Docker Image

You can pull and run the Docker image by the following command:
```
docker run -it yzyzsun/cp-next:oopsla24
```

Please jump to the confluence part to run the CP examples.

#### (Option 2) Build from Scratch

1. First of all, you need to install [Node.js](https://nodejs.org).
2. Change the current directory to `Code` in the terminal.
3. Then execute `npm install` to get all of the dev dependencies (PureScript and Spago).
4. After installation, execute `npm start` to install PureScript libraries and run a REPL.

#### (Confluence) Run the CP Examples

Inside the REPL, use the `:compile` command to execute CP files.

```
$ npm start

> cp-next@OOPSLA24 start
> spago run

[info] Build succeeded.
Next-Gen CP REPL, OOPSLA'24 version

> :compile examples/Prog1.cp
true: [ ]
 x = true: [ ]
  false: [ x; ]
   y = false: [ x; ]
    x: [ x; y; ]
     y: [ y; ]
      x = y: [ y; ]
     x: [ x; ]
      z = not x: [ ]
()
> :compile examples/Prog2.cp
10: [ ]
 x = 10: [ ]
  x: [ x; ]
   0: [ x; ]
    x: [ x; ]
     1: [ x; ]
      y = (x + 1): [ x; ]
       <Phi>: [ x; y; ]
        x: [ x; y; ]
         y: [ y; ]
          z = (x + y): [ ]
    x: [ x; ]
     1: [ x; ]
      y = (x - 1): [ x; ]
()
```

## Proof Correspondence

If a reader wishes to reuse the proofs provided, they can refer to the `syntax_ott.v` file and modify the syntax to suit their needs.

Next, we show some important lemmas and theorems correspondence with the Coq formalization. The following table shows the correspondence between lemmas discussed in the paper and their Coq code. For example, one can find `Theorem 3.1` in file `IM/TypeSafety.v` and the definition name in that file is `progress`.

| Theorems/Definitions     | Descriptions                                           | Files                     | Names in Coq        |
| ------------ | ------------------------------------------------------ | ------------------------- | ------------------- |
| Fig. 9   | Syntax                | IM/syntax_ott.v  |          |
| Fig. 10   | Bidirectional typing | IM/syntax_ott.v  | Typing   |
| Fig. 11   | Small-step semantics | IM/syntax_ott.v  | step     |
| Theorem 3.1  | Progress                                               | IM/TypeSafety.v           | progress            |
| Theorem 3.2  | Type preservation                                      | IM/TypeSafety.v           | Preservation        |
| Theorem 3.3  | Type annotations are computationally irrelevant        | IM/TypeSafety.v           | erase_step_v        |
| Fig. 12     | Syntax             | FIM/syntax_ott.v |      |
| Lemma 4.1    | Reflexivity of subtyping                               | FIM/SubtypingInversion.v  | sub_reflexivity     |
| Lemma 4.2    | Transitivity of subtyping                               | FIM/SubtypingInversion.v  | sub_transitivity     |
| Fig. 13     | Extended subtyping | FIM/syntax_ott.v | algo_sub |
| Fig. 13     | Extended type splitting | FIM/syntax_ott.v | spl |
| Fig. 13     | Disjointness           | FIM/syntax_ott.v   | disjoint |
| Fig. 13     | Top-like types          | FIM/syntax_ott.v   | topLike |
| Fig. 14     | Well-formed types         | FIM/syntax_ott.v   | WFTyp |
| Fig. 14     | Bidirectional typing | FIM/syntax_ott.v   | Typing |
| Fig. 14     | Applicative distribution             | FIM/syntax_ott.v   | appDist |
| Lemma 4.3    | Well-formedness of typing                              | FIM/Deterministic.v       | Typing_regular_0    |
| Lemma 4.4    | Uniqeness of type inference                            | FIM/TypeSafety.v          | inference_unique    |
| Lemma 4.5    | Subsumption of type checking                           | FIM/TypeSafety.v          | Typing_chk_sub      |
| Fig. 15     |  Isomorphic subtyping | FIM/syntax_ott.v   | subsub |
| Lemma 4.7    | Isomorphic subtyping                                   | FIM/IsomorphicSubtyping.v | subsub2sub          |
| Fig. 16     |  Casting              | FIM/syntax_ott.v   | Cast |
| Fig. 17     |  Small-step semantics  | FIM/syntax_ott.v   | step |
| Theorem 4.8  | Determinism of reduction                               | FIM/Deterministic.v       | step_unique_both    |
| Theorem 4.9  | Progress of reduction                                  | FIM/TypeSafety.v          | progress            |
| Theorem 4.10 | Type preservation with respect to isomorphic subtyping | FIM/TypeSafety.v          | Preservation_subsub |
|Corollary 4.11| Type preservation                                      | FIM/TypeSafety.v          | Preservation        |
| Appendix   | Disjointness of Fim+   | FIM/syntax_ott.v   | disjoint |
| Appendix   | Subtyping of Fim+  | FIM/syntax_ott.v | algo_sub |
| Appendix   | Top-like values     | FIM/syntax_ott.v | TLVal |
| Appendix   | Small-step semantics without annotations | IM/syntax_ott.v  | nstep    |

## Checking Axioms

To check the axioms that out proofs rely on, you can use `Print Assumptions theorem_name.` in Coq. For example, by adding `Print Assumptions Preservation.` to the end of `TypeSafety.v` and `make clean` then re-run `make`, you will see:

```
COQC TypeSafety.v
Axioms:
JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y
```

It should be the only axiom that the theorem relies on, which is introduced by the use of dependent induction.
