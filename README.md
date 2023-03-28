# Introduction to the Coq proof assistant

_Preuve et Déduction Automatique (Coq)_ is a course that will take place live in *Salles HP 309 and HP 303*.
You can also contact me via e-mail at the address `dominique.larchey-wendling@loria.fr`

Have a look at the herein [resource file](resources.md) for general information about `Coq` incl. installation instructions.

## Learning outcomes

After successful completion of the course, students are able to understand 
and use the Coq proof assistant; in particular to formalize propositional logic, 
quantifiers inductive types and inductive predicates. 

## Subject of course

This course gives an introduction to the Coq proof assistant:

_Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching._

## Project: [sorting algorithms](SORTING.md)

The project --- see [detailed project description](SORTING.md) --- consists in modeling
sorting algorithms in Coq and getting correct by construction OCaml implementation
of _insertion sort_, _quick sort_ and _merge sort_ using Coq extraction mechanism.

## Teaching methods

The course will take place live  in *Salles Atelis HP 309 and HP 303*.
See the [resource file](resources.md) file for a more precise schedule.

## For lab. sessions, the students need to install `Coq` and `CoqIde` on their working computer
- no need to get the latest version (`v8.16`)
- anything above `Coq 8.8` (over 6 years old) will work
- the Coq main site: https://coq.inria.fr
- for Linux, try in that order:
  1. install coq & coqide available for your distribution
  2. or follow https://github.com/coq/coq/wiki/Installation-of-Coq-on-Linux
  3. or install it through opam 2 (for experts)
- installing `Coq` for Windows or Mac users:
  - there are packages in here [Coq@GitHub](https://github.com/coq/coq/releases/tag/V8.11.0)
