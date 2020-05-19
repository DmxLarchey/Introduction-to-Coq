# Introduction to the Coq proof assistant
[TUWEL online course](https://tiss.tuwien.ac.at/course/courseDetails.xhtml?dswid=3076&dsrid=195&courseNr=192098&semester=2020S)  and the [Discord server](https://discord.gg/DEJ8Ce) or contact me on Discord: **Dominique Larchey-Wendling#0283**

Have a look at the herein [resource file](resources.md) for general information about `Coq` incl. installation instructions.

## Learning outcomes

After successful completion of the course, students are able to understand 
and use the Coq proof assistant; in particular to formalize propositional logic, 
quantifiers inductive types and inductive predicates. Hopefully they will be able
to show by themselves that the [Towers of Hanoi](https://en.wikipedia.org/wiki/Tower_of_Hanoi)
move strategy is correct and optimal.

## Subject of course

This course gives an introduction to the Coq proof assistant:

_Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching._

## Project: the Towers of Hanoi

The project --- see [detailed project description](HANOI.md) --- consists in modeling the game of 
the [Towers of Hanoi](https://en.wikipedia.org/wiki/Tower_of_Hanoi) and proving that
the well know recursive Hanoi sequence of moves is a correct.

## Teaching methods

Due to the Covid-19 infection, the course and lab sessions will be given online

### To follow the lessons students need:

- a computer with either Linux, Windows or IOS/macOS
  * not a tablet nor a smartphone
  * virtual OS is possible (eg VirtualBox)
- a microphone and headphones (mandatory)
  * headphones to avoid audio feedback/larsen effect
- camera is a plus
  * but we will certainly not use it much to save bandwith

- the [Discord app](https://discordapp.com):
  * free of charge, allows screen sharing
  * works in a navigator (tested with Chrome)
  * standalone apps for Linux, Windows & IOS
- need to register a (free) account on [discordapp.com](https://discordapp.com)
- the account of the teacher is: **Dominique Larchey-Wendling#0283**
- the Discord server: [**Introduction to Coq**](https://discord.gg/PgFSYE)

### For lab. sessions, the students need to install `Coq` and `CoqIde` on their own computer
- no need to get the latest version (`v8.11`)
- anything above `Coq 8.8` (over 3 years old) will work
- the Coq main site: https://coq.inria.fr
- for Linux, try in that order:
  1. install coq & coqide available for your distribution
  2. or follow https://github.com/coq/coq/wiki/Installation-of-Coq-on-Linux
  3. or install it through opam 2 (for experts)
- installing `Coq` for Windows or Mac users:
  - there are packages in here [Coq@GitHub](https://github.com/coq/coq/releases/tag/V8.11.0)
