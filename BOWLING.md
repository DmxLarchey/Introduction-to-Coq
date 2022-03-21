# Modeling Bowling plays and scores

## Goal of the project

The goal of the project is to model the _scoring_ in the [game of
bowling](https://fr.wikipedia.org/wiki/Bowling).
Ultimately, we show that the score of a bowling play is a natural number
between 0 (minimum score) and 300 (maximum score) and that every score 
from 0 to 300 can be realized by at least one bowling play.

## Quick informal description of the scoring in bowling

One bowling play is composed of 
* _10 initial frames_ of one or two _rolls_ cumulating up to 10 _pins_ down:
  - strictly less than 10 pins down give an _open_ frame;
  - 10 pins down in two rolls give a _spare_;
  - and 10 pins down on the first roll give a _strike_; 
* (possibly) _one extra frame_ composed of one or two rolls. 
  In case of two rolls, if the first roll strikes 10, then 
  10 new pins are made available for the second roll.

To count the score, one counts the total of pins down in the
10 initial frames. But spares and strikes get extra pin value:
* on a spare, the pins down on the following roll is counted 
  as extra on the spare. For example, a spare 9+1 followed
  by a open frame 5+3 counts as 9+1+5;
* on a strike, the pins down on the two following rolls are
  counted as extra on the strike. For example, a strike followed
  by a strike and a open frame 3+6 counts as 10+10+3.
* the reason for the existence of the extra frame is to complete the score of
  the last (or two last) initial frames, if they are spares 
  or strikes.

## The code source code to complete the project

The standalone Coq source file [`bowling.v`](bowling.v) contains
code to achieve this modeling up to the charaterization of realizable
scores. Your goal is to _fill the holes._
Holes are totally `Admitted` or partially `admit`ted proof scripts.
The proof sketch will lead you to the goal. 

* You do not need to invent complicated inductions or introduce 
  new notions, the modeling is done for you; 
* But you need to be able to understand how the informal problem
  is modeled by these definitions and notations; 
* Your capacity to use and combine tactics will be critical
  to your success in filling proof holes;
* Some holes are very easy, and some other are more difficult;
* For those willing to go further, some suggested improvements 
  appear at the end of the project file.

## Expectations and Timetable

The project starts March 28th 2022 and lasts 6 weeks. It is an 
**individual project** and students will be required to send a 
completed project file to me [Dominique Larchey-Wendling](mailto:larchey@loria.fr) 
after that six week period has expired. The deadline for sending the
completed project file is **May 6, 2022**. Please contact me if you have 
any question or difficulty regarding the project.
