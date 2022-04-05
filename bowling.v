(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia List Euclid.

Import ListNotations.

(** The tactic "destr n up to i as H" the generates the (i+1) subgoals:
  - n is 0
  - n is 1
  - n is ...
  - n is i-1
  - H: i <= n
*)

Fact lt_le_dec m n : { n < m } + { m <= n}.
Proof. destruct (le_lt_dec m n); auto. Qed.

(* Generates cases x is 0, ... x is i-1, and x is (S ... S ..)*)
Ltac destruct_up_to x i :=
  match i with
    | 0 => try lia
    | S ?i => destruct x as [ | x ]; [ | destruct_up_to x i ]
  end.

(* Generates cases x is 0, ..., x is i-1 and H:i <= x *) 
Tactic Notation "destr" ident(n) "up" "to" constr(i) "as" ident(H) := 
  destruct (lt_le_dec i n) as [ H | H ]; [ destruct_up_to n i; clear H | ].

Tactic Notation "destr" ident(n) "up" "to" constr(i) := 
  let H := fresh in destr n up to i as H.

(* Example of use of the tactic  destr _ up to _ as _*)
Goal forall n, n = 0 \/ n = 1 \/ 2 <= n.
Proof.
  intros n.
  destr n up to 2 as Hn.
  + auto.  (* subgoal n is 0 *)
  + auto.  (* subgoad n is 1 *)
  + auto.  (* subgoal Hn : 2 <= n *)
Qed.

(** Reversed (right to left) notations for lists *)

Local Notation "l '-:' x" := (cons x l) (at level 59, left associativity, format "l -: x") : list_scope.
Local Notation "l ':-:' m" := (app m l) (at level 59, left associativity, format "l :-: m") : list_scope.

Local Notation "[ x ]" := ([]-:x) : list_scope.
(* Local Notation "[ x ⊳ .. ⊳ y ⊳ z ]" := (( .. ([] -: x) .. -: y) -: z ) : list_scope. *)

Local Reserved Notation "x ↑ n" (at level 50, left associativity, format "x ↑ n"). 

(** The repeater: x↑n = [ x ⊳ x ⊳ ... ⊳ x ] where x is repeated n times *)
Fixpoint repeat {X} (x : X) n :=
  match n with 
    | 0   => []
    | S n => x↑n -: x
  end
where "x ↑ n" := (repeat x n).

Fact repeat_S X (x : X) n : x↑(S n) = x↑n -: x.
Proof. reflexivity. Qed.

(** Sum of a list of natural numbers *)
Fixpoint lsum l :=
  match l with
    | []     => 0
    | l -: x => x+lsum l
  end.

(** Some useful arithmetic inequalities *)
Local Fact lt_0_10 : 0 < 10.  Proof. lia. Qed.
Local Fact lt_1_10 : 1 < 10.  Proof. lia. Qed.
Local Fact le_0_10 : 0 <= 10. Proof. lia. Qed.
Local Fact lt_9_10 : 9 < 10.  Proof. lia. Qed.

Section Bowling.

  (** Reserved Notations for the Bowling game predicates *)

  Reserved Notation "l '//' m '-[' n ']->' s" (at level 70, format "l  //  m  -[ n ]->  s").
  Reserved Notation "'I||-' x '@' y '>>'"  (at level 70, format "I||-  x  @  y >>").
  Reserved Notation " l '+:' e '-->' s" (at level 70, format "l  +:  e  -->  s").
  Reserved Notation "'B||-' x" (at level 70, format "B||-  x").

  (** Modelling the Bowling plays with frames, rolls, pins down etc *)

  (* The (first ten) initial bowling frames 

     OPN/open:    2 rolls, no strike, no spare
     SPA/spare:   2 rolls, first roll < 10 pins down,
                           second roll completes to 10 pins
     STR/strike:  1 roll, 10 pins down

   *)

  Inductive iframe : Type :=
    | open a b : a + b < 10 -> iframe (* a pins on 1st roll, b pins on second roll *)
    | spare a  : a < 10     -> iframe (* a pins on 1st roll, 10-a on second roll *)
    | strike   :               iframe (* 10 pins on first roll, no second roll *)
    .

  Notation OPN := open.
  Notation SPA := spare.
  Notation STR := strike.

  (* empty frame, with zero pins down *)
  Definition ZERO := (OPN 0 0 lt_0_10).  

  (* The list of pins down for each roll of an initial frame *)
  Definition iframe2pins r :=
    match r with
      | OPN a b _ => [a;b]
      | SPA a _   => [a;10-a]
      | STR       => [10]
    end.

  Arguments iframe2pins r /.

  (* Value (number of pins down) of the first ball of a frame *)
  Definition ifirst r :=
    match r with
      | OPN a _ _ => a
      | SPA a _   => a
      | STR       => 10
    end.

  Arguments ifirst r /.

  (* ifirst matches the first roll of iframe2pins *)
  Fact ifirst_eq_first_pin r : 
          match iframe2pins r with 
            | []   => False
            | x::_ => ifirst r = x
          end.
  Proof. destruct r; reflexivity. Qed.

  (* Total of pins down of an initial frame *)
  Definition itotal r :=
    match r with
      | OPN a b _ => a + b
      | SPA _ _   => 10
      | STR       => 10
    end.

  Arguments itotal r /.

  (* itotal matches the sum of pins in iframe2pins *)  
  Fact itotal_eq_sum_pins r : itotal r = lsum (iframe2pins r).
  Proof. destruct r; simpl itotal; unfold iframe2pins, lsum; lia. Qed.

  (* The extra bowling frame, one or two rolls to complete 
     pending strikes or spares 

     EX0: zero extra roll
     EX1: one extra roll to complete a spare
     EX2: two extra rolls to complete one (or two) strike(s)

     Notice than if the first roll of EX2 is 10 pins down (ie strike),
     then a new set of 10 pins is made available for the second roll
  *)

  Inductive eframe : Type :=
    | extra0 :                eframe       (* no extra roll *)
    | extra1 a : a <= 10   -> eframe       (* only one extra roll *)
    | extra2 a b : (a < 10 /\ a+b <= 10    (* no strike on first extra roll *) 
                 \/ a = 10 /\ b <= 10)     (* strike on the first roll, 10 new pins *)
                           -> eframe.

  Notation ER0 := extra0.
  Notation ER1 := extra1.
  Notation ER2 := extra2.

  (* The list of pins down for each roll of an extra frame *) 
  Definition eframe2pins e :=
    match e with
      | ER0        => []
      | ER1 a _    => [a]
      | ER2 a b _  => [a;b]
    end.

  (* Status of the previous or two previous frames, if any *)
  Inductive status :=
    | status_none     (* the previous frame does not exist, or is open *)
    | status_spare    (* the last frame was a spare *)
    | status_strike   (* the last frame was a strike, but the one before, was not *)
    | status_2strikes (* the last two frames were strikes *)
    .

  Notation SNON := status_none.
  Notation SSPA := status_spare.
  Notation S1ST := status_strike.
  Notation S2ST := status_2strikes.

  (* New status from previous status after an initial frame *)
  Definition next_status (st : status) (r : iframe) :=
    match st, r with
      | S1ST , STR       => S2ST  (* strike after a strike *)
      | S2ST , STR       => S2ST  (* strike after two strikes *)
      | _    , STR       => S1ST  (* strike after not a strike *)
      | _    , SPA _ _   => SSPA  (* spare after anything *)
      | _    , OPN _ _ _ => SNON  (* open frame after anything *)
    end.

  Arguments next_status st r /.

  (* Pins down to add depending on the status of the two previous frames *)
  Definition status_count st r :=
    match st with
      | SNON => 0                  (* nothing to add here *)
      | SSPA => ifirst r           (* count the first roll value on the previous frame *)
      | S1ST => itotal r           (* count the two rolls value on the previous frame *)
      | S2ST => ifirst r+itotal r  (* count the first roll on the two previous frames 
                                      plus the second on the previous frame *) 
    end.

  Arguments status_count st r /.

  Notation NXT := next_status. 
  Notation STC := status_count.
  Notation TOT := itotal.

  Fact next_status_OPN st a b H : NXT st (OPN a b H) = SNON.
  Proof.
  Admitted.

  Fact next_status_ZERO st : NXT st ZERO = SNON.
  Proof.
  Admitted.

  Fact status_count_ZERO st : status_count st ZERO = 0.
  Proof.
  Admitted.

  (* The initial frames of a bowling play predicate:

      - l: list of frames
      - st: status according to the last two frames
      - n: number of frames
      - sc : score so far

      l // st -[n]-> sc denotes

      "given the n many initial frames stored in the
       list l, with current status st, the score is sc"

      defined by two inductive rules:

            ----------------------- empty play (zero frame)
              [] // SNON -[0]-> 0

                       l // st -[n]-> sc
           --------------------------------------------------- (n<10) next frame is r
             l-:r // NXT st r -[1+n]-> STC st r + TOT r + sc

    *)

  Inductive frames : list iframe -> status -> nat -> nat -> Prop :=
    | frames_start :         

          (*---------------------*)
             [] // SNON -[0]-> 0

    | frames_next l st n sc r : 

             n < 10      ->      l // st -[n]-> sc
      (*---------------------------------------------------*)
      ->  l-:r // NXT st r -[1+n]-> STC st r + TOT r + sc

  where "l // st -[ n ]-> sc" := (frames l st n sc).

  Tactic Notation "play" "from" constr(st) :=
    match goal with
      | |- _-:?r // _ -[ _ ]-> _ => apply (frames_next _ st _ _ r)
    end; simpl; auto; try lia.

  (* Any sequence of frames of length <= 10 is valid:
       if the length of l is below 10 then one can compute
       a status st, and a score sc such that
            l // st -[length l]-> sc *)

  Theorem frames_is_total l : 
             length l <= 10 
          -> { st : _ & { sc | l // st -[length l]-> sc } }.
  Proof.
    induction l as [ | r l IHl ]; simpl; intros Hl.
    + exists SNON, 0; constructor.
    + destruct IHl as (st & sc & Hsc); try lia.
      destruct r as [ a b H | a H | ].
      * exists SNON; destruct st.
        - exists (a+b+sc); play from SNON.
        - admit.
        - admit.
        - admit.
      * exists SSPA. admit.
      * admit.
  Admitted.

  (** A backward fixpoint computation of the score for a list of frames 
         iscore [ r1 ⊳ r2 ⊳ ... ⊳ r10 ] a b 

         l = [ r1 ⊳ r2 ⊳ ... ⊳ r10 ]
         (a,b) = extra frame, 0 if no roll

         iscore l a b = score of l considering next to 2 rolls are [a; b]

            iscore [ r1 ⊳ r2 ⊳ ... ⊳ ri ⊳ (u,v) ] a b 
          = extra + u+v + iscore [ r1 ⊳ r2 ⊳ ... ⊳ ri ] u v

          where extra is 
             - 0 if (u,v) is open
             - a if (u,v) is a spare and 
             - a+b if (u,_) is a strike 
    *)

  Fixpoint iscore l (a b : nat) :=
    match l with
      | []           => 0 
      | l-:OPN u v _ =>       u+v + iscore l u  v
      | l-:SPA u _   => a   + 10  + iscore l u (10-u)
      | l-:STR       => a+b + 10  + iscore l 10 a
    end.

  Fact iscore_fix l r a b :
       iscore (l -: r) a b 
     = match r with
         | OPN u v _ => u+v+iscore l u v
         | SPA u _   => a+10+iscore l u (10-u)
         | STR       => a+b+10+iscore l 10 a
       end.
  Proof. reflexivity. Qed.

  Theorem frames_iscore l st n sc a b :
          l // st -[n]-> sc 
       -> iscore l a b 
        = match st with
            | SNON => 0
            | SSPA => a
            | S1ST => a+b
            | S2ST => 2*a+b
          end + sc. 
  Proof.
    intros H; revert H a b.
    induction 1 as [ | l st n sc r Hn H IH ]; intros a b; auto.
    rewrite iscore_fix.
    revert IH; case_eq st; intros Est IH; (case_eq r; [intros u v Huv | intros u Hu | ]; intros Hr).
    + simpl; rewrite IH; lia.
  Admitted.

  Corollary frames_iscore_0 l st n sc :
          l // st -[n]-> sc -> sc = iscore l 0 0.
  Proof.
  Admitted. 

  Definition istatus l := 
    match l with
      | _ -: STR -: STR => S2ST
      | _ -: STR        => S1ST
      | _ -: SPA _ _    => SSPA
      | _               => SNON
    end.

  Theorem frames_istatus l st n sc : l // st -[n]-> sc -> st = istatus l.
  Proof.
    induction 1 as [ | l st n sc r Hn H IH ]; auto.
  Admitted.

  Fact frames_length l st n sc : l // st -[n]-> sc -> n = length l.
  Proof.
  Admitted.

  Lemma frames_is_functional l st1 st2 n1 n2 sc1 sc2 :
          l // st1 -[n1]-> sc1 
       -> l // st2 -[n2]-> sc2 
       -> n1 = n2 
       /\ st1 = st2 
       /\ sc1 = sc2.
  Proof.
    intros H1 H2.
    rewrite frames_length with (1 := H1),
            frames_istatus with (1 := H1), 
            frames_iscore_0 with (1 := H1).
  Admitted.

  (* This theorem allows to prove a predicate l // st -[n]-> sc
     by computation: from l, compute (length l), (iscore l 0 0) and
     (istatus l) and verify the values match n, sc and st respectivelly *)
  Theorem check_score l n st sc : 
            n <= 10 
         -> n = length l 
         -> sc = iscore l 0 0 
         -> st = istatus l 
         -> l // st -[n]-> sc.
  Proof.
    intros H1 H2 H3 H4.
    destruct (frames_is_total l) as (st' & sc' & H5); try lia.
    rewrite <- H2 in H5.
    generalize (frames_iscore_0 _ _ _ _ H5) (frames_istatus _ _ _ _ H5).
    intros; subst; auto.
  Qed.

  Tactic Notation "check" "score" :=
    apply check_score; simpl; auto; lia.

  (** "score_reached st sc" denoted "I||- sc @ st >>" below
     means: one can compute a list l of 10 initial frames
     such that the score is sc after playing these 10 frames
     of l, and the status is then st *)

  Definition score_reached_in st sc := { l | l // st -[10]-> sc }.

  Notation "I||- x @ y" := (score_reached_in y x) (at level 70).

  (** We describe how to get scores from 0 to 270 in 
      the 10 initial frames *)

  Section from_0_to_29.

    (* First the scores from 0 up to 29 *)

    Variable (sc : nat) (Hsc : sc < 10).

    Tactic Notation "frames" constr(l) := exists l; check score. 

    (* How to get a score from 0 to 9 *)
    Fact score_0_9 : I||- sc @ SNON.
    Proof. frames ([OPN 0 sc Hsc] :-: ZERO↑9). Qed.

    (* How to get a score from 10 to 19 *)
    Fact score_10_19 : I||- sc+10 @ SNON.
    Proof. 
    Admitted.

    (* How to get a score from 20 to 29 *)
    Fact score_20_29 : I||- sc+20 @ SNON.
    Proof.
    Admitted.

  End from_0_to_29.

  (* How to build scores up to 29 *)
  Inductive sut29 : nat -> Type :=
    | sut29_1 : sut29 1
    | sut29_2 a b : a+b < 10 -> sut29 (3*a+2*b)
    | sut29_3 n : 20 <= n < 30 -> sut29 n.

  (* Any score sc below 29 is either 
       - 1 
       - or of the form 3a+b with a+b < 10
       - or in between 20 and 29 *)
  Lemma score_up_to_30 sc : sc < 30 -> sut29 sc.
  Proof.
    intros Hsc.
    destruct (eucl_dev 3) with (m := sc)
      as [ q r Hr E ]; try lia.
    destruct (le_lt_dec 20 sc) as [ H1 | H1 ].
    + constructor 3; lia.
    + destr r up to 3.
      * replace sc with (3*q+2*0) by lia.
        constructor; lia.
      * destruct q as [ | q ].
        - subst; simpl; constructor.
        - replace sc with (3*q+2*2) by lia.
          constructor; lia.
      * replace sc with (3*q+2*1) by lia.
        constructor; lia.
      * lia.
  Qed.

  Section from_30_to_270.

    (* Then the score from 30 up to 270 *)

    (* How to get score 30, 60, 90, ... 240 *)
    Fact score_30n n : 1 <= n <= 8 -> I||- 30*n @ SNON.
    Proof.
      intros Hn.
      exists (STR↑(1+n) :-: ZERO↑(9-n)).
      destr n up to 9; simpl; check score. 
    Qed.

    (* How to get score 31 *)
    Fact score_31 : I||- 31 @ SNON.
    Proof.
    Admitted.

    (* How to get score 61, 91, 121, ...., 241 *)
    Fact score_30n_p1 n : 2 <= n <= 8 -> I||- 30*n+1 @ SNON.
    Proof.
    Admitted.

    (* How to get score 32-57, 62-87, 122-147, ... 242-267 *)
    Fact score_30n_p2_27 n a b : 1 <= n <= 8 -> a+b < 10 -> I||- 30*n+3*a+2*b @ SNON.
    Proof.
    Admitted.

    (* How to get score 50-59, 80-89, ... 230-239 *)
    Fact score_30n_p20_29 n a : 1 <= n <= 7 -> a < 10 -> I||- 30*n+20+a @ SNON.
    Proof.
    Admitted.

    (* How to get score 260-269 *)
    Fact score_260_269 a : a < 10 -> I||- a+260 @ SSPA. 
    Proof.
    Admitted.

    (* How to get score 270 *)
    Fact score_270 : I||- 270 @ S2ST.
    Proof. exists (STR↑10); check score. Qed.

  End from_30_to_270.

  (* How to build scores up to 270 *)
  Inductive sut270 : nat -> Type :=
    | sut270_1 n a   : n < 3 -> a < 10         -> sut270 (10*n+a)
    | sut270_2 n     : 1 <= n <= 8             -> sut270 (30*n+1)
    | sut270_3 n a b : 1 <= n <= 8 -> a+b < 10 -> sut270 (30*n+3*a+2*b)
    | sut270_4 n a   : 1 <= n <= 7 -> a < 10   -> sut270 (30*n+20+a)
    | sut270_5 a     : a < 10                  -> sut270 (260+a)
    | sut270_6       :                            sut270 270. 

  (* Any score below 270 is either
       - of the form 10n+a       with n < 3 and a < 10
       - of the form 30n+1       with 1 <= n <= 8
       - of the form 30n+3a+2b   with 1 <= n <= 8 and a+b < 10
       - of the form 30n+20+a    with 1 <= n <= 7 and a < 10
       - of the form 260+a       with a < 10
       - 270 *)
  Lemma score_up_to_270 sc : sc <= 270 -> sut270 sc.
  Proof.
    intros H1.
    destruct (eucl_dev 30) with (m := sc)
      as [ q r Hr E ]; try lia.
    destruct (eq_nat_dec q 0) as [ H2 | H2 ].
    + subst; simpl.
      destruct (eucl_dev 10) with (m := r)
        as [ a n Hn E ]; try lia.
      replace r with (10*a+n) by lia.
      constructor; lia.
    + destruct (eq_nat_dec q 9) as [ H3 | H3 ].
      * replace sc with 270 by lia; constructor 6.
      * destruct score_up_to_30 with (1 := Hr)
          as [ | a b | k ].
        - replace sc with (30*q+1) by lia.
          constructor; lia.
        - replace sc with (30*q+3*a+2*b) by lia.
          constructor; lia.
        - destruct (eq_nat_dec q 8) as [ H4 | H4 ].
          ++ replace sc with (260+(k-20)) by lia.
             constructor; lia.
          ++ replace sc with (30*q+20+(k-20)) by lia.
             constructor; lia.
  Qed.

  (** For any score below 270, one can compute a status st
      such that <<sc|st>> is reached in the 10 initial frames *) 
  Theorem score_from_0_to_270 sc : sc <= 270 -> { st & I||- sc @ st }.
  Proof.
    intros H; apply score_up_to_270 in H.
    destruct H as [ n a Hn Ha | n Hn | n a b Hn Hab | n a Hn Ha | a Ha | ].
  Admitted.

  Section frames_inversion_lemmas.

    Let frames_0 l st n sc : 
             l // st -[n]-> sc 
          -> n = 0 
          -> sc = 0 
          /\ st = SNON.
    Proof. induction 1; auto; discriminate. Qed.

    Lemma frames_0_inv l st sc : 
             l // st -[0]-> sc 
          -> sc = 0 
          /\ st = SNON.
    Proof. Admitted.

    Let frames_1 l st n sc : 
             l // st -[n]-> sc 
          -> n = 1 
          -> sc <= 10 
          /\ st <> S2ST.
    Proof. 
      induction 1 as [ | l st [] sc r H1 H3 _ ]; try discriminate; intros _.
      apply frames_0 in H3 as (H3 & ->); auto.
      destruct r; simpl; split; try (easy || lia).
    Qed.

    Lemma frames_1_inv l st sc : 
             l // st -[1]-> sc 
          -> sc <= 10 
          /\ st <> S2ST.
    Proof. Admitted.

    Lemma frames_n_bound l st n sc : l // st -[n]-> sc -> n <= 10.
    Proof. induction 1; lia. Qed.

  End frames_inversion_lemmas.

  Section the_maximum_score.

    (* We show that the maximum score after 
        - 0 frame is 0
        - 1 frame is 10
        - n>=2 frames is 30(n-1) *) 

    Definition max_score n := 
      match n with
        | 0   => 0
        | 1   => 10
        | S n => 30*n
      end.

    Fact max_score_0 : max_score 0 = 0.   Proof. reflexivity. Qed.
    Fact max_score_1 : max_score 1 = 10.  Proof. reflexivity. Qed.

    Fact max_score_ge_2 n : 2 <= n -> max_score n = 30*(n-1).
    Proof. destruct n as [ | [] ]; simpl; lia. Qed.

    Fact max_score_S n : 2 <= n -> max_score (S n) = 30 + max_score n.
    Proof. intros; rewrite !max_score_ge_2; lia. Qed.

    Lemma frames_score_bounded l st n sc : 
            l // st -[n]-> sc -> sc <= max_score n.
    Proof.
      induction 1 as [ | l st n sc r H1 H3 IH3 ]; auto.
      destr n up to 2.
      Check frames_0_inv.
    Admitted.

    Theorem frames_score_max l st sc : l // st -[10]-> sc -> sc <= 270.
    Proof. apply frames_score_bounded. Qed.

  End the_maximum_score.

  (** Definition of a bowling play:
        - composed of 10 initial frames
        - plus an extra (possibly empty) frame 
        - depending on the status of the last two rolls (status)

      A valid bowling play (l,e) of score sc is denoted 

           l +: e --> sc
   *)

  Inductive bowling : list iframe -> eframe -> nat -> Prop :=
    | bowling_none l sc :       l // SNON -[10]-> sc -> l +: ER0       -->       sc
    | bowling_ext1 l sc a H :   l // SSPA -[10]-> sc -> l +: ER1 a H   -->     a+sc
    | bowling_ext2 l sc a b H : l // S1ST -[10]-> sc -> l +: ER2 a b H -->   a+b+sc
    | bowling_ext3 l sc a b H : l // S2ST -[10]-> sc -> l +: ER2 a b H --> 2*a+b+sc
   where "l +: e --> s" := (bowling l e s).

  (* The list of pins down on each roll of a bowling play *)
  Definition bowling2pins lr e := flat_map iframe2pins lr :-: eframe2pins e.
  
  (* For every initial 10 frames l scoring sc, one can compute an extra frame
     e such that (l,e) constitute a bowling play of score sc 
     Notice that only scores below 270 can be reached that way *)
  Lemma bowling_extends_rounds l st sc : 
       l // st -[10]-> sc -> { e | l +: e --> sc }.
  Proof.
    destruct st.
    + exists ER0; constructor; auto.
  Admitted.

  (** score computes the score correcly *)
  Definition score l e :=
    match e with 
      | ER0       => iscore l 0 0
      | ER1 a _   => iscore l a 0
      | ER2 a b _ => iscore l a b
    end.

  Theorem score_correct l e sc : l +: e --> sc -> sc = score l e.
  Proof.
    induction 1 as [ ? ? H | ? ? ? ? H | ? ? ? ? ? H | ? ? ? ? ? H ].
  Admitted. 

  Lemma bowling_is_functional l e sc1 sc2 : 
          l +: e --> sc1 
       -> l +: e --> sc2 
       -> sc1 = sc2.
  Proof.
    intros H1 H2.
    apply score_correct in H1.
    apply score_correct in H2.
    subst; auto.
  Qed.

  (** "bowling_score sc" denoted "B||- sc" below 
      means one can compute 
        - a list l of initial frames 
        - and an extra frame e 
      which combined give the score sc *) 
  Definition bowling_score sc := 
    { lr : list iframe & { e : eframe | lr +: e --> sc } }.

  Notation "B||- x" := (bowling_score x).

  (* Score is bounded by 300 in the Bowling game *)
  Theorem bowling_score_bounded sc : B||- sc -> sc <= 300.
  Proof.
    intros (l & e & H); revert H.
    induction 1 as [ ? ? H | ? ? ? ? H | ? ? ? ? ? H | ? ? ? ? ? H ].
    + apply frames_score_max in H. lia.
  Admitted.

  (** Let us show the converse: any score up to 300 is possible in Bowling *)

  Section from_0_to_270.

    Lemma initial_is_bowling_score st sc : I||- sc @ st -> B||- sc.
    Proof. 
      intros (lr & H); exists lr.
      apply bowling_extends_rounds with st; auto. 
    Qed.

    Corollary bowling_from_0_to_270 sc : sc <= 270 -> B||- sc.
    Proof.
    Admitted.

  End from_0_to_270.

  Section from_270_to_300.

    (* For any value n up to 30, there is an extra frame (ER2 a b _) such that n = 2a+b *)
    Lemma from_0_to_30 n : n <= 30 -> { e | match e with ER2 a b _ => n = 2*a+b | _ => False end }.
    Proof.
      intros H1.
      destruct (le_lt_dec 20 n) as [ H2 | H2 ].
      + eexists (ER2 10 (n-20) _); try lia.
      + destruct (eucl_dev 2) with (m := n)
          as [ q r Hr E ]; try lia.
        eexists (ER2 q r _); lia.
      Unshelve.
      all: lia.
    Qed.

    Lemma bowling_from_270_to_300 sc : 270 <= sc <= 300 -> B||- sc.
    Proof.
      intros Hsc.
      destruct (from_0_to_30 (sc-270)) as (e & He); try lia.
      exists (STR↑10), e.
    Admitted.

  End from_270_to_300.

  (* Any score up to 300 can be reached by a bowling play *)
  Theorem any_is_bowling_score sc : sc <= 300 -> B||- sc.
  Proof.
    intros Hs.
    destruct (le_lt_dec sc 270).
  Admitted.

  (** Remaing extra open questions, more difficult *)

  (* Show that scores from 1 to 280 can be realized with at least
     two different bowling plays *)
  Theorem more_than_one sc : 
         1 <= sc <= 280 
      -> exists lr1 e1 lr2 e2, 
             lr1 +: e1 --> sc
          /\ lr2 +: e2 --> sc
          /\ bowling2pins lr1 e1 <> bowling2pins lr2 e2.
  Admitted.

  (* Show that for scores above 290, there is at most one
     bowling play realizing the score *)
  Theorem exactly_one sc lr1 e1 lr2 e2 : 
          290 <= sc 
       -> lr1 +: e1 --> sc
       -> lr2 +: e2 --> sc
       -> bowling2pins lr1 e1 = bowling2pins lr2 e2.
  Admitted.

  (** More complicated questions for those interested:
     - show that 287 corresponds to two bowling plays
     - characterize precisely the scores which correspond
       to exactly one bowling play, which are those in the
       set {0} U [288,300], ie either 0 or above 288.
     - same question for those with two bowling plays
   *) 

End Bowling.
