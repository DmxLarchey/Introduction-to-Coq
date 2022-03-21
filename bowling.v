(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
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
Local Notation "[ x ⊳ .. ⊳ y ⊳ z ]" := (( .. ([] -: x) .. -: y) -: z ) : list_scope.

(** The repeater: x↑n = [ x ⊳ x ⊳ ... ⊳ x ] where x is repeated n times *)

Local Reserved Notation "x ↑ n" (at level 50, left associativity, format "x ↑ n"). 

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

  (** Modelling the Bowling plays with rounds, balls, pins down etc *)

  (* The (first ten) initial bowling rounds 

     REG/regular: 2 balls, no strike, no spare
     SPA/spare:   2 balls, first ball < 10 pins down,
                           second ball completes to 10 pins
     STR/strike:  1 ball, 10 pins down

   *)

  Inductive iround : Type :=
    | regular a b : a + b < 10 -> iround (* a pins on 1st ball, b pins on second ball *)
    | spare a     : a < 10     -> iround (* a pins on 1st ball, 10-a on second ball *)
    | strike      :               iround (* 10 pins on first ball, no second ball *)
    .

  Notation REG := regular.
  Notation SPA := spare.
  Notation STR := strike.

  (* round with zero pins down *)
  Definition ZERO := (REG 0 0 lt_0_10).  

  (* The list of pins down for each ball of an initial round *)

  Definition iround2pins r :=
    match r with
      | REG a b _ => [a;b]
      | SPA a _   => [a;10-a]
      | STR       => [10]
    end.

  Arguments iround2pins r /.

 (* Value (number of pins down) of the first ball of a round *)

  Definition ifirst r :=
    match r with
      | REG a _ _ => a
      | SPA a _   => a
      | STR       => 10
    end.

  Arguments ifirst r /.

  (* ifirst matches the first pin of iround2pins *)

  Fact ifirst_eq_first_pin r : 
          match iround2pins r with 
            | []   => False
            | x::_ => ifirst r = x
          end.
  Proof. destruct r; reflexivity. Qed.

  (* Total of pins down in the initial round *)

  Definition itotal r :=
    match r with
      | REG a b _ => a + b
      | SPA _ _   => 10
      | STR       => 10
    end.

  Arguments itotal r /.

  (* itotal matches the sum of pins in iround2pins *)
  
  Fact itotal_eq_sum_pins r : itotal r = lsum (iround2pins r).
  Proof. destruct r; simpl itotal; unfold iround2pins, lsum; lia. Qed.

  (* The extra bowling round, one or two balls to complete 
     pending strikes or spares 

     EX0: zero extra ball
     EX1: one extra ball to complete a spare
     EX2: two extra balls to complete one (or two) strike(s)

     Notice than if the first ball of EX2 is 10 pins down (ie strike),
     then a new set of 10 pins is available for the second ball
  *)

  Inductive eround : Type :=
    | extra0 :                eround
    | extra1 a : a <= 10   -> eround
    | extra2 a b : (a < 10 /\ a+b <= 10    (* no strike on first extra ball *) 
                 \/ a = 10 /\ b <= 10)     (* strike on the first ball, 10 new pins *)
                           -> eround.

  Notation ER0 := extra0.
  Notation ER1 := extra1.
  Notation ER2 := extra2.

  (* The list of pins down for each ball of an extra round *) 

  Definition eround2pins e :=
    match e with
      | ER0        => []
      | ER1 a _    => [a]
      | ER2 a b _  => [a;b]
    end.

  (* Status of the previous or two previous rounds, if any *)

  Inductive status :=
    | status_none     (* no strike nor spare on the previous round *)
    | status_spare    (* last round was a spare *)
    | status_strike   (* last round was a strike, but the one before, was not *)
    | status_2strikes (* last two rounds were strikes *)
    .

  Notation SNON := status_none.
  Notation SSPA := status_spare.
  Notation S1ST := status_strike.
  Notation S2ST := status_2strikes.

  (* New status from previous status after an initial round *)

  Definition next_status (st : status) (r : iround) :=
    match st, r with
      | S1ST , STR       => S2ST  (* strike after a strike *)
      | S2ST , STR       => S2ST  (* strike after two strikes *)
      | _    , STR       => S1ST  (* strike after not a strike *)
      | _    , SPA _ _   => SSPA  (* spare after anything *)
      | _    , REG _ _ _ => SNON  (* regular round after anything *)
    end.

  Arguments next_status st r /.

 (* Pins down to add depending on the status of the two previous balls *)

  Definition status_count st r :=
    match st with
      | SNON => 0                  (* nothing to add here *)
      | SSPA => ifirst r           (* count the first ball value on the previous round *)
      | S1ST => itotal r           (* count the two balls value on the previous round *)
      | S2ST => ifirst r+itotal r  (* count the first ball on the two previous rounds 
                                      plus the second on the previous round *) 
    end.

  Arguments status_count st r /.

  Notation NXT := next_status. 
  Notation STC := status_count.
  Notation TOT := itotal.

  Fact next_status_REG st a b H : NXT st (REG a b H) = SNON.
  Proof.
  Admitted.

  Fact next_status_ZERO st : NXT st ZERO = SNON.
  Proof.
  Admitted.

  Fact status_count_ZERO st : status_count st ZERO = 0.
  Proof.
  Admitted.

  (* The initial rounds of a bowling play predicate:

      - lr: list of rounds
      - st: status according to (previous) rounds
      - nr: number of rounds
      - sc : score so far

      lr // st -[nr]-> sc denotes

      "given the nr many initial rounds stored in the
       list lr, with current status sc, the score is sc"

      two rules:

            ----------------------- empty play
              [] // SNON -[0]-> 0

                     lr // st -[nr]-> sc
           --------------------------------------------------- (nr<10) next round is r
            lr-:r // NXT st r -[1+nr]-> STC st r + TOT r + sc

    *)

  Inductive rounds : list iround -> status -> nat -> nat -> Prop :=
    | rounds_start :         

          (*---------------------*)
             [] // SNON -[0]-> 0

    | rounds_next lr st nr sc r : 

             nr < 10     ->      lr // st -[nr]-> sc
      (*---------------------------------------------------*)
      -> lr-:r // NXT st r -[1+nr]-> STC st r + TOT r + sc

  where "lr // st -[ nr ]-> sc" := (rounds lr st nr sc).

  Tactic Notation "play" "from" constr(st) :=
    match goal with
      | |- _-:?r // _ -[ _ ]-> _ => apply (rounds_next _ st _ _ r)
    end; simpl; auto; try lia.

  (* Any sequence of rounds of length <= 10 is valid:
       if the length of lr is below 10 then one can compute
       a status st, and a score sc such that
            lr // st -[length lr]-> sc *)

  Theorem rounds_is_total lr : 
             length lr <= 10 
          -> { st : _ & { sc | lr // st -[length lr]-> sc } }.
  Proof.
    induction lr as [ | r lr IHlr ]; simpl; intros Hlr.
    + exists SNON, 0; constructor.
    + destruct IHlr as (st & sc & Hsc); try lia.
      destruct r as [ a b H | a H | ].
      * exists SNON; destruct st.
        - exists (a+b+sc); play from SNON.
        - admit.
        - admit.
        - admit.
      * exists SSPA. admit.
      * admit.
  Admitted.

  (** A backward fixpoint computation of the score for a list of rounds 
         r_score [ r1 ⊳ r2 ⊳ ... ⊳ r10 ] a b 

         lr = [ r1 ⊳ r2 ⊳ ... ⊳ r10 ]
         (a,b) = extra round, 0 if no ball

         r_score lr a b = score of lr considering next to 2 balls are [a; b]

            r_score [ r1 ⊳ r2 ⊳ ... ⊳ ri ⊳ (u,v) ] a b 
          = extra + u+v + r_score [ r1 ⊳ r2 ⊳ ... ⊳ ri ] u v

          where extra is 
             - 0 if (u,v) is regular
             - a if (u,v) is a spare and 
             - a+b if (u,v) is a strike 
    *)

  Fixpoint iscore lr (a b : nat) :=
    match lr with
      | []           => 0 
      | lr-:REG u v _ =>       u+v + iscore lr u  v
      | lr-:SPA u _   => a   + 10  + iscore lr u (10-u)
      | lr-:STR       => a+b + 10  + iscore lr 10 a
    end.

  Fact iscore_fix lr r a b :
       iscore (lr -: r) a b 
     = match r with
         | REG u v _ => u+v+iscore lr u v
         | SPA u _   => a+10+iscore lr u (10-u)
         | STR       => a+b+10+iscore lr 10 a
       end.
  Proof. reflexivity. Qed.

  Theorem rounds_iscore lr st nr sc a b :
          lr // st -[nr]-> sc 
       -> iscore lr a b 
        = match st with
            | SNON => 0
            | SSPA => a
            | S1ST => a+b
            | S2ST => 2*a+b
          end + sc. 
  Proof.
    intros H; revert H a b.
    induction 1 as [ | lr st nr sc r Hn H IH ]; intros a b; auto.
    rewrite iscore_fix.
    revert IH; case_eq st; intros Est IH; (case_eq r; [intros u v Huv | intros u Hu | ]; intros Hr).
  Admitted.

  Corollary rounds_iscore_0 lr st nr sc :
          lr // st -[nr]-> sc -> sc = iscore lr 0 0.
  Proof.
  Admitted. 

  Definition istatus lr := 
    match lr with
      | _ -: STR -: STR => S2ST
      | _ -: STR        => S1ST
      | _ -: SPA _ _    => SSPA
      | _               => SNON
    end.

  Theorem rounds_istatus lr st nr sc : lr // st -[nr]-> sc -> st = istatus lr.
  Proof.
    induction 1 as [ | lr st nr sc r Hn H IH ]; auto.
  Admitted.

  Fact rounds_length lr st nr sc : lr // st -[nr]-> sc -> nr = length lr.
  Proof.
  Admitted.

  Lemma rounds_is_functional lr st1 st2 n1 n2 sc1 sc2 :
          lr // st1 -[n1]-> sc1 
       -> lr // st2 -[n2]-> sc2 
       -> n1 = n2 
       /\ st1 = st2 
       /\ sc1 = sc2.
  Proof.
    intros H1 H2.
    rewrite rounds_length with (1 := H1),
            rounds_istatus with (1 := H1), 
            rounds_iscore_0 with (1 := H1).
  Admitted.

  (* This theorem allow to verify a proposition lr // st -[nr]-> sc
     by computation: from lr, compute ⌊lr⌋, (iscore lr 0 0) and
     (istatus lr) and verify the values match nr, sc and st respectivelly *)
  Theorem check_score lr nr st sc : 
            nr <= 10 
         -> nr = length lr 
         -> sc = iscore lr 0 0 
         -> st = istatus lr 
         -> lr // st -[nr]-> sc.
  Proof.
    intros H1 H2 H3 H4.
    destruct (rounds_is_total lr) as (st' & sc' & H5); try lia.
    rewrite <- H2 in H5.
    generalize (rounds_iscore_0 _ _ _ _ H5) (rounds_istatus _ _ _ _ H5).
    intros; subst; auto.
  Qed.

  Tactic Notation "check" "score" :=
    apply check_score; simpl; auto; lia.

  (** "score_reached st sc" denoted "I||- sc @ st >>" below
     means: one can compute a list lr of initial rounds
     such that the score is sc after playing the 10 rounds
     of lr, and the status is then st *)

  Definition score_reached_in st sc := { lr | lr // st -[10]-> sc }.

  Notation "I||- x @ y" := (score_reached_in y x) (at level 70).

  (** We describe how to get scores from 0 to 270 in 
      the 10 initial rounds *)

  Section from_0_to_29.

    (* First the scores from 0 up to 29 *)

    Variable (sc : nat) (Hsc : sc < 10).

    Tactic Notation "initial" "rounds" constr(l) := exists l; check score. 

    (* How to get a score from 0 to 9 *)
    Fact score_0_9 : I||- sc @ SNON.
    Proof. initial rounds ([REG 0 sc Hsc] :-: ZERO↑9). Qed.

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
      such that <<sc|st>> is reached in the 10 initial rounds *) 
  Theorem score_from_0_to_270 sc : sc <= 270 -> { st & I||- sc @ st }.
  Proof.
    intros H; apply score_up_to_270 in H.
    destruct H as [ n a Hn Ha | n Hn | n a b Hn Hab | n a Hn Ha | a Ha | ].
  Admitted.

  Section rounds_inversion_lemmas.

    Let rounds_0 lr st nr sc : 
             lr // st -[nr]-> sc 
          -> nr = 0 
          -> sc = 0 
          /\ st = SNON.
    Proof. induction 1; auto; discriminate. Qed.

    Fact rounds_0_inv lr st sc : 
             lr // st -[0]-> sc 
          -> sc = 0 
          /\ st = SNON.
    Proof. Admitted.

    Let rounds_1 lr st nr sc : 
             lr // st -[nr]-> sc 
          -> nr = 1 
          -> sc <= 10 
          /\ st <> S2ST.
    Proof. 
      induction 1 as [ | lr st [] sc r H1 H3 _ ]; try discriminate; intros _.
      apply rounds_0 in H3 as (H3 & ->); auto.
      destruct r; simpl; split; try (easy || lia).
    Qed.

    Fact rounds_1_inv lr st sc : 
             lr // st -[1]-> sc 
          -> sc <= 10 
          /\ st <> S2ST.
    Proof. Admitted.

    Fact rounds_n_bound lr st nr sc : lr // st -[nr]-> sc -> nr <= 10.
    Proof. induction 1; lia. Qed.

  End rounds_inversion_lemmas.

  Section the_maximum_score.

    (* We show that the maximum score after 
        - 0 round is 0
        - 1 round is 10
        - n>=2 rounds is 30(n-1) *) 

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

    Lemma rounds_score_bounded lr st nr sc : 
            lr // st -[nr]-> sc -> sc <= max_score nr.
    Proof.
      induction 1 as [ | lr st nr sc r H1 H3 IH3 ]; auto.
      destr nr up to 2.
    Admitted.

    Theorem irounds_score_max lr st sc : lr // st -[10]-> sc -> sc <= 270.
    Proof. apply rounds_score_bounded. Qed.

  End the_maximum_score.

  (** Definition of a bowling play:
        - composed of 10 initial rounds
        - plus an extra (possibly empty) round 
        - depending on the status of the last two ball (status)

      A valid bowling play (lr,e) of score sc is denoted 

           lr +: e --> sc
   *)

  Inductive bowling : list iround -> eround -> nat -> Prop :=
    | bowling_none lr sc :       lr // SNON -[10]-> sc -> lr +: ER0       -->       sc
    | bowling_ext1 lr sc a H :   lr // SSPA -[10]-> sc -> lr +: ER1 a H   -->     a+sc
    | bowling_ext2 lr sc a b H : lr // S1ST -[10]-> sc -> lr +: ER2 a b H -->   a+b+sc
    | bowling_ext3 lr sc a b H : lr // S2ST -[10]-> sc -> lr +: ER2 a b H --> 2*a+b+sc
   where "l +: e --> s" := (bowling l e s).

  (* The list of pins down on each ball of a bowling play *)
  Definition bowling2pins lr e := flat_map iround2pins lr :-: eround2pins e.
  
  (* For every initial 10 rounds scoring sc, one can compute an extra round
     e such that (lr,e) compose a bowling play of score sc 
     Notice that only scores below 270 can be reached that way *)
  Lemma bowling_extends_rounds lr st sc : 
       lr // st -[10]-> sc -> { e | lr +: e --> sc }.
  Proof.
    destruct st.
    + exists ER0; constructor; auto.
  Admitted.

  (** score computes the score correcly *)

  Definition score lr e :=
    match e with 
      | ER0       => iscore lr 0 0
      | ER1 a _   => iscore lr a 0
      | ER2 a b _ => iscore lr a b
    end.

  Theorem score_correct lr e sc : lr +: e --> sc -> sc = score lr e.
  Proof.
    induction 1 as [ ? ? H | ? ? ? ? H | ? ? ? ? ? H | ? ? ? ? ? H ].
  Admitted. 

  Lemma bowling_is_functional lr e sc1 sc2 : 
          lr +: e --> sc1 
       -> lr +: e --> sc2 
       -> sc1 = sc2.
  Proof.
    intros H1 H2.
    apply score_correct in H1.
    apply score_correct in H2.
    subst; auto.
  Qed.

  (** "bowling_score sc" denoted "B||- sc" below 
      means one can compute 
        - a list lr of initial rounds 
        - and an extra round e 
      which combined give the score sc *) 
  Definition bowling_score sc := { lr : list iround & { e : eround | lr +: e --> sc } }.

  Notation "B||- x" := (bowling_score x).

  (** Score is bounded by 300 in the Bowling game *)

  Theorem is_bowling_score_bounded sc : B||- sc -> sc <= 300.
  Proof.
    intros (l & e & H); revert H.
    induction 1 as [ ? ? H | ? ? ? ? H | ? ? ? ? ? H | ? ? ? ? ? H ].
    + apply irounds_score_max in H. lia.
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

    (* For any value n up to 30, there is an extra ER2 a b round such that n = 2a+b *)
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

  (* Any score up to 300 can be reached by a play *)

  Theorem any_is_bowling_score sc : sc <= 300 -> B||- sc.
  Proof.
    intros Hs.
    destruct (le_lt_dec sc 270).
  Admitted.

  (** Remaing open questions *)

  (* Show that scores from 1 to 280 can be realized with at least
     two different bowling plays *)
  Theorem more_than_one sc : 
         1 <= sc <= 280 
      -> exists lr1 e1 lr2 e2, 
             lr1 +: e1 --> sc
          /\ lr2 +: e2 --> sc
          /\ bowling2pins lr1 e1 <> bowling2pins lr2 e2.
  Admitted.

  (* Show that for scores above 289, there is at most one
     bowling play realizing the score *)
  Theorem exactly_one sc lr1 e1 lr2 e2 : 
          289 <= sc 
       -> lr1 +: e1 --> sc
       -> lr2 +: e2 --> sc
       -> bowling2pins lr1 e1 = bowling2pins lr2 e2.
  Admitted.

  (** More complicated questions:
     - characterize precisely the scores which correspond
       to exactly one bowling play.
     - same question for two bowling plays
   *) 

End Bowling.
