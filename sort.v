(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia.

Set Implicit Arguments.

(** Human friendly notation for lists:

    - x ∈ l : x is a member of l
    - l ⊆ m : l is included in m
    - ⌊l⌋ : the length of l

    The definitions are to be found in the List
    module of the Standart Library

 *)

Infix "∈" := In (at level 70, no associativity).
Infix "⊆" := incl (at level 70, no associativity).
Notation "⌊ l ⌋" := (length l) (at level 1, format "⌊ l ⌋").

Hint Resolve incl_refl incl_appl incl_appr : core.

(** Strict sorted lists of nat(ural numbers) 

   1) slu (for strictly lower-upper) denoted infix l ⪻ r:

     every member of l is strictly below (<) every member of r 

   2) m is strictly sorted denoted prefix ↗ m: 
  
     for any split m = l++r we have l ⪻ r

*)

Definition strict_lower_upper l r := forall x y, x ∈ l -> y ∈ r -> x < y.

Infix "⪻" := strict_lower_upper (at level 70, no associativity).

(** A possible definition of strictly increasing list 
    Exercise: provide alternate characterizations for strictly 
              increasing lists and show equivalence *)

Definition si_list m := forall l r, m = l++r -> l ⪻ r.

Notation "↗ m" := (si_list m) (at level 70).

Section strict_lists.

  Implicit Type l m : list nat.

  (* ⪻  is decreasing in both arguments 
     Hint: Check for the definitions of In/∈ and incl/⊆ in the
           List module. 
   *)

  Fact slu_dec l l' m m' : l ⊆ l' -> m ⊆ m' -> l' ⪻ m' -> l ⪻ m.
  Proof.
  Admitted.

  Fact slu_nil_l l : nil ⪻ l.
  Proof.
  Admitted.

  Fact slu_nil_r l : l ⪻ nil.
  Proof.
  Admitted.

  Hint Immediate slu_nil_l slu_nil_r : core.

  (* Equivalences for ⪻ wrt list operators ::, ++ *)

  (* case of singleton lists _::nil *)

  Fact slu_sg_l x l : x::nil ⪻ l <-> forall y, y ∈ l -> x < y.
  Proof.
  Admitted.

  Fact slu_sg_r x l : l ⪻ x::nil <-> forall y, y ∈ l -> y < x.
  Proof.
  Admitted.
 
  (* What about ⪻  and ++
     Hint: in_or_app, in_app_or, in_app_iff *)

  Fact slu_app_l l1 l2 r : l1++l2 ⪻ r <-> l1 ⪻ r /\ l2 ⪻ r.
  Proof.
  Admitted.
    
  Fact slu_app_r l r1 r2 : l ⪻ r1++r2 <-> l ⪻ r1 /\ l ⪻ r2.
  Proof.
  Admitted.

  (* Strictly increasing lists and list operators *)

  Fact si_list_nil : ↗ nil.
  Proof.
  Admitted.

  Fact si_list_one x : ↗ x::nil.
  Proof.
  Admitted.
  
  Hint Resolve si_list_nil si_list_one : core.

  (* Hint: app_ass, in_or_app, in_app_iff and the above app_split *)

  Fact si_list_app l r : ↗ l++r <-> ↗ l /\ ↗ r /\ l ⪻ r.
  Proof.
  Admitted. 

  (* Hint: x::l = (x::nil)++l *)

  Fact si_list_cons x l : ↗ x::l <-> x::nil ⪻ l /\ ↗ l.
  Proof.
  Admitted.

End strict_lists.

Hint Resolve slu_nil_l slu_nil_r 
             si_list_nil si_list_one : core.

Section si_list_alt.

  Reserved Notation "'sa' l" (at level 70).

  Inductive si_list_alt : list nat -> Prop :=
    | in_sa_0 : sa nil
    | in_sa_1 : forall x l, (forall y, y ∈ l -> x < y) -> sa l -> sa x::l
  where "'sa' l" := (si_list_alt l).

  Fact si_sa l : ↗ l -> sa l.
  Admitted.

  Fact sa_si l : sa l -> ↗ l.
  Admitted.

  Theorem si_sa_equiv l : ↗l <-> sa l.
  Admitted.

End si_list_alt.

Check le_lt_dec.

Lemma bounded_decidable x l : { y | y ∈ l /\ ~ x < y } + { forall y, y ∈ l -> x < y }.
Admitted.

Lemma slu_decidable l r : { l⪻r } + { ~ l⪻r }.
Admitted.

Lemma si_decidable l : { ↗l } + { ~ ↗l }.
Admitted.