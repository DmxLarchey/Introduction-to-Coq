(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Setoid Arith.

Set Implicit Arguments.

Section list.

  Variable X : Type.

  Implicit Type l : list X.

  Infix "::" := cons.
  Infix "++" := app.
  Notation "⌊ l ⌋" := (length l) (at level 1, format "⌊ l ⌋").

  Print list.
  
  Print nil.
  Check nil.
  Check @nil.
  
  Print app.

  Arguments app {A}.
  Check app.
  
  Arguments app [A].
  Check app.

  Fact app_nil_head l : nil++l = l.
  Proof. reflexivity. Qed.

  Fact app_cons_head x l m : (x::l) ++ m = x::(l++m).
  Proof. reflexivity. Qed. 

  Fact app_assoc l m p : (l++m)++p = l++m++p.
  Proof.
  Admitted.

  Fact app_nil_end l : l++nil = l.
  Proof.
  Admitted.

  Fact app_length l m : ⌊l++m⌋ = ⌊l⌋+⌊m⌋.
  Proof.
  Admitted.

  Section map.

    Variable (Y : Type) (f : X -> Y).

    Fixpoint map l :=
      match l with 
        | nil  => nil
        | x::l => f x::map l
      end.

    Fact map_length l : ⌊map l⌋ = ⌊l⌋.
    Proof.
    Admitted.

    Fact map_app l m : map (l++m) = map l ++ map m.
    Proof.
    Admitted.

  End map.

  Fixpoint rev l :=
    match l with
      | nil  => nil
      | x::l => rev l ++ x :: nil
    end.

  Fixpoint rev_app a l :=
    match l with 
      | nil  => a
      | x::l => rev_app (x::a) l
    end.

  Fact rev_rev_app_eq a l : rev_app a l = rev l ++ a.
  Proof.
  Admitted.

  Reserved Notation "x ∈ l" (at level 70, no associativity).

  Fixpoint In x l := 
    match l with
      | nil  => False
      | y::l => x = y \/ x ∈ l
    end
  where "x ∈ l" := (In x l).

  Fact in_app_iff x l m : x ∈ l++m <-> x ∈ l \/ x ∈ m.
  Proof.
  Admitted.
    
  Definition incl l m := forall x, x ∈ l -> x ∈ m.

  Infix "⊆" := incl (at level 70, no associativity).

  Fact incl_refl l : l ⊆ l.
  Proof.
  Admitted.

  Fact incl_trans l m p : l ⊆ m -> m ⊆ p -> l ⊆ p. 
  Proof.
  Admitted.

  Hint Resolve incl_refl : core.

  Fact incl_app_l l m : l ⊆ l++m.
  Proof.
  Admitted.

  Fact incl_app_r l m : m ⊆ l++m.
  Proof.
  Admitted.

  Fact sg_incl x m : x::nil ⊆ m <-> x ∈ m.
  Proof.
  Admitted.

  Hint Resolve incl_app_l incl_app_r : core.

  Fact app_incl_left l r m : l++r ⊆ m <-> l ⊆ m /\ r ⊆ m.
  Proof.
  Admitted.

  Fact cons_incl_left x l m : x::l ⊆ m <-> x ∈ m /\ l ⊆ m.
  Proof.
  Admitted.

  Fact incl_cons_r x l : l ⊆ x::l.
  Proof.
  Admitted.

  Fact incl_nil_l l : nil ⊆ l.
  Proof.
  Admitted.

  Hint Resolve incl_nil_l incl_cons_r : core.

  Fact incl_nil_r l : l ⊆ nil <-> l = nil.
  Proof.
  Admitted.

  Fact incl_app_comm l m : l++m ⊆ m++l.
  Proof.
  Admitted.

  (* Alternative inductive definitions of In/∈ and incl/⊆ *)

  Reserved Notation "x ∈' y" (at level 70, no associativity).

  Inductive ind_In : X -> list X -> Prop :=
    | in_ind_In0 : forall x l, x ∈' x::l
    | in_ind_In1 : forall x y l, x ∈' l -> x ∈' y::l
  where "x ∈' l" := (ind_In x l).

  Fact ind_In_equiv x l : x ∈ l <-> x ∈' l.
  Proof.
  Admitted.

  Reserved Notation "x ⊆' y" (at level 70, no associativity).

  Inductive ind_incl : list X -> list X -> Prop :=
    | in_ii0 : forall m, nil ⊆' m
    | in_ii1 : forall x l m, x ∈' m -> l ⊆' m -> x::l ⊆' m 
  where "l ⊆' m" := (ind_incl l m).

  Fact ind_incl_equiv l m : l ⊆ m <-> l ⊆' m.
  Proof.
  Admitted.

End list.
  
 