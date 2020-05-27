(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Setoid.

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

  Print app.

  Fact app_nil_head l : nil++l = l.
  Proof. reflexivity. Qed.

  Fact app_cons_head x l m : (x::l) ++ m = x::(l++m).
  Proof. reflexivity. Qed. 

  Fact app_assoc l m p : (l++m)++p = l++m++p.
  Proof.
   (* induction l as [ | x l IHl ].
    + simpl. trivial.
    + simpl.
      f_equal.
      trivial. *)
    induction l; simpl; f_equal; trivial.
  Qed.

  Fact app_nil_end l : l++nil = l.
  Proof.
  (*  induction l; simpl; f_equal; trivial. *)
    induction l as [ | x l IHl ].
    + simpl. trivial.
    + simpl.
      f_equal.
      trivial.
  Qed.

  Fact app_length l m : ⌊l++m⌋ = ⌊l⌋+⌊m⌋.
  Proof.
  (*  induction l; simpl; f_equal; trivial. *)
    induction l as [ | x l IHl ].
    + simpl. 
      trivial.
    + simpl.
      f_equal.
      trivial.
  Qed.

  Section map.

    Variable (Y : Type) (f : X -> Y).

    Fixpoint map l :=
      match l with 
        | nil  => nil
        | x::l => f x::map l
      end.

    Fact map_length l : ⌊map l⌋ = ⌊l⌋.
    Proof.
      induction l; simpl; f_equal; trivial.
    Qed.

    Fact map_app l m : map (l++m) = map l ++ map m.
    Proof.
      induction l; simpl; f_equal; trivial.
    Qed.

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
    revert a; induction l as [ | x l IHl ]; intros a; simpl.
    + trivial.
    + rewrite app_assoc; simpl.
      apply IHl.
  Qed.

  Reserved Notation "x ∈ l" (at level 70, no associativity).

  Fixpoint In x l := 
    match l with
      | nil  => False
      | y::l => x = y \/ x ∈ l
    end
  where "x ∈ l" := (In x l).

  Fact in_app_iff x l m : x ∈ l++m <-> x ∈ l \/ x ∈ m.
  Proof.
    (* induction l as [ | y l IHl ]; simpl.
    + tauto.
    + rewrite IHl.
      tauto. *)
    induction l as [ | ? ? IHl ]; simpl; [ | rewrite IHl ]; tauto.
  Qed.
    
  Definition incl l m := forall x, x ∈ l -> x ∈ m.

  Infix "⊆" := incl (at level 70, no associativity).

  Fact incl_refl l : l ⊆ l.
  Proof.
    unfold incl; auto.
  Qed.

  Fact incl_trans l m p : l ⊆ m -> m ⊆ p -> l ⊆ p. 
  Proof.
    unfold incl.
  (*  intros H1 H2 x H3.
    apply H2, H1, H3. *)
    firstorder.
  Qed.

  Hint Resolve incl_refl : core.

  Fact incl_app_l l m : l ⊆ l++m.
  Proof.
(*    red.
    intros x Hx.
    apply in_app_iff.
    left; trivial. *)
    intro; rewrite in_app_iff; tauto.
  Qed.

  Fact incl_app_r l m : m ⊆ l++m.
  Proof.
    intro; rewrite in_app_iff; tauto.
  Qed.

  Fact sg_incl x m : x::nil ⊆ m <-> x ∈ m.
  Proof.
    unfold incl; split.
    + intros H.
      apply H.
      simpl.
      auto.
    + (* intros H y; simpl.
      intros D.
      destruct D as [ E | A ].
      * rewrite E; trivial.
      * destruct A. *)
      intros ? ? [ -> | [] ]; trivial.
  Qed.

  Hint Resolve incl_app_l incl_app_r : core.

  Fact app_incl_left l r m : l++r ⊆ m <-> l ⊆ m /\ r ⊆ m.
  Proof.
    split.
    + intros H.
      split; apply incl_trans with (2 := H); trivial.
    + intros [ H1 H2 ] x.
      rewrite in_app_iff.
      intros [ H | H ]; revert H.
      * auto.
      * auto.
  Qed.

  Fact cons_incl_left x l m : x::l ⊆ m <-> x ∈ m /\ l ⊆ m.
  Proof.
    rewrite <- sg_incl, <- app_incl_left.
    simpl; tauto.
  Qed.

  Fact incl_cons_r x l : l ⊆ x::l.
  Proof.
    unfold incl; simpl; auto.
  Qed.

  Fact incl_nil_l l : nil ⊆ l.
  Proof.
    (* unfold incl. 
    simpl. *)
    intros _ [].
  Qed.

  Hint Resolve incl_nil_l incl_cons_r : core.

  Fact incl_nil_r l : l ⊆ nil <-> l = nil.
  Proof.
    split.
    + unfold incl.
      simpl.
      intros H.
      destruct l as [ | x l ]. 
      * trivial.
      * destruct H with x.
        simpl; auto.
    + intros ->. (* equiv intros E; rewrite -> E *)
      auto. (* apply incl_refl. *)
  Qed.

  Fact incl_app_comm l m : l++m ⊆ m++l.
  Proof.
    intro.
    rewrite !in_app_iff.
    tauto.
  Qed.

  (* Alternative inductive definitions of In/∈ and incl/⊆ *)

  Reserved Notation "x ∈' y" (at level 70, no associativity).

  Inductive ind_In : X -> list X -> Prop :=
    | in_ind_In0 : forall x l, x ∈' x::l
    | in_ind_In1 : forall x y l, x ∈' l -> x ∈' y::l
  where "x ∈' l" := (ind_In x l).

  (**                         x ∈' l
          -------------   ---------------   
            x ∈' x::l        x ∈' y::l     *)

  Fact ind_In_equiv x l : x ∈ l <-> x ∈' l.
  Proof.
    split.
    + induction l as [ | y l IHl ]; simpl.
      * intros [].
      * intros [ -> | ]; constructor; auto.
    (*    - constructor.
        - constructor 2.
          apply IHl, H. *)
    + intros H.
      Check  ind_In_ind.
      induction H as [ x l | x y l H IH ].
      * left; reflexivity.
      * right; assumption.
  Qed.

  Reserved Notation "x ⊆' y" (at level 70, no associativity).

  Inductive ind_incl : list X -> list X -> Prop :=
    | in_ii0 : forall m, nil ⊆' m
    | in_ii1 : forall x l m, x ∈' m -> l ⊆' m -> x::l ⊆' m 
  where "l ⊆' m" := (ind_incl l m).

  (**                             x ∈' m     l ⊆' m
            -------------      ------------------------
               nil ⊆' m                x::l ⊆' m    *)

  Fact ind_incl_equiv l m : l ⊆ m <-> l ⊆' m.
  Proof.
    split.
    + intros H.
      induction l as [ | x l IHl ].
      * constructor.
      * constructor.
        - apply ind_In_equiv.
          apply H.
          simpl; auto.
        - apply IHl.
          rewrite cons_incl_left in H.
          tauto.
    + intros H.
      induction H as [ m | x l m H1 H2 IH2 ].
      * auto.
      * rewrite cons_incl_left, ind_In_equiv.
        auto.
  Qed.

End list.
  
 