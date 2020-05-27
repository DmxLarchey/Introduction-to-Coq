Require Arith.

Lemma le_n_plus_pn n p : n <= p + n.
Proof.
  Print le.
  induction p as [ | p IHp ]; simpl.
  + constructor 1.
  + constructor 2; assumption.
Qed.

Check le_ind.

Lemma le_plus n m : n <= m -> exists p, p+n = m.
Proof.
  Print le.
  induction 1 as [ | m H IH ].
  + exists 0; simpl; trivial.
  + destruct IH as (p & Hp).
    exists (S p); simpl; f_equal; trivial.
Qed.

Lemma foo_gen n : 1 <= n -> n = 0 -> False.
Proof.
  intros H.
  induction H.
  + discriminate.
  + discriminate.
Qed. 

Lemma foo_1 : ~ 1 <= 0.
Proof.
  red.
  intros H.
  destruct foo_gen with (1 := H).
  reflexivity.
Qed.

Lemma foo : ~ 1 <= 0.
Proof.
  intros H.
  inversion H.
Qed.

Lemma le_n_0 n : n <= 0 -> n = 0.
Proof.
  Print le.
  inversion 1.
  reflexivity.
Qed.

Fixpoint leb n m : bool := 
  match n, m with
    | 0, _     => true
    | S _, 0   => false
    | S n, S m => leb n m
  end.

Lemma le_5_45 : 5 <= 45.
Proof.
(*  do 40 constructor.
  constructor 1. *)
  repeat constructor.
Qed.

Lemma leb_5_45 : leb 5 45 = true.
Proof. reflexivity. Qed.

Print leb_5_45.

Lemma le_trans : forall n p q, n <= p -> p <= q -> n <= q.
Proof.
(*  intros n p q Hpq.
  induction 1 as [ | q H1 IH1 ].
  + trivial.
  + constructor; trivial. *)
  induction 2; [ | constructor ]; trivial.
Qed.

Lemma le_Sn_Sp_inv n p : S n <= S p -> n <= p.
Proof.
  inversion 1.
  + constructor.
  + apply le_trans with (2 := H1).
    do 2 constructor.
Qed.

Lemma le_Sn_Sp n p : n <= p -> S n <= S p.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma le_leb_iff n m : n <= m <-> leb n m = true.
Proof.
  split.
  + revert m.
    induction n as [ | n IHn ]; intros [ | m ]; simpl; auto.
    * inversion 1.
    * intro; apply IHn, le_Sn_Sp_inv; auto.
  + revert m.
    induction n as [ | n IHn ].
    * induction m; simpl; auto.
    * intros [ | m ]; simpl; auto.
      - discriminate.
      - intros H; apply IHn in H.
        apply le_Sn_Sp; trivial.
Qed.

Fact le_78_1090 : 78 <= 1090.
Proof.
  apply le_leb_iff.
  reflexivity.
Qed.

Print le_78_1090.

Require Import Arith.

Fact leb_n_np n p : leb n (n+p) = true.
Proof.
  apply le_leb_iff.
  rewrite plus_comm.
  apply le_n_plus_pn.
Qed.

Print le.

Inductive le' : nat -> nat -> Prop :=
  | le'_n : forall n, le' n n
  | le'_S : forall n m, le' n m -> le' n (S m).

Print le.

Print and.
Print or.
Print ex.
Print eq.
Print True.
Print False.

Check refl_equal.

Definition two_two_four : 2+2 = 4 := eq_refl.
