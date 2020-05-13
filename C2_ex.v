Section C2_1.

  Variables (A : Type) (R : A -> A -> Prop) (f : A -> A) (a : A).

  Hypothesis Hf : forall x y, R x y -> R x (f y).
  Hypothesis R_refl : forall x, R x x.

  Lemma Lf : forall x, R x (f (f (f x))).
  Proof.
    intros x.
    do 3 apply Hf.
    trivial.
  Qed.

End C2_1.

Require Import Arith.

Section C2_2.

  Check lt_n_Sn.
  Check lt_trans.

  Lemma lt_n_SSn : forall i, i < S (S i).
  Proof.
    intro i.
  (*  apply lt_trans with (1 := lt_n_Sn _), lt_n_Sn. *)
    apply lt_trans with (S i); apply lt_n_Sn.
  Qed.

  Lemma greater : forall n, exists p, n < p.
  Proof.
    intros n.
    exists (S (S n)).
    apply lt_n_SSn.
  Qed.

  Print greater.

  Section absurd.

    Hypothesis H : exists n, forall p, p < n.
  
    Lemma absurd : False.
    Proof.
      destruct H as [ x Hx ].
      apply (lt_irrefl x).
      apply Hx.
    Qed.

  End absurd.

  Lemma L36 : 9 * 3 = 3 * 9.
  Proof.
    reflexivity.
  Qed.

  Variable A : Type.

  Lemma eq_trans_on_A (x y z : A) : x = y -> y = z -> x = z.
  Proof.
    intros H1 H2.
    (* rewrite H1, <- H2; reflexivity. *)
    (* now rewrite H1. (* is the same as rewrite H1; easy. *) *)
    (* subst; reflexivity. *)
    (* symmetry; transitivity y; symmetry; trivial. *)
    replace z with y; trivial.
  Qed.

  Lemma L1 : forall x y : nat,
       x = S (S y) -> 2 <= x * x.
  Proof.
    intros x y H.
    pattern x at 1.
    rewrite H.
  Admitted.

End C2_2.

Section C2_3.

  Variable f : nat -> nat -> nat.

  Hypothesis f_comm : forall x y, f x y = f y x.

  Lemma L : forall x y z, f (f x y) z = f z (f y x).
  Proof.
    intros x y z.
    rewrite (f_comm x y).
    rewrite (f_comm _ z).
    reflexivity.
  Qed.

End C2_3.

Require Import Omega.

Lemma L' : forall n, n < 2 -> n = 0 \/ n = 1.
Proof.
  intros; omega.
Qed.

Lemma L2 : forall i, i < 2 -> i*i = i.
Proof.
  intros i H.
  destruct L' with (1 := H); subst i; reflexivity.
Qed.

Lemma or_comm : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q.
  intros [].
  + right; trivial.
  + left; trivial.
Qed.

Lemma not_ex_all_not (A : Type) (P : A -> Prop) :
  (~ exists a:A, P a) -> forall a, ~ P a.
Proof.
  intros H a H1.
  apply H.
  exists a.
  trivial.
Qed.

Lemma all_not_not_ex (A : Type) (P : A -> Prop) :
  (forall a, ~ P a) -> ~ exists a:A, P a.
Proof.
  intros H (x & Hx).
  apply (H x), Hx.
Qed.
  
Lemma test_students : exists P : nat -> Prop, P 0 /\ ~ P 1.
Proof.
  exists (fun x : nat => 0 = x).
  split; [ trivial | discriminate ].
Qed.

Lemma exf : exists f : nat -> nat,
  forall n p, 0 < p -> p <= n -> exists q, f n = q * p.
Proof.
  exists (fun _ => 0).
  intros n p _ _.
  exists 0.
  simpl.
  reflexivity.
Qed.
  
Section HO.

  Variables (A : Type) (f : A -> A)
            (f_self_inverse : forall a, f (f a) = a).
  
  Lemma f_onto : forall b, exists a, b = f a.
  Proof.
    intros b.
    exists (f b).
    rewrite f_self_inverse.
    reflexivity.
  Qed.

End HO.

Require Import ZArith Ring.

Open Scope Z_scope.

Section Z_sect.

  Variable f : Z -> Z -> Z -> Z.

  Goal forall x y z, f (x+y) z 0 = f (y+x+0) (z*(1+0)) (x-x).
  Proof.
    intros x y z.
    f_equal; ring.
    (*  
      replace (x+y) with (y+x+0).
      replace z with (z*(1+0)) at 1.
      replace 0 with (x-x) at 3.
      reflexivity. *)
  Qed.

End Z_sect.

Require Import Setoid.

Section rewrite_equivalence.

  Variable (A : Type) (P Q : A -> Prop).
  Hypothesis E : forall a : A, P a <-> ~ Q a.

  Goal (exists a, P a) -> ~ (forall x, Q x).
  Proof.
    intros (x & Hx) H1.
    rewrite E in Hx.
    apply Hx, H1.
  Qed.
  
  



Print L2.




  Check N.


  Print Lf.