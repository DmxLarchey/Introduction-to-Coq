Parameter it_is_raining : Prop.

Parameters P Q R T : Prop.

Check P.

Check P -> Q.
Check P /\ Q.
Check P \/ Q.
Check ~ P.
Check P <-> Q.

Lemma imp_dist : (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros H1 H2 H3.
  apply H1.
   assumption.
   apply H2; assumption.
Qed.

Print imp_dist.

Definition imp_trans : (P -> Q) -> (Q -> R) -> (P -> R) := fun H1 H2 H3 => H2 (H1 H3).

Goal P /\ Q -> P.
Proof.
  intros H.
  destruct H as [ H1 ? ].
  exact H1.
Qed.

Fact conj_comm : P /\ Q -> Q /\ P.
Proof.
  intros [ ]; split; trivial.
Qed.

Fact conj_comm' : P /\ Q -> Q /\ P.
Proof.
  intros H; split; destruct H; trivial.
Qed.

Fact conj_comm'' : P /\ Q -> Q /\ P.
Proof.
  intros H.
  destruct H as [ H1 H2 ].
  split; assumption.
Qed.

Fact conj_comm''' : P /\ Q -> Q /\ P.
Proof.
  intros H.
  destruct H as [ H1 H2 ].
  split; [ assumption | trivial ].
Qed.

Section assert.

  Hypothesis (H : P -> Q)
             (H0 : Q -> R)
             (H1 : (P -> R) -> T -> Q)
             (H2 : (P -> R) -> T). 

  Lemma L8 : Q.
  Proof.
    assert (H3 : P -> R).
    + intros H3.
      apply H0.
      apply H.
      apply H3.
    + apply H1.
      * trivial.
      * apply H2.
        trivial.
  Qed.

End assert.

Section Ex5.

  Hypothesis (H : T -> R -> (P \/ Q))
             (H0 : ~ (R /\ Q))
             (H1 : T).

  Lemma R5 : R -> P.
  Proof.
    intros H2.
    destruct H as [ G1 | G2 ]; trivial.
    destruct H0.
    split; assumption.
  Qed.

End Ex5.

Lemma L2 : (P \/ Q) /\ ~P -> Q.
Proof.
  intros [ [ H1 | H1 ] H2 ]; [ destruct H2 | ]; assumption.
Qed.

Print conj_comm.

Print conj_comm'.

Fact disj_comm : P \/ Q -> Q \/ P.
Proof.
  intros H.
  destruct H as [ H1 | H2 ].
   right; trivial.
   left; trivial.
Qed.

Print disj_comm.

Fact absurd_1 : False -> False.
Proof.
  intros H.
  exact H.
Qed.

Fact absurd_2 : False -> False.
Proof.
  intros H.
  destruct H.
Qed.

Print absurd_1.
Print absurd_2.

Fact absurd_3 : ~ False.
Proof.
  intros [].
Qed.




   exact H1.
   destruct H as [ H1 H2 ].
   exact H1.
   