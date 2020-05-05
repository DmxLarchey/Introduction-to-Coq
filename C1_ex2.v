Parameter it_is_raining : Prop.

Parameters P Q R : Prop.

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
   