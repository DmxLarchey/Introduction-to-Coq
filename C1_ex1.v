
Parameters P Q R : Prop.

Section my_first_proof.

  Hypothesis H  : P \/ Q.
  Hypothesis H0 : ~ Q.

  Check H.

  Lemma my_first_lemma : R -> R /\ P.
  Proof.
    intro r.
    split.
     exact r. (* assumption *)
     destruct H.
      assumption.
      absurd Q.
       assumption.
       assumption.
  Qed.

  Check H.

  Check my_first_lemma.

End my_first_proof.

(* Check H. *)

Check my_first_lemma.