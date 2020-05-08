(** This file contains some lemmas you will have to prove, i.e. replacing
   the "Admitted" joker with a sequence of tactic calls, terminated with a 
   "Qed" command.

   Each lemma could be proved several times using various combinations
   of tactics.

   Notice that, if you want to keep all solutions, you may use various 
   identifiers like in the given example : imp_dist, imp_dist' share
   the same statement, with different interactive proofs.

*)

Section Minimal_propositional_logic.

  (** Propositional Intuitionistic logic restricted to the [->] fragment *)

  Variables P Q R S : Prop.

  (* Prove the lemmas using the following tactics 

      intro[s], exact, apply, assumption, trivial

  *)

  (** The I combinator *)
  Lemma I_P : P -> P. 
  Proof.
    intro. assumption.
  Qed.

  Check I_P.

  Print I_P.

  (** The K combinator *)
  Lemma K_PQ : P -> P -> P. 
  Proof.
    intros H1 H2; exact H1.
  Qed.

  Print K_PQ.

  (** The S combinator *)
  Lemma S_PQR : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intros H1 H2 H3.
    apply H1.
    + assumption.
    + apply H2. assumption.
  Qed.

  (** The B combinator *)
  Lemma B_PQR : (Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intros H1 H2 H3.
    apply H1, H2; trivial.
  Qed.

  Print B_PQR.

  (** The C combinator *)
  Lemma C_PQR : (P -> Q -> R) -> Q -> P -> R.
  Proof.
    intros H1 H2 H3.
    apply H1; trivial.
  Qed.

  Print C_PQR.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H1 H2 H3.
    exact (H2 (H1 H3)).
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
(*    intros H1 H2 H3; revert H1 H3 H2.
    intros H _; exact H. *)

    intros H1 H2 _; apply H1, H2.
  Qed.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros H1 H2.
    exact (H1 H2 H2).
  Qed.

  Lemma delta_impR : (P -> Q) -> P -> P -> Q.
  Proof.
    intros H1 H2 H3.
    apply H1, H3.
  Qed.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
  Proof.
    intros H1 H2 H3 H4.
    apply H3; [ apply H1 | apply H2 ]; exact H4.
  Qed.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H1.
    apply H1.
    intros H2.
    apply H2.
    intros H3.
    apply H1.
    intros _.
    apply H3.
  Qed.

End Minimal_propositional_logic.

Section propositional_logic.

  (** Propositional Intuitionistic logic *)

  Variables P Q R S T : Prop.

  (* Prove the lemmas using the following tactics 

      intro[s], exact, apply, assumption, trivial
      destruct, left/right, split

      try use tactic composition

  *)

  Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
  Proof.
    intros (? & ? & ?).
    do 2 (split; trivial).
  Qed.
 
  Print and_assoc.

  Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
  Proof.
   (* intros (H1 & H2) (H3 & H4).
    split.
    + apply H1; trivial.
    + apply H2. trivial. *)
    intros (H1 & H2) [ ? ? ] ; split; [ apply H1 | apply H2 ]; trivial. 
    (* intros [] []; split; auto. *)
  Qed.

  (* ~P (not P) is defined as P -> False *)

  (* Hypothesis H0 : True. (* to illustrate name collision *) *)

  Lemma not_contrad :  ~(P /\ ~P).
  Proof.
    (* unfold not; intros [ ? H ]; apply H; trivial. *) 
    intros [ ? H ].
    destruct H. (* apply H ; *)
    trivial.
  Qed.

  Print not_contrad.

  Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
  Proof.
    intros [ [ | ] ? ]; [ absurd P | ]; trivial.
  Qed.

  Lemma not_not_exm : ~ ~ (P \/ ~ P).
  Proof.
    unfold not.
    intros H.
    apply H.
    right.
    intros H1.
    apply H.
    left.
    trivial.
  Qed.

  Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
  Proof.
    intros H.
    split.
    + intros H1.
      apply H.
      left; trivial.
    + intros H1.
      apply H.
      right.
      trivial.
    (* intros H; split; intro; apply H; [ left | right ]; trivial. *)
  Qed.
 
  Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
  Proof.
    intros ( H1 & H2 ) [ H3 | H3 ].
    + apply H1; trivial.
    + apply H2; trivial.
    (* intros (H1 & H2) []; [ apply H1 | apply H2 ]; trivial. *)
  Qed.

  Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
  Proof.
    intros [ H | H ] []; apply H; trivial.
  Qed.

  (* Fail  ~(P /\ Q) ->  ~P \/ ~Q. *)

  Lemma or_to_imp : P \/ Q -> ~ P -> Q.
  Proof.
    intros [ H1 | H1 ].
    + intros []; trivial.
    + trivial.
    (* intros []; [ intros [] | ]; trivial. *)
  Qed.

  Lemma destruct_before_left_right : (P \/ Q) -> (P -> R) -> (Q -> T) -> R \/ T.
  Proof.
    intros [ H1 | H1 ] H2 H3.
    + left; apply H2, H1.
    + right; apply H3, H1.
  Qed.

  Lemma imp_to_not_not_or : (P -> Q) -> ~~(~P \/ Q).
  Proof.
    intros H1 H2.
    assert (~ Q) as H3. (** State intermediate lemma *)
    + contradict H2. (* intros H3; apply H2. *)
      right; trivial.
    + apply H2.
      left.
      intros H4; apply H3. (* contradict H3. *)
      apply H1, H4.
  Qed.

  Lemma contraposition : (P -> Q) -> (~Q -> ~P).
  Proof.
    intros H1 H2 H3.
    apply H2, H1, H3.
    (* intros H1 H; contradict H; apply H1, H. *)
  Qed.

  (** A <-> B is defined as (A -> B) /\ (B -> A) *)

  Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
  Proof.
    split.
    + intros H1 H2 H3; apply H2, H1, H3.
    + intros H1 H2 H3.
      apply H1.
      * intros H.
        apply H.
        trivial.
      * trivial.
  Qed.

  Lemma contraposition'' : (~P -> ~Q) <-> ~~(Q -> P).
  Proof.
    split.
    + intros H1 H2.
      apply H2; intros H3.
      unfold not in H1.
      destruct H1.
      * intros H4.
        apply H2; trivial.
      * trivial.
    + intros H1 H2 H3.
      apply H1; intros H4.
      apply H2, H4, H3.
  Qed.
 
  Section weak_XM.

   Hypothesis H0 : P -> R.
   Hypothesis H1 : ~P -> R.

   Lemma weak_XM : ~~R.
   Proof.
     intros H2.
     apply H2, H1.
     intros H3; apply H2.
     apply H0; trivial.
   Qed.

   Check weak_XM.

  End weak_XM.

  Check weak_XM.

  (* Now, you may invent and solve your own exercises ! 
     Note that you can trust the tactic tauto, based on 
     Dyckhoff's LJT calculus: if it fails, then your formula
     is probably not (intuitionnistically) provable *)

  Lemma contraposition''' : (~P -> ~Q) <-> (Q -> P).
  Proof.
    (* tauto. *) (* Not provable in Intuitionistic Logic *)
  Admitted.

End propositional_logic.
