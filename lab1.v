(** This file contains some lemmas you will have to prove, i.e. replacing
   the "Admitted" joker with a sequence of tactic calls, terminated with a 
   "Qed" command.

   Each lemma could be proved several times using various combinations
   of tactics.

   Notice that, if you want to keep all solutions, you may use various 
   identifiers like in the given example : imp_dist, imp_dist' share
   the same statement, with different interactive proofs.

*)

(* Une seule étoile *)

Section Minimal_propositional_logic.

  (** Propositional Intuitionistic logic restricted to the [->] fragment *)

  Variables P Q R S : Prop.

  (* Prove the lemmas using the following tactics 

      intro[s], exact, apply, assumption, trivial

  *)

  (** The I combinator *)
  Proposition I_P : P -> P.
  Proof. 
    intro p.
    exact p. (* assumption or trivial *) 
  Qed.

  Check I_P.

  Print I_P.

  (** The K combinator *)
  Lemma K_PQ : P -> Q -> P. 
  Proof.
    intros p q.
    exact p.
    (* intros; trivial or trivial or auto *)
  Qed.

  Print K_PQ.    

  (** The S combinator *)
  Lemma S_PQR : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intros H1 H2 H3.
    apply H1.
    + apply H3.
    + apply H2, H3.
(*
    apply H1; try apply H2; apply H3.

or

    apply H1; [ apply H3 | apply H2, H3 ].

or 

    apply H1; repeat (apply H2 || apply H3).

*)
  Qed.

  Print S_PQR.

  (** The B combinator *)
  Lemma B_PQR : (Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intros H1 H2 ?.
    apply H1, H2; assumption. 
  Qed.

  (** The C combinator *)
  Lemma C_PQR : (P -> Q -> R) -> Q -> P -> R.
  Proof.
    intros H ? ?.
    apply H; assumption.
  Qed.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H1 H2 H3.
    apply H2, H1, H3.
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
  (*  intros ? H _; revert H; assumption. *)
    intros H1 H2 H3.
    clear H3.
  (*  apply H1, H2. *)
    revert H2.
    assumption.
  Qed.

  Print ignore_Q.

  Definition delta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros H ?; apply H; assumption.
(*    refine (fun H1 H2 => H1 H2 _);  trivial. *)
  Qed.

  Lemma delta_impR : (P -> Q) -> P -> P -> Q.
  Proof.
    intros H a b.
    apply H, a.
  Qed.

  Print delta_impR.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
  Proof.
    intros H1 H2 H3 H4.
    apply H3; [ apply H1 | apply H2 ]; apply H4.
(*
    apply H3.
    + apply H1, H4.
    + apply H2, H4. *)
  Qed.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H; apply H.
    intros H1; apply H1.
    intros H2; apply H.
    intros _; apply H2.
  Qed.

  Print weak_peirce.

  Lemma natural_number : (P -> P) -> (P -> P).
  Proof.
    intros H p.
    do 8 apply H.
    exact p.
  Qed.

  Print natural_number.

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
    intros [ p [ q r ] ].
    split.
    + split.
      * exact p.
      * exact q.
    + exact r.
  (*  intro H. destruct H as (p & [ q r ]). *)
 (*   destruct H as [ p qr ].
    destruct qr as [ q r ]. *)
 (*   destruct H as [ p [ q r ] ]. *)
  Qed.
 
  Print and_assoc.

  Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
  Proof.
    intros (H1 & H2) (H3 & H4).
    split.
    + apply H1, H3.
    + apply H2, H4.
  Qed.

  

  (* ~P (not P) is defined as P -> False *)

  Lemma not_contrad :  (P /\ (P -> Q)) -> Q.
  Proof.
    (* unfold not *)
    intros (p & np).
    apply np, p.
  Qed.

  Lemma not_contrad' :  ~(P /\ ~P).
  Proof.
    intros (p & np).
    destruct np.
    exact p.
  Qed.

  Print not_contrad.
  Print not_contrad'.

  Print True.
 
  Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
  Proof.
  (*
    intros ([ H | H ] & np).
    + destruct np.
      exact H.
    + exact H. *)
    intros ([|] & np); [ destruct np | idtac ]; assumption. 
(*   intros (pq & np).
    destruct pq as [ p | q ]. *)
  Admitted.

  Lemma not_not_exm : ~ ~ (P \/ ~ P).
  Proof.
    intros H.
    apply H.
    right.
    intros p.
    apply H.
    left.
    exact p.
  Qed.

  Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
  Proof.
    intros H.
    split.
    + contradict H.
      left.
      assumption.
    + intros q.
      apply H.
      right.
      assumption.
  Qed.
 
  Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
  Proof.
    intros (np & nq) [ p | q ].
    + apply np, p.
    + apply nq, q.
  Qed.

  Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
  Proof.
    intros [ np | nq ] (p & q).
    + apply np, p.
    + apply nq, q.
  Qed.

  Lemma or_to_imp : P \/ Q -> ~ P -> Q.
  Proof.
    intros [ p | q ] np.
    + destruct np.
      apply p.
    + apply q.
  Qed.

  Lemma destruct_before_left_right : (P \/ Q) -> (P -> R) -> (Q -> T) -> R \/ T.
  Proof.
    intros [ p | q ] H1 H2.
    + left.
      apply H1, p.
    + right.
      apply H2, q.
  Qed.

  Lemma imp_to_not_not_or : (P -> Q) -> ~~(~P \/ Q).
  Proof.
    intros H1 H2.
    assert (~ Q) as H3. (** State intermediate lemma *)
    + contradict H2; right; assumption.
    + apply H2.
      left.
      intros H4.
      apply H3, H1, H4.
  Qed.

  Lemma contraposition : (P -> Q) -> (~Q -> ~P).
  Proof.
    intros H1 H2. 
    contradict H2.
    apply H1, H2.
  Qed.

  (** A <-> B is defined as (A -> B) /\ (B -> A) *)

  Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
  Proof.
    (* unfold iff. *)
    split.
    + intros H1 H2. 
      contradict H2.
      apply H1, H2.
    + intros H1 H2 H3.
      apply H1; trivial.
      intros C; apply C, H3.
  Qed.

  Lemma contraposition'' : (~P -> ~Q) <-> ~~(Q -> P).
  Proof.
    split.
    + intros H1 H2.
      apply H2.
      intros H3.
      destruct H1.
      * contradict H2; intros _; assumption.
      * assumption.
    + intros H1 H2 H3.
      apply H1.
      intros H4.
      apply H2, H4, H3.
  Qed.
 
  Section weak_XM.

   Hypothesis H0 : P -> R.
   Hypothesis H1 : ~P -> R.

   Lemma weak_XM : ~~R.
   Proof.
     intros nr.
     apply nr, H1.
     intros p.
     apply nr, H0, p.
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
