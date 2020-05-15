(** This first serie of  exercises asks you to prove some derived
    inference rule. For some of them, build a small example of its application. 


   New tactics: unfold, contradict, exists, symmetry, f_equal

First, let us look at some example : *)

Lemma P3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
  intros P Q H1 H2.
  apply H1.
  intros H3.
  apply H3.
  apply H2.
Qed.

(* for P : Prop, "~ P" is a convenient notation for "not P" 
   and "not P" is defined as "P -> False" 

   use the "unfold not" tactic to unfold the definition of not

   *)

Lemma triple_neg : forall P:Prop, ~ ~ ~ P -> ~ P.
Proof.
  unfold not.
  apply (fun P => P3Q P False). 
Qed.

(* try the contradict tactic *)

Lemma not_or_1 : forall P Q : Prop, ~(P \/ Q) -> ~P.
Proof.
  intros P Q H.
  contradict H.
  left; trivial.
Qed.
 
Section not_or_1_example.

  Variable n : nat.

  (* "a <> b" is a notation for "~ (a = b)" *)

  Hypothesis H : n = 0 \/ n = 2 -> n <> n.

  Lemma L1 : ~ n = 0.
  Proof.
    intros E.
    unfold not in H.
    apply H.
    + left.
      trivial.
    + trivial.
  Qed.

End not_or_1_example.

Check L1.

Lemma de_morgan_1 : forall P Q: Prop, 
               ~ (P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q.
  split.
  + intros H.
    split; intro; apply H; [ left | right ]; trivial.
  + intros [ H1 H2 ] [|]; [ apply H1 | apply H2 ]; trivial.
Qed.

Lemma de_morgan_2 P Q : ~ P \/ ~Q -> ~(P /\ Q).
Proof.
  intros [ H | H ] [ ]; apply H; trivial.
Qed.

Check de_morgan_1.

Check de_morgan_2.

Lemma all_perm (A : Type) (P : A -> A -> Prop) :
   (forall x y:A, P x y) -> 
   forall x y:A, P y x.
Proof.
  intros H1 x y.
  (* exact (H1 y x). *)
  (* exact (H1 _ _). *)
  (* trivial *)
  apply H1.
Qed.

Check all_perm.

Lemma resolution :
 forall (A:Type) (P Q R S:A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> 
   forall c:A, P c -> R c -> S c.
Proof.
  intros A P Q R S H1 H2 c H3 H4.
(*  apply H1.
  + apply H2; trivial.
  + trivial. *)
  apply H1; [ apply H2 | ]; trivial.
Qed.

Print resolution.

(** A <-> B is short for (A -> B) /\ (B -> A)
    to prove a goal |- exists x, P x, use
    the "exists t" tactic and then prove "P t"
  *)

Lemma not_ex_forall_not A (P: A -> Prop) :
   ~(exists x, P x) <-> forall x, ~ P x.
Proof.
  split.
  + intros H1 a H2.
    apply H1.
    exists a; trivial. (* firstorder. *)
  + intros H1 (x & Hx).
    (* apply (H1 x). *)
    (* apply H1 with x. *)
    apply H1 with (1 := Hx).
Qed.

Lemma ex_not_forall_not : forall (A: Type) (P: A -> Prop),
         (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
  intros A P [ x Hx ] H.
  (* apply H with (1 := Hx). *)
  apply (H _ Hx).
Qed.

(* use "symmetry" or "rewrite" *)

Lemma diff_sym : forall (A:Type) (a b : A), 
   a <> b -> b <> a.
Proof.
  intros A a b D.
  (* unfold not in *. *)
  intros E.
  apply D.
  rewrite (* <- *) E; reflexivity.
  (* symmetry; trivial. *)
Qed.

(* to prove f a = f b, try the "f_equal" tactic 
   "rewrite" can also be used 
*) 

Lemma fun_diff :  forall (A B:Type) (f : A -> B) (a b : A), 
                       f a <> f b -> a <> b.
Proof.
  intros A B f a b.
(*  intros D E.
  apply D.
  rewrite E.
  trivial. *)
  (* intros D <-; apply D; trivial. *)
  intros D; contradict D. f_equal; trivial.
Qed.

(**  this exercise deals with five equivalent characterizations of 
     classical logic 

   Some  solutions may use the following tactics:

    unfold Ident [in H].
    destruct (H t1 ... t2)
    generalize t.
    exact t.

   Please look at Coq's documentation before doing these exercises *)

Definition Double_neg : Prop := forall P:Prop, ~~P -> P.

Definition Exm : Prop := forall P : Prop, P \/ ~P.

Definition Classical_impl : Prop := forall P Q:Prop, 
    (P -> Q) -> ~P \/ Q.

Definition Peirce : Prop := forall P Q : Prop, 
    ((P -> Q) -> P) -> P.

Definition Not_forall_not_exists : Prop :=
           forall (A:Type)(P:A->Prop), ~(forall x:A, ~P x) -> exists x, P x.

Lemma  Exm_Double_neg : Exm -> Double_neg.
Proof.
  intros XM P H.
  destruct (XM P).
  + trivial.
  + (* contradict H; trivial. *)
    (* absurd(~P); trivial. *)
    destruct H; trivial.
Qed.

Lemma Double_neg_Exm : Double_neg -> Exm.
Proof.
  intros DN P.
  apply DN. (* tauto. *)
  intros H1.
  apply H1.
  right.
  contradict H1.
  left; trivial.
Qed.

Lemma Peirce_Double_neg : Peirce -> Double_neg.
Proof.
  intros PL P HP.
  apply (PL _ False).
  intros H1.
  destruct HP; trivial.
Qed.

Lemma Exm_Peirce : Exm -> Peirce.
Proof.
  intros XM P Q H.
  destruct (XM P) as [ H1 | H1 ].
  + trivial.
  + apply H.
    intro.
    (* absurd P; trivial. *)
    destruct H1; trivial.
Qed.

Lemma Classical_impl_Exm : Classical_impl -> Exm.
Proof.
  intros CI P.
  destruct (CI P P).
  + trivial.
  + right; trivial.
  + left; trivial.
Qed.

Lemma Exm_Classical_impl : Exm -> Classical_impl.
Proof.
  intros XM P Q H.
  destruct (XM P) as [ H1 | H1 ].
  + right; apply H, H1.
  + left; trivial.
Qed.

Lemma Not_forall_not_exists_Double_neg : Not_forall_not_exists -> Double_neg.
Proof.
  intros NFE P H.
  destruct (NFE True (fun _ : True => P)) as [ _ Hx ].
  + intros H1.
    apply H, H1; trivial.
  + trivial.
Qed.

Require Import Setoid.

Lemma Exm_Not_forall_not_exists : Exm -> Not_forall_not_exists.
Proof.
  intros XM A P H.
  destruct (XM (exists x, P x)) as [ H1 | H1 ].
  + trivial.
  + (* rewrite <- not_ex_forall_not in H.
    destruct H; trivial. *)
    destruct H.
    intros x Hx; apply H1; exists x; trivial.
Qed.

(** Consider the following definitions (which could be found in the standard 
   library *)

Section On_functions.

  Variables (U V W : Type).

  Variable g : V -> W.
  Variable f : U -> V.

  Definition injective : Prop := forall x y, f x = f y -> x = y.
  Definition surjective : Prop := forall v, exists u, f u = v.

  Lemma injective' : injective -> forall x y, x <> y -> f x <> f y.
  Proof.
    intros I x y D E.
    apply D.
    apply I, E.
  Qed.

  Goal (forall x y : U, x = y \/ x <> y) -> (forall x y, x <> y -> f x <> f y) -> injective.
  Proof.
    intros XM I' x y E.
    destruct (XM x y).
    + trivial.
    + destruct I' with (1 := H).
      trivial. 
  Qed.

  Definition compose := fun u : U => g (f u).

End On_functions.

Check compose.

Arguments compose [U V W].
Arguments injective [U V].
Arguments surjective [U V].

Print compose.
Print Implicit injective.

(** use eg "f_equal" or "rewrite" *)

Infix "o" := compose (at level 61, left associativity).

Lemma injective_comp U V W (f:U->V) (g : V -> W) :
     injective (g o f) -> injective f.
Proof.
 (* unfold injective, compose. *)
  intros I x y E.
  apply I.
  (* apply (f_equal g); trivial. *)
  apply (f_equal g) in E; trivial.
  (* unfold compose.
  f_equal; trivial. *)
Qed.

Lemma surjective_comp U V W f g :
   surjective (@compose U V W g f) -> surjective g.
Proof.
  intros Hgf x.
  destruct (Hgf x) as (u & Hu).
  unfold compose in *.
  exists (f u); trivial.
Qed.

Lemma comp_injective : forall U V W (f:U->V)(g : V -> W),
   injective f -> injective g -> injective (g o f).
Proof.
  intros U V W f g Hf Hg x y E.
  (* apply Hf, Hg, E. *)
  apply Hg, Hf in E; trivial.
Qed.

Section iterate.

  Variables (U : Type) (f : U -> U).

  Fixpoint iterate (n:nat) {struct n} : U -> U :=
    match n with 
      | 0   => fun a => a
      | S p => f o (iterate p)
    end.

  Hypothesis Hf : injective f.

  (* the "simpl" tactic simplifies/unfolds Fixpoint definitions 
     the "red" tactic unfolds Definitions *)

  Lemma iterate_inj n : injective (iterate n).
  Proof.
    (* revert n; apply nat_ind; [ | intros n Hn ]. *)
    induction n as [ | n IHn ].
    + simpl. 
      unfold injective.
      trivial.
    + simpl.
      apply comp_injective.
      * exact IHn.
      * exact Hf.
  Qed.

  Require Import Arith Ring.

  Fixpoint iterate_inj' n : injective (iterate n).
  Proof.
    destruct n as [ | p ].
    + simpl; red; trivial.
    + simpl.
      apply comp_injective.
      * apply (iterate_inj' p).
      * apply Hf.
  Qed.

End iterate.

(** Last serie of exercises : Consider the following definitions
   See "impredicatve definitions" in the book *)

Definition my_False : Prop := forall P:Prop, P.

Definition my_not (P:Prop) := P -> my_False.

Definition my_or (P Q:Prop): Prop := forall R:Prop, 
                                    (P-> R)->(Q->R) -> R.

Definition my_and (P Q:Prop): Prop := forall R:Prop, 
                                    (P-> Q-> R) -> R.

Definition my_exists (A:Type)(P:A->Prop) : Prop :=
  forall R: Prop, 
    (forall a: A, P a -> R) -> R.

Print False.

Lemma my_False_ok : False <-> my_False.
Proof.
Admitted.

Lemma my_or_intro_l : forall P Q:Prop, P -> my_or P Q.
Proof.
Admitted.

Lemma my_or_ok : forall P Q:Prop, P \/ Q <-> my_or P Q.
Proof.
Admitted.

Lemma my_and_ok :  forall P Q:Prop, P /\ Q <-> my_and P Q.
Proof.
Admitted.

Lemma my_ex_ok :  forall (A:Type)(P:A->Prop),
                   (exists x, P x) <-> (my_exists A P).
Proof.
Admitted.



 




 

 

                         
  
