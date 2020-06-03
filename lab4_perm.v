(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

Set Implicit Arguments.

(** A small utility library to complement List *)

(* If l1++r1 = l2++r2 then either l1 overlaps l2 
   or the contrary and this holds computably 

   hence l1++r1 = l1++m++r2 = l2++r2 
   or    l1++r1 = l2++m++r1 = l2++r2
   holds for some computable m

   hint:
    use the injection tactic on identities 
         _::_ = _::_
*)

Lemma cons_inv {X} (x y : X) l m : x::l = y::m -> x = y /\ l = m.
Proof.
  inversion 1; auto.
Qed.

Lemma app_split X (l1 l2 r1 r2 : list X) :
          l1++r1 = l2++r2
       -> { m | l2 = l1++m /\ r1 = m++r2 }
        + { m | l1 = l2++m /\ r2 = m++r1 }.
Proof.
  revert l2. 
  induction l1 as [ | x l1 IHl1 ].
  + intros l2 E.
    left.
    (* constructor 1 with l2. *)
    exists l2.
    simpl in *.
    auto.
  + intros [ | y l2 ] E.
    * right. 
      exists (x::l1).
      auto.
    * simpl in E |- *.
      (* injection E; clear E; intros E <-. *)
      (* inversion E. *)
      destruct (@cons_inv X) with (1 := E) as [ <- E2 ].
      apply IHl1 in E2.
      destruct E2 as [ (m & H1 & H2) | (m & H1 & H2) ].
      - left.
        exists m.
        subst. 
        auto.
      - right; exists m; subst; auto.
Qed.

(* Specialization of the previous result when r1 and r2 
   are of the form = _::_ 

   hints:

    1) use the inversion tactic on identities
    2) SearchAbout [ app nil ]
*)

Lemma app_cons_split {X} (x y : X) l1 l2 r1 r2 : 
          l1++x::r1 = l2++y::r2
       -> { m | l2 = l1++x::m /\ r1 = m++y::r2 }
        + { l1 = l2 /\ x = y /\ r1 = r2 }
        + { m | l1 = l2++y::m /\ r2 = m++x::r1 }.
Proof.
  intros E.
  apply app_split in E.
  simpl in E.
  destruct E as [ (m & H1 & H2) | (m & H1 & H2) ].
  + destruct m as [ | z m ]; simpl in H2; apply cons_inv in H2.
    * destruct H2 as [ -> -> ].
      rewrite <- app_nil_end in H1.
      auto.
    * destruct H2 as [ <- -> ].
      do 2 left.
      exists m; auto.
  + destruct m as [ | z m ]; simpl in H2; apply cons_inv in H2.
    * destruct H2 as [ -> -> ].
      rewrite <- app_nil_end in H1.
      auto.
    * destruct H2 as [ <- -> ].
      right.
      exists m; auto.
Qed.

Reserved Notation "x ~p y" (at level 70, no associativity).
Reserved Notation "x ~' y" (at level 70, no associativity).

Section perm.

  Variable X : Type.

  (** One possible inductive definition of the existence
      of a permutation *)

  Inductive perm : list X -> list X -> Prop :=

    | perm_nil   : nil ~p nil

    | perm_skip  : forall x l m, l ~p m -> x::l ~p x::m

    | perm_swap  : forall x y l, x::y::l ~p y::x::l

    | perm_trans : forall l m k, l ~p m -> m ~p k -> l ~p k

  where "l ~p m" := (perm l m).

  (* hint: induction on h *)

  Lemma perm_mskip h l m : l ~p m -> h++l ~p h++m.
  Proof.
    (* induction h; simpl; intros; trivial; constructor; auto. *)
    induction h as [ | x h IH ]; intros H; simpl.
    + trivial.
    + constructor.
      (* apply IH, H. *)
      auto.
  Qed.

  (* hint: l++nil ~p l++nil *)

  Lemma perm_refl l : l ~p l.
  Proof.
   (* induction l; constructor; auto. *)
    rewrite (app_nil_end l).
    apply perm_mskip.
    constructor.
  Qed.

  (* hint: induction on l *)

  Lemma perm_middle x l r : x::l++r ~p l++x::r.
  Proof.
    induction l as [ | y l IH ]; simpl.
    + apply perm_refl.
    + apply perm_trans with (y :: x :: l ++ r).
      * apply perm_swap.
      * apply perm_skip.
        assumption.
  Qed.

  Hint Resolve perm_refl perm_skip perm_middle perm_mskip perm_swap : core.

  (* hint: induction on l (but for any m, not for fixed m) *)

  Lemma perm_comm l m : l++m ~p m++l.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros m; simpl.
    + rewrite <- app_nil_end; auto.
    + apply perm_trans with (l++x::m); auto.
      Check perm_trans.
      apply perm_trans with (1 := IHl _); simpl.
      auto.
  Qed.

  (* hint: induction on the proof of l ~p m *)

  Lemma perm_sym l m : l ~p m -> m ~p l.
  Proof.
    intros H.
    induction H as [ | x l m H1 IH1 | x y l | l m k H1 IH1 H2 IH2 ].
    + apply perm_nil.
    + apply perm_skip; auto.
    + apply perm_swap.
    + apply perm_trans with m; trivial. 
  Qed.

  (* hints: 
      1) induction on l ~p m and 
      2) use discriminate to remove absurd identities 
   *)

  Lemma perm_nil_inversion l m : l ~p m -> m = nil -> l = nil.
  Proof.
    (* induction 1; auto; discriminate. *)
    induction 1 as [ | x l m H1 IH1 | x y l | l m k H1 IH1 H2 IH2 ].
    + trivial.
    + discriminate.
    + discriminate.
    + auto.
  Qed.

  (* use perm_nil_inversion *)

  Lemma perm_nil_inv l : l ~p nil -> l = nil.
  Proof.
    intros E.
    apply perm_nil_inversion with (1 := E).
    trivial.
  Qed.

  Hint Resolve incl_refl incl_cons incl_tl : core.

  (* Check incl_[cons,tran], Print incl 
     hint: induction on l ~p m *)

  Lemma perm_incl l m : l ~p m -> incl l m.
  Proof.
    unfold incl.
    (* induction 1; auto; firstorder. *)
    induction 1 as [ | x l m H1 IH1 | x y l | l m k H1 IH1 H2 IH2 ]; intros a; simpl.
    + auto.
    + firstorder.
    + tauto.
    + auto.
  Qed.

  Lemma perm_eq l m : l ~p m -> incl l m /\ incl m l.
  Proof.
    intros H.
    split.
    + apply perm_incl; trivial.
    + apply perm_incl, perm_sym; trivial.
  Qed.

  (** This is the hard lemma to 
      1) find out
      2) and prove

      if l is l' where a has been inserted
      anywhere insided l' 
      and m is m' with a inserted anywhere inside
      and l ~p m then l' ~p m'

    *)

  Hint Resolve perm_comm perm_sym : core.

  (* hints:
       1) use discriminate and inversion
       2) do a case analysis (destruct) on l1 (and m1) 
          ie l1 = nil or l1 = _::nil or l1 := _::_::_
   *)

  Lemma perm_add_inv l m a : l ~p m 
         -> forall l1 l2 m1 m2, 
              l = l1++a::l2 
           -> m = m1++a::m2
           -> l1++l2 ~p m1++m2.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | l k m H1 IH1 H2 IH2 ]; intros l1 l2 m1 m2 El Em.
    + destruct l1; discriminate.
    + destruct l1 as [ | b l1 ]; destruct m1 as [ | c m1 ]; simpl in *;
        inversion El; inversion Em; subst; auto.
      * apply perm_trans with (1 := H1), perm_sym.
        apply perm_middle.
      * apply perm_trans with (2 := H1); auto.
    + destruct l1 as [ | b1 [  | b2 l1 ] ];
      destruct m1 as [ | c1 [ | c2 m1 ] ];
      inversion El; inversion Em; subst; simpl; auto.
      * apply perm_trans with (2 := perm_swap _ _ _).
        apply perm_skip, perm_sym, perm_middle.
      * apply perm_trans with (1 := perm_swap _ _ _); auto.
      * apply app_cons_split in H5.
        destruct H5 as [ [ (m & -> & ->) | (-> & _ & ->) ] | (m & -> & ->) ].
        - rewrite app_ass; simpl.
          apply perm_trans with (1 := perm_swap _ _ _).
          do 2 apply perm_skip.
          apply perm_mskip.
          apply perm_sym; auto.
        - apply perm_swap.
        - rewrite app_ass; simpl.
          apply perm_trans with (1 := perm_swap _ _ _).
          do 2 apply perm_skip.
          apply perm_mskip.
          apply perm_sym; auto.
    + assert (In a k) as H3.
      { apply perm_incl with (1 := H1).
        subst.
        apply in_app_iff; simpl; auto. }
      apply in_split in H3; destruct H3 as (k1 & k2 & Ek).
      apply perm_trans with (k1++k2).
      * apply IH1; auto.
      * apply IH2; auto.
  Qed.

  (* is an instance of perm_add_inv *)

  Lemma perm_cons_inv x l m : x::l ~p x::m -> l ~p m.
  Proof.
    intros H.
    Check perm_add_inv.
    apply perm_add_inv with (l1 := nil) (m1 := nil) (2 := eq_refl) (3 := eq_refl) in H.
    simpl in H; trivial.
  Qed.

  Hint Resolve perm_cons_inv : core.

  Lemma perm_app_inv_l k l m : k++l ~p k++m -> l ~p m.
  Proof.
    induction k as [ | x k IHk ]; simpl.
    + trivial.
    + intros H; apply IHk.
      revert H; apply perm_cons_inv.
  Qed.

  (* hint: use perm_sym, perm_trans and perm_app_inv *)
 
  Lemma perm_app_inv_r l m k : l++k ~p m++k -> l ~p m.
  Proof.
    intros H.
    apply (perm_app_inv_l k).
    apply perm_trans with (1 := perm_comm _ _), 
          perm_trans with (1 := H); auto.
  Qed.

  Hint Resolve perm_app_inv_l perm_app_inv_r : core.

  (* hints:
       1) induction on l ~p m
       2) use the "lia" tactic to solve arithmetic equations 
   *)

  Lemma perm_length l m : l ~p m -> length l = length m.
  Proof.
    induction 1; simpl; lia. 
(*    induction 1 as [ | x l m H1 IH1 | x y l | l k m H1 IH1 H2 IH2 ]; simpl.
    + trivial.
    + f_equal; trivial.
    + trivial.
    + transitivity (length k); auto. *)
  Qed.

  (* hints: use perm_length (with the generalize tactic) 
            to eliminate the non-singleton cases and 
            then perm_incl *)

  Lemma perm_sg_inv l x : l ~p x::nil -> l = x::nil.
  Proof.
    intros H.
    generalize (perm_length H); simpl.
    destruct l as [ | y [ | z l ] ]; simpl; try discriminate.
    intros _; f_equal.
    apply perm_incl in H.
    unfold incl in H.
    specialize (H y); simpl in H.
    destruct H as [ -> | [] ]; auto.
  Qed.

  (* hints: use perm_length to eliminate lists of length <> 2
            and then perm_[cons,sg]_inv *)

  Lemma perm_pair_inv l x y : l ~p x::y::nil -> l = x::y::nil \/ l = y::x::nil.
  Proof.
    intros H.
    generalize (perm_length H); simpl.
    destruct l as [ | a [ | b [ | c l ] ] ]; simpl; try discriminate.
    intros _.
    assert (a = x \/ a = y) as E.
    { apply perm_incl in H.
      generalize (H a); simpl.
      intros [ -> | [ -> | [] ] ]; auto. }
    destruct E as [ -> | -> ].
    + apply perm_cons_inv, perm_sg_inv in H.
      left; f_equal; trivial.
    + assert (y :: b :: nil ~p y :: x :: nil) as H1.
      { apply perm_trans with (1 := H); auto. }
      apply perm_cons_inv, perm_sg_inv in H1.
      right; f_equal; trivial.
  Qed.

(*
  Lemma perm_triple_inv l x y z : l ~p x::y::z::nil -> l = x::y::z::nil
                                                    \/ ...
  Proof.

*)

  (* hints: use perm_sg_inv and "inversion" tactic *)

  Lemma perm_eq_equiv x y : x = y <-> x::nil ~p y::nil.
  Proof.
    split.
    + now intros <-. (* equivalent to intros <-; easy *)
    + intros H.
      apply perm_sg_inv in H.
      now inversion H.
  Qed.

  Section perm_dec.

    Variable Xdec : forall x y : X, { x = y } + { x <> y }.

    Print In.

    (** finds an occurence of x into m 
        or a proof that x does not belong to m *)

    (* hint: search by induction on m *)

    Lemma in_split_dec (x : X) m : { m1 : _ & { m2 | m = m1++x::m2 } } + { ~ In x m }.
    Proof.
      induction m as [ | y m IHm ].
      + right.
        simpl.
        intros [].
      + destruct (Xdec y x) as [ H | H ].
        * subst y.
          left.
          exists nil, m; simpl; trivial.
        * destruct IHm as [ (m1 & m2 & E) | C ].
          - subst m.
            left.
            exists (y::m1), m2; simpl; trivial.
          - right; simpl; tauto.
    Qed.

    (** permutations are decidable if identity is decidable *)

    (* hint: by induction on l (for any m) 
         when l = x::_ use in_split_dec to find x into m *)

    Theorem perm_dec l m : { l ~p m } + { ~ l ~p m }.
    Proof.
      revert m; induction l as [ | x l IHl ]; intros m.
      + destruct m as [ | y m ].
        * now left.
        * right.
          intros H.
          apply perm_sym, perm_nil_inv in H.
          discriminate.
      + destruct (in_split_dec x m) as [ (m1 & m2 & ->) | C ].
        * destruct IHl with (m := m1++m2) as [ H | H ].
          - left.
            apply perm_trans with (2 := perm_middle _ _ _).
            now apply perm_skip.
          - right.
            contradict H.
            apply perm_cons_inv with x.
            apply perm_trans with (1 := H), perm_sym, perm_middle.
        * right.
          contradict C.
          apply perm_incl with (1 := C).
          simpl; auto.
    Qed.

  End perm_dec.

  (** if one can decide permutation, then identity is decidable *)

  (* hint: use the equivalence perm_eq_equiv *)

  Theorem dec_perm : (forall l m, { l ~p m } + { ~ l ~p m })
                  -> (forall x y : X, { x = y } + { x <> y }).
  Proof.
    intros Pdec x y.
    destruct (Pdec (x::nil) (y::nil)); [ left | right ];
      now rewrite perm_eq_equiv.
  Qed.

  Check perm_dec.

(*

End perm.

Require Import Extraction.

Recursive Extraction perm_dec.

*)

  Section alternate_1.

    (** An alternate definition of permutations by transitive closure
        of transpositions, we show the equivalence *)

    Inductive perm' : list X -> list X -> Prop :=
      | perm'_nil   : nil ~' nil                                (* void list *)
      | perm'_sg    : forall x, x::nil ~' x::nil                (* singleton list *)
      | perm'_swap  : forall l x y r, l++x::y::r ~' l++y::x::r  (* transposition *)
      | perm'_trans : forall l m k, l ~' m -> m ~' k -> l ~' k  (* transitivity *)
    where "l ~' m" := (perm' l m).

     (* hints: case analysis on l and transitivity for l = _::_::_ *) 

    Lemma perm'_refl l : l ~' l.
    Proof.
      destruct l as [ | x [ | y l ] ].
      + constructor.
      + constructor.
      + apply perm'_trans with (1 := perm'_swap nil _ _ _).
        apply (perm'_swap nil).
    Qed.

    (* hint: induction on l ~' m *)

    Lemma perm'_skip x l m : l ~' m -> x::l ~' x::m.
    Proof.
      induction 1 as [ | | | ? ? ? ? IH1 ].
      + apply perm'_refl.
      + apply perm'_refl.
      + constructor 3 with (l := _::_).
      + now constructor 4 with (1 := IH1).
    Qed.

    (** the two definitions of permutations are equivalent *)

    (* hint: "split" and two inductions on the permutation predicate *)

    Hint Constructors perm' : core.
    Hint Resolve perm'_refl perm'_skip : core.

    Lemma perm_perm'_eq l m : l ~p m <-> l ~' m.
    Proof.
      split.
      + induction 1 as [ | x l m | x y l | l m p H1 IH1 H2 IH2 ]; auto.
        * apply perm'_swap with (l := nil).
        * apply perm'_trans with m; auto.
      + induction 1 as [ | x | l x y m | l m p H1 IH1 H2 IH2 ]; auto.
        apply perm_trans with m; auto.
    Qed.

  End alternate_1.

  Section alternate_2.

    Fixpoint permf (l m : list X) :=
      match l with
        | nil  => m = nil
        | x::l => exists a b, m = a++x::b /\ l ~' a++b
      end
    where "l ~' m" := (permf l m).

    Lemma permf_nil : nil ~' nil.
    Proof.
      now simpl.
    Qed.

    Lemma permf_skip x l m : l ~' m -> x::l ~' x::m.
    Proof.
      intros H.
      simpl.
      exists nil, m; simpl; auto.
    Qed.

    Hint Resolve permf_nil permf_skip : core.

    Lemma permf_refl l : l ~' l.
    Proof.
      induction l; auto.
      (* induction l.
      + apply permf_nil.
      + apply permf_skip; assumption. *)
    Qed.

    Hint Resolve permf_refl : core.

    Lemma permf_swap x y l : x::y::l ~' y::x::l.
    Proof.
      simpl.
      exists (y::nil), l; simpl.
      split; auto.
      exists nil, l; simpl; auto.
    Qed.

    Hint Resolve permf_swap : core.

    Lemma permf_middle l x r m : 
        l++x::r ~' m <-> exists a b, m = a++x::b /\ l++r ~' a++b.
    Proof. 
       (* this one is more difficult, needed for permf_trans below *) 
       (** hints: induction on l after generalizing m, and use app_split *)
    Admitted.

    Lemma permf_trans l m k : l ~' m -> m ~' k -> l ~' k.
    Proof.
      revert m k; induction l as [ | x l IHl ]; intros m k; simpl.
      + intros -> ->; trivial.
      + intros (a & b & -> & H1).
        rewrite permf_middle.
        intros (a' & b' & -> & H2).
        exists a', b'; split; auto.
        revert H1 H2; apply IHl.
    Qed.

    Theorem perm_eq_permf l m : l ~p m <-> l ~' m.
    Proof.
      split.
      + induction 1 as [ | | | l m ]; auto.
        apply permf_trans with m; auto.
      + revert m; induction l as [ | x l IHl ]; intros m; simpl.
        * intros ->; auto.
        * intros (a & b & -> & H).
          apply perm_trans with (2 := perm_middle _ _ _); auto.
    Qed.
  
  End alternate_2.

End perm.