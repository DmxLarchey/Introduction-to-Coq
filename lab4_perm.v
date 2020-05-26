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

Lemma app_split {X} (l1 l2 r1 r2 : list X) : 
          l1++r1 = l2++r2
       -> { m | l2 = l1++m /\ r1 = m++r2 }
        + { m | l1 = l2++m /\ r2 = m++r1 }.
Proof.
  revert l2; induction l1 as [ | x l1 IHl1 ].
  + admit.
  + intros [ | y l2 ] E.
    * admit.
    * admit.
Admitted.

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
Admitted.

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
  Admitted.

  (* hint: l++nil ~p l++nil *)

  Lemma perm_refl l : l ~p l.
  Proof.
  Admitted.

  (* hint: induction on l *)

  Lemma perm_middle x l r : x::l++r ~p l++x::r.
  Proof.
  Admitted.

  Hint Resolve perm_refl perm_skip perm_middle perm_mskip perm_swap : core.

  (* hint: induction on l (but for any m, not for fixed m) *)

  Lemma perm_comm l m : l++m ~p m++l.
  Proof.
  Admitted.

  (* hint: induction on the proof of l ~p m *)

  Lemma perm_sym l m : l ~p m -> m ~p l.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | l m k H1 IH1 H2 IH2 ].
  Admitted.

  (* hints: 
      1) induction on l ~p m and 
      2) use discriminate to remove absurd identities 
   *)

  Lemma perm_nil_inversion l m : l ~p m -> m = nil -> l = nil.
  Proof. Admitted.

  (* use perm_nil_inversion *)

  Lemma perm_nil_inv l : l ~p nil -> l = nil.
  Proof. Admitted.

  Hint Resolve incl_refl incl_cons incl_tl : core.

  (* Check incl_[cons,tran], Print incl 
     hint: induction on l ~p m *)

  Lemma perm_incl l m : l ~p m -> incl l m.
  Proof.
  Admitted.

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
    + admit.
    + destruct l1 as [ | b l1 ]; destruct m1 as [ | c m1 ]; simpl in *;
        inversion El; inversion Em; subst; auto.
      * admit.
      * admit.
    + destruct l1 as [ | b1 [  | b2 l1 ] ];
      destruct m1 as [ | c1 [ | c2 m1 ] ];
      inversion El; inversion Em; subst; simpl; auto.
      1-3: admit.
    + assert (In a k) as H3.
      { admit. }
      apply in_split in H3; destruct H3 as (k1 & k2 & Ek).
      admit.
  Admitted.

  (* is an instance of perm_add_inv *)

  Lemma perm_cons_inv x l m : x::l ~p x::m -> l ~p m.
  Proof.
  Admitted.

  Hint Resolve perm_cons_inv : core.

  Lemma perm_app_inv_l k l m : k++l ~p k++m -> l ~p m.
  Proof. Admitted.

  (* hint: use perm_sym, perm_trans and perm_app_inv *)
 
  Lemma perm_app_inv_r l m k : l++k ~p m++k -> l ~p m.
  Proof.
  Admitted.

  Hint Resolve perm_app_inv_l perm_app_inv_r : core.

  (* hints:
       1) induction on l ~p m
       2) use the "lia" tactic to solve arithmetic equations 
   *)

  Lemma perm_length l m : l ~p m -> length l = length m.
  Proof. 
  Admitted.

  (* hints: use perm_length (with the generalize tactic) 
            to eliminate the non-singleton cases and 
            then perm_incl *)

  Lemma perm_sg_inv l x : l ~p x::nil -> l = x::nil.
  Proof.
    intros H.
    generalize (perm_length H); simpl.
    destruct l as [ | y [ | z l ] ]; simpl.
  Admitted.

  (* hints: use perm_length to eliminate lists of length <> 2
            and then perm_[cons,sg]_inv *)

  Lemma perm_pair_inv l x y : l ~p x::y::nil -> l = x::y::nil \/ l = y::x::nil.
  Proof.
  Admitted.

  (* hints: use perm_sg_inv and "inversion" tactic *)

  Lemma perm_eq_equiv x y : x = y <-> x::nil ~p y::nil.
  Proof.
  Admitted.

  Section perm_dec.

    Variable Xdec : forall x y : X, { x = y } + { x <> y }.

    Print In.

    (** finds an occurence of x into m 
        or a proof that x does not belong to m *)

    (* hint: search by induction on m *)

    Lemma in_split_dec (x : X) m : { m1 : _ & { m2 | m = m1++x::m2 } } + { ~ In x m }.
    Proof.
    Admitted.

    (** permutations are decidable if identity is decidable *)

    (* hint: by induction on l (for any m) 
         when l = x::_ use in_split_dec to find x into m *)

    Theorem perm_dec l m : { l ~p m } + { ~ l ~p m }.
    Proof.
      revert m; induction l as [ | x l IHl ]; intros m.
      + destruct m as [ | y m ].
        1-2: admit.
      + destruct (in_split_dec x m) as [ (m1 & m2 & ->) | C ].
        1-2: admit.
    Admitted.

  End perm_dec.

  (** if one can decide permutation, then identity is decidable *)

  (* hint: use the equivalence perm_eq_equiv *)

  Theorem dec_perm : (forall l m, { l ~p m } + { ~ l ~p m })
                  -> (forall x y : X, { x = y } + { x <> y }).
  Proof.
  Admitted.

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
  Admitted.

  (* hint: induction on l ~' m *)

  Lemma perm'_skip x l m : l ~' m -> x::l ~' x::m.
  Proof.
  Admitted.

  (** the two definitions of permutations are equivalent *)

  (* hint: "split" and two inductions on the permutation predicate *)

  Lemma perm_perm'_eq l m : l ~p m <-> l ~' m.
  Proof.
  Admitted.

End perm.