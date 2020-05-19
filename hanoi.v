(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia.

Set Implicit Arguments.

(** FOL equivalence lemmas *)

Lemma exists_equiv X (P Q : X -> Prop) : (forall x, P x <-> Q x) -> ex P <-> ex Q.
Proof.
Admitted.

Lemma exists_right X A (P : X -> Prop) : (exists x, A /\ P x) <-> A /\ ex P.
Proof.
Admitted.

(** List related lemmas *)

Section extra_list_results.

  Variable (A : Type).

  (* All variable names l[0-9]* have an implicit type *) 

  Implicit Type l : list A.

  (* from l1++r1 = l2++r2, find the common factor 

     Hint: by induction on l1 with generalized l2, 
           either l1 is shorter or l2 is shorter.
  *)

  Lemma app_split l1 l2 r1 r2 : 
          l1++r1 = l2++r2
       -> exists m, l2 = l1++m /\ r1 = m++r2
                 \/ l1 = l2++m /\ r2 = m++r1.
  Proof.
    revert l2; induction l1 as [ | a l1 IHl1 ].
  Admitted.

  (* A reverse induction principle for lists *)

  Section list_rev_ind.

    Variable (P : list A -> Prop)
             (HP0 : P nil)
             (HP1 : forall l a, P l -> P (l++a::nil)).

    Let P_rev : forall l, P (rev l).
    Proof.
    Admitted.

    (* Hint: l = rev (rev l) *)

    Theorem list_rev_ind l : P l.
    Proof.
    Admitted.

  End list_rev_ind.

End extra_list_results.

(** Compare the two induction principles *)

Check list_ind.
Check list_rev_ind.

(** Permutation related notation and tactics *)

(* Infix notation l ~p m is shortcut for (Permutation l m) *)

Infix "~p" := (@Permutation _) (at level 70, no associativity).

(* Permutation tactic notations for goals

   perm comm right:       k ~p l++m   becomes   k ~p m++l
   perm skip:          x::l ~p x::m   becomes   l ~p m
                       k++l ~p k++m   becomes   l ~p m
   perm sym:              l ~p m      becomes   m ~p l
   perm assoc:         rewrite goals according to associativity of ++ and ::
   perm trans H: when H : l1 ~p l2, 
                          l1 ~p m     becomes   l2 ~p m
   perm incl:             incl l m    becomes   l ~p m

*)

Tactic Notation "perm" "comm" "right" :=
  apply perm_trans with (2 := Permutation_app_comm _ _); simpl.

Tactic Notation "perm" "skip" := 
  match goal with 
    | |- _::_ ~p _::_ => apply perm_skip
    | |- ?l++_ ~p ?l++_ => apply Permutation_app_head
  end.

Tactic Notation "perm" "sym" := apply Permutation_sym. 

Tactic Notation "perm" "assoc" := repeat (rewrite !app_ass; simpl).

Tactic Notation "perm" "trans" hyp(H) :=
  match type of H with
    | ?l1 ~p ?l2 =>
    match goal with 
      | |- ?l1 ~p _ => apply perm_trans with (1 := H)
      | |- _ ~p ?l1 => apply perm_trans with (2 := Permutation_sym H)
    end
  end.

Tactic Notation "perm" "incl" :=
  let x := fresh in intro x; apply Permutation_in; clear x.

(* Example of use of the permutation tactics *)

Goal forall X l m (x : X), l++x::m ~p m++x::l.
Proof.
  intros X l m x.
  perm comm right.
  perm sym.
  perm comm right.
  perm skip.
  perm comm right.
  perm skip.
  auto.
Qed.

(** Human friendly notation for lists:

    - x ∈ l : x is a member of l
    - l ⊆ m : l is included in m
    - ⌊l⌋ : the length of l

    The definitions are to be found in the List
    module of the Standart Library

 *)

Infix "∈" := In (at level 70, no associativity).
Infix "⊆" := incl (at level 70, no associativity).
Notation "⌊ l ⌋" := (length l) (at level 1, format "⌊ l ⌋").

Hint Resolve incl_refl incl_appl incl_appr : core.

(** Strict sorted lists of nat(ural numbers) 

   1) slu (for strictly lower-upper) denoted infix l ⪻ r:

     every member of l is strictly below (<) every member of r 

   2) m is strictly sorted denoted prefix ↗ m: 
  
     for any split m = l++r we have l ⪻ r

  Notice the difference between the < and the ⪡ symbols

*)

Definition strict_lower_upper l r := forall x y, x ∈ l -> y ∈ r -> x < y.

Infix "⪻" := strict_lower_upper (at level 70, no associativity).

(** A possible definition of strictly increasing list 
    Exercise: provide alternate characterizations for strictly 
              increasing lists and show equivalence *)

Definition si_list m := forall l r, m = l++r -> l ⪻ r.

Notation "↗ m" := (si_list m) (at level 70).

Section strict_lists.

  Implicit Type l m : list nat.

  (* ⪻  is decreasing in both arguments 
     Hint: Check for the definitions of In/∈ and incl/⊆ in the
           List module. 
   *)

  Fact slu_dec l l' m m' : l ⊆ l' -> m ⊆ m' -> l' ⪻ m' -> l ⪻ m.
  Proof.
  Admitted.

  Fact slu_nil_l l : nil ⪻ l.
  Proof.
  Admitted.

  Fact slu_nil_r l : l ⪻ nil.
  Proof.
  Admitted.

  Hint Immediate slu_nil_l slu_nil_r : core.

  (* Equivalences for ⪻ wrt list operators ::, ++ *)

  (* case of singleton lists _::nil *)

  Fact slu_sg_l x l : x::nil ⪻ l <-> forall y, y ∈ l -> x < y.
  Proof.
  Admitted.

  Fact slu_sg_r x l : l ⪻ x::nil <-> forall y, y ∈ l -> y < x.
  Proof.
  Admitted.
 
  (* What about ⪻  and ++
     Hint: in_or_app, in_app_or, in_app_iff *)

  Fact slu_app_l l1 l2 r : l1++l2 ⪻ r <-> l1 ⪻ r /\ l2 ⪻ r.
  Proof.
  Admitted.
    
  Fact slu_app_r l r1 r2 : l ⪻ r1++r2 <-> l ⪻ r1 /\ l ⪻ r2.
  Proof.
  Admitted.

  (* What about ⪻  and ++ and exchange 
     Hint: rewrite using slu_app_[lr] *)

  Fact slu_xchg l1 l2 m : l1++m ⪻ l2 -> l1 ⪻ m -> l1 ⪻ m++l2.
  Proof.
  Admitted.

  (* What about ⪻  and insertion on the right  
     Hint: use "perm ..." tactics *)

  Fact slu_insert x m l1 l2 : m++x::nil ⪻ l1++l2 -> m ⪻ x::nil -> m ⪻ l1++x::l2.
  Proof.
    intros H1 H2.
    apply slu_dec with (l' := m) (m' := (x::nil)++l1++l2); auto.
    + perm incl.
      admit.
    + admit.
  Admitted.

  (* Strictly increasing lists and list operators *)

  Fact si_list_nil : ↗ nil.
  Proof.
  Admitted.

  Fact si_list_one x : ↗ x::nil.
  Proof.
  Admitted.
  
  Hint Resolve si_list_nil si_list_one : core.

  (* Hint: app_ass, in_or_app, in_app_iff and the above app_split *)

  Fact si_list_app l r : ↗ l++r <-> ↗ l /\ ↗ r /\ l ⪻ r.
  Proof.
  Admitted. 

  (* Hint: x::l = (x::nil)++l *)

  Fact si_list_cons x l : ↗ x::l <-> x::nil ⪻ l /\ ↗ l.
  Proof.
  Admitted.

End strict_lists.

Hint Resolve slu_nil_l slu_nil_r 
             si_list_nil si_list_one : core.

(** Some reservations for upcoming notations, semantics described later on *)

Reserved Notation "'£' s" (at level 1, format "£ s").
Reserved Notation "s '#' t" (at level 1, no associativity, format "s # t"). 

Reserved Notation "l '[' t ']>' s" (at level 65, right associativity, format "l [ t ]> s").

Reserved Notation "x '~[' m ']~>' y '⟦' ld '⟧'" (at level 70, format "x  ~[ m ]~>  y  ⟦ ld ⟧").
Reserved Notation "x '~{' lm '}~>' y '⟦' ld '⟧'" (at level 70, format "x  ~{ lm }~>  y  ⟦ ld ⟧").

Section Hanoi.

  (** We establish that the Hanoi strategy is a correct way to play 
      Towers of Hanoi: see https://en.wikipedia.org/wiki/Tower_of_Hanoi *)

  (* 3 indices for the towers of Hanoi, with a decidable equality *)

  Inductive tower : Type := t1 | t2 | t3.

  Definition tower_eq_dec (x y : tower) : { x = y } + { x <> y }.
  Proof.
    revert x y; intros [] []; 
    (  (left; reflexivity) 
    || (right; discriminate) ).
  Defined.

  (* Given two towers, one can always find a different one *)

  Definition tower_other x y :=
    match (x,y) with
      | (t1,t1) => t2    | (t1,t2) => t3    | (t1,t3) => t2
      | (t2,t1) => t3    | (t2,t2) => t1    | (t2,t3) => t1
      | (t3,t1) => t2    | (t3,t2) => t1    | (t3,t3) => t1
    end.

  (* tower_other x y is indeed neither x nor y *)

  Fact tower_other_spec_x : forall x y, tower_other x y <> x.
  Proof.
  Admitted.

  Fact tower_other_spec_y : forall x y, tower_other x y <> y.
  Proof.
  Admitted.

  Hint Resolve tower_other_spec_x 
               tower_other_spec_y : core.

  (* A disk is characterized by its positive integer size/diameter 
     A stack is a list of disks *)

  Notation disk := nat.
  Notation stack := (list disk).

  (* The state of play is described by three stacks
     furthermore satisfying coherence conditions described
     later on *)
 
  Definition state : Type := (stack * stack * stack)%type.

  (* The empty state, denoted ℰ *)

  Definition st_empty : state := (nil,nil,nil).

  Notation ℰ := st_empty.

  (* Which disks stack on a given tower t in state s, denoted s#t *)

  Definition st_get_tower (s : state) t :=
    match s, t with
      | (l,_,_), t1 => l
      | (_,l,_), t2 => l
      | (_,_,l), t3 => l
    end.

  Notation "s # t" := (st_get_tower s t). 

  (* state change by stacking l on a tower t: 
       l[t]>s denotes the state obtained 
       from state s by prefixing tower t 
       with a stack l *) 
  
  Definition st_stack_tower (s : state) (t : tower) (l : stack) : state :=
    match s, t with
      | (l1,l2,l3), t1 => (l++l1,l2,l3)
      | (l1,l2,l3), t2 => (l1,l++l2,l3)
      | (l1,l2,l3), t3 => (l1,l2,l++l3)
    end.

  Notation "l [ t ]> s" := (st_stack_tower s t l).

  (* Collect all the disks in state s, denoted £s 
     The list £s is always considered upto permutation
     equivalence ~p, ie it is viewed as a multiset *)

  Definition st_collect (s : state) :=
    match s with (l1,l2,l3) => l1++l2++l3 end.

  Notation "£ s" := (st_collect s).

  (* The disks in tower s#t are contained in £s *)

  Fact get_tower_incl s t : s#t ⊆ £s.
  Proof.
  Admitted.

  Hint Resolve get_tower_incl : core.

  (* If disks in l are smaller than all those in state s
     then they are also smaller than those in s#t 

     Hint: ⪻ is decreasing *)

  Lemma slu_collect s l t : l ⪻ £s -> l ⪻ s#t.
  Proof.
  Admitted.

  (* Disks from a state change *)

  Fact st_stack_tower_collect s t l : £(l[t]>s) ~p l++£s.
  Proof.
  Admitted.

  (* The nil state change *)

  Fact st_stack_tower_nil : forall s t, nil[t]>s = s.
  Proof.
  Admitted.

  (* State change twice on the same tower *)

  Fact st_stack_tower_app s t l r : 
          l[t]>r[t]> s = l++r[t]>s. 
  Proof.
  Admitted.

  (* State changes on two different towers commute *)
  
  Fact st_stack_tower_comm s t t' l r : 
          t <> t' 
       -> l[t]>r[t']>s = r[t']>l[t]> s.
  Proof.
  Admitted.

  (* State change vs st_get_tower on the same tower *)

  Fact st_get_stack_tower_eq s t l t' :
          t = t' -> (l[t]>s)#t' = l++s#t'.
  Proof.
  Admitted.

  (* State change vs st_get_tower on different towers *)

  Fact st_get_stack_tower_neq s t l t' : 
          t <> t' -> (l[t]>s)#t' = s#t'.
  Proof.
  Admitted.

  (* A sorted state has stricly increasing stacks of disks 
     over all its three towers  *)

  Definition st_sorted (s : state) := 
    match s with 
      | (l1,l2,l3) => ↗ l1 /\ ↗ l2 /\ ↗ l3
    end.

  (* Under which condition is a state change sorted ? *)

  Fact st_sorted_stack l t s : 
             st_sorted (l[t]>s) 
         <-> st_sorted s /\ l ⪻ s#t /\ ↗ l.
  Proof.
  Admitted.

  (** A coherent state wrt. a list/multiset of disks 
       1) must use each disk exactly once
       2) each tower has to be strictly sorted *)

  Definition st_coh_wrt s ld := st_sorted s /\ ld ~p £s.

  Infix "⋉" := st_coh_wrt (at level 70, no associativity).

  (* The empty state is coherent for the void list of disks *)

  Fact st_empty_coh_wrt_nil : ℰ ⋉ nil.
  Proof.
  Admitted.

  Hint Resolve st_empty_coh_wrt_nil : core.

  (* Coherence vs change 
     Hint: use st_stack_tower_collect 
   *)

  Lemma st_coh_wrt_prefix ld s l t : 
        s ⋉ ld -> l ⪻ £s -> ↗ l -> l[t]>s ⋉ l++ld.
  Proof.
  Admitted.

  (* A moves consist in displacing one disk from the top of
     one tower to the top of another tower *)

  Inductive move_disk : tower -> disk -> tower -> state -> state -> Prop :=
    | in_move_disk : forall t x t' s, move_disk t x t' (x::nil[t]>s) (x::nil[t']>s).

  (* move_disk preserves sortedness *)

  Lemma move_disk_sorted s t x t' s' : 
          move_disk t x t' s s' 
       -> x::nil ⪻ s#t' 
       -> st_sorted s 
       -> st_sorted s'.
  Proof.
    induction 1 as [ t x t' s ].
  Admitted.

  (* move_disk preserves the multiset of disks *)

  Lemma move_disk_collect s t x t' s' : move_disk t x t' s s' -> £s ~p £s'.
  Proof.
  Admitted.

  (* move_disk preserves coherence of states *)

  Lemma move_disk_coh ld s t x t' s' :
          move_disk t x t' s s' 
       -> x::nil ⪻ s#t' 
       -> s ⋉ ld 
       -> s' ⋉ ld.
  Proof.
  Admitted.

  (* Valid move is a move 
     from a coherent state
     to another coherent state *)

  Definition move := (tower * tower)%type.

  Definition valid_move_wrt ld s m s' :=
       s ⋉ ld /\ s' ⋉ ld
    /\ match m with 
         (t,t') => exists x, move_disk t x t' s s' 
       end.

  Notation "x ~[ m ]~> y ⟦ ld ⟧" := (valid_move_wrt ld x m y).

  (* Valid list of moves *)

  Fixpoint valid_moves_wrt ld s lm s' :=
    match lm with
      | nil   => s ⋉ ld /\ s = s'
      | m::lm => exists s1, s  ~[m]~>  s1 ⟦ld⟧
                         /\ s1 ~{lm}~> s' ⟦ld⟧
    end
  where "x ~{ lm }~> y ⟦ ld ⟧" := (valid_moves_wrt ld x lm y).

  (* A valid list of moves implies coherence wrt. ld *)

  Lemma valid_moves_coh_wrt ld lm s s' : 
           s ~{lm}~> s' ⟦ld⟧ -> s ⋉ ld /\ s' ⋉ ld.
  Proof.
    revert s s'; induction lm as [ | m lm IH ]; intros s s'; simpl.
    + admit.
    + admit.
  Admitted.

  (* Valid list of moves and ++ *) 

  Lemma valid_moves_wrt_app ld s1 l r s3 :
                     s1 ~{l++r}~> s3 ⟦ld⟧
      <-> exists s2, s1    ~{l}~> s2 ⟦ld⟧
                  /\ s2    ~{r}~> s3 ⟦ld⟧.
  Proof.
  Admitted.

  (* valid list of moves and _++_::_ *)

  Lemma valid_moves_wrt_hanoi ld s1 l m r s4 :
                        s1 ~{l++m::r}~> s4 ⟦ld⟧
      <-> exists s2 s3, s1       ~{l}~> s2 ⟦ld⟧
                     /\ s2       ~[m]~> s3 ⟦ld⟧
                     /\ s3       ~{r}~> s4 ⟦ld⟧.
  Proof.
  Admitted.

  (* The recursive definition of the Hanoi move of depth n for t <> t' *)

  Fixpoint hanoi_rec n t t' :=
    match n with
      | 0   => nil
      | S n => let o := tower_other t t'
               in    hanoi_rec n t o
                  ++ (t,t')
                  :: hanoi_rec n o t'
    end.

  Notation ℍr := hanoi_rec.

  (* The exponential function n => 2^n *)

  Fixpoint pow2 n := 
    match n with 
      | 0 => 1
      | S n => 2*pow2 n
    end.

  (* The length of hanoi_rec is 2^n-1 
     Hint: use lia or omega tactic
   *) 

  Fact hanoi_rec_length n t t' : 1+⌊ℍr n t t'⌋ = pow2 n.
  Proof.
  Admitted.

  (* Now hanoi whether t = t' or not *)

  Definition hanoi n t t' :=
    if tower_eq_dec t t' then nil else ℍr n t t'.

  Notation ℍ := hanoi.

  Eval compute in ℍ 3 t1 t2.

  (** Correctness statement for hanoi_rec:
        given
          - a list of disks ld
          - a coherent state s wrt ld 
          - a sorted stack l
          - st. disks in l are smaller than those in s
          - two towers t <> t'
        then (ℍr ⌊l⌋ t t') is a valid
        sequence of moves from l[t]>s to l[t']>s
     *)

  (* Hint: a) use reverse list induction 
           b) this is the longest proof
    *)

  Theorem valid_hanoi_rec ld s l t t' : 
             s ⋉ld
           -> ↗ l
           -> l ⪻ £s  
           -> t <> t'
           -> l[t]>s ~{ℍr ⌊l⌋ t t'}~> l[t']>s ⟦l++ld⟧.
  Proof.
    revert ld s t t'.
    induction l as [ | l x IHl ] using list_rev_ind.
    + admit.
    + admit. 
  Admitted.

  (** If the disks in stack l are strictly smaller than all the disks
      stacked in the three tower and l is stricly increasing
      then (ℍ (length m) t t') describes a valid sequence 
      of moves from the state src to state dst where 
         src := m[t]>s 
         dst := m[t']>s 

      Hint: test whether t =? t' using tower_eq_dec
            and then apply valid_hanoi_rec with t <> t'
      *)

  Theorem valid_hanoi ld t t' l s : 
            l ⪻ £s
         -> ↗ l
         -> s ⋉ ld
         -> l[t]>s ~{ℍ ⌊l⌋ t t'}~> l[t']>s ⟦l++ld⟧.
  Proof.
  Admitted.
    
  (** If l is a strictly increasing stack then
      hanoi ⌊l⌋ t1 t3 is a correct strategy to
      displace l stacked on t1 to the same l stacked on t3 *)

  Corollary hanoi_is_correct l : 
            ↗ l -> l[t1]>ℰ ~{ℍ ⌊l⌋ t1 t3}~> l[t3]>ℰ   ⟦l⟧.
  Proof.
  Admitted.

  Check hanoi_is_correct.

  (** Possible improvements: 
        (a) show that hanoi is the shortest possible list of moves
        (b) show how to sort out any coherent state, not just the 
            state l[t1]>ℰ so as to put every disk on a given stack *)

End Hanoi.


