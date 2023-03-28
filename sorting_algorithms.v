(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia Wellfounded Extraction.

Set Implicit Arguments.

(** Notations utilisées dans le projet 

    ⌊l⌋    :  longueur de la liste l
    l ~p m :  les listes l et m sont permutables
    x ∊ l  :  x appartient à la liste l
    x ≤ y  :  x est plus petit que y (pour l'ordre R)
    l ≲ r  :  tous les elements de la liste l sont plus petits que 
              tous les elements de la liste r (pour l'ordre R)

    Les quatres lignes ci-dessous ne font que déclarer
    la forme et les priorités des notations, leur sens
    est déclaré plus loin, la première fois qu'on les
    utilise. *)

Reserved Notation "⌊ l ⌋" (at level 1, format "⌊ l ⌋").
Reserved Notation "l ~p m" (at level 70, no associativity, format "l  ~p  m").
Reserved Notation "x ∊ l" (at level 70, no associativity, format "x  ∊  l").
Reserved Notation "x ≤ y" (at level 70, no associativity, format "x  ≤  y").
Reserved Notation "l ≲ m" (at level 70, no associativity, format "l  ≲  m").

(** Une librairie pour réaliser des inductions basées sur une mesure entière,
    par exemple la longueur d'une liste, ou encore la longueur combinée de 
    deux listes. *)

Section measure_rect.

  Variables (X : Type) (m : X -> nat)
            (P : X -> Type) (HP: forall x, (forall x', m x' < m x -> P x') -> P x).

  Definition measure_rect x : P x.
  Proof.
    refine ((fix loop x (a : Acc (fun u v => m u < m v) x) : P x := _) x _).
    + apply HP.
      intros; now apply loop, Acc_inv with (1 := a).
    + apply wf_inverse_image, lt_wf.
  Defined.

End measure_rect.

Section measure_rect2.

  Variables (X Y : Type) (m : X -> Y -> nat)
            (P : X -> Y -> Type) (HP: forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Definition measure2_rect x y : P x y.
  Proof.
    refine ((fix loop x y (a : Acc (fun u v => m (fst u) (snd u) < m (fst v) (snd v)) (x,y)) : P x y := _) x y _).
    + apply HP.
      intros; now apply loop, Acc_inv with (1 := a).
    + apply wf_inverse_image, lt_wf.
  Defined.

End measure_rect2.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x, y; revert x y; apply measure2_rect with (m := fun x y => f); intros x y IH.

Extraction Inline measure_rect measure2_rect.

(** Toute petite extension de la libraire standard sur les listes (List) *)

Require Import List.

Import ListNotations.

(* On note "In x l" de manière infixe avec "x ∊ l" *)
Infix "∊" := In.
Notation "⌊ l ⌋" := (length l).

Print Notation  "_ ∊ _".
About "_ ∊ _".
Print In.

Print Notation "⌊ _ ⌋".
About "⌊ _ ⌋".
Print length.

Print Notation "_ ++ _".
About "_ ++ _".
Print app.

Fact list_cons_inj X (x y : X) l m : x::l = y::m -> x = y /\ l = m.
Proof. intros H; inversion H; split; trivial. Qed.

#[local] Hint Resolve in_eq in_cons : core.

Check in_eq.
Check in_cons.

(** On importe une partie de la librairie sur les permutations.
    Seuls sont listés les résultats utiles aux algorithmes de tri. *)

Require Permutation.
Infix "~p" := Permutation.Permutation.

Section perm.

  Variable (X : Type).

  Implicit Types (l : list X).

  Fact perm_refl l : l ~p l.
  Proof. apply Permutation.Permutation_refl. Qed.

  Fact perm_cons x y l m : x = y -> l ~p m -> x::l ~p y::m.
  Proof. intros ->; apply Permutation.Permutation_cons; trivial. Qed.

  Fact perm_swap x y l : x::y::l ~p y::x::l.
  Proof. apply Permutation.perm_swap. Qed.

  Fact perm_trans l m k : l ~p m -> m ~p k -> l ~p k.
  Proof. apply Permutation.perm_trans. Qed.

  Fact perm_sym l m : l ~p m -> m ~p l.
  Proof. apply Permutation.Permutation_sym. Qed.

  Fact perm_middle x l m : x::l++m ~p l++x::m.
  Proof. apply Permutation.Permutation_middle. Qed.

  Fact perm_app l l' m m' : l ~p l' -> m ~p m' -> l++m ~p l'++m'.
  Proof. apply Permutation.Permutation_app. Qed.

  Fact perm_app_comm l m : l++m ~p m++l.
  Proof. apply Permutation.Permutation_app_comm. Qed.

  Fact perm_nil l : [] ~p l -> l = [].
  Proof. apply Permutation.Permutation_nil. Qed.

  Fact perm_length l m : l ~p m -> ⌊l⌋ = ⌊m⌋.
  Proof. apply Permutation.Permutation_length. Qed.

  Fact perm_in l m x : l ~p m -> x ∊ l -> x ∊ m.
  Proof. apply Permutation.Permutation_in. Qed.

  Fact perm_cons_inv x l m : x::l ~p x::m -> l ~p m.
  Proof. apply Permutation.Permutation_cons_inv. Qed.

End perm.

(** On va trier les listes en utilisant un ordre total 
    et calculable, c'est à dire, une relation binaire 

         R : X -> X -> Prop 

    notée "x ≤ y" à la place de "R x y" pour plus de lisibilité. 
    On suppose que R/≤ est
     - réflexive, antisymétrique et transitive
     - calculable, càd dotée du'une fonction R_cmp 
       qui calcule un Booléen b de sorte que
       * si b est true alors on a une preuve de x ≤ y 
       * si b est false alors on a une preuve de y ≤ x. 
     - voir ci-dessous pour quelques détails supplémentaire
       sur R_cmp. *)

Parameter (X : Type) (R : X -> X -> Prop).
Infix "≤" := R.

Parameter (R_refl  : forall x, x ≤ x)
          (R_anti  : forall x y, x ≤ y -> y ≤ x -> x = y)
          (R_trans : forall x y z, x ≤ y -> y ≤ z -> x ≤ z)
          (R_cmp   : forall x y, { b : bool | if b then x ≤ y else y ≤ x }).

(* R_cmp x y est de type { b : bool | if b then x ≤ y else y ≤ x }, càd
   une paire dépendante (b,Hb) où
      - b est de type bool; 
      - Hb est de type (if b then x ≤ y else y ≤ x).
   Donc le type de Hb dépend de la valeur de b. Plus précisément, b est true
   alors Hb : x ≤ y, et si b est false alors Hb : y ≤ x. *)

#[local] Hint Resolve R_refl : core.

(** Une librairie pour la comparaison de deux listes 
    en utilisant R/≤. On défini une relation binaire

        list_le : list X -> list X -> Prop

    notée "l ≲ r" à la place de "list_le l r" pour
    plus de lisibilité. "l ≲ r" signifie que tous les
    éléments de l sont plus petits que tous les éléments
    de r. *)

Definition list_le l r := forall x y, x ∊ l -> y ∊ r -> x ≤ y.
Infix "≲" := list_le.

(* Astuce: "Print In" vous dit que x ∊ [] est False *) 
Fact list_le_nil_l r : [] ≲ r.  Proof. admit. Admitted.
Fact list_le_nil_r l : l ≲ [].  Proof. admit. Admitted.

#[local] Hint Resolve list_le_nil_l list_le_nil_r : core.

(* Astuce: utiliser R_trans *)
Fact list_le_trans l x r : l ≲ [x] -> [x] ≲ r -> l ≲ r.
Proof.
  intros H1 H2 u v Hu Hv.
  admit.
Admitted.

(* Astuce: perm_in dit que si l ~p m alors l et m
   ont les mêmes éléments *)
Fact list_le_perm_l l m r : l ~p m -> m ≲ r -> l ≲ r.
Proof.
  intros H1 H2 u v Hu Hv.
  admit.
Admitted.

Fact list_le_perm_r l m r : r ~p m -> l ≲ m -> l ≲ r.
Proof.
  admit.
Admitted.

(* Astuce: Check in_app_iff. *)
Fact list_le_app_l l r m : l++r ≲ m <-> l ≲ m /\ r ≲ m.
Proof.
  admit.
Admitted.

Fact list_le_app_r m l r : m ≲ l++r <-> m ≲ l /\ m ≲ r.
Proof.
  admit.
Admitted.

(* Astuce:
    - utiliser list_le_app_l
    - et l'identité x::l = [x]++l *)
Fact list_le_cons_l x l r : [x] ≲ r -> l ≲ r -> x::l ≲ r.
Proof.
  admit.
Admitted.

Fact list_le_cons_r x l r : l ≲ [x] -> l ≲ r -> l ≲ x::r.
Proof.
  admit.
Admitted.

Fact list_le_singleton x y : x ≤ y -> [x] ≲ [y].
Proof.
  admit.
Admitted.

#[local] Hint Resolve list_le_singleton : core.

Fact list_le_singleton_iff x y : [x] ≲ [y] <-> x ≤ y.
Proof. split; auto. Qed.

(** Notion de liste triée par rapport à R/≤ *)

(* Si on découpe une liste triée m en deux "m = l++r", alors
   la partie gauche "l" contient des éléments tous inférieurs 
   à eux de la partie droite "r".

   C'est ainsi qu'on choisit de définir ce qu'est une liste
   triée. D'autres choix de définitions équivalentes sont 
   possibles. *)

Definition sorted m := forall l r, m = l++r -> l ≲ r.

(** Astuce:
    - seul [] = []++[] est possible
    - puis utiliser list_le_nil_* *)
Fact sorted_nil : sorted [].
Proof.
  admit.
Admitted.

(* Astuce:
   - analyse par cas sur l, première variable
     quantifiée dans la déf. de sorted.
   - utiliser list_consj_inj ensuite. *)
Fact sorted_cons x m : [x] ≲ m -> sorted m -> sorted (x::m).
Proof.
  intros H1 H2 [ | y k ] r E; simpl in *.
  + admit.
  + admit.
Admitted.

#[local] Hint Resolve sorted_nil sorted_cons : core.

Fact sorted_singleton x : sorted [x].
Proof. auto. Qed.

(* Astuce:
   - si m = l++r alors x::m = (x::l)++r 
   - aussi, x::m = [x]++m *)
Fact sorted_cons_inv x m : sorted (x::m) -> sorted m /\ [x] ≲ m.
Proof.
  admit.
Admitted.

(* Astuce:
   - par induction sur l
   - utiliser sorted_cons & sorted_cons_inv *)
Fact sorted_app l r : l ≲ r -> sorted l -> sorted r -> sorted (l++r).
Proof.
  induction l as [ | x l IHl ] in r |- *; simpl; trivial.
  admit.
Admitted.

(** Il y a une seul résultat possible au tri d'une liste 
    même s'il y a plusieurs manières de procéder à ce tri *)

(* Une fonction de tri est une fonction qui renvoie
   une liste permutable et triée *)
Definition sorting_function (s : list X -> list X) :=
  forall l, sorted (s l) /\ s l ~p l.

(* Astuce:
   - par induction sur l puis analyse par cas sur r
   - utiliser perm_*
   - utiliser sorted_cons_inv 
   - aussi, R est antisymétrique *)
Lemma perm_sorted_eq l r : l ~p r -> sorted l -> sorted r -> l = r.
Proof.
  induction l as [ | x l IHl ] in r |- *.
  + intros E _ _.
    apply perm_nil in E.
    subst.
    trivial.
  + destruct r as [ | y r ].
    * admit.
    * admit.
Admitted.

(* Toutes les fonctions de tri renvoient la même valeur *)
Corollary sorting_deterministic s1 s2 : 
           sorting_function s1 
        -> sorting_function s2 
        -> forall l, s1 l = s2 l.
Proof.
  intros H1 H2 l.
  destruct (H1 l) as (G1 & G2).
  destruct (H2 l) as (G3 & G4).
  revert G1 G3; apply perm_sorted_eq.
  now apply perm_trans with (1 := G2), perm_sym.
Qed. 

Section insertion_sort.

  (** Le tri par insertion *)

  (* On insère x dans l à sa place *)
  Fixpoint insert x l :=
    match l with
    | []   => [x]
    | y::m => if proj1_sig (R_cmp x y) then x::l else y::insert x m
    end.

  (* A permutation près, on ne fait que rajouter un élément à l *)
  (* Astuce: perm_[refl,trans,cons,swap] *)
  Fact insert_perm x l : insert x l ~p x::l.
  Proof.
    induction l as [ | y m IH ]; simpl.
    + admit.
    + admit.
  Admitted.

  (* Si l est déjà triée, l'insertion maintien cette propriété *)
  (* Astuce: sorted_cons_inv, list_le_cons, list_le_trans *)
  Fact insert_sorted x l : sorted l -> sorted (insert x l).
  Proof.
    induction l as [ | y m IH ]; simpl.
    + intros _; apply sorted_singleton.
    + intros H.
      destruct (R_cmp x y) as ([] & Hb); simpl.
      * admit.
      * admit.
  Admitted.

  (* Le tri par insertion *)
  Fixpoint insertion_sort l :=
    match l with
    | []   => []
    | x::l => insert x (insertion_sort l)
    end.

  (* Astuce:
     - insert_perm & perm_*
     - insert_sorted *)
  Theorem insert_sort_sorting : sorting_function insertion_sort.
  Proof.
    intros l.
    induction l as [ | x l IH ]; simpl.
  Admitted.

End insertion_sort.

Section quick_sort.

  (** Le tri rapide *)

  Implicit Type m : list X.

  (* On sépare la liste m avec le pivot x:
     - l qui contient les éléments plus petits que x
     - r qui contient ceux plus grands que x *)
  Fixpoint pivot_split x m :=
    match m with
    | []   => ([],[])
    | y::m => let (l,r) := pivot_split x m in
              if proj1_sig (R_cmp x y) then (l,y::r) else (y::l,r)
    end.

  (* Propriétés du pivot_split *)
  (* Astuce:
     - induction sur m = [] ou m = y::m'
     - analyse du pivot_split x m' dans
       le cas récursif 
     - comparaison de x et y *)
  Lemma pivot_split_spec x m : 
    let (l,r) := pivot_split x m 
    in  l++r ~p m /\ l ≲ [x] /\ [x] ≲ r. 
  Proof.
    induction m as [ | y m' IH ]; simpl.
    + repeat split; auto; tauto.
    + destruct (pivot_split x m') as (l,r).
      destruct IH as (H1 & H2 & H3).
      destruct (R_cmp x y) as ([] & Hxy); simpl.
      * admit.
      * admit.
  Admitted.

  (* pivot_split et sa spécification dans un seul type enrichi *)
  Definition pivot_split_full x m : { '(l,r) | l++r ~p m /\ l ≲ [x] /\ [x] ≲ r }.
  Proof. exists (pivot_split x m); apply pivot_split_spec. Defined.

  (* Argument de terminaison pour le quick_sort *)
  Lemma perm_length_cons l r x m : l++r ~p m -> ⌊l⌋ < ⌊x::m⌋ /\ ⌊r⌋ < ⌊x::m⌋.
  Proof.
    intros H%perm_length.
    rewrite app_length in H.
    simpl; lia.
  Qed.

  (* Astuce:
     - sorted_app, list_le_cons, list_le_trans *)
  Lemma sorted_quick_sort l x r :
        l ≲ [x] 
     -> [x] ≲ r
     -> sorted l
     -> sorted r
     -> sorted (l++x::r).
  Proof.
    admit.
  Admitted.

  (* Argument de correction du quick_sort *)
  (* Astuce: perm_[trans,cons,sym_middle] *)
  Lemma perm_quick_sort l r x m : l++r ~p m -> l++x::r ~p x::m.
  Proof.
    admit.
  Admitted.

  (* quick_sort construit avec sa spécification:
     la sortie s est une liste triée permutable
      avec l'entré m. *)
  (* Astuce:
     - induction sur la longueur de m
     - analyse par cas sur m = [] ou m = x::m'
     - on utilise x comme pivot:
        ((l,r),H) := pivot_split_full x m'
     - on applique l'hypothèse d'induction à l et r *)
  Lemma quick_sort_full m : { s | sorted s /\ s ~p m }.
  Proof.
    induction on m as IH with measure ⌊m⌋.
    destruct m as [ | x m' ].
    + exists [].
      admit.
    + destruct (pivot_split_full x m') as ((l,r) & H1 & H2 & H3).
      destruct (IH l) as (l' & G1 & G2); [ apply perm_length_cons with (1 := H1) | ].
      destruct (IH r) as (r' & G3 & G4); [ apply perm_length_cons with (1 := H1) | ].
      exists (l'++x::r'); split.
      * admit.
      * admit.
  Admitted.

  (* Puis on obtient le quick_sort en séparant
     le résultat et sa spécification *)

  Definition quick_sort m := proj1_sig (quick_sort_full m).

  Theorem quick_sort_sorting : sorting_function quick_sort.
  Proof. intros m; apply (proj2_sig (quick_sort_full m)). Qed.

End quick_sort.

Section merge_sort.

  (** Le tri fusion *)

  Implicit Type m : list X.

  (* merge_split [x1,x2,x3,..] = ([x1,x3,x5,...],[x2,x4,...] *)
  Fixpoint merge_split m :=
    match m with
    | []   => ([],[])
    | x::m => let (l,r) := merge_split m in (x::r,l)
    end.

  (* Spécification de "(l,r) := merge_split m" :
     - l&r contiennent les mêmes éléments que m à 
       permutation près
     - les listes l et r ont presque la même longueur *)
  (* Astuce:
     - induction sur m = [] ou m = x::m'
     - analyse de merge_split m'
     - perm_[cons,trans,app_comm] *)
  Lemma merge_split_spec m : 
    let (l,r) := merge_split m 
    in  l++r ~p m /\ ⌊r⌋ <= ⌊l⌋ <= 1+⌊r⌋.
  Proof.
    induction m as [ | y m' IH ]; simpl.
    + repeat split; auto; lia.
    + revert IH.
      destruct (merge_split m') as (l,r); simpl.
      intros (H1 & H2 & H3).
      split; [ | lia ].
      admit.
  Admitted.

  Definition merge_split_full m : { '(l,r) | l++r ~p m /\ ⌊r⌋ <= ⌊l⌋ <= 1+⌊r⌋ }.
  Proof. exists (merge_split m); apply merge_split_spec. Defined.

  (* fusion de deux listes triées l et r avec la spécification *)
  (* Astuce:
     - induction sur la longueur combinée ⌊l⌋+⌊r⌋
     - analyse par cas sur l puis sur r 
     - dans le cas où l = x::l' et r = y::r'
       comparaison de x et y avec R_dec *)
  Lemma merge l r : sorted l -> sorted r -> { m | m ~p l++r /\ sorted m }.
  Proof.
    induction on l r as IH with measure (⌊l⌋+⌊r⌋).
    intros Hl Hr.
    destruct l as [ | x l' ].
    + exists r; auto.
    + destruct r as [ | y r' ].
      * exists (x::l'); split; auto.
        now rewrite <- app_nil_end.
      * apply sorted_cons_inv in Hl as (H1 & H2).
        apply sorted_cons_inv in Hr as (H3 & H4).
        destruct (R_cmp x y) as ([] & Hxy); simpl.
        - destruct (IH l' (y::r')) as (m & G1 & G2); auto.
          exists (x::m); simpl.
          admit.
        - admit.
  Admitted.

  (* tri fusion de m avec sa spécification *)
  (* Astuce:
     - par induction sur la longueur ⌊m⌋
     - analyse par cas sur m
       * m = []
       * m = [x]
       * m = _::_::_ (longueur > 1)
         dans ce cas, on divise m en
         deux parts de longueur presque identique,
         que l'on trie récursivement, puis qu'on
         fusionne. *)
  Lemma merge_sort_full m : { s | sorted s /\ s ~p m }.
  Proof.
    induction on m as IH with measure ⌊m⌋.
    revert IH.
    case_eq m.
    + intros Hm IH.
      exists []; auto.
    + intros x [ | y m' ] Hm IH.
      * exists [x]; auto.
      * destruct (merge_split_full m) as ((l,r) & H1 & H2 & H3).
        subst m.
        generalize (perm_length H1); rewrite app_length; simpl; intros H4.
        destruct (IH l) as (l' & G1 & G2); [ simpl; lia | ].
        destruct (IH r) as (r' & G3 & G4); [ simpl; lia | ].
        admit.
  Admitted.

  Definition merge_sort m := proj1_sig (merge_sort_full m).

  Theorem meger_sort_sorting : sorting_function merge_sort.
  Proof. intros m; apply (proj2_sig (merge_sort_full m)). Qed.

End merge_sort.

(** Pour information, on peut extraire les algorithmes
    certifiés corrects vers le langage OCaml par exemple *)

Extraction Inline pivot_split_full quick_sort_full.
Extraction Inline merge_split_full merge_sort_full.

Extract Inductive prod => "( * )" [ "( , )" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction insertion_sort quick_sort merge_sort.
