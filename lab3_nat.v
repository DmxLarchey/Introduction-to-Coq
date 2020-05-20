(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Setoid.

Section plus_minus_mult.

  Print nat.

  Reserved Notation "a ⊕ b" (at level 50, left associativity).
  Reserved Notation "a ⊖ b" (at level 50, left associativity).
  Reserved Notation "a ⊗ b" (at level 40, left associativity).

  (* We redefine plus as myplus denote with ⊕ to
     avoid the conflicts with the Init module
     that contains parts of the Arith library 

     Notice that we import the inductive definition of nat

   *)

  Print nat.

  Fixpoint myplus (a b : nat) :=
    match a with
      | 0   => b
      | S a => S (a ⊕ b)
    end
  where "a ⊕ b" := (myplus a b).

  (* 0, 1, 2 is a notation of S (S ... O) 
     in particular, 0 is identical to O 
   *)

  Fact plus_0_l n : 0 ⊕ n = n.
  Proof. reflexivity. Qed.

  Fact plus_1_l n : 1 ⊕ n = S n.
  Proof. reflexivity. Qed.
  
  Fact plus_0_r n : n ⊕ 0 = n.
  Proof.
  Admitted.

  Fact plus_a_Sb a b : a ⊕ S b = S (a ⊕ b).
  Proof.
  Admitted.

  Hint Resolve plus_0_r : core.

  Fact plus_comm a b : a ⊕ b = b ⊕ a.
  Proof.
  Admitted.

  Fact plus_assoc a b c : a ⊕ b ⊕ c = a ⊕ (b ⊕ c).
  Proof.
  Admitted.

  Fixpoint myminus (a b : nat) :=
    match a, b with
      | 0, _     => 0
      | S a, 0   => S a 
      | S a, S b => a ⊖ b
    end
  where "a ⊖ b" := (myminus a b).

  Fact minus_0 a : a ⊖ 0 = a.
  Proof.
  Admitted.

  Fact plus_minus a b : a ⊕ b ⊖ a = b.
  Proof.
  Admitted.

  Fact minus_diag a : a ⊖ a = 0.
  Proof.
  Admitted.

  Hint Resolve minus_diag : core.

  Fact minus_plus_assoc a b c : a ⊖ b ⊖ c = a ⊖ (b ⊕ c).
  Proof.
  Admitted.

  Fact minus_eq a b : a = b <-> a ⊖ b = 0 /\ b ⊖ a = 0.
  Proof.
  Admitted.

  Fact plus_reg_l a b c : a ⊕ b = a ⊕ c -> b = c.
  Proof.
  Admitted.

  Fact plus_reg_r a b c : a ⊕ c = b ⊕ c -> a = b.
  Proof.
  Admitted.

  Fact plus_eq_0 a b : a ⊕ b = 0 <-> a = 0 /\ b = 0.
  Proof.
  Admitted.

  Fixpoint mymult a b :=
    match a with 
      | 0   => 0
      | S a => b ⊕ a ⊗ b
    end
  where "a ⊗ b" := (mymult a b).

  Fact mult_0_l a : 0 ⊗ a = 0.
  Proof.
  Admitted.

  Fact mult_0_r a : a ⊗ 0 = 0.
  Proof.
    induction a; simpl; f_equal; trivial.
  Qed.

  Hint Resolve plus_comm : core.

  Fact mult_a_Sb a b : a ⊗ S b = a ⊕ a ⊗ b.
  Proof.
  Admitted.

  Fact mult_comm a b : a ⊗ b = b ⊗ a.
  Proof.
  Admitted.

  Fact plus_mult_distr_l a b c : (a ⊕ b) ⊗ c = a ⊗ c ⊕ b ⊗ c.
  Proof.
  Admitted.

  Hint Resolve plus_mult_distr_l : core.

  Fact plus_mult_distr_r a b c : c ⊗ (a ⊕ b)  = c ⊗ a ⊕ c ⊗ b.
  Proof.
  Admitted.

  Fact mult_assoc a b c : a ⊗ b ⊗ c = a ⊗ (b ⊗ c).
  Proof.
  Admitted.

  Fact mult_1_l a : 1 ⊗ a = a.
  Proof.
  Admitted.

  Hint Resolve mult_1_l : core.

  Fact mult_1_r a : a ⊗ 1 = a.
  Proof.
  Admitted.

  Hint Resolve mult_1_r : core.

  Fact mult_minus a b c : a ⊗ (b ⊖ c) = a ⊗ b ⊖ a ⊗ c.
  Proof.
  Admitted.

  Fact mult_eq_0 a b : a ⊗ b = 0 <-> a = 0 \/ b = 0.
  Proof.
  Admitted.

  Fact mult_reg0 a b c : a ⊗ b = a ⊗ c -> a = 0 \/ b = c.
  Proof.
  Admitted.

  Fact mult_reg_l a b c : S a ⊗ b = S a ⊗ c -> b = c.
  Proof.
  Admitted.

  Fact mult_reg_r a b c : a ⊗ S c = b ⊗ S c -> a = b.
  Proof.
  Admitted.

End plus_minus_mult.