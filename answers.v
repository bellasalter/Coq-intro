(** Answers to Exercises **)
(** Note that these answers are just how I chose to complete the proofs. 
If Coq allows you to move past Qed., your solution works too! This is just
to help if you get stuck.**)

Module mod1.
(** 2 Proof Tactics **)

(** Exercise 2.1: Prove Modus Ponens.**)
Theorem modus_ponens: (forall P Q:Prop, ((P->Q) /\ P ) -> Q).
Proof.
  intros.
  destruct H.
  apply H.
  apply H0.
Qed.

(**############################**)

(** Exercise 2.2: Write the correct syntax and prove the principle of hypothetical 
syllogism.**)
Theorem hyp_syllogism: (forall A B C:Prop, ((A->B) /\ (B->C))->(A->C)).
Proof.
  intros.
  destruct H as [A_implies_B B_implies_C]. (** notice that this new argument allows naming**)
  apply B_implies_C.
  apply A_implies_B.
  apply H0.
Qed.

(** Alternatively, either of these tactics could be solved using only the 'tauto' tactic.**)


(**----------------------------------------------------------------------------------------------**)


(** 3 Defining Types**)

(** Exercise 3.1 : Create a boolean type and the not, or, and, and xor functions. **)
Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Not function **)
Definition not_a (a : bool) :=
  match a with
  | true => false
  | false=> true
  end. 

(** Or function **)
Definition a_or_b (a : bool) (b : bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

(** Use these testcases to make sure yours works correctly!**)
Example true_or_false : (a_or_b true false = true).
Proof. reflexivity. Qed.

Example true_or_true : (a_or_b true true = true).
Proof. reflexivity. Qed.

Example false_or_false : (a_or_b false false = false).
Proof. reflexivity. Qed.

(** And function  **)
Definition a_and_b (a: bool) (b: bool) :=
  match a, b with 
  | true, true => true
  | _, _ => false (** Note: this _ is a wildcard variable, it basically says 'anything else'**)
  end.

Example true_and_false : (a_and_b true false = false).
Proof. reflexivity. Qed.

Example true_and_true : (a_and_b true true = true).
Proof. reflexivity. Qed.

Example false_and_false : (a_and_b false false = false).
Proof. reflexivity. Qed.

(** XOR function **)
Definition a_xor_b (a : bool) (b : bool) :=
  match a with 
  | true => not_a b
  | false => b
  end.

Example true_xor_false : (a_xor_b true false = true).
Proof. reflexivity. Qed.

Example true_xor_true : (a_xor_b true true = false).
Proof. reflexivity. Qed.

Example false_xor_false : (a_xor_b false false = false).
Proof. reflexivity. Qed.

(**############################**)

(** Exercise 3.2 : Define a function that subtracts natural numbers and check all 
base cases. **)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.


Fixpoint minus (n : nat) (m : nat) : nat :=
  match n with 
  | O => O
  | S n' => match m with
            | O => n
            | S O => n'
            | S m' => S(minus n m')
            end
  end.

Example O_minus : (minus O (S (S O)) = O).
Proof. reflexivity. Qed.

End mod1.


(**----------------------------------------------------------------------------------------------**)


(** 4 Lists**)

(** Exercise 4.1 : Create a function that adds every element in a list together and check some cases. **)
Fixpoint sum_all (l :list nat) : nat :=
  match l with
  | nil => 0
  | a :: bs => a + sum_all bs
end.

Example sum_all_to_3 : (sum_all [1;2;3] = 6).
Proof. reflexivity. Qed.

Example sum_empty : (sum_all [] = 0).
Proof. reflexivity. Qed.

(**############################**)

(** Exercise 4.2 : Create a function that makes a list of the first n exponents of 2. **)
Fixpoint n_exps (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => 2^(n') :: n_exps n'
  end. 

Example n_exps_3 : (n_exps 3 = [4;2;1]).
Proof. reflexivity. Qed.

Example n_exps_0 : (n_exps 0 = []).
Proof. reflexivity. Qed.






