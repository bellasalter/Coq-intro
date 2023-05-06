
(** CSC 244 Honors Project**)
(** Author: Bella Salter **)
(** This is a basic introduction to Coq for computer science students, summing up all that I learned throughout 
the semester. **)

(** 1 Proof Syntax**)
Module Module1.
(** Welcome to Coq! Let's start with our first theorem and prove it. We'll prove that A implies A 
for any proposition. **)
Theorem first_thm : (forall A : Prop, A -> A).
(** Now, let's begin the proof.**)
Proof.
  intros. 
  exact H.
Qed.
(** As you process the proof line by line, notice that you will see 
this format:
  1 goal
  A : Prop
  H : A
  ______________________________________(1/1)
  A

Above the line, you can see the types of each parameter. Below the line is 
the current subgoal, A. We can see this more clearly by separating the intros.**)
Theorem first_thm_2 : (forall A : Prop, A -> A).
Proof.
  intros A. 
  intros H.
  exact H.
Qed.
(** Now, you can watch the subgoal transform as you run each intro statement. The subgoal is the most important thing
to keep track of in the proof, since it is the current state of the proof. It tells you where you are in the proof, so 
that you know where you need to go for it to be complete. **)
(** Also note the 'Qed.' statement at the end of the proof. This states that we are done proving
this theorem, and Coq will not let it be incomplete. In order to stifle any errors about proofs in
progress, simply write 'Admitted.' temporarily instead. **)


(**----------------------------------------------------------------------------------------------**)


(** 2 Proof Tactics **)

(** Above, we used intros to introduce each part of our theorem. Then, we used
exact to prove this theorem. This is an example of a proof technique. In particular,
exact is used when the term that proves the subgoal is already present. In this case,
we have the subgoal A, and our proposition H proves this because it defines that A is 
a proposition. **)

(** Reflexivity is another helpful simple tactic. It solves the goal if it is already 
an equality. **)
Theorem reflexive_thm: ( true = true ).
Proof.
  intros.
  reflexivity.
Qed.
(** It may seem trivial, but it is very useful near the end of proofs or for proving
examples, which we will cover later on. **)

(** Auto is a tactic that will solve many trivial proofs. It can also be used to solve the 
theorem above. Additionally, the tactic 'trivial' can be used to solve many of these, but auto is generally
able to solve more goals. **)
Theorem reflexive_thm2: ( true = true ).
Proof.
  auto.
Qed.

(** Destruct breaks down a hypothesis consisting of an and/or statement, and apply
uses implications to change the subgoal. Here, we use both of them for a more complex proof. Be sure to take note
of the syntax for defining two propositions to use in the hypothesis.**)
Theorem destruct_thm: (forall A B :Prop, (A /\ B) -> B).
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

(** The 'exact' tactic allows us to solve the goal when Coq essentially already knows the answer. If
the subgoal has gotten extremely simple, such as simply the proposition A, this can help. Also, note the use
of 'left', a tactic that separates (A \/ ~A) into A. **)
Theorem exact_thm: (forall A:Prop, A->(A \/ ~A)).
Proof.
  intros.
  left.
  exact H.
Qed.

(** Try it yourself!
We will uncover more complex proof tactics later on as we explore defining inductive types, but for now, 
here are a few exercises that can be tricky. **)

(** Exercise 2.1: Prove Modus Ponens:**)
Theorem modus_ponens: (forall P Q:Prop, ((P->Q) /\ P ) -> Q).
Proof.
Admitted.
(**fill in and change 'Admitted.' to 'Qed.'**)
(** Exercise 2.2: Write the correct syntax and prove the principle of hypothetical syllogism.**)
(**fill in here!**)


(**----------------------------------------------------------------------------------------------**)


(** 3 Defining Types**)

(** Now that we have gone over the basics, we can start defining our first types!**)
(** We will use months of the year as a simple example. First, we are going to tell Coq all of the things 
that are months.**)
Inductive month : Type :=
  | january : month
  | february : month
  | march : month
  | april : month
  | may : month
  | june : month
  | july : month
  | august : month
  | september : month
  | october : month
  | november : month
  | december : month.
(** Make note of this syntax, we defined month as a Type at the Inductive statement, and proceeded to verify
everything that would be months. Notice the period at the last definition, rather than an end statement.**)

(** Now, we can define a pattern-matching function on this new type! We will determine the next month from the input.**)
Definition next_month (this_month:month) : month :=
  match this_month with
  | january  => february
  | february => march
  | march => april
  | april => may
  | may => june
  | june => july
  | july => august
  | august => september
  | september => october
  | october => november
  | november => december
  | december => january
  end.
(** Notice the syntax for this definition. We are creating a new type, month. For the definition statement, we have:
  Definition definition_title (input_value:input_type) : output_type :=
and the input_value is used for the pattern matching.**)

(** The following is an Example. It allows us to confirm things about the function-- think edge cases and such. 
For now, we will just use it to confirm that the next month after february is indeed march.**)
Example next_month_feb: (next_month february = march).
(** Note that this example is like a theorem, but is actually an assertion, like in other programming languages. 
Here, we still need to prove it! Luckily, it is a simple proof.**)
Proof. reflexivity. Qed.
(** To determine the output of a function for a value, rather than assuming it is what we expect, we can use 
Eval.**)
Eval compute in next_month march.
(** Notice that the output not only gives the result of the function, but it also gives its type.**)

(** We can also define the set of natural numbers using a similar method. Coq does not come with anything, so even
integer addition cannot be done without importing or defining it yourself. Here, we will do the latter.**)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
(** Notice now that one of our definitions for the type includes an "implies" sign. This makes sense when thinking
about how the set of natural numbers itself is constructed; 0 is a natural number, and implies that 1 is a natural
number, and so on. This is essentially hypothetical syllogism and also represents the backbone behind induction. 
S creates a new natural number so that if n is a number, then S(n) is also. This will make more sense as we do 
functions using this type. **)

Definition next_number (n: nat) : nat :=
  match n with
  | n' => S n'
  end.
(** Notice the pattern matching in this definition. We match n with n', which is sort of a placeholder for n. 
Then, we apply S to get the next natural number.**)
Eval compute in next_number (S O).
(** This evaluation statement evaluates the definition for the number S O. For now, it is easier to think of
S as a function that adds 1 to the number, but in reality it creates the next number. So, for other types that
do not have differences of 1, S will need to be considered differently. We evaluated next_number simply for the 
number after 0(denoted by O since it is simply the first of that type), and it returned the number after the number
after 0, known to us as 2. **)

(** We can further define other functions on the natural numbers using inductive reasoning.**)
Definition num_before (n: nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
(** Notice here that we are doing something similar to recursive coding in other CS courses. We have our
base case, O, and we have all other cases, (S n'). (S n') also covers the case for if n is (S O), since n'
would just be O. We can prove our base case using Example.**)
Example num_before_O : (num_before (S O) = O).
Proof. reflexivity. Qed.


(** We can also do functions on multiple numbers. This needs to be recursive, since once again, we can't
simply add the numbers together. **)
Fixpoint add_numbers (n : nat) (m : nat) : nat :=
  match n, m with
  | O, O => O
  | O, S m' => m
  | S n', O => n
  | S n', S m' => add_numbers n' m'
  end.
(** Note that here we use Fixpoint, rather than Definition, so that we can recursively use the function. **)
(** We can also use nested matching for this function. **)
Fixpoint add_numbers2  (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => match m with
            | O => n
            | S m' => S ( S (add_numbers2 n' m'))
            end
  end.
(** We can use other functions in a new function, too! Let's use the adding numbers function to define a 
function to sum all of the numbers up to n. **)
Fixpoint add_to_n (n : nat) :=
  match n with
  | O => O 
  | S n' => add_numbers (S n') (add_to_n n')
  end.
(** Exercise 3.1 : Create a boolean type and the or, and, and xor functions. **)
(** Exercise 3.2 : Define a function that subtracts natural numbers and check all base cases. **)
(** Exercise 3.3 : Define a function that finds the factorial of a number. Hint: define a multiplication
function first!**)
End Module1.

(**----------------------------------------------------------------------------------------------**)


(** 4 Lists**)

(** Yes, lists are also in Coq! First, we need to import some helpful libraries. **)
Module Module2. (** Notice these modules. This is to isolate our environment, so
that the nat type we defined above does not interfere with arithmetic operations here. **)

Require Import List.
Require Import Arith.
Import ListNotations.
Require Import Bool.
(** First, the syntax for a list is:
  a :: b :: c :: nil
where ::(called cons) appends to the front of the list. This is the same as having the list [a, b, c].**)
(** Let's begin by doing some simple pattern matching for a list. **)
Definition head (l : list nat) : nat :=
  match l with
  | nil => O
  | a :: bs => a
  end.

Check 1 :: nil.
Definition tail (l : list nat) : nat :=
  match l with
  | nil => O
  | a :: bs => a
end.

(** Notice that the bs can denote anything in the second case; it can represent nil or any number of 
elements, then nil. The most important thing is that we have isolated the first element. Now, we will
create a list of the integers until n. Here, we need a fixpoint. This allows recursion in our function. **)

Fixpoint create_list (n:nat) : list nat :=
  match n with
  | O => nil
  | S n' => n :: create_list n'
end.

Eval compute in create_list 4.
Eval compute in create_list 0.

(** We can also create a list of the first n even numbers in descending order. **)
Fixpoint create_evens (n:nat) : list nat :=
  match n with
  | O => nil
  | S n' => (2*(S n')) :: (create_evens n') 
end.

Example first_3 : (create_evens 3 = [6; 4; 2]).
Proof. reflexivity. Qed.

Example first_0 : (create_evens 0 = []).
Proof. reflexivity. Qed.
(** Notice the change in notation here, the [6; 4; 2] and [] are allowed due to 
our ListNotations import. **)

(** Exercise 4.1 : Create a function that adds every element in a list together and check some cases. **)
(** Exercise 4.2 : Create a function that makes a list of the first n exponents of 2. **)

End Module2.
(**----------------------------------------------------------------------------------------------**)

(** Index of Common Errors & Check **)
(** Coq is very specific about types! This can cause a lot of errors, especially with inductive types. 
You can use the Check function to determine the type of something. **)
Check  S O.
(** This should return nat, indicating that S O is indeed type nat that we previously defined. **)
Check S.
(** It may be surprising that this returns nat->nat, but remember that S is a constructor, not a natural
number itself! It simply acts on natural numbers and returns one, so that is why it is type nat -> nat.**)
Check add_numbers.
(** Notice that add_number is nat->nat->nat, since it has two parameters.**)
(** These types of checks can often resolve errors such as;
The term "S" has type "nat -> nat"
while it is expected to have type "nat".
This can mean that you simply need some parentheses around your inductive term, or you need to change
what you are passing into a function.  **)
(** Reaching an error such as:
  The reference n was not found in the current environment.
  The reference add_numbers2 was not found in the current environment.
usually refers to a syntactical error such as writing Definition instead of Fixpoint, or placing a colon
where they should not be present. **)
  
