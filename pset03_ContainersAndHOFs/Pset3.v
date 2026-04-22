(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 3 *)

Require Import Frap.Frap.
From Stdlib Require Import ZArith.
Require Import Pset3.Pset3Sig.

Module Impl.
  (* In this pset, we will practice two topics:
     1) Polymorphic container types, i.e. types parametrized by types,
        such as "option A", "list A", "tree A", and finally, "bitwise_trie A",
        which combines option and tree to obtain a new useful data structure.
     2) Higher-order functions (HOFs), i.e. functions that take other functions
        as arguments.

     Once again we have posted some general tips for advancing in this lab near
     the bottom of the signature file under "TIPS". Below the tips are a set of
     problem-specific, spoiler hints that will help you with these problems. Try
     only to consult these if you get stuck!
  *)

  (* As usual, the grading rubric for this pset is in Pset3Sig.v. *)

  (** ** Higher-order functions **)

  (* In class, we talked about a few useful functions at the blackboard
   * level of detail, and here is how we can define one of them in Rocq.
   * It's the identity function [id], which just returns its argument
   * without modification: *)
  Definition id {A : Type} (x : A) : A := x.

  (* We also saw [compose], another higher-order function: [compose g f]
   * applies [f] to its input and then applies [g]. Argument order
   * follows the general convention of functional composition in
   * mathematics denoted by the small circle.
   *)
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (* Let's use a small circle to refer to [compose]. This will make our
     goals much more readable.
     It's up to you to decide whether you also want to use the circle notation
     in your definitions or whether you prefer to write "compose".

     Users of VsCode with the VsCoq extension can simply type "\circ" followed by tab
     to insert ∘. *)
  Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

  (* Here are three simple properties of function composition.
     Together, these properties mean that functions with ∘ form
     a “monoid”. *)

  (* Hint: In the following, it might be helpful to use the following fact:
     If two functions return the same value for all inputs, they are the same. *)
  Check @FunctionalExtensionality.functional_extensionality.
  (* Aside: We called it a "fact" above, but logicians disagree about whether
     we should believe this or not -- one philosophical question is
     that even if merge sort and bubble sort return the same result for
     all inputs, they are two different things.
     Therefore, this "fact" is not actually built into Rocq's kernel, but it's
     an axiom written down in the standard library, and if you believe in it,
     you can import it (the Frap library already does so).
     In any case, it is consistent with the rest of Rocq's logic, i.e. by
     assuming this axiom, you will not be able to prove False, so we're safe.*)

  (* Let's make a shorthand for this: *)
  Definition fun_ext := @FunctionalExtensionality.functional_extensionality.

  Lemma compose_id_l : forall A B (f: A -> B),
      id ∘ f = f.
  Proof.
    intros A B f. apply fun_ext. (* use functionalextensionality *)
    intro x. unfold compose. unfold id. reflexivity.
  Qed.

  Lemma compose_id_r : forall A B (f: A -> B),
      f ∘ id = f.
  Proof.
    intros A B f. apply fun_ext. intro x. unfold compose. unfold id. reflexivity.
  Qed.

  Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
      h ∘ (g ∘ f) = h ∘ g ∘ f.
  Proof.
    intros A B C D f g h. unfold compose. reflexivity.
  Qed.

  (* The selfCompose function takes a function and applies this function n times
     to the argument. There are different ways of defining it, but let's
     define it using only [id] and [compose]. *)
  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => f ∘ (selfCompose f n')
    end.

  Lemma selfCompose_reduce {A}: forall (f: A -> A) (n: nat),
      0 < n -> selfCompose f n = f ∘ selfCompose f (n - 1).
  Proof.
    induct n; simpl; intro H; try linear_arithmetic.
    rewrite Nat.sub_0_r. reflexivity.
  Qed.

  (* Here's an example of what [selfCompose] can do:
     If we apply the function that adds 2 to its argument 7 times to the starting
     value 3, we obtain 3 + 7 * 2 = 17. *)
  Example selfCompose_plus1: selfCompose (plus 2) 7 3 = 17. Proof. equality. Qed.

  (* We can also use [selfCompose] to define exponentiation on natural numbers, by
     saying "to raise [base] to the power [e], apply the function that multiplies
     its argument by [base] to [1] [e] times".
     Define [exp] using [selfCompose] and [Nat.mul]. *)
  Definition exp(base e: nat): nat := selfCompose (Nat.mul base) e 1.

  (* Once you define [exp], you can replace [Admitted.] below by [Proof. equality. Qed.] *)
  Lemma test_exp_2_3: exp 2 3 = 8. Proof. equality. Qed.
  Lemma test_exp_3_2: exp 3 2 = 9. Proof. equality. Qed.
  Lemma test_exp_4_1: exp 4 1 = 4. Proof. equality. Qed.
  Lemma test_exp_5_0: exp 5 0 = 1. Proof. equality. Qed.
  Lemma test_exp_1_3: exp 1 3 = 1. Proof. equality. Qed.

  (* And here's another example to illustrate [selfCompose]. Make sure you understand
     why its result is 256. *)
  Example selfCompose_square: selfCompose (fun (x: nat) => x * x) 3 2 = 256. Proof. equality. Qed.

  (** ** Inverse functions **)

  (* Using [compose] and [id], we can write a concise definition of when
     a function [g] is the left inverse of a function [f]: *)
  Definition left_inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := g ∘ f = id.

  (* Here's an example: The function that subtracts two from its argument
     is the left inverse of the function that adds two to its argument. *)
  Example plus2minus2: left_inverse (fun (x: nat) => x + 2) (fun (x: nat) => x - 2).
  Proof.
    unfold left_inverse. unfold compose.
    (* use functional extensionality to get the body of two function *)
    apply fun_ext. intro x. rewrite Nat.add_sub. unfold id. reflexivity.
  Qed.

  (* On the other hand, note that the other direction does not hold, because
     if a subtraction on natural numbers underflows, it just returns 0, so
     there are several [x] for which [x-2] returns 0 (namely 0, 1, and 2),
     so it can't have a left inverse. *)
  Example minus2plus2: ~ left_inverse (fun (x: nat) => x - 2) (fun (x: nat) => x + 2).
  Proof.
    unfold left_inverse. unfold compose.
    (* Give a counter example *)
    intro H.
    pose proof (f_equal (fun f => f 1) H) as H1.
    simpl in H1. discriminate H1.
  Qed.

  (* Let us make the intuition from the previous paragraph more
     concrete, by proving that a function that is not injective
     cannot have a left inverse; or, in other words, that
     functions with left inverses are injective. *)

  (* HINT 1 (see Pset3Sig.v) *)
  Lemma left_invertible_injective {A}:
    forall (f g: A -> A),
      left_inverse f g ->
      (forall x y, f x = f y -> x = y).
  Proof.
    intros f g H. unfold left_inverse in H. unfold compose in H.
    intros x y Hf.
    (* Use f_equal on H, for the function g (f x) *)
    pose proof (f_equal g Hf) as Hx.
    assert (Hfunc: forall a, g (f a) = id a).
    { intro a. simpl. rewrite <- H. reflexivity. }
    rewrite (Hfunc x) in Hx. rewrite (Hfunc y) in Hx. unfold id in Hx.
    exact Hx.
  Qed.

  (* Bonus question (no points): can you prove the reverse;
     i.e., can you prove that all injective functions have left
     inverses? *)

  (* The identity function is the inverse of itself.
     Note: we're using "@" in front of "id" to say "we want to provide all implicit
     type arguments explicitly, because otherwise Rocq would not be able to infer them." *)
  Lemma left_inverse_id: forall A, left_inverse (@id A) (@id A).
  Proof.
    intro A. unfold left_inverse. apply compose_id_l.
  Qed.

  (* A lemma about self compose *)
  Lemma selfCompose_comm{A: Type}: forall (f: A -> A) (n: nat),
      f ∘ (selfCompose f n) = (selfCompose f n) ∘ f.
  Proof.
    induct n; simpl.
    - rewrite compose_id_l. rewrite compose_id_r. reflexivity.
    - rewrite <- compose_assoc. rewrite IHn. reflexivity.
  Qed.

  (* Now we can start proving interesting facts about inverse functions: *)
  (* Here's how to invert the power function: *)
  (* HINT 2 (see Pset3Sig.v) *)
  Lemma invert_selfCompose{A: Type}: forall (f g: A -> A) (n: nat),
      left_inverse f g ->
      left_inverse (selfCompose f n) (selfCompose g n).
  Proof.
    induct n; simpl; intro Hinv. try apply left_inverse_id.
    unfold left_inverse. rewrite compose_assoc. rewrite selfCompose_comm.
    (* change the form of compose *)
    replace (selfCompose g n ∘ g ∘ f) with (selfCompose g n ∘ (g ∘ f))
      by apply compose_assoc.
    unfold left_inverse in Hinv. rewrite Hinv. rewrite compose_id_r. apply IHn.
    apply Hinv.
  Qed.

  (** ** Polymorphic container types *)

  (* First, we'll reproduce some definitions we need from Lecture 2,
     [tree] and [flatten]: *)

  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  (* Bitwise tries are finite maps keyed by lists of Booleans.
   * We will implement a bitwise trie with entries of type [A]
   * by [tree (option A)]. The value at the root of the tree
   * corresponds to the entry for the key [nil : list bool],
   * the left subtree contains entries for those keys that
   * begin with [true], and the right subtree contains entries
   * for those keys that begin with [false].
   *
   * Tries are a common and powerful data structure; you can read
   * more about them at https://en.wikipedia.org/wiki/Trie .
   *)
  Definition bitwise_trie A := tree (option A).

  (* Define [lookup] such that [lookup k t] looks up the
   * map entry corresponding to the key [k : list bool] in the
   * bitwise trie [t : bitwise_trie A].
   *
   * Look at the examples below to get a better sense of what
   * this operation does: the argument [k] is a path, in which
   * [true] means "go left" and [false] means "go right".
   *)
  Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A
    := match t with
       | Leaf => None
       | Node l d r =>
           match k with
           | [] => d
           | true :: tail => lookup tail l
           | false :: tail => lookup tail r
           end
       end.
  Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
  Proof.
    equality.
  Qed.

  Example lookup_example2 : lookup [false; true]
      (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                            = Some 1.
  Proof.
    equality.
  Qed.

  (* [Leaf] represents an empty bitwise trie, so a lookup for
   * any key should return [None].
   *)
  Theorem lookup_empty {A} (k : list bool)
    : lookup k (Leaf : bitwise_trie A) = None.
  Proof.
    equality.
  Qed.

  (* HINT 3 (see Pset3Sig.v) *)

  (* Define an operation to "insert" a key and optional value
   * into a bitwise trie. The [insert] definition should satisfy two
   * properties: one is [lookup_insert] below, which says that if we
   * look up a key [k] in a trie where [(k, v)] has just been inserted,
   * the result should be [v]. The other is that lookups on keys different
   * from the one just inserted should be the same as on the original map.
   *
   * If an entry for that key already exists, [insert] should replace
   * that entry with the new one being inserted. Note that [insert] can
   * be used to remove an entry from the trie, too, by inserting [None]
   * as the value.
   *
   * Hint: it may be helpful to define an auxiliary function
   * that creates a singleton tree (a tree containing a single
   * key-value pair).
   *)
  Definition singleton {A} (v : option A) : bitwise_trie A :=
    Node Leaf v Leaf.

  (* use struct k to give hints to insert to understand terminaiton *)
  Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct k}
    : bitwise_trie A :=
    match k, t with
    | [], Leaf => singleton v
    | [], Node l _ r => Node l v r
    | true :: tail, Leaf => Node (insert tail v Leaf) None Leaf
    | false :: tail, Leaf => Node Leaf None (insert tail v Leaf)
    | true :: tail, Node l d r => Node (insert tail v l) d r
    | false :: tail, Node l d r => Node l d (insert tail v r)
    end.

  Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
  Proof.
    equality.
  Qed.

  Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
  Proof.
    equality.
  Qed.

  Theorem lookup_insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) :
    lookup k (insert k v t) = v.
  Proof.
    induct k; destruct t; simpl; try reflexivity.
    (* use induction to finish all non leaf trie *)
    all: destruct a; simpl; rewrite IHk; reflexivity.
  Qed.

  (* Define an operation to "merge" that takes two bitwise tries and merges
   * them together. The [merge] definition should combine two bitwise tries,
   * preferring map entries from the first bitwise trie when an entry exists
   * for both bitwise tries.
   *
   * The [merge] definition should satisfy three properties: one is
   * [left_lookup_merge], which says that if a trie contains an entry [v] for a
   * key [k], then when this trie is the first trie in a merge with any other
   * trie, then the resulting merged trie also contains an entry [v] for key [k].
   * The other, [lookup_merge_None], says that if the merge of two tries
   * contains no entry for a given key [k], then neither did the two original
   * tries. The final is [merge_selfCompose], which says that if you repeatedly
   * merge one trie with another one or more times, it is the same as merging
   * the tries once.
   *)

  Fixpoint merge {A} (t1 t2 : bitwise_trie A) : bitwise_trie A :=
    match t1, t2 with
    | Leaf, Leaf => Leaf
    | Leaf, Node l d r => Node l d r
    | Node l d r, Leaf => Node l d r
    (* if the first v is None, use the second one *)
    | Node l1 None r1, Node l2 v r2 => Node (merge l1 l2) v (merge r1 r2)
    | Node l1 v r1, Node l2 _ r2 => Node (merge l1 l2) v (merge r1 r2)
    end.

  Lemma merge_example1 :
    merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.
  Proof. equality. Qed.
  Lemma merge_example2 :
    merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.
  Proof. equality. Qed.
  Lemma merge_example3 :
    merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.
  Proof. equality. Qed.

  Theorem left_lookup_merge {A} : forall (t1 t2 : bitwise_trie A) k v,
      lookup k t1 = Some v ->
      lookup k (merge t1 t2) = Some v.
  Proof.
    induct t1; simpl; intros t2 k v H; try discriminate H.
    destruct k; simpl.
    - subst d. destruct t2; simpl; reflexivity.
    - destruct b; simpl; destruct d; destruct t2; simpl;
        try apply IHt1_1; try apply IHt1_2; exact H.
  Qed.

  Theorem lookup_merge_None {A} : forall (t1 t2 : bitwise_trie A) k,
      lookup k (merge t1 t2) = None ->
      lookup k t1 = None /\ lookup k t2 = None.
  Proof.
    induct t1; destruct t2; simpl; intros k H; split; try reflexivity.
    (* the first case is empty tree t1 *)
    { simpl; try reflexivity. destruct k; simpl in H;
        try (destruct b; simpl); exact H. }
    (* The case is first destruct k as empty and tail list, and discriminate H
     * with None lookup. The other cases are trying IHt1_1 and IHt1_2 to discuss
     * all cases are satisfied.
     *)
    all: destruct k; simpl; destruct d; simpl in H; try discriminate H;
      try exact H; try reflexivity; destruct b; simpl; try exact H;
      try first [apply IHt1_1 in H | apply IHt1_2 in H];
      destruct H as [Ht1 Ht2]; try first [exact Ht1 | exact Ht2].
  Qed.

  (* a simple lemma for merge with itself *)
  Lemma merge_identity {A} : forall (t : bitwise_trie A), merge t t = t.
  Proof.
    induct t; simpl.
    all: try (destruct d; rewrite IHt1; rewrite IHt2); reflexivity.
  Qed.

  (* a simple lemma to prove merge once *)
  Lemma merge_once {A} : forall (t1 t2 : bitwise_trie A),
      merge t1 (merge t1 t2) = merge t1 t2.
  Proof.
    induct t1; destruct t2; simpl; try reflexivity.
    - destruct d; simpl; rewrite (merge_identity t1_1);
        rewrite (merge_identity t1_2); reflexivity.
    - destruct d; simpl; rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  Qed.

  (* HINT 5 (see Pset3Sig.v) *)
  Theorem merge_selfCompose {A} : forall n (t1 t2 : bitwise_trie A),
      0 < n ->
      selfCompose (merge t1) n t2 = merge t1 t2.
  Proof.
    induct n; intros t1 t2 Hn0; try linear_arithmetic.
    (* the first case n = 0 is false *)
    (* discuss the n = 1 and n > 1 case *)
    rewrite (selfCompose_reduce (merge t1) (S n) Hn0). simpl. rewrite Nat.sub_0_r.
    assert (Hn: n = 0 \/ n > 0) by linear_arithmetic.
    cases Hn.
    - subst n. simpl. rewrite compose_id_r. reflexivity.
    - apply (IHn t1 t2) in H. unfold compose. rewrite H. apply merge_once.
  Qed.

  (* Define an operation to "mirror" that takes a tree (not necessarily a
   * trie) and returns the mirrored version of the tree.
   *
   * The [mirror] definition should satisfy two properties: one is
   * [mirror_mirror_id], which says that if you mirror a tree twice, it
   * results in the original tree. The other is [flatten_mirror_rev] which
   * states that flattening a mirrored tree is equivalent to reversing the
   * list resulting from the flattening of that same tree.
 *)

  Fixpoint mirror {A} (t : tree A) : tree A :=
    match t with
    | Leaf => Leaf
    | Node l d r => Node (mirror r) d (mirror l)
    end.

  Example mirror_test1 :
    mirror (Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf))) =
    Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf.
  Proof.
    equality.
  Qed.

  Theorem mirror_mirror_id {A} : forall (t : tree A),
      mirror (mirror t) = t.
  Proof.
    induct t; simpl; try (rewrite IHt1; rewrite IHt2); reflexivity.
  Qed.

  Theorem flatten_mirror_rev {A} : forall (t : tree A),
      flatten (mirror t) = rev (flatten t).
  Proof.
    induct t; simpl; try reflexivity.
    (* use some builtin theorem for rev and other list operations *)
    rewrite rev_app_distr. rewrite IHt1. rewrite IHt2. simpl.
    rewrite <- app_assoc. simpl. reflexivity.
  Qed.

  (** ** HOFs on lists and trees **)

  (* Just like we defined [map] for lists, we can similarly define
   * a higher-order function [tree_map] that applies a function on
   * elements to all of the elements in the tree, leaving the tree
   * structure intact.
   *)
  Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
    : tree B :=
    match t with
    | Leaf => Leaf
    | Node l d r => Node (tree_map f l) (f d) (tree_map f r)
    end.

  Example tree_map_example :
    tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
    = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
  Proof.
    equality.
  Qed.

  (* [tree_map_flatten] shows that [map]
   * and [tree_map] are related by the [flatten] function.
   *)
  (* HINT 6 (see Pset3Sig.v) *)
  Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
      flatten (tree_map f t) = map f (flatten t).
  Proof.
    induct t; simpl; try reflexivity.
    (* Use some builtin theorems for map *)
    rewrite map_app. rewrite IHt1. rewrite IHt2. simpl. reflexivity.
  Qed.

  (* This function asserts that a predicate holds over all
     elements of a tree. *)
  Fixpoint tree_forall {A} (P: A -> Prop) (tr: tree A) :=
    match tr with
    | Leaf => True
    | Node l d r => tree_forall P l /\ P d /\ tree_forall P r
    end.

  (* Define a similar function for the [exists] case; that is, define
     a function that asserts that a predicate holds for at least
     one value of a tree. *)
  Fixpoint tree_exists {A} (P: A -> Prop) (tr: tree A) {struct tr} : Prop :=
    match tr with
    | Leaf => False
    | Node l d r => tree_exists P l \/ P d \/ tree_exists P r
    end.

  (* Two sanity checks for your function: *)
  Lemma tree_exists_Leaf {A} (P: A -> Prop):
    ~ tree_exists P Leaf.
  Proof.
    equality.
  Qed.

  Lemma tree_forall_exists {A} (P: A -> Prop):
    forall tr, tr <> Leaf -> tree_forall P tr -> tree_exists P tr.
  Proof.
    destruct tr; simpl; intro H; try easy. intro HAll.
    destruct HAll as [Hl [Hd Hr]].
    right. left. exact Hd.      (* simply choose the middle case *)
  Qed.

  (* What does the following theorem mean? Write a short
     explanation below. *)

  (* If a predicate holds for all data in tree, for every data d that exists in
     the tree, the predicate P d holds. *)
  Lemma tree_forall_sound {A} (P: A -> Prop):
    forall tr, tree_forall P tr ->
          forall d, tree_exists (fun d' => d' = d) tr ->
               P d.
  Proof.
    intros tr HAll d HExists. induct tr; try easy. simpl in HAll.
    destruct HAll as [Hl [Hd Hr]]. simpl in HExists.
    (* discuss by HExists cases *)
    destruct HExists as [HEl | [HEd | HEr]].
    - apply IHtr1; [ exact Hl | exact HEl ].
    - rewrite HEd in Hd. exact Hd.
    - apply IHtr2; [ exact Hr | exact HEr ].
  Qed.

  Lemma tree_forall_conjuction {A} (P: A -> Prop) (Q: A -> Prop) :
    forall tr, tree_forall (fun x => P x /\ Q x) tr ->
          tree_forall P tr /\ tree_forall Q tr.
  Proof.
    intros tr HAll. induct tr; simpl; try easy. simpl in HAll.
    destruct HAll as [Hl [[HPd HQd] Hr]]. repeat split.
    all: try (apply IHtr1; exact Hl); try exact HPd;
      try (apply IHtr2; exact Hr); try exact HQd.
  Qed.

  (** ** Binary search trees **)

  (* Like tries, binary search trees (BSTs) are a popular way to
     store structured data.  We will use them to implement a set
     data type, with methods to insert a new element, remove an
     existing element, and check whether the set contains a
     given element.

     Proving a complete BST implementation in a week is a bit
     too much at this point in the term, so we will start this
     week with definitions and correctness proofs for membership
     tests. *)

  (* BSTs will allow us to illustrate an important idea: data
     abstraction, the general principle that data structures
     should expose interfaces that abstract over (i.e., hide)
     the complexities of their internal representation.  Data
     abstraction is a key ingredient of modularity in most
     programming languages.  (We have a lecure on it coming in
     a week.)

     Concretely, this means that client code using our set
     library built with BSTs shouldn't have to think about
     binary trees at all: instead, we'll write all specs in
     terms of abstract sets, representing a set of values of
     type [A] using the type [A -> Prop].
   *)


  (* This makes our numeric notations refer to integers instead of nats.
     We use integers in this assignment since they'll work more nicely
     with monotonicity later. Don't worry, [linear_arithmetic] can handle
     integers as well as nats.
   *)
  Local Open Scope Z_scope.
  Check 1.

  Fixpoint bst (tr : tree Z) (s : Z -> Prop) :=
    match tr with
    | Leaf => forall x, ~ (s x) (* s is empty set *)
    | Node l d r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (* First, let's get familiar with this definition by proving
     that [bst tr s] implies that all elements of [tr] have
     property [s].  Recall that you may need to prove a stronger
     lemma than the one we show here. *)

  (* If you want to apply a lemma that binds terms that don't appear
     in the goal, Rocq can't infer what those terms should be. You
     may need to give them explicitly when you apply the lemma.
     A potentially helpful tip: you can use the `apply` tactic like so:

                   apply <theorem name> with (<x>:=<term>)

     where <x> is a forall-bound name in theorem statement you're
     trying to apply and <term> is what you what to fill in for <x>.
   *)

  (* HINT 7 (see Pset3Sig.v) *)
  Lemma bst_implies:
    forall tr s, bst tr s -> tree_forall s tr.
  Proof.
    intros tr s Hbst. induct tr; simpl; try easy; simpl in Hbst;
      destruct Hbst as [Hd [Hl Hr]]. repeat split.
    - apply IHtr1 in Hl. apply tree_forall_conjuction in Hl as [Hs _]. exact Hs.
    - exact Hd.
    - apply IHtr2 in Hr. apply tree_forall_conjuction in Hr as [Hs _]. exact Hs.
  Qed.

  (* Helper: from a bst subtree hypothesis, extract one component of
     the conjunction in tree_forall (uses bst_implies + tree_forall_conjuction). *)
  Ltac bst_forall_extract H :=
    apply bst_implies in H; apply tree_forall_conjuction in H as [? ?]; assumption.

  (* Next, let's prove that elements of the left subtree of a
     BST node are less than the node's data and that all
     elements of the right subtree are greater than it.  This
     should be a consequence of the lemma you proved for
     [bst_implies]; our solution does not use induction here. *)

  Lemma bst_node_ordered :
    forall l d r s,
      bst (Node l d r) s ->
      tree_forall (fun x => x < d) l /\ tree_forall (fun x => d < x) r.
  Proof.
    intros l d r s H. simpl in H. destruct H as [Hd [Hl Hr]]. split;
      [ bst_forall_extract Hl | bst_forall_extract Hr ].
  Qed.

  (* Here is another convenient property: if two sets are the
     same, then a bst representing one also represents the
     other.  Hint: [rewrite] and related tactics can be used
     with logical equivalence, not just equality! *)

  (* Helper: given bst tr P and (forall x, P x <-> Q x), produce bst for
     a subtree whose predicate is P /\ R, lifting the iff to Q /\ R. *)
  Ltac bst_iff_subtree IH HPQ H :=
    let HPQ' := fresh "HPQ'" in
    assert (HPQ' : forall x : Z, _ <-> _) by (intro; apply and_iff_compat_r, HPQ);
    exact (IH _ _ H HPQ').

  Lemma bst_iff : forall tr P Q,
      bst tr P ->
      (forall x, P x <-> Q x) ->
      bst tr Q.
  Proof.
    intros tr P Q HBP HPQ. induct tr; simpl.
    { intro x. specialize (HPQ x). simpl in HBP. specialize (HBP x). intro.
      apply HPQ in H. apply HBP. exact H. }

    repeat split; simpl in HBP; destruct HBP as [Hd [Hl Hr]].
    - apply HPQ. exact Hd.
    (* extend the equivalence to subtree predicates P /\ (< d) and P /\ (d <) *)
    - bst_iff_subtree IHtr1 HPQ Hl.
    - bst_iff_subtree IHtr2 HPQ Hr.
  Qed.

  (* Let's prove something about the way we can map over binary search
     trees while preserving the bst structure. In order to preserve the
     ordered structure of the data in a BST, the function that is mapped over
     must be strictly monotonically increasing. This means that if "f" is a
     strictly monotone-increasing function, and x and y are numbers where
     x is less than y, then f x must also be less than f y.

     The resulting predicate of the mapped tree is then recharacterized as
     a property that holds for all and only the mapped values of the
     original tree.
     *)

  (* Common Leaf case: an empty bst mapped through an invertible function
     still represents the empty set. *)
  Lemma bst_map_leaf : forall (P Q : Z -> Prop) (f g : Z -> Z),
      (forall x, ~ P x) ->
      left_inverse g f ->
      (forall x, P x <-> Q (f x)) ->
      forall x, ~ Q x.
  Proof.
    intros P Q f g HBP Hinv HPQ x HQ.
    apply (HBP (g x)). apply (HPQ (g x)).
    unfold left_inverse, compose in Hinv.
    pose proof (f_equal (fun h => h x) Hinv) as Hpt. cbn in Hpt.
    rewrite Hpt. exact HQ.
  Qed.

  Theorem bst_strict_monotone_increasing : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x < f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (tree_map f tr) Q.
  Proof.
    intros tr P Q f g. induct tr.
    - intros HBP Hinv Hmono HPQ. simpl in HBP |-*.
      exact (bst_map_leaf P Q f g HBP Hinv HPQ).
    - intros HBP Hinv Hmono HPQ. simpl in HBP |-*. destruct HBP as [Hd [Hl Hr]].
      repeat split.
      + apply HPQ. exact Hd.
      (* lift the predicate equivalence through monotonicity for each subtree *)
      + assert (HPQl: forall x : Z, P x /\ x < d <-> Q (f x) /\ f x < f d).
        { intro x; rewrite (Hmono x d); apply and_iff_compat_r; now apply HPQ. }
        apply (IHtr1 _ _ f g Hl Hinv Hmono HPQl).
      + assert (HPQr: forall x : Z, P x /\ d < x <-> Q (f x) /\ f d < f x).
        { intro x; rewrite (Hmono d x); apply and_iff_compat_r; now apply HPQ. }
        apply (IHtr2 _ _ f g Hr Hinv Hmono HPQr).
  Qed.

  (* Monotone functions can be characterized as monotone increasing or
     monotone decreasing. In the case of a strictly monotonically decreasing
     function we have the property that for a function f, if x is less than y
     then f y is less than f x.

     Let's prove the result of mapping a strictly monotonically decreasing
     function over a binary search tree. This will be similar to the mapping
     a strictly monotone-increasing function over a tree, only now to preserve
     the ordered property the resulting tree must be mirrored.
     *)

  (* Helper: rewrite x < y <-> f x > f y into x < y <-> f y < f x *)
  Local Lemma gt_lt_flip : forall f,
      (forall x y : Z, x < y <-> f x > f y) ->
      (forall x y : Z, x < y <-> f y < f x).
  Proof. intros f Hm x y. rewrite (Hm x y). apply Z.gt_lt_iff. Qed.

  Theorem bst_strict_monotone_decreasing_mirror : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x > f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (mirror (tree_map f tr)) Q.
  Proof.
    intros tr P Q f g. induct tr.
    - intros HBP Hinv Hmono HPQ. simpl in HBP |-*.
      exact (bst_map_leaf P Q f g HBP Hinv HPQ).
    - intros HBP Hinv Hmono HPQ. simpl in HBP |-*. destruct HBP as [Hd [Hl Hr]].
      pose proof (gt_lt_flip f Hmono) as Hmono'.
      repeat split.
      + apply HPQ. exact Hd.
      (* mirror swaps subtrees: right subtree (d < x) maps to left (f x < f d) *)
      + assert (HPQr: forall x : Z, P x /\ d < x <-> Q (f x) /\ f x < f d).
        { intro x; rewrite (Hmono' d x); apply and_iff_compat_r; now apply HPQ. }
        apply (IHtr2 _ _ f g Hr Hinv Hmono HPQr).
      (* left subtree (x < d) maps to right (f d < f x) *)
      + assert (HPQl: forall x : Z, P x /\ x < d <-> Q (f x) /\ f d < f x).
        { intro x; rewrite (Hmono' x d); apply and_iff_compat_r; now apply HPQ. }
        apply (IHtr1 _ _ f g Hl Hinv Hmono HPQl).
  Qed.

  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)

  Fixpoint bst_member (a: Z) (tr: tree Z) : bool :=
    match tr with
    | Leaf => false
    | Node lt v rt =>
      match compare a v with
      | Lt => bst_member a lt
      | Eq => true
      | Gt => bst_member a rt
      end
    end.

  Lemma member_bst : forall tr s a,
      bst tr s -> bst_member a tr = true <-> s a.
  Proof.
    intros tr s a Hb. induct tr; simpl.
    { split; intro H; try discriminate H.
      simpl in Hb. apply Hb in H. easy. }
    (* Lt/Gt cases: the compare constraint makes s a equivalent to
       the subtree predicate (s a /\ ordering), so rewrite and recurse. *)
    cases (compare a d); simpl in Hb |-*.
    - destruct Hb as [_ [Hb _]].
      assert (Hl: s a <-> (fun x : Z => s x /\ x < d) a) by (split; intro; easy).
      rewrite Hl. apply (IHtr1 _ a Hb).
    - destruct Hb as [Hd _]. subst a. easy.
    - destruct Hb as [_ [_ Hb]].
      assert (Hr: s a <-> (fun x : Z => s x /\ d < x) a) by (split; intro; easy).
      rewrite Hr. apply (IHtr2 _ a Hb).
  Qed.

  (* Next week, we will look at insertion and deletion in
     BSTs. *)

  Local Close Scope Z_scope.

  (** ****** Optional exercises ****** *)

  (* Everything below this line is optional! *)

  (* You've reached the end of the problem set. Congrats!
   *
   * [fold] is a higher-order function that is even more general
   * than [map]. In essence, [fold f z] takes as input a list
   * and produces a term where the [cons] constructor is
   * replaced by [f] and the [nil] constructor is replaced
   * by [z].
   *
   * [fold] is a "right" fold, which associates the binary operation
   * the opposite way as the [fold_left] function from Rocq's
   * standard library.
   *)
  Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
           (xs : list A) : B :=
    match xs with
    | nil => b_nil
    | cons x xs' => b_cons x (fold b_cons b_nil xs')
    end.

  (* For instance, we have
         fold plus 10 [1; 2; 3]
       = 1 + (2 + (3 + 10))
       = 16
   *)
  Example fold_example : fold plus 10 [1; 2; 3] = 16.
  Proof.
    simplify.
    equality.
  Qed.

  (* Prove that [map] can actually be defined as a particular
   * sort of [fold].
   *)
  Lemma map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
      map f xs = fold (fun x ys => cons (f x) ys) nil xs.
  Proof.
  Admitted.

  (* Since [fold f z] replaces [cons] with [f] and [nil] with
   * [z], [fold cons nil] should be the identity function.
   *)
  Theorem fold_id : forall {A : Type} (xs : list A),
      fold cons nil xs = xs.
  Proof.
  Admitted.

  (* If we apply [fold] to the concatenation of two lists,
   * it is the same as folding the "right" list and using
   * that as the starting point for folding the "left" list.
   *)
  Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                               (xs ys : list A),
      fold f z (xs ++ ys) = fold f (fold f z ys) xs.
  Proof.
  Admitted.

  (* Using [fold], define a function that computes the
   * sum of a list of natural numbers.
   *)
  Definition sum : list nat -> nat. Admitted.

  Example sum_example : sum [1; 2; 3] = 6.
  Proof.
  Admitted.

  (* Using [fold], define a function that computes the
   * conjunction of a list of Booleans (where the 0-ary
   * conjunction is defined as [true]).
   *)
  Definition all : list bool -> bool. Admitted.

  Example all_example : all [true; false; true] = false.
  Proof.
  Admitted.


  (* The following two theorems, [sum_append] and [all_append],
   * say that the sum of the concatenation of two lists
   * is the same as summing each of the lists first and then
   * adding the result.
   *)
  Theorem sum_append : forall (xs ys : list nat),
      sum (xs ++ ys) = sum xs + sum ys.
  Proof.
  Admitted.


  Theorem all_append : forall (xs ys : list bool),
      all (xs ++ ys) = andb (all xs) (all ys).
  Proof.
  Admitted.

  (* Using [fold], define a function that composes a list of functions,
   * applying the *last* function in the list *first*.
   *)
  Definition compose_list {A : Type} : list (A -> A) -> A -> A. Admitted.

  Example compose_list_example :
    compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
  Proof.
  Admitted.


  (* Show that [sum xs] is the same as converting each number
   * in the list [xs] to a function that adds that number,
   * composing all of those functions together, and finally
   * applying that large composed function to [0].
   * Note that function [plus], when applied to just one number as an
   * argument, returns a function over another number, which
   * adds the original argument to it!
   *)
  Theorem compose_list_map_add_sum : forall (xs : list nat),
      compose_list (map plus xs) 0 = sum xs.
  Proof.
  Admitted.
End Impl.

Module ImplCorrect : Pset3Sig.S := Impl.

(* Authors:
 * Ben Sherman
 * Adam Chlipala
 * Samuel Gruetter
 * Clément Pit-Claudel
 * Amanda Liu
 *)
