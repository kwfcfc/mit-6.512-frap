(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 4 *)

(** * Correctness of Binary Search Trees (BSTs) *)

(* This week we'll continue proving the correctness of a binary-search-tree implementation.
 * BSTs are a famous data structure for finite sets, allowing fast (log-time)
 * lookup, insertion, and deletion of items. (We omit the rebalancing heuristics
 * needed to achieve worst-case log-time operations, but you will prove the
 * correctness of rotation operations these heuristics use to modify the tree.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined by relating them to operations on functional sets. *)

(* Since almost all of this assignment's points come from two proofs,
 * make sure to break out any useful facts you come across into helper lemmas
 * to maximize your partial credit in the case that you don't finish one of the proofs. *)

(* As usual, a set of spoiler-containing hints to help you along when you
 * get stuck with certain pset questions has been provided at the bottom of
 * the signature file! *)

Require Import Frap Pset4.Pset4Sig.

(* We will study binary trees of natural numbers only for convenience.
   Almost everything here would also work with an arbitrary type
   [t], but with [nat] you can use [linear_arithmetic] to prove
   goals about ordering of multiple elements (e.g., transitivity). *)
Local Notation t := nat.

Module Impl.
  (* Trees are an inductive structure, where [Leaf] doesn't have any items,
   * whereas [Node] has an item and two subtrees. Note that a [tree] can
   * contain nodes in arbitrary order, so not all [tree]s are valid binary
   * search trees. *)

  (* (* Imported from Sig file: *)
  Inductive tree :=
  | Leaf (* an empty tree *)
  | Node (d : t) (l r : tree).
  *)
  (* Then a singleton is just a node without subtrees. *)
  Definition Singleton (v: t) := Node v Leaf Leaf.

  (* [bst] relates a well-formed binary search tree to the set of elements it
     contains. Note that an invalid tree with misordered elements is not a valid
     representation of any set. All operations on a binary tree are specified
     in terms of how they affect the set that the tree represents. That
     set is encoded as function that takes a [t] and returns the proposition "[t]
     is in this set". *)
  Fixpoint bst (tr : tree) (s : t -> Prop) :=
    match tr with
    | Leaf => forall x, not (s x) (* s is empty set *)
    | Node d l r =>
        s d /\
        bst l (fun x => s x /\ x < d) /\
        bst r (fun x => s x /\ d < x)
    end.

  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)
  Fixpoint member (a: t) (tr: tree) : bool :=
    match tr with
    | Leaf => false
    | Node v lt rt =>
      match compare a v with
      | Lt => member a lt
      | Eq => true
      | Gt => member a rt
      end
    end.

  (* Here is a typical insertion routine for BSTs.
   * From a given value, we recursively compare the value with items in
   * the tree from the root, until we find a leaf whose place the new value can take. *)
  Fixpoint insert (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Singleton a
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (insert a lt) rt
      | Eq => tr
      | Gt => Node v lt (insert a rt)
      end
    end.

  (* Helper functions for [delete] below. The *main task* in this pset
     is to understand, specify, and prove these helpers. *)
  Fixpoint rightmost (tr: tree) : option t :=
    match tr with
    | Leaf => None
    | Node v _ rt =>
      match rightmost rt with
      | None => Some v
      | r => r
      end
    end.

  Definition is_leaf (tr : tree) : bool :=
    match tr with Leaf => true | _ => false end.

  Fixpoint delete_rightmost (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      if is_leaf rt
      then lt
      else Node v lt (delete_rightmost rt)
    end.

  Definition merge_ordered lt rt :=
    match rightmost lt with
    | Some rv => Node rv (delete_rightmost lt) rt
    | None => rt
    end.

  (* [delete] searches for an element by its value and removes it if it is found.
     Removing an element from a leaf is degenerate (nothing to do), and
     removing the value from a node with no other children (both Leaf) can be done
     by replacing the node itself with a Leaf. Deleting a non-leaf node is
     substantially trickier because the type of [tree] does not allow for a Node
     with two subtrees but no value -- merging two trees is nontrivial. The
     implementation here removes the value anyway and then moves the rightmost
     node of the left subtree up to replace the removed value. This is equivalent
     to using rotations to move the value to be removed into leaf position and
     removing it there. *)
  Fixpoint delete (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (delete a lt) rt
      | Eq => merge_ordered lt rt
      | Gt => Node v lt (delete a rt)
      end
    end.

  (* Here is a lemma that you will almost definitely want to use. *)
  Example bst_iff : forall tr P Q, bst tr P -> (forall x, P x <-> Q x) -> bst tr Q.
  Proof.
    induct tr; simplify.
    { rewrite <- H0. apply H with (x:=x). }
    rewrite H0 in H.
    propositional.
    { apply IHtr1 with (P:=(fun x : t => (fun d => P x /\ x < d) d));
        propositional; cycle 1.
      { rewrite H0; trivial. }
      { rewrite <-H0; trivial. } }
    { apply IHtr2 with (P:=(fun x : t => (fun d => P x /\ d < x) d));
      propositional; cycle 2.
      { rewrite <-H0; trivial. }
      { rewrite H0; trivial. } }
  Qed.

  (* You may want to call these tactics to use the previous lemma. *)
  (* They are just a means to save some typing of [apply ... with]. *)
  Ltac use_bst_iff known_bst :=
    lazymatch type of known_bst with
    | bst ?tree2 ?set2 =>
        lazymatch goal with
        | |- bst ?tree1 ?set1 =>
            apply bst_iff with (P:=set2) (Q := set1);
            lazymatch goal with
            |- bst tree2 set2 => apply known_bst
            | _ => idtac
            end
        end
    end.

  Ltac use_bst_iff_assumption :=
    match goal with
    | H : bst ?t _ |- bst ?t _ =>
      use_bst_iff H
    end.

  (* If you are comfortable with it, [eapply bst_iff] followed by careful
   * application of other [bst] facts (e.g., inductive hypotheses) can
   * save typing in some places where this tactic does not apply, though
   * keep in mind that forcing an incorrect choice for a ?unification
   * variable can make the goal false. *)

  (* It may also be useful to know that you can switch to proving [False] by
   * calling [exfalso]. This, for example, enables you to apply lemmas that end in
   * [-> False]. Of course, only do this if the hypotheses are contradictory. *)

  (* Other tactics used in our solution: apply, apply with, apply with in
   * (including multiple "with" clauses like in [use_bst_iff]), cases, propositional,
     linear_arithmetic, simplify, trivial, try, induct, equality, rewrite, assert. *)

  (* Warm-up exercise: rebalancing rotations *)

  (* Transcribe and prove one of the two rotations shown in [rotation1.svg] and [rotation2.svg].
     The AA-tree rebalancing algorithm applies these only if the annotations of relevant
     subtrees are in violation of a performance-critical invariant, but the rotations
     themselves are correct regardless. (These are straight from
     https://en.wikipedia.org/wiki/AA_tree#Balancing_rotations.) *)
  (* Each one can be written as a simple nonrecursive definition
     containing two "match" expressions that returns the original
     tree in cases where the expected structure is not present. *)

  (* HINT 1 (see Pset4Sig.v) *)
  Definition rotate (T : tree) : tree :=
    match T with
    (* left rotation *)
    | Node v (Node l A B) R => Node l A (Node v B R)
    (* right rotation *)
    (* | Node v A (Node r B X) => Node r (Node v A B) X *)
    | _ => T
    end.

  Lemma bst_rotate T s (H : bst T s) : bst (rotate T) s.
  Proof.
    destruct T as [| d L R]; simpl.
    - simpl in H. exact H.
    - destruct L as [| l A B]; try (destruct R as [| r B X]; exact H).
      simpl. simpl in H. destruct H as [Hd [[[Hl Hld] [HA HB]] HR]].
      (* some of the goals are exact from H *)
      repeat split; try easy.
      (* some other goals can be solved using lt_trans with d r x *)
      + use_bst_iff HA. intro x. rewrite and_assoc. propositional.
        apply (Nat.lt_trans _ l _ H1 Hld).
      + (* B case is easy because the goal and hypotheses are just rewritten in
           different order. *)
        use_bst_iff HB. intro x. rewrite and_assoc. rewrite and_assoc. easy.
      + use_bst_iff HR. intro x. rewrite and_assoc. propositional.
        (* The second goals are exactly part of Hypotheses *)
        apply (Nat.lt_trans _ d _ Hld H1).
  Qed.

  (* There is a hint in the signature file that completely gives away the proofs
   * of these rotations. We recommend you study that code after completing this
   * exercise to see how we did it, maybe picking up a trick or two to use below. *)

  Lemma bst_insert : forall tr s a,
      bst tr s ->
      bst (insert a tr) (fun x => s x \/ x = a).
  Proof.
    intros tr s a H. induct tr; simpl.
    1: { (* Leaf case *)
      simpl in H. split; try (right; reflexivity). split;
      (* whether it is inserted into the left or the right of a Leaf, this must
         hold because in the Leaf, no s and a are true. *)
      intro x; unfold not; intro Hf; destruct Hf as [Hor Hxa];
        destruct Hor as [Hsx | Hxea];
        [ apply (H x); exact Hsx | linear_arithmetic
        | apply (H x); exact Hsx | linear_arithmetic ].
      }

    cases (compare a d); simpl; simpl in H; destruct H as [Hd [Hl Hr]].
    - repeat split.
      + left. exact Hd.
      + apply (IHtr1 _ a) in Hl. simpl in Hl. use_bst_iff_assumption.
        (* now prove when x = a, x < d is satisfied. *)
        propositional. subst x. exact l.
      + (* this cases should be false because a < d and it is inserted to the
           right. *)
        use_bst_iff_assumption. propositional. subst x. linear_arithmetic.
    - repeat split; subst a;
      (* the case when a = d, substitute all of a and simplify *)
      try (right; reflexivity);
        use_bst_iff_assumption; propositional; linear_arithmetic.
    - repeat split.
      + left. exact Hd.
      + use_bst_iff_assumption. propositional. linear_arithmetic.
      + (* this is the case when x = a, x > d is satisfied. *)
        apply (IHtr2 _ a) in Hr. simpl in Hr. use_bst_iff_assumption.
        propositional. subst x. exact l.
  Qed.

  (* To prove [bst_delete], you will need to write specifications for its helper
     functions, find suitable statements for proving correctness by induction, and use
     proofs of some helper functions in proofs of other helper functions. The hints
     in the signature file provide examples and guidance but no longer ready-to-prove
     lemma statements. For time-planning purposes: you are not halfway done yet.
     (The Sig file also has a rough point allocation between problems.)

     It is up to you whether to use one lemma per function, multiple lemmas per
     function, or (when applicable) one lemma per multiple functions. However,
     the lemmas you prove about one function need to specify everything a caller
     would need to know about this function. *)

  (* HINT 2-5 (see Pset4Sig.v) *)
  Lemma is_leaf_prop : forall tr, is_leaf tr = true <-> tr = Leaf.
  Proof.
    intro tr. propositional.
    - destruct tr; [ reflexivity | discriminate H ].
    - rewrite H. compute. reflexivity.
  Qed.

  Lemma rightmost_in_bst : forall tr s n, bst tr s -> rightmost tr = Some n -> s n.
  Proof.
    intros tr s n Hbst Hright. induct tr; simpl; [ discriminate Hright | ].
    cases (is_leaf tr2).
    - rewrite is_leaf_prop in Heq. subst tr2. simpl in Hright. inversion Hright.
      subst n. simpl in Hbst. destruct Hbst as [Hd _]. exact Hd.
    - simpl in Hbst. destruct Hbst as [Hd [Hl Hr]].
      cases (rightmost tr2); simpl in Hright; rewrite Heq0 in Hright;
        inversion Hright.
      + apply (IHtr2 _ _ Hr Hright).
      + subst n. exact Hd.
  Qed.

  Lemma rightmost_none_leaf : forall tr s, bst tr s -> rightmost tr = None -> tr = Leaf.
  Proof.
    intros tr s Hbst Hright. destruct tr; [ reflexivity | ].
    simpl in Hright. destruct (rightmost tr2).
    all: discriminate Hright.
  Qed.

  Lemma rightmost_is_max : forall tr s n,
      bst tr s -> rightmost tr = Some n -> forall x : t, s x -> x <= n.
  Proof.
    intros tr s n Hbst Hright x Hsx. induct tr; simpl;
      [ simpl in Hright; discriminate Hright | ].
    cases (is_leaf tr2).
    - rewrite is_leaf_prop in Heq. destruct Hbst as [Hd [Htr1 Htr2]].
      subst tr2. inversion Hright. subst n.
      (* Use the bst for Leaf tr2 to get an inequality. *)
      simpl in Htr2. assert (Hcases: x <= d \/ d < x) by linear_arithmetic.
      destruct Hcases as [Ht | Hwrong]; [ exact Ht | ].
      exfalso. apply ((Htr2 x) (conj Hsx Hwrong)).
    - destruct Hbst as [Hd [Htr1 Htr2]]. simpl in Hright.
      (* disgard the case where rightmost tr2 is None *)
      cases (rightmost tr2).
      + assert (Hcases: x <= d \/ d < x) by linear_arithmetic.
        inversion Hright. rewrite H0 in Heq0.
        pose proof (rightmost_in_bst tr2 _ n Htr2 Heq0) as Hn. simpl in Hn.
        destruct Hn as [Hsn Hdn]. destruct Hcases as [Hxd | Hdx];
          [ linear_arithmetic | ].
        apply (IHtr2 _ n Htr2 Hright x). split; [ exact Hsx | exact Hdx ].
      + pose proof (rightmost_none_leaf tr2 _ Htr2 Heq0) as Hwrong.
        rewrite Hwrong in Heq. discriminate Heq.
  Qed.

  Lemma delete_rightmost_preserve_bst :
    forall tr s n, bst tr s -> rightmost tr = Some n ->
              bst (delete_rightmost tr) (fun x => s x /\ x < n).
  Proof.
    intros tr s n Hbst Hright. induct tr; try discriminate Hright.
    cases (is_leaf tr2).
    { rewrite is_leaf_prop in Heq. subst tr2. cbn. simpl in Hbst, Hright.
      inversion Hright. subst n. destruct Hbst as [Hd [Htr1 Hleaf]].
      use_bst_iff_assumption. reflexivity.
    }
    cbn. rewrite Heq. simpl in Hbst, Hright.
    destruct Hbst as [Hd [Htr1 Htr2]]. cases (rightmost tr2).
    - simpl. inversion Hright. subst n0. repeat split.
      + exact Hd.
      + (* use rightmost in bst to prove d <> n *)
        apply (rightmost_in_bst tr2 _ n Htr2) in Heq0. linear_arithmetic.
      + use_bst_iff_assumption. propositional.
        apply (rightmost_in_bst tr2 _ n Htr2) in Heq0. linear_arithmetic.
      + apply (IHtr2 _ n Htr2) in Hright. use_bst_iff_assumption. propositional.
    - (* when tr2 is not Leaf, rightmost r2 should not be None *)
      apply (rightmost_none_leaf tr2 _ Htr2) in Heq0. subst tr2.
      discriminate Heq.
  Qed.

  Lemma merge_with_rightmost : forall d l r s n,
      bst (Node d l r) s -> rightmost l = Some n ->
      bst (merge_ordered l r) (fun x => s x /\ x <> d).
  Proof.
    intros d l r s n Hbst Hright. unfold merge_ordered. rewrite Hright.
    destruct Hbst as [Hd [Hl Hr]]. simpl.
    pose proof (rightmost_in_bst l _ n Hl Hright) as Hn. simpl in Hn.
    destruct Hn as [Hsn Hnd]. repeat split.
    - exact Hsn.
    - apply (delete_rightmost_preserve_bst l _ n Hl) in Hright.
      linear_arithmetic.
    - (* bst iff is not working here, because now r tree can accept more
           elements that ranges from n to d *)
      apply (delete_rightmost_preserve_bst l _ n Hl) in Hright.
      use_bst_iff_assumption. propositional.
      all: linear_arithmetic.
    - pose proof (rightmost_is_max l _ n Hl Hright) as Hn. simpl in Hn.
      apply (delete_rightmost_preserve_bst l _ n Hl) in Hright.
      (* Call bst iff to pick a specific function *)
      use_bst_iff_assumption. propositional;
        [ linear_arithmetic | linear_arithmetic | ].
      assert (Hcases: x < d \/ d < x) by linear_arithmetic.
      destruct Hcases as [Hlt | Hgt].
      + pose proof ((Hn x) (conj H Hlt)) as Hcontra. linear_arithmetic.
      + exact Hgt.
  Qed.

  Lemma bst_delete : forall tr s a, bst tr s ->
    bst (delete a tr) (fun x => s x /\ x <> a).
  Proof.
    intros tr s a H. induct tr; simpl.
    1: {
      (* delete in the leaf is false *)
      simpl in H. intro x. unfold not. intro Hf. destruct Hf as [Hsx _].
      apply (H x). exact Hsx.
    }

    cases (compare a d); simpl.
    - destruct H as [Hd [Hl Hr]]. repeat split; try exact Hd;
      try linear_arithmetic.
      + apply (IHtr1 _ a) in Hl. simpl in Hl. use_bst_iff_assumption.
        propositional.
      + (* discriminate this case because a is less than d *)
        use_bst_iff_assumption. propositional. subst a. linear_arithmetic.
    - subst a. cases (rightmost tr1).
      + apply (merge_with_rightmost d tr1 tr2 _ n H Heq).
      + destruct H as [_ [Htr1 Htr2]].
        pose proof (rightmost_none_leaf tr1 _ Htr1 Heq) as Hleaf. subst tr1.
        unfold merge_ordered. simpl. use_bst_iff_assumption. propositional;
        [ linear_arithmetic | ].
        simpl in Htr1. assert (Hcases: x < d \/ d < x) by linear_arithmetic.
        destruct Hcases as [Hlt | hgt];
          [ exfalso; apply ((Htr1 x) (conj H0 Hlt)) | exact hgt].
    - repeat split.
      + destruct H as [Hd _]. exact Hd.
      + linear_arithmetic.
      + destruct H as [_ [Htr1 Htr2]]. use_bst_iff_assumption. propositional.
        subst x. linear_arithmetic.
      + destruct H as [_ [_ Htr2]]. apply (IHtr2 _ a) in Htr2. simpl in Htr2.
        use_bst_iff_assumption. propositional.
  Qed.

  (* Great job! Now you have proven all tree-structure-manipulating operations
     necessary to implement a balanced binary search tree. Rebalancing heuristics
     that achieve worst-case-logarithmic running time maintain annotations on
     nodes of the tree (and decide to rebalance based on these). The implementation
     here omits them, but as the rotation operations are correct regardless of
     the annotations, any way of calling them from heuristic code would result in a
     functionally correct binary tree. *)
End Impl.

Module ImplCorrect : Pset4Sig.S := Impl.

(* Authors:
 * Joonwon Choi
 * Adam Chlipala
 * Benjamin Sherman
 * Andres Erbsen
 * Amanda Liu
 *)
