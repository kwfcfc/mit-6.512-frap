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
   [t] equipped with a strict total order. We factor out the
   ordering properties so that replacing [nat] only requires
   changing three definitions below. *)
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

  (* ===== Strict total order interface =====
     All BST proofs only depend on these three properties.
     To switch from [nat] to another ordered type, change only these
     three definitions and the [compare] function. *)

  Definition lt_irrefl := Nat.lt_irrefl.         (* forall x, ~ x < x *)
  Definition lt_trans  := Nat.lt_trans.           (* forall x y z, x<y -> y<z -> x<z *)
  Definition lt_trichotomy := Nat.lt_trichotomy.  (* forall x y, x<y \/ x=y \/ y<x *)

  (* Derived order lemmas *)
  Lemma lt_asymm : forall x y : t, x < y -> ~ y < x.
  Proof. intros. intro. exact (lt_irrefl _ (lt_trans _ _ _ H H0)). Qed.

  Lemma lt_neq : forall x y : t, x < y -> x <> y.
  Proof. intros. intro. subst. exact (lt_irrefl _ H). Qed.

  Lemma gt_neq : forall x y : t, y < x -> x <> y.
  Proof. intros. intro. subst. exact (lt_irrefl _ H). Qed.

  (* Automated order tactic: solves goals using irrefl/asymm/trans *)
  Ltac order :=
    subst; try assumption;
    try (exfalso;
      match goal with
      | H: ?x < ?x |- _ => exact (lt_irrefl _ H)
      | H1: ?x < ?y, H2: ?y < ?x |- _ => exact (lt_asymm _ _ H1 H2)
      | H1: ?x < ?y, H2: ?y < ?z, H3: ?z < ?x |- _ =>
          exact (lt_asymm _ _ H1 (lt_trans _ _ _ H3 H2))
      | H1: ?x < ?y, H2: ?y < ?z, H3: ?z < ?x |- _ =>
          exact (lt_asymm _ _ (lt_trans _ _ _ H1 H2) H3)
      end);
    try match goal with
    | |- ?x < ?z => eapply lt_trans; eassumption
    | H: ?x < ?y |- ?x <> ?y => exact (lt_neq _ _ H)
    | H: ?y < ?x |- ?x <> ?y => exact (gt_neq _ _ H)
    | |- ?x <> ?y => exact (lt_neq _ _ ltac:(eapply lt_trans; eassumption))
    | |- ?x <> ?y => exact (gt_neq _ _ ltac:(eapply lt_trans; eassumption))
    | |- ?x <> ?y =>
        let Heq := fresh in intro Heq; subst;
        match goal with H1: ?a < ?a |- _ => exact (lt_irrefl _ H1) end
    end.

  (* Trichotomy: case-split on the ordering of x and y *)
  Ltac trichotomy x y :=
    destruct (lt_trichotomy x y) as [? | [? | ?]].

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
        eapply lt_trans; eassumption.
      + (* B case is easy because the goal and hypotheses are just rewritten in
           different order. *)
        use_bst_iff HB. intro x. rewrite and_assoc. rewrite and_assoc. easy.
      + use_bst_iff HR. intro x. rewrite and_assoc. propositional.
        (* The second goals are exactly part of Hypotheses *)
        eapply lt_trans; eassumption.
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
      simpl in H. split; [ right; reflexivity | ]. split;
      intro x; intro Hf; destruct Hf as [[Hsx | Hxea] Hxa];
        [ exact (H x Hsx) | subst x; exact (lt_irrefl _ Hxa)
        | exact (H x Hsx) | subst x; exact (lt_irrefl _ Hxa) ]. }

    cases (compare a d); simpl; simpl in H; destruct H as [Hd [Hl Hr]].
    - (* a < d: insert left *)
      repeat split.
      + left. exact Hd.
      + apply (IHtr1 _ a) in Hl. simpl in Hl. use_bst_iff_assumption.
        propositional. subst x. exact l.
      + use_bst_iff_assumption. propositional; order.
    - (* a = d: no change *)
      repeat split; subst a; try (right; reflexivity);
        use_bst_iff_assumption; propositional; order.
    - (* d < a: insert right *)
      repeat split.
      + left. exact Hd.
      + use_bst_iff_assumption. propositional; order.
      + apply (IHtr2 _ a) in Hr. simpl in Hr. use_bst_iff_assumption.
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
    simpl in Hright. destruct (rightmost tr2); discriminate Hright.
  Qed.

  (* Using ~(n < x) instead of x <= n avoids dependence on nat's [le]. *)
  Lemma rightmost_is_max : forall tr s n,
      bst tr s -> rightmost tr = Some n -> forall x : t, s x -> ~ (n < x).
  Proof.
    intros tr s n Hbst Hright x Hsx Hnx. induct tr; simpl;
      [ simpl in Hright; discriminate Hright | ].
    cases (is_leaf tr2).
    - rewrite is_leaf_prop in Heq. destruct Hbst as [Hd [Htr1 Htr2]].
      subst tr2. simpl in Hright. inversion Hright. subst n.
      simpl in Htr2.
      trichotomy x d.
      + exact (lt_asymm _ _ H Hnx).
      + subst x. exact (lt_irrefl _ Hnx).
      + exact ((Htr2 x) (conj Hsx H)).
    - destruct Hbst as [Hd [Htr1 Htr2]]. simpl in Hright.
      cases (rightmost tr2).
      + inversion Hright. subst n0.
        pose proof (rightmost_in_bst tr2 _ n Htr2 Heq0) as HnR.
        simpl in HnR. destruct HnR as [_ Hdn].
        trichotomy x d.
        * exact (lt_asymm _ _ (lt_trans _ _ _ H Hdn) Hnx).
        * subst x. exact (lt_asymm _ _ Hdn Hnx).
        * apply (IHtr2 _ n Htr2 Hright x (conj Hsx H) Hnx).
      + pose proof (rightmost_none_leaf tr2 _ Htr2 Heq0).
        rewrite H in Heq. discriminate Heq.
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
    - simpl. inversion Hright. subst n0.
      pose proof (rightmost_in_bst tr2 _ n Htr2 Heq0) as HnR.
      simpl in HnR. destruct HnR as [_ Hdn].
      repeat split.
      + exact Hd.
      + exact Hdn.
      + use_bst_iff_assumption. propositional;
          eapply lt_trans; eassumption.
      + apply (IHtr2 _ n Htr2) in Hright. use_bst_iff_assumption. propositional.
    - apply (rightmost_none_leaf tr2 _ Htr2) in Heq0. subst tr2.
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
    - (* n <> d from n < d *)
      exact (lt_neq _ _ Hnd).
    - (* left subtree *)
      pose proof (delete_rightmost_preserve_bst l _ n Hl Hright) as Hdel.
      simpl in Hdel. use_bst_iff Hdel. propositional; order.
    - (* right subtree *)
      pose proof (rightmost_is_max l _ n Hl Hright) as Hmax.
      use_bst_iff Hr. intros x; split.
      + intros [Hsx Hdx]. repeat split.
        * exact Hsx.
        * exact (gt_neq _ _ Hdx).
        * trichotomy x n.
          { exfalso. exact (lt_asymm _ _ H (lt_trans _ _ _ Hnd Hdx)). }
          { subst x. exfalso. exact (lt_asymm _ _ Hnd Hdx). }
          { exact H. }
      + intros [[Hsx Hxned] Hnx]. split.
        * exact Hsx.
        * trichotomy x d.
          { exfalso. exact (Hmax x (conj Hsx H) Hnx). }
          { subst x. contradiction. }
          { exact H. }
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
    - (* a < d *)
      destruct H as [Hd [Hl Hr]]. repeat split.
      + exact Hd.
      + intro Hda. subst d. exact (lt_irrefl _ l).
      + apply (IHtr1 _ a) in Hl. simpl in Hl.
        use_bst_iff_assumption. propositional.
      + use_bst_iff_assumption. propositional; order.
    - (* a = d *)
      subst a. cases (rightmost tr1).
      + apply (merge_with_rightmost d tr1 tr2 _ n H Heq).
      + destruct H as [_ [Htr1 Htr2]].
        pose proof (rightmost_none_leaf tr1 _ Htr1 Heq) as Hleaf. subst tr1.
        unfold merge_ordered. simpl. use_bst_iff Htr2. intros x; split.
        * intros [Hsx Hdx]. split; [ exact Hsx | ].
          exact (gt_neq _ _ Hdx).
        * intros [Hsx Hxnd]. split; [ exact Hsx | ].
          simpl in Htr1.
          trichotomy x d.
          { exfalso. exact ((Htr1 x) (conj Hsx H)). }
          { subst x. contradiction. }
          { exact H. }
    - (* d < a *)
      destruct H as [Hd [Hl Hr]]. repeat split.
      + exact Hd.
      + intro Hda. subst d. exact (lt_irrefl _ l).
      + use_bst_iff_assumption. propositional; order.
      + apply (IHtr2 _ a) in Hr. simpl in Hr.
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
