(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 7 *)

Require Import Frap.Frap.
Require Import Pset7.Pset7Sig.

(* The following line forces you to use bullets or braces.  Remove it if you get
   errors like "Expected a single focused goal but 2 goals are focused." and you
   don't want to structure your proofs. *)
Set Default Goal Selector "!".
Set Implicit Arguments.

Module Impl.
  (** * Subtyping *)

  (* We can't resist fitting in another crucial aspect of type systems:
   * *subtyping*, which formalizes when any value of one type should also be
   * permitted as a value of some other type. Languages like Java include
   * *nominal* subtyping, based on declared type hierarchies. Instead, here we
   * will prove the soundness of *structural* subtyping, whose rules we'll get to
   * shortly. The simply typed lambda calculus will be our starting point. *)

  (* Expression syntax *)
  Inductive exp  :=
  (* Our old friends from simply typed lambda calculus *)
  | Var (x : var)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)

  (* New features, surrounding *tuple* types, which build composite types out of
   * constituents *)
  | TupleNil
  (* Empty tuple (no fields) *)
  | TupleCons (e1 e2 : exp)
  (* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
   * nested tuple with all the remaining fields *)

  | Proj (e : exp) (n : nat)
  (* Grab the [n]th field of tuple [e]. *)
  .

  (* Values (final results of evaluation) *)
  Inductive value : exp -> Prop :=
  | VAbs : forall x e1, value (Abs x e1)
  | VTupleNil : value TupleNil
  | VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
  .

  (* The next few definitions are quite routine and should be safe to skim through
   * quickly; but start paying more attention when we get to defining the
   * subtyping relation! *)

  (* Substitution (not capture-avoiding, for the usual reason) *)
  Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
    match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    | TupleNil => TupleNil
    | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
    | Proj e2' n => Proj (subst e1 x e2') n
    end.

  (* Evaluation contexts *)
  Inductive context :=
  | Hole
  | App1 (C : context) (e2 : exp)
  | App2 (v1 : exp) (C : context)
  | TupleCons1 (C : context) (e2 : exp)
  | TupleCons2 (v1 : exp) (C : context)
  | Proj1 (C : context) (n : nat)
  .

  (* Plugging an expression into a context *)
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugApp1 : forall e e' C e2,
      plug C e e'
      -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (App2 v1 C) e (App v1 e')
  | PlugTupleCons1 : forall C e e' e2,
      plug C e e'
      -> plug (TupleCons1 C e2) e (TupleCons e' e2)
  | PlugTupleCons2 : forall v1 C e e',
      value v1
      -> plug C e e'
      -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
  | PlugProj : forall C e e' n,
      plug C e e'
      -> plug (Proj1 C n) e (Proj e' n)
  .

  (* Small-step, call-by-value evaluation *)
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
      value v
      -> step0 (App (Abs x e) v) (subst v x e)

  (* To project field 0 out of a tuple, just grab the first component. *)
  | Proj0 : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Proj (TupleCons v1 v2) 0) v1

  (* To project field [1+n], drop the first component and continue with [n]. *)
  | ProjS : forall v1 v2 n,
      value v1
      -> value v2
      -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
  .

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
      plug C e1 e1'
      -> plug C e2 e2'
      -> step0 e1 e2
      -> step e1' e2'.

  Definition trsys_of (e : exp) :=
    {| Initial := {e}; Step := step |}.

  (* Syntax of types *)
  Inductive type :=
  | Fun (dom ran : type)
  | TupleTypeNil
  | TupleTypeCons (t1 t2 : type)
  .

  Inductive subtype : type -> type -> Prop :=

  (* Two function types are related if their components are related pairwise.
   * Counterintuitively, we *reverse* the comparison order for function domains!
   * It may be worth working through some examples to see why the relation would
   * otherwise be unsound. *)
  | StFun : forall t1' t2' t1 t2,
      subtype t1 t1' ->
      subtype t2' t2 ->
      subtype (Fun t1' t2') (Fun t1 t2)

  (* An empty tuple type is its own subtype. *)
  | StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

  (* However, a nonempty tuple type is also a subtype of the empty tuple type.
   * This rule gives rise to *width* subtyping, where we can drop some fields of
   * a tuple type to produce a subtype. *)
  | StTupleNilCons : forall t1 t2,
      subtype (TupleTypeCons t1 t2) TupleTypeNil

  (* We also have *depth* subtyping: we can replace tuple components with
   * subtypes. *)
  | StTupleCons : forall t1' t2' t1 t2,
      subtype t1' t1 ->
      subtype t2' t2 ->
      subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
  .

  (* Here's a more compact notation for subtyping. *)
  Infix "$<:" := subtype (at level 70).

  Local Hint Constructors subtype : core.

  (* Projecting out the nth field of a tuple type *)
  Inductive proj_t : type -> nat -> type -> Prop :=
  | ProjT0 : forall t1 t2,
      proj_t (TupleTypeCons t1 t2) 0 t1
  | ProjTS : forall t1 t2 n t,
      proj_t t2 n t ->
      proj_t (TupleTypeCons t1 t2) (1 + n) t
  .

  (* Expression typing relation stating something _has_ a _ty_pe *)
  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
      G $? x = Some t ->
      has_ty G (Var x) t
  | HtAbs : forall G x e1 t1 t2,
      has_ty (G $+ (x, t1)) e1 t2 ->
      has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
      has_ty G e1 (Fun t1 t2) ->
      has_ty G e2 t1 ->
      has_ty G (App e1 e2) t2
  | HtTupleNil : forall G,
      has_ty G TupleNil TupleTypeNil
  | HtTupleCons: forall G e1 e2 t1 t2,
      has_ty G e1 t1 ->
      has_ty G e2 t2 ->
      has_ty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
  | HtProj : forall G e n t t',
      has_ty G e t' ->
      proj_t t' n t ->
      has_ty G (Proj e n) t

  (* This is the crucial rule: when an expression has a type, it also has any
   * supertype of that type. We call this rule *subsumption*. *)
  | HtSub : forall G e t t',
      has_ty G e t' ->
      t' $<: t ->
      has_ty G e t
  .

  (* Before we get started proving properties of our type system, please read
   * Pset7Sig.v and consider the questions below. This task is ungraded,
   * but we are assigning it in hopes it helps you complete the
   * following parts.

 What does it mean for the subtyping order of the arguments in `StFun` to be
 reversed?


 If t1 $<: t2, what is known about some t3 that is a supertype of t2? And
 likewise if it's a subtype of t1?


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 has_ty G (Abs x e1) t
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `has_ty`, and what
 information do you have about `t`?

 To contrast, how many goals do you expect with the `has_ty` definition of
 this pset? Why is this the case?

 Can you formulate a lemma that consolidates the information present in these
 branches into one conclusion? (Imagine inverting now is equivalent to an
 "or" generating branches for each constructor; can you rephrase a lemma that
 leads to a conclusion with an "and" instead?)


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 has_ty G e (Fun t1 t2)
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `has_ty`, and what
 information do you have about `e`?

 To contrast, how many goals do you expect with the `has_ty` definition
 of this pset? Why is this the case?

 Can you formulate a lemma to recover information similar to what inverting
 gave you in FRAP's `has_ty` definition?

   *)

  (* Prove these two basic algebraic properties of subtyping. *)

  Lemma subtype_refl : forall t1, t1 $<: t1.
  Proof.
    induct t1; now constructor.
  Qed.

  Definition subtype_right t1 t2 := forall t3, t2 $<: t3 -> t1 $<: t3.

  Definition subtype_left t1 t2 := forall t3, t3 $<: t1 -> t3 $<: t2.

  Lemma subtype_trans_aux t1 t2:
    t1 $<: t2 -> subtype_left t1 t2 /\ subtype_right t1 t2.
  Proof.
    induct 1; split; unfold subtype_left in *; unfold subtype_right in *;
      intros t3 Ht3; invert Ht3; constructor.
    - destruct IHsubtype1 as [_ Ht1_right]. apply (Ht1_right t1'0 H4).
    - destruct IHsubtype2 as [Ht2_left _]. apply (Ht2_left t2'0 H5).
    - destruct IHsubtype1 as [Ht1_left _]. apply (Ht1_left t0 H3).
    - destruct IHsubtype2 as [_ Ht2_right]. apply (Ht2_right t4 H5).
    - destruct IHsubtype1 as [Ht1_left _]. apply (Ht1_left t1'0 H4).
    - destruct IHsubtype2 as [Ht2_left _]. apply (Ht2_left t2'0 H5).
    - destruct IHsubtype1 as [_ Ht1_right]. apply (Ht1_right t0 H3).
    - destruct IHsubtype2 as [_ Ht2_right]. apply (Ht2_right t4 H5).
  Qed.

  (* HINT 1 (see Pset7Sig.v) *)
  Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
  Proof.
    intros t1 t2 t3 Ht12. pose proof (subtype_trans_aux Ht12) as H.
    destruct H as [Hleft Hright]. apply Hright.
  Qed.

  (* BEGIN handy tactic that we suggest for these proofs *)
  Ltac tac0 :=
    match goal with
    | [ H : ex _ |- _ ] => invert H
    | [ H : _ /\ _ |- _ ] => invert H
    | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
    | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
    | [ H : step _ _ |- _ ] => invert H
    | [ H : step0 _ _ |- _ ] => invert1 H
    | [ H : has_ty _ _ _ |- _ ] => invert1 H
    | [ H : proj_t _ _ _ |- _ ] => invert1 H
    | [ H : plug _ _ _ |- _ ] => invert1 H
    | [ H : subtype _ _ |- _ ] => invert1 H
    | [ H : Some _ = Some _ |- _ ] => invert H
    end;
    subst.

  Ltac tac := simplify; subst; propositional; repeat (tac0; simplify); try equality.
  (* END handy tactic *)


  (* The real prize: prove soundness of this type system.
   * We suggest starting from a copy of the type-safety proof from the book's
   * EvaluationContexts.v.
   * The soundness argument for simply typed lambda calculus is genuinely difficult
   * (a celebrated result!). We're not expecing you to reinvent it. Rather, the
   * task of this pset is to *extend* it to cover subtyping. This will involve
   * changing some proofs and making appropriate additional helper lemmas (there
   * are more hints in Pset7Sig.v).
   * Trying to write this proof from scratch is *not* recommended for this pset.
   * This is in contrast to the *previous* psets, which we tried to design so that
   * they could be solved from scratch with a good understanding of the lecture
   * material. *)

  (* HINT 2-3 (see Pset7Sig.v) *)
  Lemma step0_is_step e1 e2:
    step0 e1 e2 -> step e1 e2.
  Proof.
    apply StepRule with (C := Hole) (e1 := e1) (e2 := e2).
    all: apply PlugHole.
  Qed.

  Lemma canonical_form_abs e t1 t2 :
    has_ty $0 e (Fun t1 t2) ->
    value e ->
    exists x e1, e = Abs x e1.
  Proof.
    (* Use eauto to prove the canonical form, invert Vapp and VProj because they
     are not values *)
    induct 1; tac; eauto; invert H1.
  Qed.

  Lemma canonical_form_tuple e t t1 :
    has_ty $0 e (TupleTypeCons t t1) ->
    value e ->
    exists e1 e2, e = TupleCons e1 e2.
  Proof.
    (* Use eauto to prove the canonical form, invert Vapp and VProj because they
     are not values *)
    induct 1; tac; eauto; invert H1.
  Qed.

  Lemma progress : forall e t,
      has_ty $0 e t
      -> value e
        \/ (exists e' : exp, step e e').
  Proof.
    induct 1; tac.
    - left. apply VAbs.           (* Vabs *)
    - right. apply (canonical_form_abs H) in H3.      (* Vapp *)
      destruct H3 as [x [e' Habs]]. rewrite Habs. exists (subst e2 x e'). (* step0 *)
      apply step0_is_step. apply (Beta x e' H1).
    - right. apply PlugApp1 with (e2 := e2) in H3,H4. exists (App x e2).
      apply (StepRule H3 H4 H5). (* App e1 e2 where e1 can step *)
    - right. apply (PlugApp2 H3) in H1,H4. exists (App e1 x).
      apply (StepRule H1 H4 H5). (* App e1 e2 where e1 is value *)
    - right. apply PlugApp1 with (e2 := e2) in H3,H6. exists (App x e2).
      apply (StepRule H3 H6 H7). (* App e1 e2 where both e1 and e2 can step *)
    - left. apply VTupleNil.
    - left. apply (VTupleCons H3 H1).
    - right. apply PlugTupleCons1 with (e2 := e2) in H3,H4. exists (TupleCons x e2).
      apply (StepRule H3 H4 H5).  (* Cons e1 v2 where e1 can step *)
    - right. apply (PlugTupleCons2 H3) in H1,H4. exists (TupleCons e1 x).
      apply (StepRule H1 H4 H5). (* Cons v1 e2 where e2 can step *)
    - right. apply PlugTupleCons1 with (e2 := e2) in H3,H6. exists (TupleCons x e2).
      apply (StepRule H3 H6 H7). (* Cons e1 e2 where e1 can step *)
    - right. invert H0; pose proof (canonical_form_tuple H H1) as Htuple;
        destruct Htuple as [e1 [e2 Htuple]]; subst e; invert H1;
        [ exists e1 | exists (Proj e2 n0) ]; (* apply proj0 or projS *)
        apply step0_is_step; [ apply (Proj0 H3 H4) | apply (ProjS n0 H4 H5) ].
    - right. apply PlugProj with (n := n) in H1,H3. exists (Proj x n).
      apply (StepRule H1 H3 H4).  (* Proj e n where e can step *)
  Qed.

  Lemma weakening_override : forall (G G' : fmap var type) x t,
      (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
      -> (forall x' t', G $+ (x, t) $? x' = Some t'
                  -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  Local Hint Resolve weakening_override : core.

  Lemma weakening : forall G e t,
      has_ty G e t
      -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
              -> has_ty G' e t.
  Proof.
    induct 1; tac; try (constructor; eauto).
    - pose proof (IHhas_ty1 G' H1) as He1. pose proof (IHhas_ty2 G' H1) as He2.
      apply (HtApp He1 He2).
    - pose proof (IHhas_ty G' H1) as Hproj. apply (HtProj Hproj H0).
    - pose proof (IHhas_ty G' H1) as Hsubtype.
      apply (HtSub Hsubtype H0). (* Subtype *)
  Qed.

  Local Hint Resolve weakening : core.

  (* Replacing a typing context with an equal one has no effect (useful to guide
   * proof search as a hint). *)
  Lemma has_ty_change : forall G e t,
      has_ty G e t
      -> forall G', G' = G
              -> has_ty G' e t.
  Proof.
    tac.
  Qed.

  Local Hint Resolve has_ty_change : core.

  Lemma substitution : forall G x t' e t e',
      has_ty (G $+ (x, t')) e t
      -> has_ty $0 e' t'
      -> has_ty G (subst e' x e) t.
  Proof.
    induct 1; tac; try constructor; eauto.
    - assert (HG: G $+ (x, t') = G $+ (x, t')) by reflexivity.
      pose proof (IHhas_ty1 G x t'  HG H1) as He1.
      apply (HtApp He1 H2).
    - apply (HtProj H2 H0).
    - apply (HtSub H2 H0).
  Qed.

  Local Hint Resolve substitution : core.

  Lemma has_ty_abs G x e t1 t2 :
    has_ty G (Abs x e) (Fun t1 t2) ->
    exists D S, has_ty (G $+ (x, D)) e S /\ (Fun D S) $<: (Fun t1 t2).
  Proof.
    induct 1; tac.
    - exists t1, t2. split; [ exact H | apply subtype_refl ].
    - specialize (IHhas_ty x e t1' t2'). specialize ((IHhas_ty eq_refl) eq_refl).
      destruct IHhas_ty as [D [S [Hty Hsub]]]. exists D, S. split; [ exact Hty | ].
      apply subtype_trans with (t2 := (Fun t1' t2')); [ exact Hsub | ].
      apply (StFun H4 H5).
  Qed.

  Lemma has_ty_app G e1 e2 t:
    has_ty G (App e1 e2) t ->
    exists D S, has_ty G e1 (Fun D S) /\ has_ty G e2 D /\ S $<: t.
  Proof.
    induct 1; tac.
    - exists t1, t2. repeat split; auto. apply subtype_refl.
    - exists x, x0. repeat split; auto. apply (subtype_trans H4 H0).
  Qed.

  Lemma has_ty_TupleCons G e e' t:
    has_ty G (TupleCons e e') t ->
    exists t1 t2, has_ty G e t1 /\ has_ty G e' t2 /\ (TupleTypeCons t1 t2) $<: t.
  Proof.
    induct 1; tac.
    - exists t1, t2. repeat split; eauto. apply subtype_refl.
    - exists x, x0. repeat split; eauto. apply subtype_trans with (t2 := t'); eauto.
  Qed.

  Lemma has_ty_proj G e n t:
    has_ty G (Proj e n) t ->
    exists t' l, has_ty G e l /\ proj_t l n t' /\ t' $<: t.
  Proof.
    induct 1; tac.
    - exists t, t'. repeat split; eauto. apply subtype_refl.
    - exists x, x0. repeat split; eauto. apply subtype_trans with (t2 := t'); eauto.
  Qed.

  Lemma preservation0 : forall e1 e2,
      step0 e1 e2
      -> forall t, has_ty $0 e1 t
             -> has_ty $0 e2 t.
  Proof.
    invert 1; tac.
    - apply has_ty_app in H. destruct H as [t1 [t2 [Habs [Hv Ht1]]]].
      apply has_ty_abs in Habs. destruct Habs as [ta [tb [Hext Hf]]]. invert Hf.
      apply substitution with (t' := ta).
      + apply HtSub with (t' := tb); eauto. apply (subtype_trans H5 Ht1).
      + apply HtSub with (t' := t1); eauto.
    - apply has_ty_proj in H. destruct H as [t0 [tl [Hl [Hproj Hsub]]]].
      apply has_ty_TupleCons in Hl. destruct Hl as [t1 [t2 [Ht1 [Ht2 Hcons]]]].
      apply HtSub with (t' := t1); [ exact Ht1 | ]. invert Hproj. invert Hcons.
      apply (subtype_trans H4 Hsub).
    - apply has_ty_proj in H. destruct H as [t0 [tl [Hl [Hproj Hsub]]]].
      apply has_ty_TupleCons in Hl. destruct Hl as [t1 [t2 [Ht1 [Ht2 Hcons]]]].
      invert Hproj. invert Hcons. apply HtSub with (t' := t0); [ | exact Hsub ].
      apply HtProj with (t' := t4).
      + apply HtSub with (t' := t2); eauto.
      + exact H3.
  Qed.

  Local Hint Resolve preservation0 : core.

  Lemma preservation' : forall C e1 e1',
      plug C e1 e1'
      -> forall e2 e2' t, plug C e2 e2'
                    -> step0 e1 e2
                    -> has_ty $0 e1' t
                    -> has_ty $0 e2' t.
  Proof.
    induct 1; tac; eauto.
    - apply has_ty_app in H2. destruct H2 as [t1 [t2 [He' [He2 Hsub]]]].
      apply HtApp with (t1 := t1); eauto. apply HtSub with (t' := (Fun t1 t2)).
      + apply IHplug with (e2 := e0); eauto.
      + constructor; eauto. apply subtype_refl.
    - apply has_ty_app in H3. destruct H3 as [t1 [t2 [Hv1 [He' Hsub]]]].
      apply HtApp with (t1 := t1); eauto. (* Use preservation0 for step once *)
      apply HtSub with (t' := (Fun t1 t2)); eauto. constructor; eauto.
      apply subtype_refl.
    - apply has_ty_TupleCons in H2. destruct H2 as [t1 [t2 [He' [He2 Hcons]]]].
      apply HtSub with (t' := (TupleTypeCons t1 t2)); eauto.
      apply HtTupleCons; eauto.
    - apply has_ty_TupleCons in H3. destruct H3 as [t1 [t2 [He' [He2 Hcons]]]].
      apply HtSub with (t' := (TupleTypeCons t1 t2)); eauto.
      apply HtTupleCons; eauto.
    - apply has_ty_proj in H2. destruct H2 as [t' [tl [He' [Hproj Hsub]]]].
      apply HtSub with (t' := t'); eauto. apply HtProj with (t' := tl); eauto.
  Qed.

  Local Hint Resolve preservation' : core.

  Lemma preservation : forall e1 e2,
      step e1 e2
      -> forall t, has_ty $0 e1 t
             -> has_ty $0 e2 t.
  Proof.
    invert 1; tac; eauto.
  Qed.

  Local Hint Resolve progress preservation : core.

  Theorem safety :
    forall e t,
      has_ty $0 e t -> invariantFor (trsys_of e)
                        (fun e' => value e'
                                \/ exists e'', step e' e'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t); eauto.
    apply invariant_induction; simplify; eauto; equality.
  Qed.

End Impl.

(* The following line checks that your `Impl` module implements the right
   signature. Make sure that it works, or the auto-grader will break!
   If there are mismatches, Rocq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset7Sig.S := Impl.

(* Authors:
 * Peng Wang
 * Adam Chlipala
 * Samuel Gruetter
 * Amanda Liu
 * Paul Mure
 *)
