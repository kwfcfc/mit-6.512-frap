(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 5 *)

Require Import Frap.Frap Pset5.Pset5Sig.

Module Impl.
  (* In this pset, we will explore different ways of defining semantics for the
     simple imperative language we used in Chapter 4 (Interpreters.v) and
     Chapter 7 (OperationalSemantics.v).
     Make sure to reread these two files, because many definitions we ask you
     to come up with in this pset are similar to definitions in these two files.

     Pset5Sig.v contains the number of points you get for each definition and
     proof. Note that since we ask you to come up with some definitions
     yourself, all proofs being accepted by Rocq does not necessarily guarantee a
     full score: you also need to make sure that your definitions correspond to
     what we ask for in the instructions. *)

  (* Our language has arithmetic expressions (note that we removed Times and Minus,
     because they don't add anything interesting for this pset): *)
  Inductive arith: Set :=
  | Const (n: nat)
  | Var (x: var)
  | Plus (e1 e2: arith).

  (* And it has commands, some of which contain arithmetic expressions: *)
  Inductive cmd :=
  | Skip
  | Assign (x: var) (e: arith)
  | Sequence (c1 c2: cmd)
  | If (e: arith) (thn els: cmd)
  | While (e: arith) (body: cmd).

  (* As in the lecture, we use a finite map to store the values of variables: *)
  Definition valuation := fmap var nat.

  (** * Part 1: Using a recursive function **)

  (* To make it a bit more interesting, we add a twist:
     If an arithmetic expression reads an undefined variable, instead of just
     returning 0, we specify that an arbitrary value can be returned.
     Therefore, the signature we used in class,

       Fixpoint interp (e: arith) (v: valuation): nat :=
         ...

     will not work any more, because it can only return one value.
     Instead, we will use the following definition: *)

  Fixpoint interp (e: arith) (v: valuation) (retval: nat): Prop :=
    match e with
    | Const n => retval = n
    | Var x =>
      match v $? x with
      | None => True (* any retval is possible! *)
      | Some n => retval = n
      end
    | Plus e1 e2 =>
      exists a1 a2,
      interp e1 v a1 /\
      interp e2 v a2 /\
      retval = a1 + a2
    end.
  (* You can read [interp e v retval] as the claim that "interpreting expression
     e under the valuation v can return the value retval".
     And if we don't provide the last argument, we can think of "interp e v",
     which has type "nat -> Prop", as "the set of all possible values e could
     return". *)

  (* Let's look at some examples: *)

  (* The only result allowed by [Const 3] is [3]: *)
  Compute interp (Const 3) _.

  (* If we interpret the expression "y + z" in a valuation where
     y is 2 and z is 3, then the only possible result is 5. *)

  Goal forall retval,
      interp (Plus (Var "y") (Var "z"))
             ($0 $+ ("y", 2) $+ ("z", 3))
             retval <->
      retval = 5.
  Proof.
    simplify; propositional.
    - cases H; cases H.
      linear_arithmetic.
    - exists 2, 3.
      propositional.
  Qed.

  (* We can also look at this in terms of a partial application: *)

  Goal interp (Plus (Var "y") (Var "z"))
              ($0 $+ ("y", 2) $+ ("z", 3)) =
       (fun retval => retval = 5).
  Proof.
    simplify.
    apply sets_equal; simplify; propositional.
    - cases H; cases H.
      linear_arithmetic.
    - exists 2, 3.
      propositional.
  Qed.

  (* But if we leave [z] unset in the valuation, then [Var "z"] can return any
     value, and hence the complete program can return any value greater than or
     equal to 2. *)
  Goal interp (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) = (fun retval => 2 <= retval).
  Proof.
    simplify.
    apply sets_equal.
    propositional.
    - cases H. cases H. linear_arithmetic.
    - exists 2, (x - 2). linear_arithmetic.
  Qed.

  (* Hint that will be useful later:
     In the above proof, you can see how you can deal with existentials:
     - If you have an [H: exists x, P] above the line, you can "cases H"
       to obtain such an "x" and "H: P".
     - If you have an [exists x, P] below the line, you can use "exists x0" to
       provide the value [x0] for which you want to prove the existential.
     Instead of repeating [cases], you can also use [first_order]. *)

  (** * Part 2: Using an inductive relation **)

  (* An alternative way of specifying how arithmetic expressions are evaluated
     is by using inference rules, where we put preconditions above the line,
     the conclusion below the line, and a name of the rule to the right of
     the line, using "Oxford brackets" to write statements of the form
     "a ∈ ⟦e⟧ᵥ" which we read as "the natural number a is in the set of
     values to which e can evaluate under the valuation v".
     If we were to write this on a blackboard, it might look like this:

                           n1 = n2
                        ------------ ValuesConst
                         n1 ∈ ⟦n2⟧ᵥ

                         (x ↦ a) ∈ v
                        -------------- ValuesVarDefined
                           a ∈ ⟦x⟧ᵥ

                         x ∉ dom(v)
                       ------------- ValuesVarUndefined
                         a ∈ ⟦x⟧ᵥ

            a1 ∈ ⟦e1⟧ᵥ   a2 ∈ ⟦e2⟧ᵥ   a=a1+a2
            ----------------------------------- ValuesPlus
                       a ∈ ⟦e1+e2⟧ᵥ

     Let's translate this to an Inductive Prop in Rocq called "values". That is,
     [values e v a] should mean “the natural number a is in the set of
     values to which e can evaluate under the valuation v”.

     Define an Inductive with four constructors, one for each of the four rules
     above, using the names written to the rights of the lines above as the
     constructor names.  We have included ValuesConst to give you a hint.
  *)

  Inductive values: arith -> valuation -> nat -> Prop :=
  | ValuesConst: forall v n1 n2,
      n1 = n2 ->
      values (Const n1) v n2
  | ValuesVarDefined: forall v x a,
      v $? x = Some a ->
      values (Var x) v a
  | ValuesVarUndefined: forall v x a,
      v $? x = None ->
      values (Var x) v a
  | ValuesPlus: forall v e1 e2 a1 a2 a,
      values e1 v a1 ->
      values e2 v a2 ->
      a = a1 + a2 ->
      values (Plus e1 e2) v a
  .

  (** ===== 自动化辅助 tactic（Part 1: arith 相关） ===== *)
  (* 以下 tactic 用于自动化 interp/values 之间的等价性证明。
     设计目标：添加新的 arith constructor（如 Times, Minus）时，
     大部分证明无需修改，新 case 会被自动处理。 *)

  (* break_hyps: 递归分解假设中的存在量词、合取、析取和矛盾。
     这是所有自动化 tactic 的基础构建块。
     匹配模式说明：
     - [H: exists _, _ |- _] : H 形如 [exists x, P x]，destruct 拆出 witness x 和命题 P x
     - [H: _ /\ _ |- _]      : H 形如 [P /\ Q]，destruct 拆成两个独立假设
     - [H: _ \/ _ |- _]       : H 形如 [P \/ Q]，destruct 产生两个子目标（P 分支和 Q 分支）
     - [H: False |- _]        : 假设矛盾，contradiction 直接关闭目标
     使用 repeat 递归处理嵌套结构（如 [exists x, exists y, P /\ Q]），
     直到没有更多可分解的假设为止。 *)
  Ltac break_hyps :=
    repeat match goal with
    | H: exists _, _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | H: _ \/ _ |- _ => destruct H
    | H: False |- _ => contradiction
    end.

  (* solve_interp_to_values: 将 interp (Fixpoint) 的证明转换为 values (Inductive) 的证明。
     在 [induction e; intros; simpl in *] 之后调用，处理每个 arith constructor 的 case。
     按优先级尝试三种证明模式：

     1. Const-like（目标中无递归、假设是直接等式 [a = n]）：
        subst 消除等式，econstructor 自动选择 ValuesConst，reflexivity 完成。
        例如：[H: a = 3 |- values (Const 3) v a] → subst → [|- values (Const 3) v 3]

     2. Plus-like（假设含嵌套 [exists a1 a2, interp e1 v a1 /\ interp e2 v a2 /\ ...]）：
        break_hyps 分解所有 exists/and，econstructor 选择 ValuesPlus（或类似 constructor），
        eauto 自动应用归纳假设 IHe1, IHe2 来证明子项。
        ★ 新增的递归 arith constructor（如 Times, Minus）只要 interp 定义使用
          exists + and 的标准模式，就会自动被此分支覆盖，无需修改 ★

     3. Var（假设含 [match v $? x with Some n => a = n | None => True end]）：
        对 [v $? x] 做 case analysis（destruct ... eqn:? 保留等式）：
        - Some 分支：eapply ValuesVarDefined，congruence 统一 [v $? x = Some n] 和 [a = n]
        - None 分支：eapply ValuesVarUndefined，congruence 统一 [v $? x = None]
        此模式通过匹配目标 [values (Var ?x) ?v _] 精确识别 Var case。 *)
  Ltac solve_interp_to_values :=
    try (subst; econstructor; reflexivity);
    try (break_hyps; econstructor; eauto; fail);
    match goal with
    | |- values (Var ?x) ?v _ =>
      destruct (v $? x) eqn:?;
      [ eapply ValuesVarDefined; congruence
      | eapply ValuesVarUndefined; congruence ]
    end.

  (* solve_values_to_interp: 将 values (Inductive) 的证明转回 interp (Fixpoint) 的证明。
     在归纳（对证明树 [induct 1] 或对表达式 [induct e; ...; inversion H]）之后调用。
     按优先级尝试三种证明模式：

     1. 等式类（如 ValuesConst 的 [n1 = n2] → 目标 [n2 = n1]）：
        congruence 处理对称/传递等式，一步完成。

     2. Var 的 match 类（目标形如 [match v $? x with Some n => ... | None => True end]）：
        匹配模式 [H: _ $? _ = _ |- _] 精确找到 lookup 等式假设
        （如 [H: v $? x = Some a] 或 [H: v $? x = None]），
        rewrite H 将目标中的 match 化简为具体分支，auto 关闭剩余目标。
        用 fail 包裹确保：如果此模式匹配但未完全解决目标，不会跳到下一步。

     3. 递归情况（如 ValuesPlus 产生的 exists 目标）：
        [repeat eexists] 逐层引入存在量词的 witness（交给 Coq unification 确定值），
        [repeat split] 分解所有合取，
        [eauto] 利用上下文中的归纳假设和等式假设填充所有子目标。
        ★ 新增的递归 arith constructor 会自动被此模式覆盖 ★ *)
  Ltac solve_values_to_interp :=
    try congruence;
    try (match goal with
         | H: _ $? _ = _ |- _ => rewrite H; auto
         end; fail);
    repeat eexists; repeat split; eauto.

  (* Note that the following alternative would also work for ValuesConst and
     ValuesPlus:

                    ---------- ValuesConst
                     n ∈ ⟦n⟧ᵥ

            a1 ∈ ⟦e1⟧ᵥ     a2 ∈ ⟦e2⟧ᵥ
            --------------------------- ValuesPlus
                a1+a2 ∈ ⟦e1+e2⟧ᵥ

     But in Rocq, this would be a bit less convenient, because the tactic
     [eapply ValuesPlus] would only work if the goal is of the shape
     [values _ _ (_ + _)], whereas if we add this extra equality,
     [eapply ValuesPlus] works no matter what the last argument to [values] is,
     and similarly for [ValuesConst]. *)

  (* Contrary to the Fixpoint-based definition "interp", we can't do simplification
     of the kind "replace interp by its body and substitute the arguments in it",
     because an Inductive Prop describes a family of proof trees and isn't a
     function with a right-hand side you could plug in somewhere else.
     In order to prove the example Goal from above for "values", we need to construct
     the following proof tree:

    ("y"↦2) ∈ {"y"↦2}              "z" ∉ dom({"y"↦2})
   -------------------- Defined    ----------------------- Undefined
    2 ∈ ⟦"y"⟧_{"y"↦2}               a-2 ∈ ⟦"z"⟧_{"y"↦2}              a=2+a-2
   ---------------------------------------------------------------------------- ValuesPlus
                        a ∈ ⟦"y"+"z"⟧_{"y"↦2}
  *)
  Example values_example: forall a,
      2 <= a ->
      values (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) a.
  Proof.
    (* "simplify" only introduces the hypotheses but can't really simplify
       anything here. This is not a limitation of "simplify"; it's due to the
       way [values] is defined. *)
    simplify.
    (* Once you define the four constructors for "values", you can uncomment
       the script below. Make sure you understand how it relates to the proof
       tree above! *)
    eapply ValuesPlus with (a1 := 2) (a2 := a - 2).
    - eapply ValuesVarDefined. simplify. equality.
    - eapply ValuesVarUndefined. simplify. equality.
    - linear_arithmetic.
  Qed.

  (* Now, let's prove that "interp" and "values" are equivalent.
     First, [interp -> values]: *)
  Theorem interp_to_values: forall e v a,
      interp e v a -> values e v a.
  Proof.
    induction e; intros; simpl in *; solve_interp_to_values.
  Qed.

  (* To prove the other direction, we have a choice: we can either induct on
     [e] or directly on the proof of [values e v a], because [values] is an
     inductively defined predicate.

     Let's do both proofs.  In general, inducting on the proof tree is the right
     approach, so let's start with that: *)
  Theorem values_to_interp: forall e v a,
      values e v a -> interp e v a.
  Proof.
    induct 1; (* ← do not change this line *)
      simpl; solve_values_to_interp.
  Qed.

  (* Now let's see how things look with an induction on e.  In this simple case,
     it's very similar: *)
  Theorem values_to_interp_induction_on_e: forall e v a,
      values e v a -> interp e v a.
  Proof.
    induct e; (* ← not the best, but for the sake of the exercise do not change this line *)
      simplify; inversion H; subst; solve_values_to_interp.
  Qed.

  (* Let's define nondeterministic big-step semantics for evaluating a command.
     Define [eval] as an Inductive Prop such that [eval v1 c v2] means
     "If we run command c on valuation v1, we can obtain valuation v2".
     Whenever you encounter an arithmetic expression, use [values] to obtain a
     value it can step to.
     Hint: This will be quite similar to [eval] in OperationalSemantics.v! *)
  Inductive eval: valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval v Skip v
  | EvalAssign: forall v x e n,
      values e v n ->
      eval v (Assign x e) (v $+ (x, n))
  | EvalSeq : forall v c1 v1 c2 v2,
      eval v c1 v1 -> eval v1 c2 v2 ->
      eval v (Sequence c1 c2) v2
  | EvalIfTrue : forall v e n thn els v',
      values e v n -> n <> 0 ->
      eval v thn v' ->
      eval v (If e thn els) v'
  | EvalIfFalse : forall v e thn els v',
      values e v 0 ->
      eval v els v' ->
      eval v (If e thn els) v'
  | EvalWhileTrue : forall v e n body v' v'',
      values e v n -> n <> 0 ->
      eval v body v' ->
      eval v' (While e body) v'' ->
      eval v (While e body) v''
  | EvalWhileFalse : forall v e body,
      values e v 0 ->
      eval v (While e body) v
  .

  (* Hint: Many of the proofs below will depend on definitions we ask you to
     find yourself, and if you get these definitions wrong, the proofs will
     not work, so keep in mind that you might have to go back and adapt your
     definitions!
     Also, it can happen that many proofs go through and you become (overly)
     confident that your definitions are correct, even though they aren't. *)

  (* Here's an example program. If we run it on the empty valuation, reading the
     variable "oops" can return any value, but after that, no matter whether
     "oops" was zero or not, we assign a nonzero value to "tmp", so the answer
     will always be 42. *)
  Example the_answer_is_42 :=
    Sequence (Assign "x" (Var "oops"))
             (Sequence (If (Var "x")
                           (Assign "tmp" (Plus (Var "x") (Var "x")))
                           (Assign "tmp" (Const 1)))
                       (If (Var "tmp")
                           (Assign "answer" (Const 42))
                           (Assign "answer" (Const 24)))).

  (* To prove that this sample program always returns 42, we first prove a handy
     helper lemma (the [simplify] tactic will help with [$+]): *)
  Lemma read_last_value: forall x v c n,
      values (Var x) (v $+ (x, c)) n -> n = c.
  Proof.
    intros x v c n H. inversion H; subst a; subst x0; subst v0;
      rewrite lookup_add_eq in H1;
      [ inversion H1 | | discriminate H1 | ]; reflexivity.
  Qed.


  (* Hint: This next theorem is a bit boring -- it's about 30 lines of "invert",
     "simplify", "discriminate", "equality", "linear_arithmetic" and
     "apply read_last_value in H", "subst" in our solution.

     But it's a good test case to make sure you got the definition of "eval"
     right! And note that inverting the hypotheses in the right order, i.e. in
     the order the program is executed, as well as using "read_last_value"
     whenever possible, will make your proof less long.

     (Or, you could use automation — our automated proof is 8 lines long.) *)
  Theorem the_answer_is_indeed_42:
    forall v, eval $0 the_answer_is_42 v -> v $? "answer" = Some 42.
  Proof.
    unfold the_answer_is_42. simplify. invert H.
    invert H5.                  (* The two If sequences *)
    invert H3.                  (* The Assignment for x *)
    invert H6;                  (* The last if for answer *)
      [ invert H9; invert H6; rewrite lookup_add_eq;
        [ reflexivity | reflexivity ]
      | ].
    invert H2.
    - apply read_last_value in H4. subst n0. invert H5;
        [ rewrite lookup_empty in H0; discriminate H0 | ].
      (* The second case is to discriminate 0 = n + n *)
      invert H10. invert H4. apply read_last_value in H2,H3,H7. subst a1.
      subst a2. symmetry in H7. apply Nat.eq_add_0 in H7. linear_arithmetic.
    - apply read_last_value in H6. subst n. invert H9.
      (* This case is to prove that tmp and x should not be zero *)
      apply read_last_value in H7. invert H3. discriminate H0.
  Qed.

  (* Here's another example program. If we run it on a valuation that is
     undefined for "x", it will read the undefined variable "x" to decide
     whether to abort the loop, so any number of loop iterations is possible. *)
  Example loop_of_unknown_length :=
    (While (Var "x") (Assign "counter" (Plus (Var "counter") (Const 1)))).

  (* Hint: you might need the "maps_equal" tactic to prove that two maps are the same. *)
  Theorem eval_loop_of_unknown_length: forall n initialCounter,
      eval ($0 $+ ("counter", initialCounter))
           loop_of_unknown_length
           ($0 $+ ("counter", initialCounter + n)).
  Proof.
    unfold loop_of_unknown_length.
    induct n; simplify.
    - assert (Hmap: ($0 $+ ("counter", initialCounter + 0)) =
                      ($0 $+ ("counter", initialCounter)))
        by (rewrite Nat.add_0_r; reflexivity).
      rewrite Hmap. apply EvalWhileFalse. apply ValuesVarUndefined.
      rewrite lookup_add_ne; [ apply lookup_empty | easy ].
    - apply EvalWhileTrue with (n := 1)
                               (v' := ($0 $+ ("counter", initialCounter + 1))).
      (* Use a non zero n valuation for var x and induction hypotheses *)
      + apply ValuesVarUndefined. rewrite lookup_add_ne;
          [ apply lookup_empty | easy ].
      + linear_arithmetic.
      + assert (Hmap: ($0 $+ ("counter", initialCounter + 1)) =
                        ($0 $+ ("counter", initialCounter)
                           $+ ("counter", initialCounter + 1))) by maps_equal.
        (* Add a more key "counter" to use the prop for eval *)
        rewrite Hmap. apply EvalAssign.
        apply ValuesPlus with (a1 := initialCounter) (a2 := 1).
        * apply ValuesVarDefined. now apply lookup_add_eq.
        * apply ValuesConst. reflexivity.
        * reflexivity.
      + assert (Hn: S n = 1 + n) by linear_arithmetic. rewrite Hn.
        rewrite Nat.add_assoc.
        (* These are middle steps in the loop that satisfy the induction hypotheses *)
        apply IHn.
  Qed.

  (* Wherever this TODO_FILL_IN is used, you should replace it with your own code. *)
  Axiom TODO_FILL_IN: Prop.

  (** * Part 3: Fixpoints with fuel **)

  (* You might wonder whether we can use "Fixpoint" instead of "Inductive" to define
     such nondeterministic big-step evaluation of commands, and indeed we can.
     But we need some trick to convince Rocq that this Fixpoint will always terminate,
     even though there could be infinite loops.

     We achieve this by using a "fuel" argument that limits the recursion depth.
     This does not exclude any possible final valuations, because for every final
     valuation, there exists a recursion depth sufficient to reach it.

     So let's define a Fixpoint [run] such that [run fuel v1 c v2] means
     "if we run command c on valuation v1 and limit the recursion depth to fuel,
     we can obtain valuation v2".

     We already defined all cases for you except the [While] case, but all the
     building blocks you need can be found in the other cases, too.
   *)
  Fixpoint run (fuel: nat) (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    match fuel with
    | O => False
    | S fuel' =>
      match c with
      | Skip => v1 = v2
      | Assign x e => exists a, interp e v1 a /\ v2 = (v1 $+ (x, a))
      | Sequence c1 c2 => exists vmid, run fuel' v1 c1 vmid /\ run fuel' vmid c2 v2
      | If e c1 c2 =>
        (exists r, interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 v2) \/
        (interp e v1 0 /\ run fuel' v1 c2 v2)
      | While e c1 =>
          (* TODO_FILL_IN *)
          (exists r, interp e v1 r /\ r <> 0 /\
                  (exists vmid, run fuel' v1 c1 vmid /\ run fuel' vmid c v2)) \/
            (interp e v1 0 /\ v1 = v2)
      end
    end.

  (* Now let's prove that [run] and [eval] are equivalent! *)

  Local Hint Constructors eval : core.

  (** ===== 自动化辅助 tactic（Part 2: cmd 相关） ===== *)
  (* 以下 tactic 用于自动化 run/eval/wrun 之间的等价性证明。
     设计目标：添加新的 cmd constructor（如 Unset）时，
     只需修改 eval/run 的定义和添加对应的 WRun 引理，
     而 run_to_eval、run_monotone 等核心证明无需改动。 *)

  (* run_to_eval_solver: 将 run (Fixpoint) 的证明转换为 eval (Inductive) 的证明。
     在 [induction fuel; ...; destruct c] 之后，对每个 cmd case 调用。

     工作流程：
     1. break_hyps + subst: 分解 run 展开后的 exists/and/or 结构，消除等式。
        例如 Skip 的 [H: v1 = v2] 会被 subst 消除，
        Sequence 的 [exists vmid, run fuel v1 c1 vmid /\ run fuel vmid c2 v2]
        会被 break_hyps 拆成 [vmid], [H1: run fuel v1 c1 vmid], [H2: run fuel vmid c2 v2]。
     2. interp → values: eval 使用 values 而非 interp 来评估表达式，
        匹配模式 [H: interp _ _ _ |- _] 将每个 interp 假设通过 interp_to_values 转换。
        例如 Assign 的 [H: interp e v1 a] 变成 [H: values e v1 a]。
     3. run → eval: 匹配 [H: run _ _ _ _ |- _] 通过归纳假设 IHfuel 将递归的 run 转为 eval。
        例如 [H: run fuel v1 c1 vmid] 变成 [H: eval v1 c1 vmid]。
     4. eauto 7: 利用 [Hint Constructors eval] 自动选择正确的 eval constructor。
        深度 7 足以覆盖 EvalWhileTrue（最深的 constructor，需统一 4 个前提）。
        eauto 的搜索过程：尝试 eapply EvalWhileTrue/EvalSeq/...，
        然后递归地用 eassumption 匹配各前提。

     ★ 添加新的 cmd constructor 时：
       只要 run 的新 case 使用 exists/and/or/interp 的标准模式，
       且 eval 的新 constructor 已注册为 Hint，此 tactic 自动覆盖 ★ *)
  Ltac run_to_eval_solver :=
    break_hyps; subst;
    repeat match goal with
    | H: interp _ _ _ |- _ => apply interp_to_values in H
    end;
    (* 通过类型模式匹配找到归纳假设 IH，而非依赖具体名称。
       匹配模式 [IH: forall _ _ _, run _ _ _ _ -> eval _ _ _] 精确匹配
       "对任意 v1 c v2，run fuel v1 c v2 → eval v1 c v2" 形状的假设。
       这样即使 Coq 将 IH 命名为 IHfuel、IHn 或其他名称，都能正确找到。 *)
    repeat match goal with
    | H: run _ _ _ _ |- _ =>
        match goal with
        | IH: forall _ _ _, run _ _ _ _ -> eval _ _ _ |- _ =>
            apply IH in H
        end
    end;
    eauto 7.

  (* mono_rebuild_core: 递归重建目标的 exists/and/or 结构。
     参数 run_handler 是一个 tactic，用于处理叶子位置的 [run] 目标。
     目前在 run_monotone 中使用：传入 [idtac]（fuel 已由 upgrade_fuel 预处理）。

     注意：Ltac1 中将复杂 tactic 作为参数传递给递归 tactic 时存在已知问题
     （tactic closure 在递归调用中可能丢失上下文）。
     因此，combine_wrun 使用独立的 [wrun_rebuild] tactic（将 run_monotone 逻辑硬编码），
     而非 [mono_rebuild_core ltac:(run_handler)]。

     递归重建过程（自顶向下匹配目标结构）：
     - try subst: 消除上下文中的等式假设
     - try eassumption: 如果目标与某假设一致（含 unification），直接完成
     - try reflexivity: 处理 [v = v] 等自反等式
     - try run_handler: 尝试用传入的 handler 处理 [run] 目标

     结构匹配（match goal with）：
     - [|- _ \/ _]: 析取目标（如 If/While 的两种情况）。
       用 first 尝试 left 再 right，利用 Ltac 的 backtracking 机制：
       如果 left 分支的递归重建失败，自动回退尝试 right。
     - [|- exists _, _]: 存在量词目标。
       eexists 引入 unification variable，递归处理子目标。
     - [|- _ /\ _]: 合取目标。split 分解后递归处理两个子目标。
     - 默认: eassumption 或 reflexivity。

     终止性：每次递归，目标严格变小（剥离一层 or/exists/and），保证终止。 *)
  (* 注意：使用 eassumption 而非 assumption，因为 eexists 引入的 unification variable
     需要在匹配时进行统一（unification），而 assumption 不支持 unification variable，
     只有 eassumption 会尝试将目标中的 evar 与假设统一。
     例如：eexists 后目标为 [interp e v ?a]，假设为 [H: interp e v 42]，
     assumption 失败（?a ≠ 42），eassumption 成功（统一 ?a := 42）。 *)
  Ltac mono_rebuild_core run_handler :=
    try subst;
    try eassumption;
    try reflexivity;
    try run_handler;
    match goal with
    | |- _ \/ _ =>
        first [ left; mono_rebuild_core run_handler
              | right; mono_rebuild_core run_handler ]
    | |- exists _, _ =>
        eexists; mono_rebuild_core run_handler
    | |- _ /\ _ =>
        split; [ mono_rebuild_core run_handler
               | mono_rebuild_core run_handler ]
    | _ => eassumption || reflexivity
    end.

  (* upgrade_fuel: 将假设中所有 [run fuel1 v c v2] 升级为 [run fuel2 v c v2]。
     专用于 run_monotone 的归纳步骤，配合归纳假设 IHfuel1 使用。

     匹配模式 [H: run _ ?v ?c ?v2 |- _]:
     - 捕获任何 run 假设（不限定 fuel）
     - ?v, ?c, ?v2 分别绑定 valuation、cmd、结果 valuation
     - 使用 [IHfuel1 _ v c v2 ltac:(assumption) H]:
       · IHfuel1 的类型: [forall fuel2 v1 c v2, fuel1 <= fuel2 -> run fuel1 v1 c v2 -> run fuel2 v1 c v2]
       · 第一个 _ 留给 Coq 推断目标 fuel（通过 assumption 找到 [Hlt: fuel1 <= fuel2] 来确定）
       · ltac:(assumption) 自动在上下文中找到 [fuel1 <= fuel2] 的证明
       · H 是原始的 [run fuel1 ...] 假设
     - clear + rename: 用升级后的假设替换原始假设，保持名称不变

     防止无限循环：升级后 H 变为 [run fuel2 v c v2]。
     再次匹配时，IHfuel1 期望 [run fuel1 ...]，unification 将 fuel2 与 fuel1 统一会失败
     （因为它们是不同的变量），于是 pose proof 失败，repeat 停止。 *)
  (* upgrade_fuel: 将假设中所有 [run fuel_old v c v2] 升级为 [run fuel_new v c v2]。
     专用于 run_monotone 的归纳步骤。

     工作流程：
     1. 外层 match 找到一个 [run] 假设 H
     2. 内层 match 通过类型模式找到归纳假设 IH（而非依赖名称 IHfuel1）：
        [IH: forall _ _ _ _, _ <= _ -> run _ _ _ _ -> run _ _ _ _]
        匹配 "对任意 fuel2 v c v2，fuel1 <= fuel2 → run fuel1 ... → run fuel2 ..."
     3. 用 IH 升级 H 的 fuel：pose proof (IH _ v c v2 ltac:(assumption) H)
        · 第一个 _ 由 Coq 推断（通过 assumption 找到 [fuel1 <= fuel2] 确定 fuel2）
        · assumption 自动在上下文中找到不等式证明
     4. clear + rename: 替换旧假设

     防止无限循环：升级后 H 的 fuel 从 fuel1 变为 fuel2，
     再次 apply IH 时 Coq 无法将 fuel2 统一为 IH 期望的 fuel1，pose proof 失败。 *)
  Ltac upgrade_fuel :=
    repeat match goal with
    | H: run _ ?v ?c ?v2 |- _ =>
        match goal with
        | IH: forall _ _ _ _, _ <= _ -> run _ _ _ _ -> run _ _ _ _ |- _ =>
            let H' := fresh in
            (* 使用 eassumption 而非 assumption：
               IH 的第一个参数 _ 是 unification variable（目标 fuel），
               需要 eassumption 将 [fuel1 <= ?fuel2] 与 [Hlt: fuel1 <= fuel2] 统一 *)
            pose proof (IH _ v c v2 ltac:(eassumption) H) as H';
            clear H; rename H' into H
        end
    end.

  Theorem run_to_eval: forall fuel v1 c v2,
      run fuel v1 c v2 ->
      eval v1 c v2.
  Proof.
    (* 用 induction 而非 Frap 的 induct，保持 IHfuel 通用（不被 instantiate_obviouses 特化） *)
    induction fuel; simpl; intros v1 c v2 Hrun;
      [ contradiction | ].
    destruct c; run_to_eval_solver.
  Qed.


  (* To prove the other direction, we will need the following lemma, which shows
     that excess fuel isn't an issue.

     Hint: Here, some proof automation might pay off!

     You could try writing a [repeat match goal] loop, to do all possible
     simplifications on your hypotheses and then use [eauto] to solve
     the goal. Maybe you need to increase the maximum search depth of eauto;
     in our solution, we had to write [eauto 9] instead of just [eauto],
     which defaults to [eauto 5].

     Some useful documentation pointers:
     - https://rocq-prover.org/doc/V9.0.0/refman/proofs/automatic-tactics/auto.html#coq:tacn.eauto
     - https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/ltac.html#pattern-matching-on-goals-and-hypotheses-match-goal

     And note that [eauto] does not know about linear arithmetic by default,
     so you could consider registering it as a [Hint Extern], but a simpler
     way here would be to use the lemma "le_S_n" to turn "S fuel1 <= S fuel2"
     into "fuel1 <= fuel2", which will be needed for the IH. *)

  Lemma run_monotone: forall fuel1 fuel2 v1 c v2,
      fuel1 <= fuel2 ->
      run fuel1 v1 c v2 ->
      run fuel2 v1 c v2.
  Proof.
    (* 用 induction 而非 Frap 的 induct，保持 IH 通用 *)
    induction fuel1; simpl; intros fuel2 v1 c v2 Hleq Hfuel1;
      [ exfalso; exact Hfuel1 | ].
    destruct fuel2; [ linear_arithmetic | ].
    assert (Hlt: fuel1 <= fuel2) by (apply (le_S_n fuel1 fuel2 Hleq)).
    destruct c; cbn;
      break_hyps; upgrade_fuel;
      mono_rebuild_core ltac:(idtac).
  Qed.

  (* For the other direction, we could naively start proving it like this: *)
  Theorem eval_to_run: forall v1 c v2,
      eval v1 c v2 -> exists fuel, run fuel v1 c v2.
  Proof.
    induct 1; simplify.
    (* This proof is relatively short and straightforward, but dealing with
       existentials is not very pleasant!

       This problem becomes worse if we make many proofs about "run".  So, instead,
       let's look at a nicer formulation of this theorem. *)
  Abort. (* <-- do not change this line *)


  (* We will first define a wrapper around "run" that hides the existential: *)
  Definition wrun (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    exists fuel, run fuel v1 c v2.

  (* The idea is that in the run_to_eval proof above, using the constructors of
     "eval", i.e. doing "eapply EvalAssign", "eapply EvalSeq", "eapply EvalIfTrue",
     was quite convenient, so let's expose the same "API" for constructing proofs
     of "run" (or actually, proofs of the slightly nicer "wrun"). *)

  (* Now let's define proof rules to get the same "API" for "wrun" as for "eval".
     Hint: Again, some proof automation might simplify the task (but manual proofs are
     possible too, of course).  You may find the `max` function useful. *)

  (* combine_wrun: 合并 wrun 证明中的多个 fuel 值。
     所有 WRun* 引理共用此 tactic，极大减少重复代码。

     工作流程：
     1. unfold wrun: 暴露 [exists fuel, run fuel ...] 结构
     2. break_hyps: 分解 exists/and，得到具体的 fuel 值和 run 假设
     3. 选择足够大的 fuel（用 first 按优先级尝试三种情况）：
        - 两个 run 假设（如 Seq, WhileTrue）: 用 S (f1 + f2)
          确保 f1 <= f1+f2 且 f2 <= f1+f2，run_monotone 可升级两个子 run
        - 一个 run 假设（如 Assign, IfTrue, IfFalse）: 用 S f
          一层 S 展开外层 run，内层 run 直接用原 fuel
        - 无 run 假设（如 Skip, WhileFalse）: 用 1
          一步 fuel 就足够
     4. simpl 展开外层 run 的 match
     5. mono_rebuild_core 递归重建目标结构
        传入 run_handler 使用 [eapply run_monotone; [linear_arithmetic | exact H]]
        即时将内层 run 的 fuel 从 fi 升级到 f1+f2

     ★ 添加新的 cmd constructor 时：
       只需定义新的 WRun* 引理的 statement + 一行 [combine_wrun] 证明 ★ *)
  (* wrun_rebuild: 专用于 combine_wrun 的重建 tactic。
     与 mono_rebuild_core 类似，但将 run_monotone 处理硬编码在内，
     避免 Ltac1 的 tactic 参数在递归中传递时的问题。

     工作流程与 mono_rebuild_core 相同，但在处理 run 目标时，
     直接调用 wrun_run_monotone 而非依赖参数化的 run_handler。 *)
  Ltac wrun_rebuild :=
    try subst;
    try eassumption;
    try reflexivity;
    try (match goal with
         | H: run _ _ _ _ |- run _ _ _ _ =>
             eapply run_monotone; [| exact H]; linear_arithmetic
         end);
    match goal with
    | |- _ \/ _ =>
        first [ left; wrun_rebuild | right; wrun_rebuild ]
    | |- exists _, _ =>
        eexists; wrun_rebuild
    | |- _ /\ _ =>
        split; [ wrun_rebuild | wrun_rebuild ]
    | _ => eassumption || reflexivity
    end.

  (* combine_wrun: 合并 wrun 证明中的多个 fuel 值。
     所有 WRun* 引理共用此 tactic。

     工作流程：
     1. unfold wrun: 暴露 [exists fuel, run fuel ...] 结构
     2. break_hyps: 分解 exists/and，得到具体的 fuel 值和 run 假设
     3. 选择足够大的 fuel（用 first 按优先级尝试三种情况）：
        - 两个 run 假设（如 Seq, WhileTrue）: 用 S (f1 + f2)
        - 一个 run 假设（如 Assign, IfTrue, IfFalse）: 用 S f
        - 无 run 假设（如 Skip, WhileFalse）: 用 1
     4. simpl 展开外层 run 的 match
     5. mono_rebuild_core 递归重建目标结构，
        传入 wrun_run_monotone 处理 run 子目标

     ★ 添加新的 cmd constructor 时：
       只需定义新的 WRun* 引理的 statement + 一行 [combine_wrun] 证明 ★ *)
  Ltac combine_wrun :=
    unfold wrun in *; break_hyps;
    first
    [ (* 两个 run 假设的情况 *)
      match goal with
      | H1: run ?f1 _ _ _, H2: run ?f2 _ _ _ |- _ =>
          exists (S (f1 + f2)); simpl; wrun_rebuild
      end
    | (* 一个 run 假设的情况 *)
      match goal with
      | H: run ?f _ _ _ |- _ =>
          exists (S f); simpl; wrun_rebuild
      end
    | (* 无 run 假设的情况 *)
      exists 1; simpl; wrun_rebuild
    ].

  Definition WRunSkip_statement : Prop :=
    forall v,
      wrun v Skip v.
  Lemma WRunSkip: WRunSkip_statement.
  Proof. unfold WRunSkip_statement; intros; combine_wrun. Qed.

  Definition WRunAssign_statement : Prop :=
    forall v x e a,
      interp e v a ->
      wrun v (Assign x e) (v $+ (x, a)).
  Lemma WRunAssign: WRunAssign_statement.
  Proof. unfold WRunAssign_statement; intros; combine_wrun. Qed.

  Definition WRunSeq_statement : Prop :=
    forall v c1 v1 c2 v2,
      wrun v c1 v1 ->
      wrun v1 c2 v2 ->
      wrun v (Sequence c1 c2) v2.
  Lemma WRunSeq: WRunSeq_statement.
  Proof. unfold WRunSeq_statement; intros; combine_wrun. Qed.

  (* For the next few lemmas, we've left you the job of stating the theorem as
     well as proving it. *)

  Definition WRunIfTrue_statement : Prop :=
    forall v e c1 v2 c2,
      (exists r, interp e v r /\ r <> 0 /\ wrun v c1 v2) ->
      wrun v (If e c1 c2) v2.
  Lemma WRunIfTrue: WRunIfTrue_statement.
  Proof. unfold WRunIfTrue_statement; intros; combine_wrun. Qed.

  Definition WRunIfFalse_statement : Prop :=
    forall v e c1 v1 c2,
      interp e v 0 /\ wrun v c2 v1 ->
      wrun v (If e c1 c2) v1.
  Lemma WRunIfFalse: WRunIfFalse_statement.
  Proof. unfold WRunIfFalse_statement; intros; combine_wrun. Qed.

  Definition WRunWhileTrue_statement : Prop :=
    forall v e c v1,
      (exists r, interp e v r /\ r <> 0 /\
              (exists vmid, wrun v c vmid /\ wrun vmid (While e c) v1)) ->
      wrun v (While e c) v1.
  Lemma WRunWhileTrue: WRunWhileTrue_statement.
  Proof. unfold WRunWhileTrue_statement; intros; combine_wrun. Qed.

  Definition WRunWhileFalse_statement : Prop :=
    forall v e c v1,
      interp e v 0 /\ v = v1 ->
      wrun v (While e c) v1.
  Lemma WRunWhileFalse: WRunWhileFalse_statement.
  Proof. unfold WRunWhileFalse_statement; intros; combine_wrun. Qed.

  (* solve_eval_to_wrun: 将 eval (Inductive) 的证明转换为 wrun 的证明。
     在 [induct 1]（对 eval 的证明树归纳）之后，对每个 eval constructor 调用。

     使用 first 按优先级尝试每个 WRun 引理：
     - WRunSkip: 匹配 [eval v Skip v]，直接完成
     - WRunAssign: 匹配 [eval v (Assign x e) ...]，需要 values_to_interp 转换表达式
     - WRunSeq: 匹配 [eval v (Sequence c1 c2) v2]，用 eassumption 匹配两个归纳假设
     - WRunIfTrue/False: 匹配 [eval v (If e c1 c2) v']，
       用 first 尝试 True 分支和 False 分支（由 backtracking 自动选择正确分支）
     - WRunWhileTrue/False: 匹配 [eval v (While e c) v']，同上
     每种情况用 values_to_interp 将 eval 的 values 前提转换为 interp 前提（wrun 使用 interp）。

     ★ 添加新的 cmd constructor 时：
       只需在此 tactic 中添加一个新的 [apply WRunXxx; ...] 分支 ★ *)
  Ltac solve_eval_to_wrun :=
    first
    [ apply WRunSkip
    | apply WRunAssign; apply values_to_interp; eassumption
    | eapply WRunSeq; eassumption
    | apply WRunIfTrue; eexists; repeat split;
      [ apply values_to_interp; eassumption | assumption | assumption ]
    | apply WRunIfFalse; split;
      [ apply values_to_interp; eassumption | assumption ]
    | apply WRunWhileTrue; eexists; repeat split;
      [ apply values_to_interp; eassumption | assumption
      | eexists; split; eassumption ]
    | apply WRunWhileFalse; split;
      [ apply values_to_interp; eassumption | reflexivity ]
    ].

  (* Now, thanks to these helper lemmas, proving the direction from eval to wrun
     becomes easy: *)
  Theorem eval_to_wrun: forall v1 c v2,
      eval v1 c v2 ->
      wrun v1 c v2.
  Proof.
    induct 1; solve_eval_to_wrun.
  Qed.

  (* Remember when we said earlier that [induct 1] does induction on the proof
     of [eval], whereas [induct c] does induction on the program itself?  Try
     proving the above with [induct c] instead of [induct 1], skipping straight
     to the [While] cases.  Why isn't the theorem provable this way? *)

  (* The following definitions are needed because of a limitation of Rocq
     (the kernel does not recognize that a parameter can be instantiated by an
     inductive type).
     Please do not remove them! *)
  Definition values_alias_for_grading := values.
  Definition eval_alias_for_grading := eval.

  (* You've reached the end of this pset, congratulations! *)

  (* ****** Everything below this line is optional ****** *)

  (* Many of the proofs above can be automated.  A good way to test your
     automation is to make small changes to the language.

     For example, you could add an [Unset: string -> cmd] constructor to the
     definition of [cmd]; the semantics of that command should be to remove a
     variable from the current valuation (use [v $- "x"] to remove ["x"] from
     [v]).

     In our solution, adding [Unset] and updating definitions and proofs
     accordingly takes just a few extra lines.  Try it in yours! *)

  (* Let's take the deterministic semantics we used in OperationalSemantics.v but
     prefix them with "d" to mark them as deterministic: *)

  Fixpoint dinterp (e: arith) (v: valuation): nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => dinterp e1 v + dinterp e2 v
    end.

  Inductive deval: valuation -> cmd -> valuation -> Prop :=
  | DEvalSkip: forall v,
      deval v Skip v
  | DEvalAssign: forall v x e,
      deval v (Assign x e) (v $+ (x, dinterp e v))
  | DEvalSeq: forall v c1 v1 c2 v2,
      deval v c1 v1 ->
      deval v1 c2 v2 ->
      deval v (Sequence c1 c2) v2
  | DEvalIfTrue: forall v e thn els v',
      dinterp e v <> 0 ->
      deval v thn v' ->
      deval v (If e thn els) v'
  | DEvalIfFalse: forall v e thn els v',
      dinterp e v = 0 ->
      deval v els v' ->
      deval v (If e thn els) v'
  | DEvalWhileTrue: forall v e body v' v'',
      dinterp e v <> 0 ->
      deval v body v' ->
      deval v' (While e body) v'' ->
      deval v (While e body) v''
  | DEvalWhileFalse: forall v e body,
      dinterp e v = 0 ->
      deval v (While e body) v.

  (* Now let's prove that if a program evaluates to a valuation according to the
     deterministic semantics, it also evaluates to that valuation according to
     the nondeterministic semantics (the other direction does not hold, though). *)
  Theorem deval_to_eval: forall v1 v2 c,
      deval v1 c v2 ->
      eval v1 c v2.
  Proof.
  Admitted.

  (* In deterministic semantics, Fixpoints work a bit better, because they
     can return just one value, and let's use "option" to indicate whether
     we ran out of fuel: *)
  Fixpoint drun(fuel: nat) (v: valuation) (c: cmd): option valuation. Admitted.

  (* More open-ended exercise:
     Now we have six different definitions of semantics:

                          deterministic     nondeterministic

     Inductive            deval             eval

     Wrapped Fixpoint     dwrun             wrun

     Fixpoint             drun              run

     We have proved that all the nondeterministic semantics are equivalent among
     each other.
     If you want, you could also prove that all the deterministic semantics are
     equivalent among each other and experiment whether it's worth creating an
     "Inductive"-like API for "dwrun", or whether you're ok dealing with drun's
     existentials when proving deval_to_drun.
     Moreover, we have proved that "deval" implies "eval", so every definition in
     the left column of the above table implies every definition in the right
     column of the table.
     If you're curious to learn more about the trade-offs between Inductive Props
     and Fixpoints, you can try to prove some of these implications directly
     and see how much harder than "deval_to_eval" it is (we believe that
     "deval_to_eval" is the simplest one).
   *)

End Impl.

Module ImplCorrect : Pset5Sig.S := Impl.

(* Authors:
   Samuel Gruetter
   Clément Pit-Claudel *)
