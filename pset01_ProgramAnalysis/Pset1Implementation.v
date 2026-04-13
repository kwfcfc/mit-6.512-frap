(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 1 *)

(* Welcome to 6.512!  Read through `Pset1Signature.v` before starting here. *)

Require Import Frap Pset1Signature.

Module Impl.
  (* The first part of this assignment involves the [bool] datatype,
   * which has the following definition.
   * <<
       Inductive bool :=
       | true
       | false.
     >>
   * We will define logical negation and conjunction of Boolean values,
   * and prove some properties of these definitions.
   *)

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Definition Neg (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Theorem Neg_true : Neg true = false.
  Proof.
      simpl. reflexivity.
  Qed.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
  Proof.
    intro b. destruct b.
    all: simpl; reflexivity.
  Qed.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  Definition And (x y : bool) : bool :=
    match x with
    | true => y
    | false => false
    end.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Theorem And_true_true : And true true = true.
  Proof.
    simpl; reflexivity.
  Qed.

  Theorem And_false_true : And false true = false.
  Proof.
    simpl; reflexivity.
  Qed.


  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Theorem And_comm : forall x y : bool, And x y = And y x.
  Proof.
    intros x y. destruct x.
    (* split by x for true and false, and then induct on y *)
    all: simpl; destruct y;
      simpl; reflexivity.
Qed.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Theorem And_true_r : forall x : bool, And x true = x.
  Proof.
    intro x; destruct x.
    all: simpl; reflexivity.
  Qed.

  (* You may have noticed that the [=] operator above does not return a [bool]. *)
  Check (true = false).

  (* [a = b] is instead a [Prop], short for proposition, the type of logical
   * statements. The set of propositions in Rocq is large and contains a variety
   * of statements, many of which are undecideable, so we can't in general
   * treat statements in [Prop] as functions with Boolean output. This means
   * that you can't use expressions of type [Prop] when defining a program,
   * since they don't have computational behavior. For example, compare how
   * the following two expressions evaluate. The first expression uses functions
   * we can compute with, while the second uses propositions:
   *)
  Compute (if 1 ==n 2 then (And true false) else true).
  Compute (1 = 2 -> True /\ False).

  (* The following operations that you have seen or will see soon are in [Prop],
   * so they cannot be used in if-then-else statements:
   * - [a = b] (equality at an arbitrary type)
   * - [a <= b] (a less than or equal to b for natural numbers)
   * - [a < b] (a less than b for natural numbers)
   * - [a >= b] (a greater than or equal to b for natural numbers)
   * - [a > b] (a greater than b for natural numbers)
   * - [a <> b] (inequality at an arbitrary type)
   * - [a /\ b] (propositional conjunction)
   * - [~ a] (propositional negation)
   *
   * These operations are defined as functions, so you can evalute them:
   * - [a ==n b] (decidable equality for natural numbers)
   * - [a ==v b] (decidable equality for variables)
   * - [And a b] (Boolean conjunction, defined above)
   * - [Neg a] (Boolean negation, defined above)
   *
   * To see an example of what can go wrong, uncommment the following [Compute] command
   * and note the reported error message.
   *)

  (* Compute if 0 < 1 then 0 else 1. *)

  (* The correct boolean version. *)
  Compute if Nat.ltb 0 1 then 0 else 1.

  (* In the second part of this assignment, we will work with a simple language
   * of imperative arithmetic programs that sequentially apply operations
   * to a natural-number-valued state.
   *
   * Remember that we are working with natural division which rounds down.
   * Note the output of these [Compute] commands.
   *)

  Compute 3 / 3.
  Compute 2 / 3.
  Compute 4 / 3.

  (*

   * The [Prog] datatype defines abstract syntax trees for this language.
   *)

  Print Prog.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Fixpoint run (p : Prog) (initState : nat) : nat :=
    match p with
    | Done => initState
    | AddThen n p' => run p' (n + initState)
    | MulThen n p' => run p' (n * initState)
    | DivThen n p' => run p' (initState / n)
    | VidThen n p' => run p' (n / initState)
    | SetToThen n p' => run p' n
    end.

  Theorem run_Example1 : run Done 0 = 0.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  Proof.
    simpl. reflexivity.
  Qed.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Fixpoint numInstructions (p : Prog) : nat :=
    match p with
    | Done => 0
    | AddThen _ p' => 1 + numInstructions(p')
    | MulThen _ p' => 1 + numInstructions(p')
    | DivThen _ p' => 1 + numInstructions(p')
    | VidThen _ p' => 1 + numInstructions(p')
    | SetToThen _ p' => 1 + numInstructions(p')
    end.

  Theorem numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  Proof.
    simpl. reflexivity.
  Qed.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Fixpoint concatProg (p1 p2 : Prog) : Prog :=
    match p1 with
    | Done => p2
    | AddThen n p' => AddThen n (concatProg p' p2)
    | MulThen n p' => MulThen n (concatProg p' p2)
    | DivThen n p' => DivThen n (concatProg p' p2)
    | VidThen n p' => VidThen n (concatProg p' p2)
    | SetToThen n p' => SetToThen n (concatProg p' p2)
    end.


  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Theorem concatProg_numInstructions
    : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                        = numInstructions p1 + numInstructions p2.
  Proof.
    intros p1 p2. induction p1.
    all: simpl; try reflexivity; rewrite IHp1; reflexivity.
  Qed.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Theorem concatProg_run
    : forall (p1 p2 : Prog) (initState : nat),
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).
  Proof.
    intros p1 p2. induction p1; try reflexivity.
    all: simpl; intro s; apply IHp1.
  Qed.

  (* Read this definition and understand how division by zero is handled. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.
  Arguments Nat.div : simpl never. (* you don't need to understand this line *)

  (* Here are a few examples: *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Example runPortable_good : forall n,
    runPortable goodProgram1 n = (true, 10/(1+n)).
  Proof. simplify. equality. Qed.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Example runPortable_bad : let n := 0 in
    runPortable badProgram1 n = (false, 0).
  Proof. simplify. equality. Qed.

  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  Example runPortable_bad2 : forall n,
    runPortable badProgram2 n = (false, 1+n).
  Proof. simplify. equality. Qed.

  (* Prove that running the concatenation [p] using [runPortable]
     coincides with using [run], as long as [runPortable] returns
     [true] to confirm that no divison by zero occurred. *)
  Lemma runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.
  Proof.
    intros p. induction p; intros s0 s1 H; simpl; simpl in H; try (inversion H; reflexivity).
    (* use apply IHP1 to finish Add, Mul and Set*)
    all: try (apply IHp; exact H).
    - destruct n; simpl in H;
      [ inversion H | apply IHp in H; exact H ].
    - destruct s0; simpl in H;
      [ inversion H | apply IHp in H; exact H ].
  Qed.

  (* The final goal of this pset is to implement [validate : Prog -> bool]
     such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     division by zero, but it must recognize as good the examples given below.  In
     jargon, [validate] is required to be sound but not complete, but "complete
     enough" for the use cases defined by the examples given here: *)

  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

  (* If you already see a way to build [validate] that meets the
   * requirements above, _and have a plan for how to prove it correct_,
   * feel free to just code away. Our solution uses one intermediate definition
   * and one intermediate lemma in the soundness proof -- both of which are more
   * sophisticated than the top-level versions given here. *)

  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
   * take a look at the hints for this pset at the end of the signature file.
   * It is not expected that this pset is doable for everyone without the hints,
   * and some planning is required to complete the proof successfully.
   * In particular, repeatedly trying out different combinations of tactics
   * and ideas from hints until something sticks can go on for arbitrarily long
   * with little insight and no success; just guessing a solution is unlikely.
   * Thus, we encourage you to take your time to think, look at the hints when
   * necessary, and only jump into coding when you have some idea why it should
   * succeed. Some may call Rocq a video game, but it is not a grinding contest. *)

  Fixpoint validateFunc (p : Prog) (stateNonZero : bool) : bool :=
    match p with
    | Done => true
    (* because it is on natural number, no non zero numbers can add to zero *)
    | AddThen n p' => validateFunc p' (stateNonZero || (Nat.ltb 0 n))
    | MulThen n p' => validateFunc p' (And stateNonZero (Nat.ltb 0 n))
    | DivThen 0 p' => false
    | DivThen 1 p' => validateFunc p' stateNonZero
    | DivThen (S (S _)) p' => validateFunc p' false
    (* We cannot handle some cases when division rounds down to 0 so we set it to false*)
    | VidThen _ p' => And stateNonZero (validateFunc p' false)
    | SetToThen n p' => validateFunc p' (Nat.ltb 0 n)
    end.

  Definition validate (p : Prog) : bool := validateFunc p false.

  Lemma validateFuncZeroImpliesNonZero :
    forall p : Prog, validateFunc p false = true -> validateFunc p true = true.
  Proof.
    intros p H. induct p; simpl; try reflexivity.
    all: destruct n; try discriminate H; try destruct n;
      cbn; cbn in H; try exact H; apply IHp; exact H.
    (* - destruct n; cbn; cbn in H; try exact H; apply IHp; exact H. *)
    (* - destruct n. *)
    (*   + cbn. cbn in H. exact H. *)
    (*   + cbn. cbn in H. apply IHp. exact H. *)
    (* - destruct n. *)
    (*   + discriminate H. *)
    (*   + destruct n. *)
    (*     * cbn in H. apply IHp. exact H. *)
    (*     * cbn in H. exact H. *)
    (* - destruct n. cbn; cbn in H. discriminate H. *)
  Qed.

  Lemma validateFunc_sound :
    forall p : Prog,
        (validateFunc p true = true -> forall s, s <> 0 -> runPortable p s = (true, run p s)) /\
        (validateFunc p false = true -> forall s, runPortable p s = (true, run p s)).
  Proof.
    (* two common tactics *)
    Ltac use_IH0 IH Hp := apply IH; exact Hp.
    Ltac use_IH IH Hp := apply IH; [ exact Hp | discriminate ].
    
    intros p. induction p; split.
    all: try reflexivity; intros Hp s; destruct IHp as [ IHps IHps0 ]; simpl.
    - intro Hs. apply IHps.
      + exact Hp.
      + destruct s as [|s']; [ contradiction | rewrite Nat.add_succ_r; discriminate ].
    - destruct n; simpl.
      { apply IHps0. cbn in Hp. exact Hp. }
      cbn in Hp. apply IHps; [ exact Hp | discriminate ].
    - intro Hs. destruct n; simpl; cbn in Hp.
      + apply IHps0. exact Hp.
      + apply IHps; [
            exact Hp |
            destruct s as [|s']; [ contradiction | discriminate ] ].
    - destruct s; cbn in Hp.
      { rewrite Nat.mul_0_r. apply IHps0. exact Hp. }
      destruct n.
      + rewrite Nat.mul_0_l. apply IHps0. exact Hp.
      + cbn. apply IHps; [
        apply validateFuncZeroImpliesNonZero; exact Hp |
        discriminate].
    - intro Hs. destruct n; simpl; cbn in Hp; try discriminate.
      destruct n; simpl; cbn in Hp.
      + rewrite Nat.div_1_r.
        destruct s as [|s']; [ contradiction |
                               apply IHps; [ exact Hp | discriminate ] ].
      + apply IHps0. exact Hp.
    - destruct n; simpl; try discriminate.
      destruct n; simpl; cbn in Hp.
      + rewrite Nat.div_1_r.
        destruct s as [|s'];
          [ apply IHps0; exact Hp |
            apply IHps;
            [ apply validateFuncZeroImpliesNonZero; exact Hp |
              discriminate]].
      + apply IHps0. exact Hp.
    - intro Hs. destruct s; simpl; try contradiction. cbn in Hp. apply IHps0.
      exact Hp.
    - destruct s; simpl; try discriminate.
    - intro Hs. destruct n; simpl; cbn in Hp;
        [ apply IHps0; exact Hp | apply IHps; [ exact Hp | discriminate ] ].
    - destruct n; simpl; cbn in Hp;
        [ apply IHps0; exact Hp | apply IHps; [ exact Hp | discriminate ] ].
  Qed.
      

  (* Start by making sure that your solution passes the following tests, and add
   * at least one of your own tests: *)

  Example validate1 : validate goodProgram1 = true. compute. reflexivity. Qed.
  Example validate2 : validate goodProgram2 = true. compute. reflexivity. Qed.
  Example validate3 : validate goodProgram3 = true. compute. reflexivity. Qed.
  Example validate4 : validate goodProgram4 = true. compute. reflexivity. Qed.
  Example validate5 : validate goodProgram5 = true. compute. reflexivity. Qed.
  Example validate6 : validate goodProgram6 = true. compute. reflexivity. Qed.
  Example validate7 : validate goodProgram7 = true. compute. reflexivity. Qed.
  Example validateb1 : validate badProgram1 = false. compute. reflexivity. Qed.
  Example validateb2 : validate badProgram2 = false. compute. reflexivity. Qed.

  (* Then, add your own example of a bad program here, and check that `validate`
   * returns `false` on it: *)

  Definition badProgram3 : Prog := AddThen 3 (MulThen 0 (VidThen 1 Done)).
  Example validateb3 : validate badProgram3 = false. compute. reflexivity. Qed.



  (* Finally, before diving into the Rocq proof, try to convince yourself that
   * your code is correct by applying induction by hand.  Can you describe the
   * high-level structure of the proof?  Which cases will you have to reason
   * about?  What do the induction hypotheses look like?  Which key lemmas do
   * you need?  Write a short (~10-20 lines) informal proof sketch before
   * proceeding. *)

  (** Proof sketch: **)
  (* Split into different cases. Return true on Done. Pass down to inner Prog
   * if it is Set, Add and Mul, and try to guess the current state. Test on Div
   * and Vid by compare whether current state and popped out number is zero.
   *)

  (* Now you're ready to write the proof in Rocq: *)

  Lemma validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
  Proof.
    unfold validate. intros p Hp s.
    apply validateFunc_sound. exact Hp.
  Qed.

  (* Here is the complete list of commands used in one possible solution:
    - Search, for example Search (_ + 0).
    - induct, for example induct x
    - simplify
    - propositional
    - equality
    - linear_arithmetic
    - cases, for example cases (X ==n Y)
    - apply, for example apply H
    - apply in, for example apply H1 in H2 or apply somelemma in H1
    - apply with, for example apply H1 with (x:=2)
    - apply in with, for example apply H1 with (x:=2) in H2
    - rewrite, for example rewrite H
    - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
    - ;, for example simplify; propositional *)
End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Rocq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset1Signature.S := Impl.
