import Plausible.GeneratingGoodGenerators.Schedules
open Lean

/-- The sort of monad we are compiling to, i.e. one of the following:
    - An unconstrained / constrained generator (`Gen` / `OptionT Gen`)
    - An unconstrained / constrained enumerator (`Enumerator` / `OptionT Enumerator`)
    - A Checker (`Option Bool` monad) -/
inductive MonadSort
  | Gen
  | OptionTGen
  | Enumerator
  | OptionTEnumerator
  | Checker
  deriving Repr

/-- An intermediate representation of monadic expressions that are
    used in generators/enumerators/checkers.
    - Schedules are compiled to `MExp`s, which are then compiled to Lean code

    - Note: `MExp`s make it easy to optimize generator code down the line
      (e.g. combine pattern-matches when we have disjoint patterns)
    - Going directly from schedules to Lean code (a wrapper on top of `TSyntax`) might be fine?
      + The wrapper should expose `bind, return, backtrack` and pattern-matches
    - The cool thing about `MExp` is that we can interpret it differently
      based on the `MonadSort`

    - TODO: we may want `MHole`, `MFail`, `MOutOfFuel`
    - the other constructors in the Rocq [mexp]
-/
inductive MExp : Type where
  /-- `MRet e` represents `return e` in some monad -/
  | MRet (e : MExp)

  /-- `MBind monadSort m1 vars m2` represents `m1 >>= fun vars => m2` in a particular monad,
       as determined by `monadSort` -/
  | MBind (monadSort : MonadSort) (m1 : MExp) (vars : List Unknown) (m2 : MExp)

  /-- N-ary function application -/
  | MApp (f : MExp) (args : List MExp)

  /-- N-ary constructor application -/
  | MCtr (c : Name) (args : List MExp)

  /-- Some constant name (e.g. refers to functions) -/
  | MConst (name : Name)

  /-- `MMatch scrutinee [(p1, e1), …, (pn, en)]` represents
       ```lean
       match scrutinee with
       | p1 => e1
       ...
       | pn => en
       ```
  -/
  | MMatch (scrutinee : MExp) (cases : List (Pattern × MExp))

  /-- Refers to a variable identifier -/
  | MId (name : Name)

  deriving Repr, Inhabited


/-- Converts a `ProducerSort` to a `MonadSort` -/
def prodSortToMonadSort (prodSort : ProducerSort) : MonadSort :=
  match prodSort with
  | .Enumerator => MonadSort.Enumerator
  | .Generator => MonadSort.Gen


/-- `MExp` representation of an unconstrained producer,
    parameterized by a `producerSort` -/
def unconstrainedProducer (prodSort : ProducerSort) : MExp :=
  match prodSort with
  | .Enumerator => .MConst ``Enum.enum
  | .Generator => .MConst ``Arbitrary.arbitrary

/-- Converts a `ConstructorExpr` to an `MExp` -/
partial def constructorExprToMExp (expr : ConstructorExpr) : MExp :=
  match expr with
  | .Unknown u => .MId u
  | .Ctor c args => .MCtr c (constructorExprToMExp <$> args)


/-- `MExp` representation of a recursive function call,
    where `f` is the function name and `args` are the arguments
    (each represented as a `ConstructorExpr`) -/
def recCall (f : Name) (args : List ConstructorExpr) : MExp :=
  .MApp (.MId f) $
    [.MId `initSize, .MId `size'] ++ (constructorExprToMExp <$> args)


/-- Compiles a `ScheduleStep` to an `MExp`
    - Note that we represent `MExp`s as a function `MExp → MExp`,
      akin to difference lists in Haskell
-/
def scheduleStepToMexp (step : ScheduleStep) (mfuel : MExp) (defFuel : MExp) : MExp → MExp :=
  fun k =>
    match step with
    | .Unconstrained v src prodSort =>
      let producer :=
        match src with
        | .NonRec ty => unconstrainedProducer prodSort
        | .Rec f args => recCall f args
      .MBind (prodSortToMonadSort prodSort) producer [v] k
    | _ => sorry
