import Plausible.New.DecOpt
import Plausible.New.DeriveChecker

open DecOpt

set_option guard_msgs.diff true

-- Example taken from section 3.1 of "Computing Correctly with Inductive Relations"
-- Note how `n * n` is a function call that appears in the conclusion of a constructor
-- for an inductive relation
inductive square_of : Nat → Nat → Prop where
  | sq : forall n, square_of n (n * n)

/--
info: Try this checker: instance : DecOpt (square_of n m) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_0 : Nat) (m_0 : Nat) : Option Bool :=
      match size with
      | Nat.zero => DecOpt.checkerBacktrack [fun _ => DecOpt.andOptList [DecOpt.decOpt (@Eq Nat m (n * n)) initSize]]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack [fun _ => DecOpt.andOptList [DecOpt.decOpt (@Eq Nat m (n * n)) initSize]]
    fun size => aux_dec size size n m
-/
#guard_msgs(info, drop warning) in
#derive_checker (square_of n m)
