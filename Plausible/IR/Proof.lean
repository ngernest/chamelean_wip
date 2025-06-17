
import Plausible.IR.PlausibleIR
import Plausible
open Plausible.IR
open Plausible
open Nat
open Gen


axiom IO_rand_proof :  ∃ n ,IO.rand 5 10 m = EStateM.Result.ok n ()

axiom uniform_backtracking : ∃ x, (uniform_backtracking_IO l = pure x ∧ x ∈ l)

def try_uniform_backtracking_IO {ty: Type}  (a: Array (ty → IO Bool))
    (inp: ty) (i: Nat) (b: Nat): IO Bool:= do
 for _i in [i:b] do
  let f ← uniform_backtracking_IO a
  let ret ← IO_to_option (f inp)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

def try_uniform_backtracking_IO_size {ty: Type}  (a: Array (ty → (size: Nat) → IO Bool))
    (inp: ty) (size: Nat) (i: Nat) (b: Nat): IO Bool:= do
 for _i in [i:b] do
  let f ← uniform_backtracking_IO a
  let ret ← IO_to_option (f inp size)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")


def try_uniform_backtracking_IO_sizepos {ty: Type}  (a: Array (ty → (size: Nat) → (size > 0) → IO Bool))
    (inp: ty) (size: Nat) (g: size > 0) (i: Nat) (b: Nat): IO Bool:= do
 for _i in [i:b] do
  let f ← uniform_backtracking_IO a
  let ret ← IO_to_option (f inp size g)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")


def weight_IO_rand (size: Nat)  : IO Bool := do
  let idx ← monadLift <| IO.rand 0 size
  return (idx = 0)



def try_backtracking_IO_range_size {ty: Type}  (a1: Array (ty → IO Bool)) (a2: Array (ty → (size: Nat) → IO Bool))
    (inp: ty) (size: Nat) (i: Nat) (b: Nat): IO Bool:= do
  match g: size with
  | zero =>  return ← try_uniform_backtracking_IO a1 inp i b
  | succ size' =>
    let l ← weight_IO_rand size
    if l then
      return ← try_uniform_backtracking_IO a1 inp i b
    else
      return ← try_uniform_backtracking_IO_size a2 inp size' i b



def try_backtracking_IO_range_sizepos {ty: Type}  (a1: Array (ty → IO Bool)) (a2: Array (ty → (size: Nat) → (size > 0) → IO Bool))
    (inp: ty) (size: Nat) (i: Nat) (b: Nat): IO Bool:= do
  match g: size with
  | zero =>  return ← try_uniform_backtracking_IO a1 inp i b
  | succ size0 =>
    let l ← weight_IO_rand size
    if l then
      return ← try_uniform_backtracking_IO a1 inp i b
    else
      return ← try_uniform_backtracking_IO_sizepos a2 inp size (by omega) i b




theorem try_uniform_backtracking_IO_proof {ty: Type}
  {inp: ty} {IR: ty → Prop} {a: Array (ty → IO Bool)}
  (gf: ∀ f ∈ a, (f inp m = EStateM.Result.ok true () → IR inp))
  (g: try_uniform_backtracking_IO a inp i b n = EStateM.Result.ok true ())
    : IR inp :=by
  generalize gs: b - i = s
  induction s generalizing b i n
  unfold try_uniform_backtracking_IO at g
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.zero_sub, Nat.zero_add,
    Nat.sub_self, Nat.div_one, List.range'_zero, List.forIn_nil, gs] at g
  simp  [bind, EStateM.bind, pure, EStateM.pure] at g
  simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, reduceCtorEq] at g
  rename_i s ind
  have ind:= @ind (i+1) b
  have gs2: b - 1 -i = s := by omega
  unfold try_uniform_backtracking_IO at g ind
  simp[Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.add_one_sub_one,
    Nat.div_one,gs, gs2] at g ind
  have: b - (i + 1) = s := by omega
  rw[this] at ind
  rw[List.range'_succ] at g
  simp only [List.forIn_cons] at g
  simp [bind, pure] at g
  unfold EStateM.bind  EStateM.pure at g
  split at g; simp at g;
  rename_i x a s g
  cases a; simp at g; split at g; injections
  injections
  split at g; simp at g; split at g; simp at g;
  rename_i g1
  split at g1; simp at g1
  split at g1; split at g1
  simp_all
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  rename_i hu ho; simp[hf.left, pure, EStateM.pure] at hu
  rw[← hu.left, ← hu.right ] at ho
  simp [IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at ho
  split at ho; simp [pure, EStateM.pure] at ho
  simp [bind, EStateM.bind , pure, EStateM.pure ] at ho ; split at ho; simp at ho
  rename_i hi; simp [ho] at hi
  have gf:= gf f hf.right hi;
  assumption
  any_goals contradiction
  simp_all
  rename_i r _ _ _
  simp [bind, pure] at ind; unfold EStateM.bind  EStateM.pure at ind
  simp at ind
  rename_i g0
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  simp[hf.left, pure, EStateM.pure, IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at g0
  split at g0; split at g0; simp at g0; simp at g0; simp [← g0.left] at g; simp_all
  have ind:= @ind r
  simp[g] at ind
  exact ind
  contradiction


theorem try_uniform_backtracking_IO_size_proof {ty: Type}
  {inp: ty} {IR: ty → Prop} {a: Array (ty → (size: Nat) → IO Bool)}
  (size: Nat)
  (gf: ∀ f ∈ a, (f inp size  m = EStateM.Result.ok true () → IR inp))
  (g: try_uniform_backtracking_IO_size a inp size i b n = EStateM.Result.ok true ())
    : IR inp :=by
  generalize gs: b - i = s
  induction s generalizing b i n
  unfold try_uniform_backtracking_IO_size at g
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.zero_sub, Nat.zero_add,
    Nat.sub_self, Nat.div_one, List.range'_zero, List.forIn_nil, gs] at g
  simp  [bind, EStateM.bind, pure, EStateM.pure] at g
  simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, reduceCtorEq] at g
  rename_i s ind
  have ind:= @ind (i+1) b
  have gs2: b - 1 -i = s := by omega
  unfold try_uniform_backtracking_IO_size at g ind
  simp[Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.add_one_sub_one,
    Nat.div_one,gs, gs2] at g ind
  have: b - (i + 1) = s := by omega
  rw[this] at ind
  rw[List.range'_succ] at g
  simp only [List.forIn_cons] at g
  simp [bind, pure] at g
  unfold EStateM.bind  EStateM.pure at g
  split at g; simp at g;
  rename_i x a s g
  cases a; simp at g; split at g; injections
  injections
  split at g; simp at g; split at g; simp at g;
  rename_i g1
  split at g1; simp at g1
  split at g1; split at g1
  simp_all
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  rename_i hu ho; simp[hf.left, pure, EStateM.pure] at hu
  rw[← hu.left, ← hu.right ] at ho
  simp [IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at ho
  split at ho; simp [pure, EStateM.pure] at ho
  simp [bind, EStateM.bind , pure, EStateM.pure ] at ho ; split at ho; simp at ho
  rename_i hi; simp [ho] at hi
  have gf:= gf f hf.right hi;
  assumption
  any_goals contradiction
  simp_all
  rename_i r _ _ _
  simp [bind, pure] at ind; unfold EStateM.bind  EStateM.pure at ind
  simp at ind
  rename_i g0
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  simp[hf.left, pure, EStateM.pure, IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at g0
  split at g0; split at g0; simp at g0; simp at g0; simp [← g0.left] at g; simp_all
  have ind:= @ind r
  simp[g] at ind
  exact ind
  contradiction



theorem try_uniform_backtracking_IO_sizepos_proof {ty: Type}
  {inp: ty} {IR: ty → Prop} {a: Array (ty → (size: Nat) →  (size > 0) → IO Bool)}
  (size: Nat)
  (gsize: size > 0)
  (gf: ∀ f ∈ a, (f inp size gsize m = EStateM.Result.ok true () → IR inp))
  (g: try_uniform_backtracking_IO_sizepos a inp size gsize i b n = EStateM.Result.ok true ())
    : IR inp :=by
  generalize gs: b - i = s
  induction s generalizing b i n
  unfold try_uniform_backtracking_IO_sizepos at g
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.zero_sub, Nat.zero_add,
    Nat.sub_self, Nat.div_one, List.range'_zero, List.forIn_nil, gs] at g
  simp  [bind, EStateM.bind, pure, EStateM.pure] at g
  simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, reduceCtorEq] at g
  rename_i s ind
  have ind:= @ind (i+1) b
  have gs2: b - 1 -i = s := by omega
  unfold try_uniform_backtracking_IO_sizepos at g ind
  simp[Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.add_one_sub_one,
    Nat.div_one,gs, gs2] at g ind
  have: b - (i + 1) = s := by omega
  rw[this] at ind
  rw[List.range'_succ] at g
  simp only [List.forIn_cons] at g
  simp [bind, pure] at g
  unfold EStateM.bind  EStateM.pure at g
  split at g; simp at g;
  rename_i x a s g
  cases a; simp at g; split at g; injections
  injections
  split at g; simp at g; split at g; simp at g;
  rename_i g1
  split at g1; simp at g1
  split at g1; split at g1
  simp_all
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  rename_i hu ho; simp[hf.left, pure, EStateM.pure] at hu
  rw[← hu.left, ← hu.right ] at ho
  simp [IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at ho
  split at ho; simp [pure, EStateM.pure] at ho
  simp [bind, EStateM.bind , pure, EStateM.pure ] at ho ; split at ho; simp at ho
  rename_i hi; simp [ho] at hi
  have gf:= gf f hf.right hi;
  assumption
  any_goals contradiction
  simp_all
  rename_i r _ _ _
  simp [bind, pure] at ind; unfold EStateM.bind  EStateM.pure at ind
  simp at ind
  rename_i g0
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  simp[hf.left, pure, EStateM.pure, IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at g0
  split at g0; split at g0; simp at g0; simp at g0; simp [← g0.left] at g; simp_all
  have ind:= @ind r
  simp[g] at ind
  exact ind
  contradiction


theorem try_backtracking_IO_range_sizepos_proof {ty: Type} {inp: ty} {IR: ty → Prop}
  {a1: Array (ty  → IO Bool)}
  {a2: Array (ty → (size: Nat) →  (size > 0) → IO Bool)}
  (size: Nat)
  (gf1: ∀ f ∈ a1, (f inp m = EStateM.Result.ok true () → IR inp))
  (gf2: ∀ f ∈ a2, ((g: size > 0) → f inp size g m = EStateM.Result.ok true () → IR inp))
  (g: try_backtracking_IO_range_sizepos a1 a2 inp size i b n = EStateM.Result.ok true ())
    : IR inp :=by
  simp [try_backtracking_IO_range_sizepos] at g
  split at g
  simp [bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at g;
  split at g;
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  exact try_uniform_backtracking_IO_proof gf1 g0
  contradiction
  simp [bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at g;
  split at g
  split at g
  simp [EStateM.bind] at g; split at g
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  exact try_uniform_backtracking_IO_proof gf1 g0
  contradiction
  simp [EStateM.bind] at g; split at g
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  rename_i size _ _ _ _ _ _ _ _
  have gf2' : ∀ f ∈ a2, (f inp (size + 1) (by omega) m = EStateM.Result.ok true () → IR inp) :=by
    intro f g1
    have : size.succ = size + 1 := by omega
    rw[this] at gf2
    exact gf2 f g1 (by omega)
  exact try_uniform_backtracking_IO_sizepos_proof (size + 1) (by omega) gf2' g0
  contradiction
  contradiction



theorem try_backtracking_IO_range_size_proof {ty: Type} {inp: ty} {IR: ty → Prop}
  {a1: Array (ty  → IO Bool)}
  {a2: Array (ty → (size: Nat) → IO Bool)}
  (g: try_backtracking_IO_range_size a1 a2 inp size i b n = EStateM.Result.ok true ())
  (gf1: ∀ f ∈ a1, (f inp m = EStateM.Result.ok true () → IR inp))
  (gf2: ∀ f ∈ a2, (f inp (size - 1) m = EStateM.Result.ok true () → IR inp))
    : IR inp :=by
  simp [try_backtracking_IO_range_size] at g
  split at g
  simp [bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at g;
  split at g;
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  exact try_uniform_backtracking_IO_proof gf1 g0
  contradiction
  simp [bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at g;
  split at g
  split at g
  simp [EStateM.bind] at g; split at g
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  exact try_uniform_backtracking_IO_proof gf1 g0
  contradiction
  simp [EStateM.bind] at g; split at g
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  rename_i size _ _ _ _ _ _ _ _
  have : size.succ - 1 = size := by omega
  simp [this] at gf2
  exact try_uniform_backtracking_IO_size_proof size gf2 g0
  contradiction
  contradiction




mutual
-- CHECKER

def check_balanced_by_con_1 (h : Nat) (T : Tree) : IO Bool:= do
{match h , T  with
| 0 , Tree.Leaf x  =>  return true
| _ , _  => return false}


def check_balanced_by_con_2  (h : Nat) (T : Tree) (size: Nat): IO Bool:= do
{match h , T  with
| succ n , Tree.Node x l r  =>
let check1 ← check_balanced size n l
let check2 ← check_balanced size n r
return check1 && check2
| _ , _  => return false}


def check_balanced (size : Nat) (h : Nat) (T : Tree) : IO Bool := do
  let a1 := #[check_balanced_by_con_1 h]
  let a2 := #[check_balanced_by_con_2 h]
  let ret ←  try_backtracking_IO_range_size a1 a2 T size 1 100
  return ret

end


theorem check_balanced_by_con_1_proof (g: check_balanced_by_con_1 h T m = EStateM.Result.ok true ()) : balanced h T :=by
  simp [check_balanced_by_con_1, pure] at g
  split at g; apply balanced.B0
  simp [EStateM.pure] at g

theorem check_balanced_by_con_2_proof (g: check_balanced_by_con_2 h T size m = EStateM.Result.ok true ())
    (g2: ∀ h t, check_balanced size h t m = EStateM.Result.ok true n → balanced h t): balanced h T :=by
  unfold check_balanced_by_con_2 at g
  split at g <;> try simp[pure, EStateM.pure] at g
  simp [bind, EStateM.bind] at g
  repeat split at g <;> try contradiction
  simp [EStateM.pure] at g; rename_i g0 _ _ _ g1; simp [g] at g1 g0
  have g0:= g2 _ _ g0
  have g1:= g2 _ _ g1
  apply balanced.BS
  any_goals assumption

theorem array_size_zero_check:∀ f ∈ #[check_balanced_by_con_1 h], f T m = EStateM.Result.ok true () →  balanced h T :=by
  intro f g1 g2
  simp at g1
  rw[g1] at g2 ; exact check_balanced_by_con_1_proof g2

theorem array_size_pos_check
  (g1: f ∈ #[check_balanced_by_con_2 h]) (g2: f T size m = EStateM.Result.ok true ())
  (gi: ∀ h t, check_balanced size h t m = EStateM.Result.ok true n → balanced h t)
      : balanced h T :=by
  simp at g1
  rw[g1] at g2
  apply check_balanced_by_con_2_proof g2 gi


theorem check_balanced_proof (g: check_balanced size h T m = EStateM.Result.ok true ()) : balanced h T :=by
  induction size generalizing h T m
  simp [check_balanced, bind, EStateM.bind, try_backtracking_IO_range_size] at g
  split at g <;> try contradiction
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  split at g0 <;> try contradiction
  simp [pure, EStateM.pure] at g0; rename_i g1; simp [g0] at g1
  apply try_uniform_backtracking_IO_proof _ g1
  assumption
  apply array_size_zero_check
  rename_i ind
  simp [check_balanced, bind, EStateM.bind] at g
  split at g <;> try contradiction
  simp [pure, EStateM.pure] at g; rename_i g0; simp [g] at g0
  apply try_backtracking_IO_range_size_proof g0
  apply array_size_zero_check
  intro f g1 g2
  apply array_size_pos_check g1 g2
  rw[Nat.succ_sub_one]; rw[Nat.succ_sub_one] at g2
  intro h t
  apply ind
  any_goals assumption









/-

def try_uniform_backtracking_IO_2_inputs {ty1 ty2: Type}  (a: Array (ty1 → ty2 → IO Bool))
    (inp1: ty1) (inp2: ty2)  (i: Nat) (b: Nat): IO Bool:= do
 for _i in [i:b] do
  let f ← uniform_backtracking_IO a
  let ret ← IO_to_option (f inp1 inp2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")


theorem try_uniform_backtracking_IO_2_inputs_proof {ty1 ty2: Type}
  {inp1: ty1} {inp2: ty2} {IR: ty1 → ty2 → Prop} {a: Array (ty1 → ty2 → IO Bool)}
  (gf: ∀ f ∈ a, (f inp1 inp2 m = EStateM.Result.ok true () → IR inp1 inp2))
  (g: try_uniform_backtracking_IO_2_inputs a inp1 inp2 i b n = EStateM.Result.ok true ())
    : IR inp1 inp2 :=by
  generalize gs: b - i = s
  induction s generalizing b i n
  unfold try_uniform_backtracking_IO_2_inputs at g
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.zero_sub, Nat.zero_add,
    Nat.sub_self, Nat.div_one, List.range'_zero, List.forIn_nil, gs] at g
  simp  [bind, EStateM.bind, pure, EStateM.pure] at g
  simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, reduceCtorEq] at g
  rename_i s ind
  have ind:= @ind (i+1) b
  have gs2: b - 1 -i = s := by omega
  unfold try_uniform_backtracking_IO_2_inputs at g ind
  simp[Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.add_one_sub_one,
    Nat.div_one,gs, gs2] at g ind
  have: b - (i + 1) = s := by omega
  rw[this] at ind
  rw[List.range'_succ] at g
  simp only [List.forIn_cons] at g
  simp [bind, pure] at g
  unfold EStateM.bind  EStateM.pure at g
  split at g; simp at g;
  rename_i x a s g
  cases a; simp at g; split at g; injections
  injections
  split at g; simp at g; split at g; simp at g;
  rename_i g1
  split at g1; simp at g1
  split at g1; split at g1
  simp_all
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  rename_i hu ho; simp[hf.left, pure, EStateM.pure] at hu
  rw[← hu.left, ← hu.right ] at ho
  simp [IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at ho
  split at ho; simp [pure, EStateM.pure] at ho
  simp [bind, EStateM.bind , pure, EStateM.pure ] at ho ; split at ho; simp at ho
  rename_i hi; simp [ho] at hi
  have gf:= gf f hf.right hi;
  assumption
  any_goals contradiction
  simp_all
  rename_i r _ _ _
  simp [bind, pure] at ind; unfold EStateM.bind  EStateM.pure at ind
  simp at ind
  rename_i g0
  have t1 := @uniform_backtracking _ a
  have ⟨f, hf⟩:= t1
  simp[hf.left, pure, EStateM.pure, IO_to_option, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch] at g0
  split at g0; split at g0; simp at g0; simp at g0; simp [← g0.left] at g; simp_all
  have ind:= @ind r
  simp[g] at ind
  exact ind
  contradiction
-/
