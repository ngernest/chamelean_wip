import Plausible.GeneratingGoodGenerators.DeriveSubGenerator

/--
info: Derived generator:
```
match Γ_1 with
| ((List.cons type) τ) Γ =>
  match DecOpt.decOpt (τ == τ_1) initSize with
  | Option.some Bool.true => do
    return Nat.zero
  | _ => OptionT.fail
| _ => OptionT.fail
```
-/
#guard_msgs(info, drop warning) in
#derive_subgenerator (fun (x : Nat) => lookup Γ x τ)

/--
info: Derived generator:
```
do
  let r ← Arbitrary.arbitrary
  let x ← Arbitrary.arbitrary
  let l ← Arbitrary.arbitrary
  return Tree.Node x l r
```
-/
#guard_msgs(info, drop warning) in
#derive_subgenerator (fun (tree : Tree) => nonempty tree)

/--
info: Derived generator:
```
match DecOpt.decOpt (in1_1 == in2_1) initSize with
| Option.some Bool.true => do
  return Tree.Leaf
| _ => OptionT.fail
```
-/
#guard_msgs(info, drop warning) in
#derive_subgenerator (fun (t : Tree) => goodTree in1 in2 t)
