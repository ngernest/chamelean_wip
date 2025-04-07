import Lean
import Std
import Plausible
import Lean.Meta.Eval
import Plausible.IR.PlausibleIR
open Nat
open Lean Meta


open Plausible
open Plausible.IR
open Random Gen


#gen_mutual_rec balanced with_name ["h", "T"] backtrack 10

#derive_generator balanced with_name ["h", "T"] backtrack 100

#eval gen_balanced_at_1 2 1




#eval Nat.shrink 5

def TreeSize (t: Tree) : Nat := match t with
| Tree.Leaf _ => 1
| Tree.Node _ l r => succ (max (TreeSize l) (TreeSize r))

instance  : SampleableExt (Fin 5) :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    return ⟨min x 4, by omega⟩
/-
instance : Shrinkable Tree where
  shrink := fun x => match x with
    | Tree.Leaf n =>
      let proxy := Nat.shrink n
      proxy.map (fun n => Tree.Leaf n)
    | Tree.Node n l r =>
-/
--#sample (List Nat)
--#check Fin 5

def t := SampleableExt.interpSample (Fin 10)
#eval Gen.run t 3
#check  SampleableExt.interpSample (Fin 5)

instance : Shrinkable Tree where
  shrink := fun x => [x]


def gentree (size: Nat): Gen Tree := do
  match size with
  | zero =>
    let x ← SampleableExt.interpSample Nat
    return Tree.Leaf x
  | succ size =>
    let x ← SampleableExt.interpSample Nat
    let l_size ← choose Nat 0 size (by omega)
    let r_size ← choose Nat 0 size (by omega)
    let l ← gentree l_size
    let r ← gentree r_size
    return Tree.Node x l r

instance : SampleableExt Tree :=
  SampleableExt.mkSelfContained (gentree 3)


#eval Gen.run (SampleableExt.interpSample (List Tree)) 5

#sample List Tree

--example (t :  Tree) : TreeSize t = 5 := by
 -- plausible
