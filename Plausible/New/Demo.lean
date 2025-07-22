import Plausible

-- `#derive_generator` derives a generator for random `Tree`s that satisfy the `bst` & `balanced` inductive relations respectively
#derive_generator (fun (t : Tree) => bst lo hi t)
#derive_generator (fun (t : Tree) => balanced n t)

-- `#derive_enumerator` derives a (deterministic) enumerator of trees satisfying `bst` & `balanced`
#derive_enumerator (fun (t : Tree) => bst lo hi t)
#derive_enumerator (fun (t : Tree) => balanced n t)

-- `#derive_checker` derives (boolean functions) which check whether the `bst` & `balanced` predicates are satisfied
#derive_checker (bst lo hi t)
#derive_checker (balanced n t)
