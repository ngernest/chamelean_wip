# Inductive relation generator

We develop a random generator for inductive relations (IR) which is based on QuickChick Algorithm. 
The generator will be integrated into Plaisible in near future. 

# Usage

## Import the libraries

First, we need to import neccessar components and open related namespaces.

```lean
import Plausible
import Plausible.IR.PlausibleIR
open Plausible
open Plausible.IR
```

## Derive and use the inductive relation generator

The syntax for deriving the generator for a IR is 

```lean
#derive_generator inductive_relation_name backtrack backtrack_number
```

where 
`inductive_relation_name: Name` is the name of the defined inductive relation, 
`backtrack_number: Nat` is the number of backtrack tries the generator used to generate the output 


For example, we define the `balanced` IR (for balanced tree) as follows:

```lean
inductive balanced : Nat → Tree → Prop where
| B0 : ∀ x, balanced 0 (Tree.Leaf x)
| BS : ∀ n x l r, balanced n l → balanced n r → balanced (succ n) (Tree.Node x l r)
```

The command for deriving the generator for it is:

```lean
#derive_generator balanced  backtrack 100 
```

The generator provides the following functions:
- `check_IRname (size: Nat) input1 input2 ... : IO Bool` : check if `IRname input1 input2 ... = true` upto size `size`.
- For each input position `i` (starts from `0`), there is a function `gen_IRname_at_i (size: Nat) input1 ... input(i-1) input(i+1) ... : IO type_of_input_i`
which generate input at position `i` for the IR such that the IR holds for the output and all other given inputs.

We can use the `#eval` command to generate the desired input of the TR using the provided functions. 
For example, we want to generate a balanced tree of size upto `5` and the height `3` (i.e. generate input at position `1` for the balanced IR),
the command is as follows:
```lean
#eval gen_balanced_at_1 5 3
```

Note that the command `#derive_generator` only the derive the generator for the provided IR name. 
If the IR depends on other IRs and inductive types, the generator for the dependences should be derived in advanced. 
If the IR only depends on other IRs within the same namespace, we can use the following command to derive the IR with all the dependences:

```lean
#derive_generator_with_dependencies inductive_relation_name backtrack backtrack_number
```

## Get the generated code for generator

For the sake of debugging and customizing the generator, we provide a way to output the generated code (as String) 
of the generator with the following commands:

```lean
#get_mutual_rec inductive_relation_name backtrack backtrack_number monad monad_name
```

where 
`inductive_relation_name` and `backtrack_number` are the same as those of the `#derive_generator` command and
`monad_name: String` is the monad which the generator use, currently, we support two monads: `IO` and `Gen`.
Without the monad specification, the monad is `IO` by default.

Similarly, we define the `#gen_mutual_rec_with_dependencies` command to get the generated code of all IR dependences in the 
same namespace.




