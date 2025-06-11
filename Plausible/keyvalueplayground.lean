import Lean
import Std
import Plausible
import Lean.Meta.Eval
import Plausible.IR.PlausibleIR
import Plausible.IR.KeyValueStore
open Nat
open Lean Meta


open Plausible
open Plausible.IR
open Random Gen

open KeyValueStore



-- #get_relation lookup_kv
-- #get_checker_call lookup_kv


-- #gen_producer lookup_kv with_name ["s", "l", "T"] for_arg 1 backtrack 10

-- #gen_mutual_rec lookup_kv with_name ["s", "l"] backtrack 10 monad "IO"
mutual
-- CHECKER

-- Constructor: #[] → lookup_kv [] (state_result.Failure "no such key", k, 0, v)
partial def check_lookup_kv_by_con_1 (size : Nat) (s : List (String × String)) (l : state_result × String × Nat × String) : IO Bool:= do
match s , l  with
| [] , (state_result.Failure "no such key", k, 0, v)  =>  return true
| _ , _  => return false

-- Constructor: #[] → lookup_kv ((k, v) :: s) (state_result.Ok, k, 0, v)
partial def check_lookup_kv_by_con_2 (size : Nat) (s : List (String × String)) (l : state_result × String × Nat × String) : IO Bool:= do
match s , l  with
| (k, v) :: s , (state_result.Ok, k0, 0, v0)  =>  return (k == k0) && (v == v0)
| _ , _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Ok, k1, n', v1)
partial def check_lookup_kv_by_con_3 (size : Nat) (s : List (String × String)) (l : state_result × String × Nat × String) : IO Bool:= do
match s , l  with
| (k2, v2) :: s , (state_result.Ok, k1, n', v1)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k1_1, n, v1_1) := tcond1 then
  return (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
return false
| _ , _  => return false

-- Constructor: #[] → lookup_kv [(k, v)] (state_result.Failure "no such version", k, succ n, v)
partial def check_lookup_kv_by_con_4 (size : Nat) (s : List (String × String)) (l : state_result × String × Nat × String) : IO Bool:= do
match s , l  with
| [(k, v)] , (state_result.Failure "no such version", k0, succ n, v0)  =>  return (k == k0) && (v == v0)
| _ , _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Failure "no such version", k1, n', v1)
partial def check_lookup_kv_by_con_5 (size : Nat) (s : List (String × String)) (l : state_result × String × Nat × String) : IO Bool:= do
match s , l  with
| (k2, v2) :: s , (state_result.Failure "no such version", k1, n', v1)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k1_1, n, v1_1) := tcond1 then
  return (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
return false
| _ , _  => return false

partial def check_lookup_kv (size : Nat) (s : List (String × String)) (l : state_result × String × Nat × String) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_lookup_kv_by_con_1, check_lookup_kv_by_con_2, check_lookup_kv_by_con_4]
  let ret ← IO_to_option (f size s l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_lookup_kv_by_con_1, check_lookup_kv_by_con_2, check_lookup_kv_by_con_4, check_lookup_kv_by_con_3, check_lookup_kv_by_con_5] 3 size
  let ret ← IO_to_option (f size s l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[] → lookup_kv [] (state_result.Failure "no such key", k, 0, v)
partial def gen_lookup_kv_at_0_by_con_1 (size : Nat) (l : state_result × String × Nat × String) : IO (List (String × String)):= do
match l  with
| (state_result.Failure "no such key", k, 0, v)  =>
return []
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv ((k, v) :: s) (state_result.Ok, k, 0, v)
partial def gen_lookup_kv_at_0_by_con_2 (size : Nat) (l : state_result × String × Nat × String) : IO (List (String × String)):= do
match l  with
| (state_result.Ok, k, 0, v)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
return (k, v) :: s
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Ok, k1, n', v1)
partial def gen_lookup_kv_at_0_by_con_3 (size : Nat) (l : state_result × String × Nat × String) : IO (List (String × String)):= do
match l  with
| (state_result.Ok, k1, n', v1)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
if let (state_result.Ok, k1_1, n, v1_1) := tcond1 then
  if (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
  then return (k2, v2) :: s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv [(k, v)] (state_result.Failure "no such version", k, succ n, v)
partial def gen_lookup_kv_at_0_by_con_4 (size : Nat) (l : state_result × String × Nat × String) : IO (List (String × String)):= do
match l  with
| (state_result.Failure "no such version", k, succ n, v)  =>
return [(k, v)]
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Failure "no such version", k1, n', v1)
partial def gen_lookup_kv_at_0_by_con_5 (size : Nat) (l : state_result × String × Nat × String) : IO (List (String × String)):= do
match l  with
| (state_result.Failure "no such version", k1, n', v1)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
if let (state_result.Failure "no such version", k1_1, n, v1_1) := tcond1 then
  if (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
  then return (k2, v2) :: s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_lookup_kv_at_0 (size : Nat) (l : state_result × String × Nat × String) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_lookup_kv_at_0_by_con_1, gen_lookup_kv_at_0_by_con_2, gen_lookup_kv_at_0_by_con_4]
  let ret ← IO_to_option (f size l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_lookup_kv_at_0_by_con_1, gen_lookup_kv_at_0_by_con_2, gen_lookup_kv_at_0_by_con_4, gen_lookup_kv_at_0_by_con_3, gen_lookup_kv_at_0_by_con_5] 3 size
  let ret ← IO_to_option (f size l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[] → lookup_kv [] (state_result.Failure "no such key", k, 0, v)
partial def gen_lookup_kv_at_1_by_con_1 (size : Nat) (s : List (String × String)) : IO (state_result × String × Nat × String):= do
match s  with
| []  =>
let k ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let v ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
return (state_result.Failure "no such key", k, 0, v)
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv ((k, v) :: s) (state_result.Ok, k, 0, v)
partial def gen_lookup_kv_at_1_by_con_2 (size : Nat) (s : List (String × String)) : IO (state_result × String × Nat × String):= do
match s  with
| (k, v) :: s  =>
return (state_result.Ok, k, 0, v)
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Ok, k1, n', v1)
partial def gen_lookup_kv_at_1_by_con_3 (size : Nat) (s : List (String × String)) : IO (state_result × String × Nat × String):= do
match s  with
| (k2, v2) :: s  =>
let tcond1 ← gen_lookup_kv_at_1 size s
let n' ← monadLift <| Gen.run (SampleableExt.interpSample Nat) 100
if let (state_result.Ok, k1, n, v1) := tcond1 then
  if (n' = ver k1 k2 n)
  then return (state_result.Ok, k1, n', v1)
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv [(k, v)] (state_result.Failure "no such version", k, succ n, v)
partial def gen_lookup_kv_at_1_by_con_4 (size : Nat) (s : List (String × String)) : IO (state_result × String × Nat × String):= do
match s  with
| [(k, v)]  =>
let n ← monadLift <| Gen.run (SampleableExt.interpSample Nat) 100
return (state_result.Failure "no such version", k, succ n, v)
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Failure "no such version", k1, n', v1)
partial def gen_lookup_kv_at_1_by_con_5 (size : Nat) (s : List (String × String)) : IO (state_result × String × Nat × String):= do
match s  with
| (k2, v2) :: s  =>
let tcond1 ← gen_lookup_kv_at_1 size s
let n' ← monadLift <| Gen.run (SampleableExt.interpSample Nat) 100
if let (state_result.Failure "no such version", k1, n, v1) := tcond1 then
  if (n' = ver k1 k2 n)
  then return (state_result.Failure "no such version", k1, n', v1)
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_lookup_kv_at_1 (size : Nat) (s : List (String × String)) : IO (state_result × String × Nat × String) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_lookup_kv_at_1_by_con_1, gen_lookup_kv_at_1_by_con_2, gen_lookup_kv_at_1_by_con_4]
  let ret ← IO_to_option (f size s)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_lookup_kv_at_1_by_con_1, gen_lookup_kv_at_1_by_con_2, gen_lookup_kv_at_1_by_con_4, gen_lookup_kv_at_1_by_con_3, gen_lookup_kv_at_1_by_con_5] 3 size
  let ret ← IO_to_option (f size s)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end



def ti : IO (String) :=  monadLift <| Gen.run (SampleableExt.interpSample String) 10
#eval ti

#eval gen_lookup_kv_at_1_by_con_1 4 []
#eval gen_lookup_kv_at_1_by_con_2 4 [("cc", "dd")]
#eval gen_lookup_kv_at_1 4 [("cc", "dd")]
#eval gen_lookup_kv_at_1 4 [("cc", "dd"), ("ee", "ff")]


--------ADD_KV------------

#gen_mutual_rec add_kv with_name ["s1", "s2", "l1", "l2"] backtrack 10 monad "IO"


mutual
-- CHECKER

-- Constructor: #[] → add_kv s1 s2 l1 ((s1, s2) :: l1)
partial def check_add_kv_by_con_1 (size : Nat) (s1 : String) (s2 : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO Bool:= do
match l2  with
| (s10, s20) :: l10  =>  return (s1 == s10) && (s2 == s20) && (l1 == l10)
| _  => return false

partial def check_add_kv (size : Nat) (s1 : String) (s2 : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_add_kv_by_con_1]
  let ret ← IO_to_option (f size s1 s2 l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_add_kv_by_con_1] 1 size
  let ret ← IO_to_option (f size s1 s2 l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[] → add_kv s1 s2 l1 ((s1, s2) :: l1)
partial def gen_add_kv_at_0_by_con_1 (size : Nat) (s2 : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO String:= do
match l2  with
| (s1, s20) :: l10  =>
if (s2 == s20) && (l1 == l10)
then return s1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_add_kv_at_0 (size : Nat) (s2 : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO String := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_0_by_con_1]
  let ret ← IO_to_option (f size s2 l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_0_by_con_1] 1 size
  let ret ← IO_to_option (f size s2 l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[] → add_kv s1 s2 l1 ((s1, s2) :: l1)
partial def gen_add_kv_at_1_by_con_1 (size : Nat) (s1 : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO String:= do
match l2  with
| (s10, s2) :: l10  =>
if (s1 == s10) && (l1 == l10)
then return s2
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_add_kv_at_1 (size : Nat) (s1 : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO String := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_1_by_con_1]
  let ret ← IO_to_option (f size s1 l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_1_by_con_1] 1 size
  let ret ← IO_to_option (f size s1 l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG2

-- Constructor: #[] → add_kv s1 s2 l1 ((s1, s2) :: l1)
partial def gen_add_kv_at_2_by_con_1 (size : Nat) (s1 : String) (s2 : String) (l2 : List (String × String)) : IO (List (String × String)):= do
match l2  with
| (s10, s20) :: l1  =>
if (s1 == s10) && (s2 == s20)
then return l1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_add_kv_at_2 (size : Nat) (s1 : String) (s2 : String) (l2 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_2_by_con_1]
  let ret ← IO_to_option (f size s1 s2 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_2_by_con_1] 1 size
  let ret ← IO_to_option (f size s1 s2 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG3

-- Constructor: #[] → add_kv s1 s2 l1 ((s1, s2) :: l1)
partial def gen_add_kv_at_3_by_con_1 (size : Nat) (s1 : String) (s2 : String) (l1 : List (String × String)) : IO (List (String × String)):= do
return (s1, s2) :: l1

partial def gen_add_kv_at_3 (size : Nat) (s1 : String) (s2 : String) (l1 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_3_by_con_1]
  let ret ← IO_to_option (f size s1 s2 l1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_3_by_con_1] 1 size
  let ret ← IO_to_option (f size s1 s2 l1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end

#eval gen_add_kv_at_3 2 "aa" "bb" [("cc", "dd")]
#eval gen_add_kv_at_3 2 "aa" "bb" [("cc", "dd"), ("ee", "ff")]

-----------------------REMOVE KV-----------------------------------------------


#get_checker_call remove_kv

#gen_mutual_rec remove_kv with_name ["s", "l1", "l2"] backtrack 10 monad "IO"


mutual
-- CHECKER

-- Constructor: #[] → remove_kv s [] []
partial def check_remove_kv_by_con_1 (size : Nat) (s : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO Bool:= do
match l1 , l2  with
| [] , []  =>  return true
| _ , _  => return false

-- Constructor: #[remove_kv s s1 l2] → remove_kv s ((s, v) :: s1) l2
partial def check_remove_kv_by_con_2 (size : Nat) (s : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO Bool:= do
match l1  with
| (s0, v) :: s1  =>
let check1 ← check_remove_kv size s s1 l2
return check1 && (s == s0)
| _  => return false

-- Constructor: #[(s != k2) = true, remove_kv s s1 s2] → remove_kv s ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def check_remove_kv_by_con_3 (size : Nat) (s : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO Bool:= do
match l1 , l2  with
| (k2, v2) :: s1 , (k20, v20) :: s2  =>
let check1 ← check_remove_kv size s s1 s2
return check1 && (k2 == k20) && (v2 == v20) && ((s != k2) = true)
| _ , _  => return false

partial def check_remove_kv (size : Nat) (s : String) (l1 : List (String × String)) (l2 : List (String × String)) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_remove_kv_by_con_1]
  let ret ← IO_to_option (f size s l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_remove_kv_by_con_1, check_remove_kv_by_con_2, check_remove_kv_by_con_3] 1 size
  let ret ← IO_to_option (f size s l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[] → remove_kv s [] []
partial def gen_remove_kv_at_0_by_con_1 (size : Nat) (l1 : List (String × String)) (l2 : List (String × String)) : IO String:= do
match l1 , l2  with
| [] , []  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
return s
| _ , _  => throw (IO.userError "fail")

-- Constructor: #[remove_kv s s1 l2] → remove_kv s ((s, v) :: s1) l2
partial def gen_remove_kv_at_0_by_con_2 (size : Nat) (l1 : List (String × String)) (l2 : List (String × String)) : IO String:= do
match l1  with
| (s, v) :: s1  =>

let check1 ← check_remove_kv size s s1 l2
if check1
then return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[(s != k2) = true, remove_kv s s1 s2] → remove_kv s ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def gen_remove_kv_at_0_by_con_3 (size : Nat) (l1 : List (String × String)) (l2 : List (String × String)) : IO String:= do
match l1 , l2  with
| (k2, v2) :: s1 , (k20, v20) :: s2  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let check1 ← check_remove_kv size s s1 s2
if check1 && (k2 == k20) && (v2 == v20) && ((s != k2) = true)
then return s
throw (IO.userError "fail at checkstep")
| _ , _  => throw (IO.userError "fail")

partial def gen_remove_kv_at_0 (size : Nat) (l1 : List (String × String)) (l2 : List (String × String)) : IO String := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_remove_kv_at_0_by_con_1]
  let ret ← IO_to_option (f size l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_remove_kv_at_0_by_con_1, gen_remove_kv_at_0_by_con_2, gen_remove_kv_at_0_by_con_3] 1 size
  let ret ← IO_to_option (f size l1 l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[] → remove_kv s [] []
partial def gen_remove_kv_at_1_by_con_1 (size : Nat) (s : String) (l2 : List (String × String)) : IO (List (String × String)):= do
match l2  with
| []  =>
return []
| _  => throw (IO.userError "fail")

-- Constructor: #[remove_kv s s1 l2] → remove_kv s ((s, v) :: s1) l2
partial def gen_remove_kv_at_1_by_con_2 (size : Nat) (s : String) (l2 : List (String × String)) : IO (List (String × String)):= do
let s1 ← gen_remove_kv_at_1 size s l2
let v ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
return (s, v) :: s1

-- Constructor: #[(s != k2) = true, remove_kv s s1 s2] → remove_kv s ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def gen_remove_kv_at_1_by_con_3 (size : Nat) (s : String) (l2 : List (String × String)) : IO (List (String × String)):= do
match l2  with
| (k2, v2) :: s2  =>
let s1 ← gen_remove_kv_at_1 size s s2
if ((s != k2) = true)
then return (k2, v2) :: s1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_remove_kv_at_1 (size : Nat) (s : String) (l2 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_remove_kv_at_1_by_con_1]
  let ret ← IO_to_option (f size s l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_remove_kv_at_1_by_con_1, gen_remove_kv_at_1_by_con_2, gen_remove_kv_at_1_by_con_3] 1 size
  let ret ← IO_to_option (f size s l2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG2

-- Constructor: #[] → remove_kv s [] []
partial def gen_remove_kv_at_2_by_con_1 (size : Nat) (s : String) (l1 : List (String × String)) : IO (List (String × String)):= do
match l1  with
| []  =>
return []
| _  => throw (IO.userError "fail")

-- Constructor: #[remove_kv s s1 l2] → remove_kv s ((s, v) :: s1) l2
partial def gen_remove_kv_at_2_by_con_2 (size : Nat) (s : String) (l1 : List (String × String)) : IO (List (String × String)):= do
match l1  with
| (s0, v) :: s1  =>
let l2 ← gen_remove_kv_at_2 size s s1
if (s == s0)
then return l2
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[(s != k2) = true, remove_kv s s1 s2] → remove_kv s ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def gen_remove_kv_at_2_by_con_3 (size : Nat) (s : String) (l1 : List (String × String)) : IO (List (String × String)):= do
match l1  with
| (k2, v2) :: s1  =>
let s2 ← gen_remove_kv_at_2 size s s1
if ((s != k2) = true)
then return (k2, v2) :: s2
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_remove_kv_at_2 (size : Nat) (s : String) (l1 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
<<<<<<< HEAD
 for _i in [1:100] do
=======
 for _i in [1:10] do
>>>>>>> 2ebbb5a
  let f ← uniform_backtracking_IO #[gen_remove_kv_at_2_by_con_1]
  let ret ← IO_to_option (f size s l1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:100] do
  let f ← weight_backtracking_IO #[gen_remove_kv_at_2_by_con_1, gen_remove_kv_at_2_by_con_2, gen_remove_kv_at_2_by_con_3] 1 size
  let ret ← IO_to_option (f size s l1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end

#eval gen_remove_kv_at_2 2 "ee" [("cc", "ff")]
#eval gen_remove_kv_at_2 4 "ee" [("cc", "dd"), ("ee", "ff")]
#eval gen_remove_kv_at_2 3 "cc" [("cc", "dd"), ("ee", "ff")]




------EVAL STATE API CALL ----



#get_relation eval_state_api_call
#get_checker_call eval_state_api_call
#gen_producer eval_state_api_call with_name ["in1", "in2"] for_arg 0 backtrack 100
#gen_mutual_rec eval_state_api_call with_name ["s", "l"] backtrack 10 monad "IO"

mutual
-- CHECKER

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v)] → eval_state_api_call s (state_api_call.get k none, state_result.Result v, s)
partial def check_eval_state_api_call_by_con_1 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.get k none, state_result.Result v, s0)  =>
let check1 ← check_lookup_kv size s (state_result.Ok, k, 0, v)
return check1 && (s == s0)
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.get k none, state_result.Failure "no such key", s)
partial def check_eval_state_api_call_by_con_2 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.get k none, state_result.Failure "no such key", s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (s == s0) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k, n, v)] → eval_state_api_call s (state_api_call.get k (some n), state_result.Result v, s)
partial def check_eval_state_api_call_by_con_3 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.get k (some n), state_result.Result v, s0)  =>
let check1 ← check_lookup_kv size s (state_result.Ok, k, n, v)
return check1 && (s == s0)
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k, n, v)] → eval_state_api_call s (state_api_call.get k (some n), state_result.Failure "no such version", s)
partial def check_eval_state_api_call_by_con_4 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.get k (some n), state_result.Failure "no such version", s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k_1, n_1, v) := tcond1 then
 return (s == s0) && (k == k_1) && (n == n_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v)] → eval_state_api_call s (state_api_call.key_exists k, state_result.Ok, s)
partial def check_eval_state_api_call_by_con_5 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.key_exists k, state_result.Ok, s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 return (s == s0) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.key_exists k, state_result.Result "no such key", s)
partial def check_eval_state_api_call_by_con_6 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.key_exists k, state_result.Result "no such key", s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (s == s0) && (k == k_1)
return false
| _  => return false

-- Constructor: #[add_kv k v s s2] → eval_state_api_call s (state_api_call.set k v, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_7 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.set k v, state_result.Ok, s2)  =>
let check1 ← check_add_kv size k v s s2
return check1
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), add_kv k2 v s s2] → eval_state_api_call s (state_api_call.copy k k2, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_8 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.copy k k2, state_result.Ok, s2)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_add_kv size k2 v s s2
 return check1 && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.copy k k2, state_result.Failure "no such key", s)
partial def check_eval_state_api_call_by_con_9 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.copy k k2, state_result.Failure "no such key", s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (s == s0) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), v3 = append_string v v2, add_kv k v3 s s2] → eval_state_api_call s (state_api_call.append k v3, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_10 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.append k v3, state_result.Ok, s2)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let check1 ← check_add_kv size k v3 s s2
 return check1 && (k == k_1) && (v3 = append_string v v2)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.append k v2, state_result.Failure "no such key", s)
partial def check_eval_state_api_call_by_con_11 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.append k v2, state_result.Failure "no such key", s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (s == s0) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), remove_kv k s s2] → eval_state_api_call s (state_api_call.delete k, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_12 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.delete k, state_result.Ok, s2)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_remove_kv size k s s2
 return check1 && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.delete k, state_result.Failure "no such key", s)
partial def check_eval_state_api_call_by_con_13 (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool:= do
match l  with
| (state_api_call.delete k, state_result.Failure "no such key", s0)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (s == s0) && (k == k_1)
return false
| _  => return false

partial def check_eval_state_api_call (size : Nat) (s : List (String × String)) (l : state_api_call × state_result × List (String × String)) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_eval_state_api_call_by_con_1, check_eval_state_api_call_by_con_2, check_eval_state_api_call_by_con_3, check_eval_state_api_call_by_con_4, check_eval_state_api_call_by_con_5, check_eval_state_api_call_by_con_6, check_eval_state_api_call_by_con_7, check_eval_state_api_call_by_con_8, check_eval_state_api_call_by_con_9, check_eval_state_api_call_by_con_10, check_eval_state_api_call_by_con_11, check_eval_state_api_call_by_con_12, check_eval_state_api_call_by_con_13]
  let ret ← IO_to_option (f size s l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_eval_state_api_call_by_con_1, check_eval_state_api_call_by_con_2, check_eval_state_api_call_by_con_3, check_eval_state_api_call_by_con_4, check_eval_state_api_call_by_con_5, check_eval_state_api_call_by_con_6, check_eval_state_api_call_by_con_7, check_eval_state_api_call_by_con_8, check_eval_state_api_call_by_con_9, check_eval_state_api_call_by_con_10, check_eval_state_api_call_by_con_11, check_eval_state_api_call_by_con_12, check_eval_state_api_call_by_con_13] 13 size
  let ret ← IO_to_option (f size s l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v)] → eval_state_api_call s (state_api_call.get k none, state_result.Result v, s)
partial def gen_eval_state_api_call_at_0_by_con_1 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.get k none, state_result.Result v, s)  =>

let check1 ← check_lookup_kv size s (state_result.Ok, k, 0, v)
if check1
then return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.get k none, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_0_by_con_2 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.get k none, state_result.Failure "no such key", s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k, n, v)] → eval_state_api_call s (state_api_call.get k (some n), state_result.Result v, s)
partial def gen_eval_state_api_call_at_0_by_con_3 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.get k (some n), state_result.Result v, s)  =>

let check1 ← check_lookup_kv size s (state_result.Ok, k, n, v)
if check1
then return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k, n, v)] → eval_state_api_call s (state_api_call.get k (some n), state_result.Failure "no such version", s)
partial def gen_eval_state_api_call_at_0_by_con_4 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.get k (some n), state_result.Failure "no such version", s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k_1, n_1, v) := tcond1 then
 if (k == k_1) && (n == n_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v)] → eval_state_api_call s (state_api_call.key_exists k, state_result.Ok, s)
partial def gen_eval_state_api_call_at_0_by_con_5 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.key_exists k, state_result.Ok, s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.key_exists k, state_result.Result "no such key", s)
partial def gen_eval_state_api_call_at_0_by_con_6 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.key_exists k, state_result.Result "no such key", s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[add_kv k v s s2] → eval_state_api_call s (state_api_call.set k v, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_7 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.set k v, state_result.Ok, s2)  =>
let s ← gen_add_kv_at_2 size k v s2
return s
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), add_kv k2 v s s2] → eval_state_api_call s (state_api_call.copy k k2, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_8 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.copy k k2, state_result.Ok, s2)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_add_kv size k2 v s s2
 if check1 && (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.copy k k2, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_0_by_con_9 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.copy k k2, state_result.Failure "no such key", s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), v3 = append_string v v2, add_kv k v3 s s2] → eval_state_api_call s (state_api_call.append k v3, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_10 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.append k v3, state_result.Ok, s2)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let check1 ← check_add_kv size k v3 s s2
 if check1 && (k == k_1) && (v3 = append_string v v2)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.append k v2, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_0_by_con_11 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.append k v2, state_result.Failure "no such key", s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), remove_kv k s s2] → eval_state_api_call s (state_api_call.delete k, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_12 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.delete k, state_result.Ok, s2)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_remove_kv size k s s2
 if check1 && (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.delete k, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_0_by_con_13 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match l  with
| (state_api_call.delete k, state_result.Failure "no such key", s)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_eval_state_api_call_at_0 (size : Nat) (l : state_api_call × state_result × List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_eval_state_api_call_at_0_by_con_1, gen_eval_state_api_call_at_0_by_con_2, gen_eval_state_api_call_at_0_by_con_3, gen_eval_state_api_call_at_0_by_con_4, gen_eval_state_api_call_at_0_by_con_5, gen_eval_state_api_call_at_0_by_con_6, gen_eval_state_api_call_at_0_by_con_7, gen_eval_state_api_call_at_0_by_con_8, gen_eval_state_api_call_at_0_by_con_9, gen_eval_state_api_call_at_0_by_con_10, gen_eval_state_api_call_at_0_by_con_11, gen_eval_state_api_call_at_0_by_con_12, gen_eval_state_api_call_at_0_by_con_13]
  let ret ← IO_to_option (f size l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_eval_state_api_call_at_0_by_con_1, gen_eval_state_api_call_at_0_by_con_2, gen_eval_state_api_call_at_0_by_con_3, gen_eval_state_api_call_at_0_by_con_4, gen_eval_state_api_call_at_0_by_con_5, gen_eval_state_api_call_at_0_by_con_6, gen_eval_state_api_call_at_0_by_con_7, gen_eval_state_api_call_at_0_by_con_8, gen_eval_state_api_call_at_0_by_con_9, gen_eval_state_api_call_at_0_by_con_10, gen_eval_state_api_call_at_0_by_con_11, gen_eval_state_api_call_at_0_by_con_12, gen_eval_state_api_call_at_0_by_con_13] 13 size
  let ret ← IO_to_option (f size l)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v)] → eval_state_api_call s (state_api_call.get k none, state_result.Result v, s)
partial def gen_eval_state_api_call_at_1_by_con_1 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k, 0, v) := tcond1 then
 return (state_api_call.get k none, state_result.Result v, s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.get k none, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_1_by_con_2 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 return (state_api_call.get k none, state_result.Failure "no such key", s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Ok, k, n, v)] → eval_state_api_call s (state_api_call.get k (some n), state_result.Result v, s)
partial def gen_eval_state_api_call_at_1_by_con_3 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k, n, v) := tcond1 then
 return (state_api_call.get k (some n), state_result.Result v, s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k, n, v)] → eval_state_api_call s (state_api_call.get k (some n), state_result.Failure "no such version", s)
partial def gen_eval_state_api_call_at_1_by_con_4 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k, n, v) := tcond1 then
 return (state_api_call.get k (some n), state_result.Failure "no such version", s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v)] → eval_state_api_call s (state_api_call.key_exists k, state_result.Ok, s)
partial def gen_eval_state_api_call_at_1_by_con_5 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k, 0, v) := tcond1 then
 return (state_api_call.key_exists k, state_result.Ok, s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.key_exists k, state_result.Result "no such key", s)
partial def gen_eval_state_api_call_at_1_by_con_6 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 return (state_api_call.key_exists k, state_result.Result "no such key", s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[add_kv k v s s2] → eval_state_api_call s (state_api_call.set k v, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_7 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let k ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let v ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let s2 ← gen_add_kv_at_3 size k v s
return (state_api_call.set k v, state_result.Ok, s2)

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), add_kv k2 v s s2] → eval_state_api_call s (state_api_call.copy k k2, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_8 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k, 0, v) := tcond1 then
 let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let s2 ← gen_add_kv_at_3 size k2 v s
 return (state_api_call.copy k k2, state_result.Ok, s2)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.copy k k2, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_1_by_con_9 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 return (state_api_call.copy k k2, state_result.Failure "no such key", s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), v3 = append_string v v2, add_kv k v3 s s2] → eval_state_api_call s (state_api_call.append k v3, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_10 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k, 0, v) := tcond1 then
 let v3 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let s2 ← gen_add_kv_at_3 size k v3 s
 if (v3 = append_string v v2)
 then  return (state_api_call.append k v3, state_result.Ok, s2)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.append k v2, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_1_by_con_11 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 return (state_api_call.append k v2, state_result.Failure "no such key", s)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Ok, k, 0, v), remove_kv k s s2] → eval_state_api_call s (state_api_call.delete k, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_12 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k, 0, v) := tcond1 then
 let s2 ← gen_remove_kv_at_2 size k s
 return (state_api_call.delete k, state_result.Ok, s2)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv s (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call s (state_api_call.delete k, state_result.Failure "no such key", s)
partial def gen_eval_state_api_call_at_1_by_con_13 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 return (state_api_call.delete k, state_result.Failure "no such key", s)
throw (IO.userError "fail at checkstep")

partial def gen_eval_state_api_call_at_1 (size : Nat) (s : List (String × String)) : IO (state_api_call × state_result × List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_eval_state_api_call_at_1_by_con_1, gen_eval_state_api_call_at_1_by_con_2, gen_eval_state_api_call_at_1_by_con_3, gen_eval_state_api_call_at_1_by_con_4, gen_eval_state_api_call_at_1_by_con_5, gen_eval_state_api_call_at_1_by_con_6, gen_eval_state_api_call_at_1_by_con_7, gen_eval_state_api_call_at_1_by_con_8, gen_eval_state_api_call_at_1_by_con_9, gen_eval_state_api_call_at_1_by_con_10, gen_eval_state_api_call_at_1_by_con_11, gen_eval_state_api_call_at_1_by_con_12, gen_eval_state_api_call_at_1_by_con_13]
  let ret ← IO_to_option (f size s)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_eval_state_api_call_at_1_by_con_1, gen_eval_state_api_call_at_1_by_con_2, gen_eval_state_api_call_at_1_by_con_3, gen_eval_state_api_call_at_1_by_con_4, gen_eval_state_api_call_at_1_by_con_5, gen_eval_state_api_call_at_1_by_con_6, gen_eval_state_api_call_at_1_by_con_7, gen_eval_state_api_call_at_1_by_con_8, gen_eval_state_api_call_at_1_by_con_9, gen_eval_state_api_call_at_1_by_con_10, gen_eval_state_api_call_at_1_by_con_11, gen_eval_state_api_call_at_1_by_con_12, gen_eval_state_api_call_at_1_by_con_13] 13 size
  let ret ← IO_to_option (f size s)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end


-- #eval gen_eval_state_api_call_at_1 5 [("aa" ,"bb"), ("cc", "dd")]
-- #eval gen_eval_state_api_call_at_1 3 [("aa" ,"bb"), ("cc", "dd"), ("ee", "ff")]
-- #eval gen_eval_state_api_call_at_1 3 [("aa" ,"bb"), ("cc", "dd"), ("ee", "ff")]
