import Lean
import Std
import Plausible
--import Lean.Meta.Eval
import Plausible.IR.PlausibleIR
import Plausible.IR.KeyValueStore
open Nat
open Lean Meta


open Plausible
open Plausible.IR
open Random Gen

open KeyValueStore



--#gen_mutual_rec add_kv with_name ["s1", "s2", "l1", "l2"] backtrack 10 monad "IO"

#get_InductiveInfo eval_state_api_call
#gen_mutual_rec eval_state_api_call with_name ["s", "l"] backtrack 10 monad "IO"


--#gen_mutual_rec add_kv with_name ["in_1" , "in_2" , "in_3" , "in_4" ] backtrack 10 monad "IO"

#gen_mutual_rec_deps eval_state_api_call  backtrack 10 monad "IO"


mutual
-- CHECKER

-- Constructor: #[] → lookup_kv [] (state_result.Failure "no such key", k, 0, v)
partial def check_lookup_kv_by_con_1 (size : Nat) (in_1 : List (String × String)) (in_2 : state_result × String × Nat × String) : IO Bool:= do
match in_1 , in_2  with
| [] , (state_result.Failure "no such key", k, 0, v)  =>  return true
| _ , _  => return false

-- Constructor: #[] → lookup_kv ((k, v) :: s) (state_result.Ok, k, 0, v)
partial def check_lookup_kv_by_con_2 (size : Nat) (in_1 : List (String × String)) (in_2 : state_result × String × Nat × String) : IO Bool:= do
match in_1 , in_2  with
| (k, v) :: s , (state_result.Ok, k0, 0, v0)  =>  return (k == k0) && (v == v0)
| _ , _  => return false

-- Constructor: #[lookup_kv s (state_result.Ok, k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Ok, k1, n', v1)
partial def check_lookup_kv_by_con_3 (size : Nat) (in_1 : List (String × String)) (in_2 : state_result × String × Nat × String) : IO Bool:= do
match in_1 , in_2  with
| (k2, v2) :: s , (state_result.Ok, k1, n', v1)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k1_1, n, v1_1) := tcond1 then
 return (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
return false
| _ , _  => return false

-- Constructor: #[] → lookup_kv [(k, v)] (state_result.Failure "no such version", k, succ n, v)
partial def check_lookup_kv_by_con_4 (size : Nat) (in_1 : List (String × String)) (in_2 : state_result × String × Nat × String) : IO Bool:= do
match in_1 , in_2  with
| [(k, v)] , (state_result.Failure "no such version", k0, succ n, v0)  =>  return (k == k0) && (v == v0)
| _ , _  => return false

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Failure "no such version", k1, n', v1)
partial def check_lookup_kv_by_con_5 (size : Nat) (in_1 : List (String × String)) (in_2 : state_result × String × Nat × String) : IO Bool:= do
match in_1 , in_2  with
| (k2, v2) :: s , (state_result.Failure "no such version", k1, n', v1)  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k1_1, n, v1_1) := tcond1 then
 return (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
return false
| _ , _  => return false

partial def check_lookup_kv (size : Nat) (in_1 : List (String × String)) (in_2 : state_result × String × Nat × String) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_lookup_kv_by_con_1, check_lookup_kv_by_con_2, check_lookup_kv_by_con_4]
  let ret ← IO_to_option (f size in_1 in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_lookup_kv_by_con_1, check_lookup_kv_by_con_2, check_lookup_kv_by_con_4, check_lookup_kv_by_con_3, check_lookup_kv_by_con_5] 3 size
  let ret ← IO_to_option (f size in_1 in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[] → lookup_kv [] (state_result.Failure "no such key", k, 0, v)
partial def gen_lookup_kv_at_0_by_con_1 (size : Nat) (in_2 : state_result × String × Nat × String) : IO (List (String × String)):= do
match in_2  with
| (state_result.Failure "no such key", k, 0, v)  =>
return []
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv ((k, v) :: s) (state_result.Ok, k, 0, v)
partial def gen_lookup_kv_at_0_by_con_2 (size : Nat) (in_2 : state_result × String × Nat × String) : IO (List (String × String)):= do
match in_2  with
| (state_result.Ok, k, 0, v)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
return (k, v) :: s
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Ok, k1, n', v1)
partial def gen_lookup_kv_at_0_by_con_3 (size : Nat) (in_2 : state_result × String × Nat × String) : IO (List (String × String)):= do
match in_2  with
| (state_result.Ok, k1, n', v1)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k1_1, n, v1_1) := tcond1 then
 let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 if (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
 then  return (k2, v2) :: s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv [(k, v)] (state_result.Failure "no such version", k, succ n, v)
partial def gen_lookup_kv_at_0_by_con_4 (size : Nat) (in_2 : state_result × String × Nat × String) : IO (List (String × String)):= do
match in_2  with
| (state_result.Failure "no such version", k, succ n, v)  =>
return [(k, v)]
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Failure "no such version", k1, n', v1)
partial def gen_lookup_kv_at_0_by_con_5 (size : Nat) (in_2 : state_result × String × Nat × String) : IO (List (String × String)):= do
match in_2  with
| (state_result.Failure "no such version", k1, n', v1)  =>
let s ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k1_1, n, v1_1) := tcond1 then
 let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 if (k1 == k1_1) && (v1 == v1_1) && (n' = ver k1 k2 n)
 then  return (k2, v2) :: s
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_lookup_kv_at_0 (size : Nat) (in_2 : state_result × String × Nat × String) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_lookup_kv_at_0_by_con_1, gen_lookup_kv_at_0_by_con_2, gen_lookup_kv_at_0_by_con_4]
  let ret ← IO_to_option (f size in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_lookup_kv_at_0_by_con_1, gen_lookup_kv_at_0_by_con_2, gen_lookup_kv_at_0_by_con_4, gen_lookup_kv_at_0_by_con_3, gen_lookup_kv_at_0_by_con_5] 3 size
  let ret ← IO_to_option (f size in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[] → lookup_kv [] (state_result.Failure "no such key", k, 0, v)
partial def gen_lookup_kv_at_1_by_con_1 (size : Nat) (in_1 : List (String × String)) : IO (state_result × String × Nat × String):= do
match in_1  with
| []  =>
let k ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let v ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
return (state_result.Failure "no such key", k, 0, v)
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv ((k, v) :: s) (state_result.Ok, k, 0, v)
partial def gen_lookup_kv_at_1_by_con_2 (size : Nat) (in_1 : List (String × String)) : IO (state_result × String × Nat × String):= do
match in_1  with
| (k, v) :: s  =>
return (state_result.Ok, k, 0, v)
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Ok, k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Ok, k1, n', v1)
partial def gen_lookup_kv_at_1_by_con_3 (size : Nat) (in_1 : List (String × String)) : IO (state_result × String × Nat × String):= do
match in_1  with
| (k2, v2) :: s  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Ok, k1, n, v1) := tcond1 then
 let n' ← monadLift <| Gen.run (SampleableExt.interpSample Nat) 100
 if (n' = ver k1 k2 n)
 then  return (state_result.Ok, k1, n', v1)
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[] → lookup_kv [(k, v)] (state_result.Failure "no such version", k, succ n, v)
partial def gen_lookup_kv_at_1_by_con_4 (size : Nat) (in_1 : List (String × String)) : IO (state_result × String × Nat × String):= do
match in_1  with
| [(k, v)]  =>
let n ← monadLift <| Gen.run (SampleableExt.interpSample Nat) 100
return (state_result.Failure "no such version", k, succ n, v)
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv s (state_result.Failure "no such version", k1, n, v1), n' = ver k1 k2 n] → lookup_kv ((k2, v2) :: s) (state_result.Failure "no such version", k1, n', v1)
partial def gen_lookup_kv_at_1_by_con_5 (size : Nat) (in_1 : List (String × String)) : IO (state_result × String × Nat × String):= do
match in_1  with
| (k2, v2) :: s  =>
let tcond1 ← gen_lookup_kv_at_1 size s
if let (state_result.Failure "no such version", k1, n, v1) := tcond1 then
 let n' ← monadLift <| Gen.run (SampleableExt.interpSample Nat) 100
 if (n' = ver k1 k2 n)
 then  return (state_result.Failure "no such version", k1, n', v1)
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_lookup_kv_at_1 (size : Nat) (in_1 : List (String × String)) : IO (state_result × String × Nat × String) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_lookup_kv_at_1_by_con_1, gen_lookup_kv_at_1_by_con_2, gen_lookup_kv_at_1_by_con_4]
  let ret ← IO_to_option (f size in_1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_lookup_kv_at_1_by_con_1, gen_lookup_kv_at_1_by_con_2, gen_lookup_kv_at_1_by_con_4, gen_lookup_kv_at_1_by_con_3, gen_lookup_kv_at_1_by_con_5] 3 size
  let ret ← IO_to_option (f size in_1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end
mutual
-- CHECKER

-- Constructor: #[] → add_kv in_1 in_2 in_3 ((in_1, in_2) :: in_3)
partial def check_add_kv_by_con_1 (size : Nat) (in_1 : String) (in_2 : String) (in_3 : List (String × String)) (in_4 : List (String × String)) : IO Bool:= do
match in_4  with
| (in_10, in_20) :: in_30  =>  return (in_1 == in_10) && (in_2 == in_20) && (in_3 == in_30)
| _  => return false

partial def check_add_kv (size : Nat) (in_1 : String) (in_2 : String) (in_3 : List (String × String)) (in_4 : List (String × String)) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_add_kv_by_con_1]
  let ret ← IO_to_option (f size in_1 in_2 in_3 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_add_kv_by_con_1] 1 size
  let ret ← IO_to_option (f size in_1 in_2 in_3 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[] → add_kv in_1 in_2 in_3 ((in_1, in_2) :: in_3)
partial def gen_add_kv_at_0_by_con_1 (size : Nat) (in_2 : String) (in_3 : List (String × String)) (in_4 : List (String × String)) : IO String:= do
match in_4  with
| (in_1, in_20) :: in_30  =>
if (in_2 == in_20) && (in_3 == in_30)
then return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_add_kv_at_0 (size : Nat) (in_2 : String) (in_3 : List (String × String)) (in_4 : List (String × String)) : IO String := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_0_by_con_1]
  let ret ← IO_to_option (f size in_2 in_3 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_0_by_con_1] 1 size
  let ret ← IO_to_option (f size in_2 in_3 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[] → add_kv in_1 in_2 in_3 ((in_1, in_2) :: in_3)
partial def gen_add_kv_at_1_by_con_1 (size : Nat) (in_1 : String) (in_3 : List (String × String)) (in_4 : List (String × String)) : IO String:= do
match in_4  with
| (in_10, in_2) :: in_30  =>
if (in_1 == in_10) && (in_3 == in_30)
then return in_2
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_add_kv_at_1 (size : Nat) (in_1 : String) (in_3 : List (String × String)) (in_4 : List (String × String)) : IO String := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_1_by_con_1]
  let ret ← IO_to_option (f size in_1 in_3 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_1_by_con_1] 1 size
  let ret ← IO_to_option (f size in_1 in_3 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG2

-- Constructor: #[] → add_kv in_1 in_2 in_3 ((in_1, in_2) :: in_3)
partial def gen_add_kv_at_2_by_con_1 (size : Nat) (in_1 : String) (in_2 : String) (in_4 : List (String × String)) : IO (List (String × String)):= do
match in_4  with
| (in_10, in_20) :: in_3  =>
if (in_1 == in_10) && (in_2 == in_20)
then return in_3
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_add_kv_at_2 (size : Nat) (in_1 : String) (in_2 : String) (in_4 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_2_by_con_1]
  let ret ← IO_to_option (f size in_1 in_2 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_2_by_con_1] 1 size
  let ret ← IO_to_option (f size in_1 in_2 in_4)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG3

-- Constructor: #[] → add_kv in_1 in_2 in_3 ((in_1, in_2) :: in_3)
partial def gen_add_kv_at_3_by_con_1 (size : Nat) (in_1 : String) (in_2 : String) (in_3 : List (String × String)) : IO (List (String × String)):= do
return (in_1, in_2) :: in_3

partial def gen_add_kv_at_3 (size : Nat) (in_1 : String) (in_2 : String) (in_3 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_add_kv_at_3_by_con_1]
  let ret ← IO_to_option (f size in_1 in_2 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_add_kv_at_3_by_con_1] 1 size
  let ret ← IO_to_option (f size in_1 in_2 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end
mutual
-- CHECKER

-- Constructor: #[] → remove_kv in_1 [] []
partial def check_remove_kv_by_con_1 (size : Nat) (in_1 : String) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO Bool:= do
match in_2 , in_3  with
| [] , []  =>  return true
| _ , _  => return false

-- Constructor: #[remove_kv in_1 s1 in_3] → remove_kv in_1 ((in_1, v) :: s1) in_3
partial def check_remove_kv_by_con_2 (size : Nat) (in_1 : String) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO Bool:= do
match in_2  with
| (in_10, v) :: s1  =>
let check1 ← check_remove_kv size in_1 s1 in_3
return check1 && (in_1 == in_10)
| _  => return false

-- Constructor: #[(in_1 != k2) = true, remove_kv in_1 s1 s2] → remove_kv in_1 ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def check_remove_kv_by_con_3 (size : Nat) (in_1 : String) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO Bool:= do
match in_2 , in_3  with
| (k2, v2) :: s1 , (k20, v20) :: s2  =>
let check1 ← check_remove_kv size in_1 s1 s2
return check1 && (k2 == k20) && (v2 == v20) && ((in_1 != k2) = true)
| _ , _  => return false

partial def check_remove_kv (size : Nat) (in_1 : String) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_remove_kv_by_con_1]
  let ret ← IO_to_option (f size in_1 in_2 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_remove_kv_by_con_1, check_remove_kv_by_con_2, check_remove_kv_by_con_3] 1 size
  let ret ← IO_to_option (f size in_1 in_2 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[] → remove_kv in_1 [] []
partial def gen_remove_kv_at_0_by_con_1 (size : Nat) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO String:= do
match in_2 , in_3  with
| [] , []  =>
let in_1 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
return in_1
| _ , _  => throw (IO.userError "fail")

-- Constructor: #[remove_kv in_1 s1 in_3] → remove_kv in_1 ((in_1, v) :: s1) in_3
partial def gen_remove_kv_at_0_by_con_2 (size : Nat) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO String:= do
match in_2  with
| (in_1, v) :: s1  =>

let check1 ← check_remove_kv size in_1 s1 in_3
if check1
then return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[(in_1 != k2) = true, remove_kv in_1 s1 s2] → remove_kv in_1 ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def gen_remove_kv_at_0_by_con_3 (size : Nat) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO String:= do
match in_2 , in_3  with
| (k2, v2) :: s1 , (k20, v20) :: s2  =>
let in_1 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let check1 ← check_remove_kv size in_1 s1 s2
if check1 && (k2 == k20) && (v2 == v20) && ((in_1 != k2) = true)
then return in_1
throw (IO.userError "fail at checkstep")
| _ , _  => throw (IO.userError "fail")

partial def gen_remove_kv_at_0 (size : Nat) (in_2 : List (String × String)) (in_3 : List (String × String)) : IO String := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_remove_kv_at_0_by_con_1]
  let ret ← IO_to_option (f size in_2 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_remove_kv_at_0_by_con_1, gen_remove_kv_at_0_by_con_2, gen_remove_kv_at_0_by_con_3] 1 size
  let ret ← IO_to_option (f size in_2 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[] → remove_kv in_1 [] []
partial def gen_remove_kv_at_1_by_con_1 (size : Nat) (in_1 : String) (in_3 : List (String × String)) : IO (List (String × String)):= do
match in_3  with
| []  =>
return []
| _  => throw (IO.userError "fail")

-- Constructor: #[remove_kv in_1 s1 in_3] → remove_kv in_1 ((in_1, v) :: s1) in_3
partial def gen_remove_kv_at_1_by_con_2 (size : Nat) (in_1 : String) (in_3 : List (String × String)) : IO (List (String × String)):= do
let s1 ← gen_remove_kv_at_1 size in_1 in_3
let v ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
return (in_1, v) :: s1

-- Constructor: #[(in_1 != k2) = true, remove_kv in_1 s1 s2] → remove_kv in_1 ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def gen_remove_kv_at_1_by_con_3 (size : Nat) (in_1 : String) (in_3 : List (String × String)) : IO (List (String × String)):= do
match in_3  with
| (k2, v2) :: s2  =>
let s1 ← gen_remove_kv_at_1 size in_1 s2
if ((in_1 != k2) = true)
then return (k2, v2) :: s1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_remove_kv_at_1 (size : Nat) (in_1 : String) (in_3 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_remove_kv_at_1_by_con_1]
  let ret ← IO_to_option (f size in_1 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_remove_kv_at_1_by_con_1, gen_remove_kv_at_1_by_con_2, gen_remove_kv_at_1_by_con_3] 1 size
  let ret ← IO_to_option (f size in_1 in_3)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG2

-- Constructor: #[] → remove_kv in_1 [] []
partial def gen_remove_kv_at_2_by_con_1 (size : Nat) (in_1 : String) (in_2 : List (String × String)) : IO (List (String × String)):= do
match in_2  with
| []  =>
return []
| _  => throw (IO.userError "fail")

-- Constructor: #[remove_kv in_1 s1 in_3] → remove_kv in_1 ((in_1, v) :: s1) in_3
partial def gen_remove_kv_at_2_by_con_2 (size : Nat) (in_1 : String) (in_2 : List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (in_10, v) :: s1  =>
let in_3 ← gen_remove_kv_at_2 size in_1 s1
if (in_1 == in_10)
then return in_3
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[(in_1 != k2) = true, remove_kv in_1 s1 s2] → remove_kv in_1 ((k2, v2) :: s1) ((k2, v2) :: s2)
partial def gen_remove_kv_at_2_by_con_3 (size : Nat) (in_1 : String) (in_2 : List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (k2, v2) :: s1  =>
let s2 ← gen_remove_kv_at_2 size in_1 s1
if ((in_1 != k2) = true)
then return (k2, v2) :: s2
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_remove_kv_at_2 (size : Nat) (in_1 : String) (in_2 : List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_remove_kv_at_2_by_con_1]
  let ret ← IO_to_option (f size in_1 in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_remove_kv_at_2_by_con_1, gen_remove_kv_at_2_by_con_2, gen_remove_kv_at_2_by_con_3] 1 size
  let ret ← IO_to_option (f size in_1 in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end
mutual
-- CHECKER

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v)] → eval_state_api_call in_1 (state_api_call.get k none, state_result.Result v, in_1)
partial def check_eval_state_api_call_by_con_1 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.get k none, state_result.Result v, in_10)  =>
let check1 ← check_lookup_kv size in_1 (state_result.Ok, k, 0, v)
return check1 && (in_1 == in_10)
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.get k none, state_result.Failure "no such key", in_1)
partial def check_eval_state_api_call_by_con_2 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.get k none, state_result.Failure "no such key", in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, n, v)] → eval_state_api_call in_1 (state_api_call.get k (some n), state_result.Result v, in_1)
partial def check_eval_state_api_call_by_con_3 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.get k (some n), state_result.Result v, in_10)  =>
let check1 ← check_lookup_kv size in_1 (state_result.Ok, k, n, v)
return check1 && (in_1 == in_10)
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such version", k, n, v)] → eval_state_api_call in_1 (state_api_call.get k (some n), state_result.Failure "no such version", in_1)
partial def check_eval_state_api_call_by_con_4 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.get k (some n), state_result.Failure "no such version", in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such version", k_1, n_1, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1) && (n == n_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v)] → eval_state_api_call in_1 (state_api_call.key_exists k, state_result.Ok, in_1)
partial def check_eval_state_api_call_by_con_5 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.key_exists k, state_result.Ok, in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.key_exists k, state_result.Result "no such key", in_1)
partial def check_eval_state_api_call_by_con_6 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.key_exists k, state_result.Result "no such key", in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1)
return false
| _  => return false

-- Constructor: #[add_kv k v in_1 s2] → eval_state_api_call in_1 (state_api_call.set k v, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_7 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.set k v, state_result.Ok, s2)  =>
let check1 ← check_add_kv size k v in_1 s2
return check1
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), add_kv k2 v in_1 s2] → eval_state_api_call in_1 (state_api_call.copy k k2, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_8 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.copy k k2, state_result.Ok, s2)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_add_kv size k2 v in_1 s2
 return check1 && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.copy k k2, state_result.Failure "no such key", in_1)
partial def check_eval_state_api_call_by_con_9 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.copy k k2, state_result.Failure "no such key", in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), v3 = append_string v v2, add_kv k v3 in_1 s2] → eval_state_api_call in_1 (state_api_call.append k v3, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_10 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.append k v3, state_result.Ok, s2)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let check1 ← check_add_kv size k v3 in_1 s2
 return check1 && (k == k_1) && (v3 = append_string v v2)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.append k v2, state_result.Failure "no such key", in_1)
partial def check_eval_state_api_call_by_con_11 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.append k v2, state_result.Failure "no such key", in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), remove_kv k in_1 s2] → eval_state_api_call in_1 (state_api_call.delete k, state_result.Ok, s2)
partial def check_eval_state_api_call_by_con_12 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.delete k, state_result.Ok, s2)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_remove_kv size k in_1 s2
 return check1 && (k == k_1)
return false
| _  => return false

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.delete k, state_result.Failure "no such key", in_1)
partial def check_eval_state_api_call_by_con_13 (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool:= do
match in_2  with
| (state_api_call.delete k, state_result.Failure "no such key", in_10)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 return (in_1 == in_10) && (k == k_1)
return false
| _  => return false

partial def check_eval_state_api_call (size : Nat) (in_1 : List (String × String)) (in_2 : state_api_call × state_result × List (String × String)) : IO Bool := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[check_eval_state_api_call_by_con_1, check_eval_state_api_call_by_con_2, check_eval_state_api_call_by_con_3, check_eval_state_api_call_by_con_4, check_eval_state_api_call_by_con_5, check_eval_state_api_call_by_con_6, check_eval_state_api_call_by_con_7, check_eval_state_api_call_by_con_8, check_eval_state_api_call_by_con_9, check_eval_state_api_call_by_con_10, check_eval_state_api_call_by_con_11, check_eval_state_api_call_by_con_12, check_eval_state_api_call_by_con_13]
  let ret ← IO_to_option (f size in_1 in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[check_eval_state_api_call_by_con_1, check_eval_state_api_call_by_con_2, check_eval_state_api_call_by_con_3, check_eval_state_api_call_by_con_4, check_eval_state_api_call_by_con_5, check_eval_state_api_call_by_con_6, check_eval_state_api_call_by_con_7, check_eval_state_api_call_by_con_8, check_eval_state_api_call_by_con_9, check_eval_state_api_call_by_con_10, check_eval_state_api_call_by_con_11, check_eval_state_api_call_by_con_12, check_eval_state_api_call_by_con_13] 13 size
  let ret ← IO_to_option (f size in_1 in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG0

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v)] → eval_state_api_call in_1 (state_api_call.get k none, state_result.Result v, in_1)
partial def gen_eval_state_api_call_at_0_by_con_1 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.get k none, state_result.Result v, in_1)  =>

let check1 ← check_lookup_kv size in_1 (state_result.Ok, k, 0, v)
if check1
then return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.get k none, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_0_by_con_2 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.get k none, state_result.Failure "no such key", in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, n, v)] → eval_state_api_call in_1 (state_api_call.get k (some n), state_result.Result v, in_1)
partial def gen_eval_state_api_call_at_0_by_con_3 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.get k (some n), state_result.Result v, in_1)  =>

let check1 ← check_lookup_kv size in_1 (state_result.Ok, k, n, v)
if check1
then return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such version", k, n, v)] → eval_state_api_call in_1 (state_api_call.get k (some n), state_result.Failure "no such version", in_1)
partial def gen_eval_state_api_call_at_0_by_con_4 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.get k (some n), state_result.Failure "no such version", in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such version", k_1, n_1, v) := tcond1 then
 if (k == k_1) && (n == n_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v)] → eval_state_api_call in_1 (state_api_call.key_exists k, state_result.Ok, in_1)
partial def gen_eval_state_api_call_at_0_by_con_5 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.key_exists k, state_result.Ok, in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.key_exists k, state_result.Result "no such key", in_1)
partial def gen_eval_state_api_call_at_0_by_con_6 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.key_exists k, state_result.Result "no such key", in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[add_kv k v in_1 s2] → eval_state_api_call in_1 (state_api_call.set k v, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_7 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.set k v, state_result.Ok, s2)  =>
let in_1 ← gen_add_kv_at_2 size k v s2
return in_1
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), add_kv k2 v in_1 s2] → eval_state_api_call in_1 (state_api_call.copy k k2, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_8 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.copy k k2, state_result.Ok, s2)  =>
let in_1 ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_add_kv size k2 v in_1 s2
 if check1 && (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.copy k k2, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_0_by_con_9 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.copy k k2, state_result.Failure "no such key", in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), v3 = append_string v v2, add_kv k v3 in_1 s2] → eval_state_api_call in_1 (state_api_call.append k v3, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_10 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.append k v3, state_result.Ok, s2)  =>
let in_1 ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let check1 ← check_add_kv size k v3 in_1 s2
 if check1 && (k == k_1) && (v3 = append_string v v2)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.append k v2, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_0_by_con_11 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.append k v2, state_result.Failure "no such key", in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), remove_kv k in_1 s2] → eval_state_api_call in_1 (state_api_call.delete k, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_0_by_con_12 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.delete k, state_result.Ok, s2)  =>
let in_1 ← monadLift <| Gen.run (SampleableExt.interpSample (List (String × String))) 100
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k_1, 0, v) := tcond1 then
 let check1 ← check_remove_kv size k in_1 s2
 if check1 && (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.delete k, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_0_by_con_13 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)):= do
match in_2  with
| (state_api_call.delete k, state_result.Failure "no such key", in_1)  =>
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k_1, 0, v) := tcond1 then
 if (k == k_1)
 then  return in_1
throw (IO.userError "fail at checkstep")
| _  => throw (IO.userError "fail")

partial def gen_eval_state_api_call_at_0 (size : Nat) (in_2 : state_api_call × state_result × List (String × String)) : IO (List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_eval_state_api_call_at_0_by_con_1, gen_eval_state_api_call_at_0_by_con_2, gen_eval_state_api_call_at_0_by_con_3, gen_eval_state_api_call_at_0_by_con_4, gen_eval_state_api_call_at_0_by_con_5, gen_eval_state_api_call_at_0_by_con_6, gen_eval_state_api_call_at_0_by_con_7, gen_eval_state_api_call_at_0_by_con_8, gen_eval_state_api_call_at_0_by_con_9, gen_eval_state_api_call_at_0_by_con_10, gen_eval_state_api_call_at_0_by_con_11, gen_eval_state_api_call_at_0_by_con_12, gen_eval_state_api_call_at_0_by_con_13]
  let ret ← IO_to_option (f size in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_eval_state_api_call_at_0_by_con_1, gen_eval_state_api_call_at_0_by_con_2, gen_eval_state_api_call_at_0_by_con_3, gen_eval_state_api_call_at_0_by_con_4, gen_eval_state_api_call_at_0_by_con_5, gen_eval_state_api_call_at_0_by_con_6, gen_eval_state_api_call_at_0_by_con_7, gen_eval_state_api_call_at_0_by_con_8, gen_eval_state_api_call_at_0_by_con_9, gen_eval_state_api_call_at_0_by_con_10, gen_eval_state_api_call_at_0_by_con_11, gen_eval_state_api_call_at_0_by_con_12, gen_eval_state_api_call_at_0_by_con_13] 13 size
  let ret ← IO_to_option (f size in_2)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

-- GENERATOR FOR ARG1

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v)] → eval_state_api_call in_1 (state_api_call.get k none, state_result.Result v, in_1)
partial def gen_eval_state_api_call_at_1_by_con_1 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k, 0, v) := tcond1 then
 return (state_api_call.get k none, state_result.Result v, in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.get k none, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_1_by_con_2 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 return (state_api_call.get k none, state_result.Failure "no such key", in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, n, v)] → eval_state_api_call in_1 (state_api_call.get k (some n), state_result.Result v, in_1)
partial def gen_eval_state_api_call_at_1_by_con_3 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k, n, v) := tcond1 then
 return (state_api_call.get k (some n), state_result.Result v, in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such version", k, n, v)] → eval_state_api_call in_1 (state_api_call.get k (some n), state_result.Failure "no such version", in_1)
partial def gen_eval_state_api_call_at_1_by_con_4 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such version", k, n, v) := tcond1 then
 return (state_api_call.get k (some n), state_result.Failure "no such version", in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v)] → eval_state_api_call in_1 (state_api_call.key_exists k, state_result.Ok, in_1)
partial def gen_eval_state_api_call_at_1_by_con_5 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k, 0, v) := tcond1 then
 return (state_api_call.key_exists k, state_result.Ok, in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.key_exists k, state_result.Result "no such key", in_1)
partial def gen_eval_state_api_call_at_1_by_con_6 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 return (state_api_call.key_exists k, state_result.Result "no such key", in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[add_kv k v in_1 s2] → eval_state_api_call in_1 (state_api_call.set k v, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_7 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let k ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let v ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
let s2 ← gen_add_kv_at_3 size k v in_1
return (state_api_call.set k v, state_result.Ok, s2)

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), add_kv k2 v in_1 s2] → eval_state_api_call in_1 (state_api_call.copy k k2, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_8 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k, 0, v) := tcond1 then
 let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let s2 ← gen_add_kv_at_3 size k2 v in_1
 return (state_api_call.copy k k2, state_result.Ok, s2)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.copy k k2, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_1_by_con_9 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 let k2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 return (state_api_call.copy k k2, state_result.Failure "no such key", in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), v3 = append_string v v2, add_kv k v3 in_1 s2] → eval_state_api_call in_1 (state_api_call.append k v3, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_10 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k, 0, v) := tcond1 then
 let v3 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 let s2 ← gen_add_kv_at_3 size k v3 in_1
 if (v3 = append_string v v2)
 then  return (state_api_call.append k v3, state_result.Ok, s2)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.append k v2, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_1_by_con_11 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 let v2 ← monadLift <| Gen.run (SampleableExt.interpSample String) 100
 return (state_api_call.append k v2, state_result.Failure "no such key", in_1)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Ok, k, 0, v), remove_kv k in_1 s2] → eval_state_api_call in_1 (state_api_call.delete k, state_result.Ok, s2)
partial def gen_eval_state_api_call_at_1_by_con_12 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Ok, k, 0, v) := tcond1 then
 let s2 ← gen_remove_kv_at_2 size k in_1
 return (state_api_call.delete k, state_result.Ok, s2)
throw (IO.userError "fail at checkstep")

-- Constructor: #[lookup_kv in_1 (state_result.Failure "no such key", k, 0, v)] → eval_state_api_call in_1 (state_api_call.delete k, state_result.Failure "no such key", in_1)
partial def gen_eval_state_api_call_at_1_by_con_13 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)):= do
let tcond1 ← gen_lookup_kv_at_1 size in_1
if let (state_result.Failure "no such key", k, 0, v) := tcond1 then
 return (state_api_call.delete k, state_result.Failure "no such key", in_1)
throw (IO.userError "fail at checkstep")

partial def gen_eval_state_api_call_at_1 (size : Nat) (in_1 : List (String × String)) : IO (state_api_call × state_result × List (String × String)) := do
match size with
| zero =>
 for _i in [1:10] do
  let f ← uniform_backtracking_IO #[gen_eval_state_api_call_at_1_by_con_1, gen_eval_state_api_call_at_1_by_con_2, gen_eval_state_api_call_at_1_by_con_3, gen_eval_state_api_call_at_1_by_con_4, gen_eval_state_api_call_at_1_by_con_5, gen_eval_state_api_call_at_1_by_con_6, gen_eval_state_api_call_at_1_by_con_7, gen_eval_state_api_call_at_1_by_con_8, gen_eval_state_api_call_at_1_by_con_9, gen_eval_state_api_call_at_1_by_con_10, gen_eval_state_api_call_at_1_by_con_11, gen_eval_state_api_call_at_1_by_con_12, gen_eval_state_api_call_at_1_by_con_13]
  let ret ← IO_to_option (f size in_1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")
| succ size =>
 for _i in [1:10] do
  let f ← weight_backtracking_IO #[gen_eval_state_api_call_at_1_by_con_1, gen_eval_state_api_call_at_1_by_con_2, gen_eval_state_api_call_at_1_by_con_3, gen_eval_state_api_call_at_1_by_con_4, gen_eval_state_api_call_at_1_by_con_5, gen_eval_state_api_call_at_1_by_con_6, gen_eval_state_api_call_at_1_by_con_7, gen_eval_state_api_call_at_1_by_con_8, gen_eval_state_api_call_at_1_by_con_9, gen_eval_state_api_call_at_1_by_con_10, gen_eval_state_api_call_at_1_by_con_11, gen_eval_state_api_call_at_1_by_con_12, gen_eval_state_api_call_at_1_by_con_13] 13 size
  let ret ← IO_to_option (f size in_1)
  match ret with
  | some ret => return ret
  | _ => continue
 throw (IO.userError "fail")

end
