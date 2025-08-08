import Lean
open Nat

namespace KeyValueStore

inductive state_api_call where
| get (k: String) (ver: Option Nat): state_api_call
| key_exists (k: String): state_api_call
| set (k: String) (v: String): state_api_call
| copy (k: String) (k2: String): state_api_call
| append (k: String) (v: String): state_api_call
| delete (k: String): state_api_call
deriving Repr

inductive state_result where
| Ok
| Failure (s:String): state_result
| Result (s:String): state_result
deriving Repr

inductive api_call where
| create_bucket
| op_bucket (bucket_id: Nat) (c: state_api_call): api_call
| delete_bucket (bucket_id: Nat): api_call

inductive result where
| Created (n:Nat) : result
| Removed: result
| Error (s:String): result
| Op_result (r: state_result): result

inductive add_kv : String -> String -> (List (String × String)) -> (List (String × String)) -> Prop where
| A_nil: ∀ k v s, add_kv k v s ((k,v)::s)

def ver (k1:String) (k2:String) (n:Nat) : Nat := if k1 == k2 then (succ n) else n

def append_string (s1:String) (s2:String) : String := s1 ++ s2

inductive lookup_kv : (List (String × String)) -> state_result ×  String ×  Nat  ×  String -> Prop where
| L_none: forall k v, lookup_kv [] ((state_result.Failure "no such key"),k,0,v)
| L_found: forall k v s, lookup_kv ((k,v)::s) (.Ok,k,0,v)
| L_found_S: forall k1 k2 v1 v2 s n n',
    lookup_kv s (.Ok,k1,n,v1) ->
    n' = ver k1 k2 n ->
    lookup_kv ((k2,v2)::s) (.Ok,k1,n',v1)
| L_wrongver: forall k v n,
    lookup_kv [(k,v)] ((.Failure "no such version"),k,(succ n),v)
| L_wrongver_S: forall k1 v1 k2 v2 s n n',
    lookup_kv s ((.Failure "no such version"),k1,n,v1) ->
    n' = ver k1 k2 n ->
    lookup_kv ((k2,v2)::s) ((.Failure "no such version"),k1,n',v1)


inductive remove_kv : String -> (List (String × String)) -> (List (String × String)) -> Prop where
| R_nil: forall k, remove_kv k [] []
| R_found: forall k v s1 s2,
    remove_kv k s1 s2 ->
    remove_kv k ((k,v)::s1) s2
| R_cons: forall k1 k2 v2 s1 s2,
    k1 != k2 ->
    remove_kv k1 s1 s2 ->
    remove_kv k1 ((k2,v2)::s1) ((k2,v2)::s2)


inductive eval_state_api_call : (List (String × String)) -> (state_api_call × state_result × (List (String × String))) -> Prop where
| E_get : forall s k v,
    lookup_kv s (.Ok,k,0,v) ->
    eval_state_api_call s ((.get k none),(.Result v),s)
| E_get_fail_no_key: forall s k v,
    lookup_kv s ((.Failure "no such key"),k,0,v) ->
    eval_state_api_call s ((.get k none),(.Failure "no such key"),s)
| E_get_version : forall s k n v,
    lookup_kv s (.Ok,k,n,v) ->
    eval_state_api_call s ((.get k (some n)),(.Result v),s)
| E_get_fail_no_ver: forall s k n v,
    lookup_kv s ((.Failure "no such version"),k,n,v) ->
    eval_state_api_call s ((.get k (some n)),(.Failure "no such version"),s)
| E_exists : forall k v s,
    lookup_kv s (.Ok,k,0,v) ->
    eval_state_api_call s ((.key_exists k),.Ok,s)
| E_exists_fail : forall k v s,
    lookup_kv s ((.Failure "no such key"),k,0,v) ->
    eval_state_api_call s ((.key_exists k),(.Result "no such key"),s)
| E_set : forall s1 s2 k v,
    add_kv k v s1 s2 ->
    eval_state_api_call s1 ((.set k v),.Ok,s2)
| E_copy : forall k v k2 s1 s2,
    lookup_kv s1 (.Ok,k,0,v) ->
    add_kv k2 v s1 s2 ->
    eval_state_api_call s1 ((.copy k k2),.Ok,s2)
| E_copy_fail : forall k v k2 s,
    lookup_kv s ((.Failure "no such key"),k,0,v) ->
    eval_state_api_call s ((.copy k k2),(.Failure "no such key"),s)
| E_append : forall s1 s2 k v v2 v3,
    lookup_kv s1 (.Ok,k,0,v) ->
    v3 = append_string v v2 ->
    add_kv k v3 s1 s2 ->
    eval_state_api_call s1 ((.append k v3),.Ok,s2)
| E_append_fail : forall s k v v2,
    lookup_kv s ((.Failure "no such key"),k,0,v) ->
    eval_state_api_call s ((.append k v2),(.Failure "no such key"),s)
| E_delete_present : forall s1 s2 k v,
    lookup_kv s1 (.Ok,k,0,v) ->
    remove_kv k s1 s2 ->
    eval_state_api_call s1 ((.delete k),.Ok,s2)
| E_delete_fail : forall s k v,
    lookup_kv s ((.Failure "no such key"),k,0,v) ->
    eval_state_api_call s ((.delete k),(.Failure "no such key"),s)

inductive get_bucket: List (Nat × (List (String × String))) -> (Nat × (List (String ×  String))) -> Prop where
| GB_found : forall n x s, get_bucket ((n,x)::s) (n,x)
| GB_next: forall n n' x x' s,
    n != n' ->
    get_bucket s (n,x) ->
    get_bucket ((n',x')::s) (n,x)

end KeyValueStore
