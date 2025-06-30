import Plausible.New.Enumerators

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] -/
#guard_msgs in
#eval (Enum.enum 15 : LazyList Nat)

/-- info: [0, 1, 2, 3, 4, 5, 6, 7] -/
#guard_msgs in
#eval (Enum.enum 7 : LazyList Nat)

/-- info: [0, 1, 2, 3, 4] -/
#guard_msgs in
#eval (Enum.enum 5 : LazyList (Fin 5))

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] -/
#guard_msgs in
#eval (Enum.enum 10 : LazyList (Fin 10))


/-- info: [false, true] -/
#guard_msgs in
#eval (Enum.enum 10 : LazyList Bool)

/--
info: [(0, false),
 (0, true),
 (1, false),
 (1, true),
 (2, false),
 (2, true),
 (3, false),
 (3, true),
 (4, false),
 (4, true),
 (5, false),
 (5, true)]
-/
#guard_msgs in
#eval (Enum.enum 5 : LazyList (Nat × Bool))

/--
info: [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr false, Sum.inr true]
-/
#guard_msgs in
#eval (Enum.enum 5 : LazyList (Nat ⊕ Bool))

/--
info: [[], [0], [0, 0], [0, 1], [1], [1, 0], [1, 1], [2], [2, 0], [2, 1], [3], [3, 0], [3, 1]]
-/
#guard_msgs in
#eval (Enum.enum 3 : LazyList (List Nat))

/--
info: [' ', '!', '\"', '#', '$', '%', '&', ''', '(', ')', '*', '+', ',', '-', '.', '/', '0', '1', '2', '3']
-/
#guard_msgs in
#eval (Enum.enum 20 : LazyList Char)
