inductive MyVector (α : Type u) : Nat → Type u where
  | nil  : MyVector α 0
  | cons : (x : α) → {n : Nat} → MyVector α n → MyVector α (n+1)

#check MyVector

def v1 : MyVector Nat 3 :=
  MyVector.cons 1 (MyVector.cons 2 (MyVector.cons 3 MyVector.nil))

#check v1

def v2 : MyVector Nat 2 :=
  MyVector.cons 1 (MyVector.cons 2 MyVector.nil)

#check v2
