inductive MyVector (α : Type u) : Nat → Type u where
  | nil  : MyVector α 0
  | cons : (x : α) → {n : Nat} → MyVector α n → MyVector α (n+1)

#check MyVector

def v1 : MyVector Nat 3 :=
  MyVector.cons 1 (MyVector.cons 2 (MyVector.cons 3 MyVector.nil))

#check v1

def v2 : MyVector Nat 2 :=
  MyVector.cons 1 (MyVector.cons 2 MyVector.nil)

def MyStream (batch_size : Nat) (T : Type u) := Nat → MyVector T batch_size

def batched_map {T U : Type u} (batch_size : Nat) (f : T → U) (s : MyStream batch_size T) : MyStream batch_size U :=
  fun n =>
    let batch := s n
      match batch with
      | MyVector.nil => MyVector.nil
      | MyVector.cons x xs => MyVector.cons (f x) (batched_map batch_size f (fun m => xs))
