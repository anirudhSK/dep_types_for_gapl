inductive MyVector (α : Type u) : Nat → Type u where
  | nil  : MyVector α 0
  | cons : (x : α) → {n : Nat} → MyVector α n → MyVector α (n+1)

def MyVector.length
  {α : Type u}
  {n : Nat}
  (v : MyVector α n)
  : Nat :=
    n

def MyVector.concat
  {α : Type u}
  {n m : Nat}
  (v1 : MyVector α n)
  (v2 : MyVector α m)
  : MyVector α (n + m) :=
    match v1 with
    | MyVector.nil => by simp [Nat.zero_add]; exact v2
    | MyVector.cons x xs =>
        by simp [Nat.succ_add]; exact
        MyVector.cons x (MyVector.concat xs v2)


theorem MyVector.concat_commutative_lengths
  {α : Type u}
  {n m : Nat}
  (v1 : MyVector α n)
  (v2 : MyVector α m)
  : MyVector.length (MyVector.concat v1 v2) = MyVector.length (MyVector.concat v2 v1) :=
    by
      simp [MyVector.length]
      rw [Nat.add_comm n m]

def MyVector.concat_many
  {α : Type u}
  {n : Nat}
  (start: Nat)
  (count: Nat)
  (vecs: Nat → MyVector α n)
  : MyVector α (n * count) :=
    match count with
    | 0 => by simp [Nat.mul_zero]; exact MyVector.nil
    | count'+1 =>
        let first_batch: MyVector α n := vecs start
        MyVector.concat
          first_batch
          (MyVector.concat_many (start + 1) count' vecs)


def MyVector.singleton
  {α : Type u}
  (x : α)
  : MyVector α 1 :=
    MyVector.cons x MyVector.nil

def MyVector.first
  {α : Type u}
  (v : MyVector α 1)
  : α :=
    match v with
    | MyVector.cons x MyVector.nil => x

-- map function over MyVector
def MyVector.map
  {α β : Type u}
  {n : Nat}
  (v : MyVector α n)
  (f : α → β)
  : MyVector β n :=
    match v with
    | MyVector.nil => MyVector.nil
    | MyVector.cons x xs => MyVector.cons (f x) (MyVector.map xs f)

def MyVector.foldl
  {α β : Type u}
  {n : Nat}
  (v : MyVector α n)
  (current_state : β)
  (f : β → α → β)
  : β :=
    match v with
    | MyVector.nil => current_state
    | MyVector.cons x xs => MyVector.foldl xs (f current_state x) f

#check MyVector

def v1 : MyVector Nat 3 :=
  MyVector.cons 1 (MyVector.cons 2 (MyVector.cons 3 MyVector.nil))

#check v1

def v2 : MyVector Nat 2 :=
  MyVector.cons 1 (MyVector.cons 2 MyVector.nil)

def MyStream (batch_size : Nat) (T : Type u) := Nat → MyVector T batch_size

def batched_map
  {T U : Type u}
  {batch_size : Nat}
  (f : T → U)
  (s : MyStream batch_size T)
  : MyStream batch_size U :=
    fun n =>
    let batch: MyVector T batch_size := s n
    MyVector.map batch f


def replicated_fold_up_to
  {T U : Type u}
  {batch_size : Nat}
  (s : MyStream batch_size T)
  (initial_state : U)
  (f : U → T → U)
  (n : Nat)
  : U :=
    let prev_state: U :=
      match n with
      | 0 => initial_state
      | n'+1 =>
        replicated_fold_up_to s initial_state f n'
    let batch: MyVector T batch_size := s n
    let new_state: U := MyVector.foldl batch prev_state f
    new_state


def replicated_fold
  {T U : Type u}
  {batch_size : Nat}
  (s : MyStream batch_size T)
  (initial_state : U)
  (f : U → T → U)
  : MyStream 1 U :=
    fun n =>
    let final_state: U := replicated_fold_up_to s initial_state f n
    MyVector.singleton final_state



def rebatch_smaller_to_larger
  {T : Type u}
  {small_batch_size large_batch_size : Nat}
  (h : large_batch_size % small_batch_size = 0)
  (s : MyStream small_batch_size T)
  : MyStream large_batch_size T :=
    let factor: Nat := large_batch_size / small_batch_size
    fun n =>
      let num_smaller_batches: Nat := factor * n
      let start := num_smaller_batches
      let stop := num_smaller_batches + factor
