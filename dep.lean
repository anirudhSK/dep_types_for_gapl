import Init.Data.Vector
import Init.Data.Vector.Basic

abbrev MyVector (α : Type u) (n : Nat) := Vector α n

def vnil : MyVector α 0 :=
  (Array.toVector (#[] : Array α ))

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
  Vector.append v1 v2

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
  : MyVector α (count * n) :=
    match count with
    | 0 => by
       let mul_zero : 0 * n = 0 := by
          exact Nat.zero_mul n
       rw [mul_zero];
       exact vnil
    | count'+1 =>
        let first_batch: MyVector α n := vecs start
        let tail_batches: MyVector α (count' * n) :=
          MyVector.concat_many (start + 1) count' vecs
        let result: MyVector α (count' * n + n) :=
          by simp [Nat.add_comm]; exact
          MyVector.concat first_batch tail_batches
        let h: (count'+1) * n = count' * n + n :=
          by simp [Nat.mul_succ,Nat.mul_comm]
        by rw [h]; exact result

def MyVector.singleton
  {α : Type u}
  (x : α)
  : MyVector α 1 :=
    Vector.singleton x

-- map function over MyVector
def MyVector.map
  {α β : Type u}
  {n : Nat}
  (v : MyVector α n)
  (f : α → β)
  : MyVector β n :=
    Vector.map f v

def MyVector.foldl
  {α β : Type u}
  {n : Nat}
  (v : MyVector α n)
  (current_state : β)
  (f : β → α → β)
  : β :=
    Vector.foldl f current_state v

#check MyVector

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
  (h : small_batch_size ∣ large_batch_size)
  (s : MyStream small_batch_size T)
  : MyStream large_batch_size T :=
    let factor: Nat := large_batch_size / small_batch_size
    let hh: large_batch_size = factor * small_batch_size :=
      by rw [Nat.mul_comm, Nat.mul_div_cancel']; exact h
    fun n =>
      let start := factor * n
      by rw [hh]; exact MyVector.concat_many start factor s

  -- a latency-insensitive stream: a stream that might produce "no data" at some time steps
def MyLIStream (T : Type u) (batch_size : Nat) := Nat → Option (MyVector T batch_size)

-- define a function to go from a MyLIStream to a MyStream
-- that fills in missing data with the last available data
def current
  {T}
  {batch_size : Nat}
  (li_s : MyLIStream T batch_size)
  (default_batch : MyVector T batch_size)
  : MyStream batch_size T :=
    -- helper function to keep track of last available batch
    let rec helper
      (n : Nat)
      (last_batch : MyVector T batch_size)
      : MyVector T batch_size :=
        match li_s n with
        | some batch => batch
        | none => last_batch -- "holds" the last available batch
    -- a stream is a function from nat to something, so define this function
    fun n =>
      -- for the first element, if none, use default
      if n = 0 then
        match li_s 0 with
        | some batch => batch
        | none => default_batch
      -- for subsequent elements, use helper
      else
        helper n (current li_s default_batch (n - 1))
