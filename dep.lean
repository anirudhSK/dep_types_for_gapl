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
  : MyVector α (count * n) :=
    match count with
    | 0 => by simp; exact MyVector.nil
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
def MyLIStream (T : Type u) := Nat → Option (MyVector T 1)

-- We need an auxiliary function to find the next non-None time step in s, given a starting time step
noncomputable def find_next_some
  (start : Nat)
  (s : MyLIStream T)
  (h : ∀ start : Nat, ∃ pos : Nat, pos ≥ start ∧ (s pos).isSome)
  : Nat × (MyVector T 1) :=
    -- Find the next Some value starting from 'start'
    -- We use Classical.choose to extract the witness from the existence proof
    let pos := Classical.choose (h start)
    let h_pos := Classical.choose_spec (h start)
    match h_val : s pos with
    | Option.none =>
      -- This case is impossible given our hypothesis
      absurd h_val (by sorry)
    | Option.some v => (pos, v)

-- Find the nth Some value by iterating n times
noncomputable def find_nth_some
  (n : Nat) -- the stream index
  (current_pos : Nat) -- the current position in the LI stream
  (s : MyLIStream T)
  (h : ∀ start : Nat, ∃ pos : Nat, pos ≥ start ∧ (s pos).isSome)
  : MyVector T 1 :=
    match n with
    | 0 =>
        -- Find the first Some from current_pos
        let (_, v) := find_next_some current_pos s h
        v
    | n' + 1 =>
        -- Find the next Some, then continue searching
        let (next_pos, _) := find_next_some current_pos s h
        find_nth_some n' (next_pos + 1) s h

-- convert a latency-insensitive stream to a normal stream by eliminating the "no data" time steps
noncomputable def li_to_normal_stream
  {T : Type u}
  (s : MyLIStream T)
  -- Key addition: proof that for every starting position, there exists a Some value at or after it
  (h : ∀ start : Nat, ∃ pos : Nat, pos ≥ start ∧ (s pos).isSome)
  : MyStream 1 T :=
    fun n => find_nth_some n 0 s h
