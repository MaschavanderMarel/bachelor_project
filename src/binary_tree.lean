import data.tree
import utilities
import data.nat.pow

set_option trace.simplify.rewrite true

open tree

variable {α : Type}
variable a: α 
variable t: tree α 

/-
## Definitions
-/

def height : tree α → ℕ
| nil := 0
| (node a l r) := max (height l) (height r) + 1

def min_height: tree α → ℕ 
| nil := 0
| (node a l r) := min (min_height l) (min_height r) + 1

def size: tree α → ℕ
| nil := 0
| (node a l r) := size l + size r + 1

def size1: tree α → ℕ
| nil := 1
| (node a l r) := size1 l + size1 r


/-
## Lemmas size
-/

lemma size1_size: size1 t = size t + 1 :=
begin
  induction' t,
  repeat { simp [size, size1, *]},
  cc
end

/-
## Lemmas height
-/

/-
Only in Isabelle file
-/
@[simp]
lemma eq_height_0 : height t = 0 ↔ t = nil :=
begin
  cases t,
  repeat { simp [height],},
end

/-
Only in Isabelle file
-/
@[simp]
lemma eq_0_height : 0 = height t ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [height, nat.add_one]},
  have: 0 < (max (height l) (height r)).succ, from nat.succ_pos (max (height l) (height r)),
  linarith
end

/-
Only in Isabelle file
-/
@[simp]
lemma height_le_size_tree: height t <= size t :=
begin
  induction' t,
  repeat { simp [height, size] },
  apply and.intro,
  { calc
      height t <= size t : by simp * 
      ... ≤ size t + size t_1 :by simp},
  calc
    height t_1 <= size t_1: by simp * 
    ... ≤ size t + size t_1 : by simp
end

lemma min_height_le_height : min_height t <= height t:=
begin
  induction' t,
  repeat { simp [height, min_height, *]}
end

lemma size1_height: size1 t <= 2 ^ height t :=
begin
  have h2: 2 <= 2, by trivial,
  induction' t with a l r,
  repeat { simp [size1, height, max_def] },
  split_ifs,
  { have h3: 2 ^ height r <= 2 ^height l, from iff.elim_right (nat.pow_le_iff_le_right h2) h,
    calc
      size1 l + size1 r <= 2 ^ height l + size1 r : by simp *
      ... <= 2 ^ height l + 2 ^ height r  : by simp *
      ... <= 2 ^ height l + 2 ^ height l  : by simp *
      ... = 2 ^ (height l + 1) : by ring },
  have h1: height l <= height r, by linarith, 
  have h3: 2 ^ height l <= 2 ^height r, by apply iff.elim_right (nat.pow_le_iff_le_right h2) h1,
  calc
    size1 l + size1 r <= 2 ^ height l + size1 r: by simp *
    ... <= 2 ^ height l + 2 ^ height r : by simp *
    ... <= 2 ^ height r + 2 ^ height r : by simp *
    ... = 2 ^ (height r + 1) : by ring
end

/-
Only in Isabelle file
-/
lemma size_height: size t <= 2 ^ height t - 1 :=
begin
  have h: size1 t <= 2 ^ height t, from size1_height t,
  have h1: size1 t = size t + 1, from size1_size t,
  rw h1 at h,
  have h2: 1 <= 2 ^ height t, from nat.one_le_two_pow (height t),
  have h3:size t + 1 ≤ 2 ^ height t ↔ size t ≤ 2 ^ height t - 1, from nat.add_le_to_le_sub (size t) h2,
  exact iff.elim_left h3 h,
end

#check @tsub_le_iff_right

lemma min_height_size1: 2 ^ min_height t <= size1 t :=
begin
  have h2: 2 <= 2, by trivial,
  induction' t with a l r,
  repeat { simp [min_height, size1, min_def] },
  split_ifs,
  { have h3: 2 ^ min_height l <= 2 ^ min_height r, from iff.elim_right (nat.pow_le_iff_le_right h2) h,
    calc
      2 ^ (min_height l + 1) = 2 ^ min_height l + 2 ^ min_height l : by ring
      ... <= 2 ^ min_height l + 2 ^ min_height r : by simp *
      ... <= size1 l + 2 ^ min_height r: by simp *
      ... <= size1 l + size1 r : by simp * },
  have h1: min_height r <= min_height l, by linarith, 
  have h3: 2 ^ min_height r <= 2 ^ min_height l, from iff.elim_right (nat.pow_le_iff_le_right h2) h1,
    calc
      2 ^ (min_height r + 1) = 2 ^ min_height r + 2 ^ min_height r : by ring
      ... <= 2 ^ min_height l + 2 ^ min_height r : by simp *
      ... <= 2 ^ min_height l + size1 r: by simp *
      ... <= size1 l + size1 r : by simp *
end

