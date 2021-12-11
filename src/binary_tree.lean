import data.tree
import utilities
import data.nat.pow

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true

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
