import data.tree
import utilities
import data.nat.pow

set_option trace.simplify.rewrite true

open tree

variable {α : Type}
variable a: α 
variables t l r s: tree α 

/-
## Definitions

A binary tree is already defined in Lean as tree. 
The difference with __Functional Algorithms, Verified!__ is that a leaf is called nil, 
and the order of the node is (value, tree, tree) instead of (tree, value, tree). 
Since this does not change the structure of the proofs, the Lean definition is reused.
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

def subtrees: tree α → set (tree α)
| nil := {tree.nil}
| (node a l r) := { (node a l r)} ∪ subtrees l ∪ subtrees r

#check subtrees (node 1 (node 2 nil nil) nil)

/-
## Lemmas Size
-/

lemma size1_size: size1 t = size t + 1 :=
begin
  induction' t,
  repeat { simp [size, size1, *]},
  cc
end

/- Only in Isabelle file -/
@[simp]
lemma size1_ge0: 0 < size1 t :=
begin
  simp [size1_size],
end

/- Only in Isabelle file -/
@[simp]
lemma eq_size_0 : size t = 0 ↔ t = nil :=
begin
  cases t,
  repeat { simp [size] },
end

/- Only in Isabelle file -/
@[simp]
lemma eq_0_size: 0 = size t ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [size, nat.add_one, ← ne.def]},
  apply ne.symm,
  simp,
end

/- Only in Isabelle file -/
lemma neq_nil_iff: t ≠ nil ↔ ∃ a l r, t = (node a l r) :=
begin
  cases t with a l r,
  repeat { simp },
end  

/-
## Lemmas Height
-/

/- Only in Isabelle file -/
@[simp]
lemma eq_height_0 : height t = 0 ↔ t = nil :=
begin
  cases t,
  repeat { simp [height],},
end

/- Only in Isabelle file -/
@[simp]
lemma eq_0_height : 0 = height t ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [height, nat.add_one, ← ne.def]},
  apply ne.symm,
  simp,
end

/- Only in Isabelle file -/
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

/- Only in Isabelle file -/
lemma size_height: size t <= 2 ^ height t - 1 :=
begin
  have h: size1 t <= 2 ^ height t, from size1_height t,
  have h1: size1 t = size t + 1, from size1_size t,
  rw h1 at h,
  have h2: 1 <= 2 ^ height t, from nat.one_le_two_pow (height t),
  have h3:size t + 1 ≤ 2 ^ height t ↔ size t ≤ 2 ^ height t - 1, from nat.add_le_to_le_sub (size t) h2,
  exact iff.elim_left h3 h,
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

/-
## Lemmas Subtrees
These lemmas are only in the Isabelle file.
-/

@[simp]
lemma neq_subtrees_empty : subtrees t ≠ {} :=
begin
  cases t with a l r,
  repeat { simp [subtrees, set.nonempty.ne_empty] },
end

@[simp]
lemma neg_empty_subtrees : {} ≠ subtrees t :=
begin
  apply ne.symm,
  cases t,
  repeat { simp [subtrees, set.nonempty.ne_empty] },
end

lemma size_subtrees: s ∈ subtrees t → size s <= size t :=
begin
  induction' t with a l r,
  repeat { simp [subtrees, size] },
  intro h,
  cases h,
  { cases h,
    { calc
        size s = size l + size r + 1 : by simp [*, size]
        ... ≤ size l + size r + 1: by ring},
    calc 
      size s <= size l: by simp *
      ... ≤ size l + size r + 1: by linarith,},
  calc 
  size s <= size r: by simp *
  ... ≤ size l + size r + 1: by linarith,
end

#reduce ({1}: set ℕ)
#reduce ({nil}: set (tree α )).nonempty
#check ({nil}: set (tree α )).nonempty

#check node 1 nil nil