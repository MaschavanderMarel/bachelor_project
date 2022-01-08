import data.tree
import utilities
import data.nat.pow

set_option trace.simplify.rewrite true

open tree

variable {α : Type}
variable a: α 
variables t l r s: tree α 

/-
## Basic Functions

A binary tree is already defined in Lean as tree. 
The difference with __Functional Algorithms, Verified!__ is that a leaf is called nil, 
and the order of the node is (value, tree, tree) instead of (tree, value, tree). 
Since this does not change the structure of the proofs, the Lean definition is reused.
-/

def set_tree: tree α → set α 
| nil := {}
| (node a l r) := set_tree l ∪ {a} ∪ set_tree r

/-
map_tree is already defined in Lean as map and is reused.
-/

def inorder: tree α → list α 
| nil := []
| (node a l r) := inorder l ++ [a] ++ inorder r

/-
The name preorder is already used in lean, therefore the name preorder' is used.
-/
def preorder': tree α → list α 
| nil := []
| (node a l r) := [a] ++ preorder' l ++ preorder' r

def postorder: tree α → list α 
| nil := []
| (node a l r) := postorder l ++ postorder r ++ [a]

def size: tree α → ℕ
| nil := 0
| (node a l r) := size l + size r + 1

def size1: tree α → ℕ
| nil := 1
| (node a l r) := size1 l + size1 r

def height : tree α → ℕ
| nil := 0
| (node a l r) := max (height l) (height r) + 1

def min_height: tree α → ℕ 
| nil := 0
| (node a l r) := min (min_height l) (min_height r) + 1

def subtrees: tree α → set (tree α)
| nil := {tree.nil}
| (node a l r) := { (node a l r)} ∪ subtrees l ∪ subtrees r

/-
## Lemmas Size
Except for the first lemma, these lemmas are only in the Isabelle file
-/

lemma size1_size: size1 t = size t + 1 :=
begin
  induction' t,
  repeat { simp [size, size1, *]},
  cc
end

@[simp]
lemma size1_ge0: 0 < size1 t :=
begin
  simp [size1_size],
end

@[simp]
lemma eq_size_0 : size t = 0 ↔ t = nil :=
begin
  cases t,
  repeat { simp [size] },
end

@[simp]
lemma eq_0_size: 0 = size t ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [size, nat.add_one, ← ne.def]},
  apply ne.symm,
  simp,
end

/-
This lemma is called __neq_Leaf_iff__ in the Isabelle file.
-/
lemma neq_nil_iff: t ≠ nil ↔ ∃ a l r, t = (node a l r) :=
begin
  cases t with a l r,
  repeat { simp },
end  

/-
## Lemmas Height
Some of these lemmas are only in the Isabelle file.
-/

@[simp]
lemma eq_height_0 : height t = 0 ↔ t = nil :=
begin
  cases t,
  repeat { simp [height],},
end

@[simp]
lemma eq_0_height : 0 = height t ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [height, nat.add_one, ← ne.def]},
  apply ne.symm,
  simp,
end

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
## Lemmas set_tree
These lemmas are only in the Isabelle file.
-/

@[simp]
lemma eq_set_tree_empty : set_tree t = {} ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [set_tree, set.nonempty.ne_empty]},
end

@[simp]
lemma eq_empty_set_tree: {} = set_tree t ↔ t = nil :=
begin
  cases t with a l r,
  repeat { simp [ set_tree]},
  apply ne.symm,
  simp [set.nonempty.ne_empty],
end

@[simp]
lemma finite_set_tree : (set_tree t).finite :=
begin
  induction' t with a l r,
  repeat { simp [set_tree] },
  apply set.finite.union,
  { simp *,},
  assumption
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

lemma set_treeE: a ∈ set_tree t → ∃ l r, (node a l r) ∈ subtrees t :=
begin
  induction' t fixing * with x l r,
  repeat {simp [set_tree],},
  intro h,
  cases h,
  { cases h,
    { apply exists.intro l,
      apply exists.intro r,
      rw h,
      simp [subtrees],},
    have ih_l' : ∃ (l_1 r : tree α), node a l_1 r ∈ subtrees l, from ih_l h,
    apply exists.elim ih_l',
    intros a_1 h1,
    apply exists.elim h1,
    intros a_2 h2,
    apply exists.intro a_1,
    apply exists.intro a_2,
    simp [subtrees],
    cc, },
  have ih_r': ∃ (l r_1 : tree α), node a l r_1 ∈ subtrees r, from ih_r h,
  apply exists.elim ih_r',
  intros a_1 h1,
  apply exists.elim h1,
  intros a_2 h2,
  apply exists.intro a_1,
  apply exists.intro a_2,
  simp [subtrees],
  cc,
end

@[simp]
lemma node_notin_subtrees_if : a ∉ set_tree t → node a l r ∉ subtrees t :=
begin
  induction' t fixing *,
  { simp [set_tree, subtrees] },
  simp [set_tree],
  intro h,
  rw not_or_distrib at h,
  cases h,
  rw not_or_distrib at h_left,
  have: node a l r ∉ subtrees t_1, from ih_t_1 h_right,
  have: node a l r ∉ subtrees t, from ih_t h_left.right,
  simp [subtrees],
  cc,
end

lemma in_set_tree_if: node a l r ∈ subtrees t → a ∈ set_tree t :=
begin
  contrapose,
  exact node_notin_subtrees_if a t l r
end
