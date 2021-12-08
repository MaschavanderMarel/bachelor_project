import data.tree
import utilities

set_option trace.simplify.rewrite true

open tree

variable {α : Type}
variable a: α 
variable t: tree α 

inductive btree (α : Type) : Type
| empty {} : btree
| node     : btree → α  → btree → btree

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

lemma size1_size: size1 t = size t + 1 :=
begin
  induction' t,
  repeat { simp [size, size1, *]},
  cc
end

lemma min_height_le_height : min_height t <= height t:=
begin
  induction' t,
  repeat { simp [height, min_height, *]}
end

#reduce min_height (node a nil (node a nil nil))
#reduce height nil

def complete : tree α → Prop
| nil := true
| (node a l r ) := height l = height r ∧ complete l ∧ complete r

#reduce complete (node a nil (node a nil nil))

lemma complete_iff_height: complete t ↔ min_height t = height t :=
begin
  induction t with a l r l_ih r_ih,
  { simp [complete, min_height, height] },
  simp [complete, min_height, height, min_def, max_def, *],
  have: min_height r <= height r, from min_height_le_height r,
  have: min_height l <= height l, from min_height_le_height l,
  split_ifs,
  { apply iff.intro,
    { cc },
    intro h2,
    apply and.intro,
    repeat { linarith },
    apply and.intro,
    repeat { linarith } },
  { apply iff.intro,
    repeat { cc} },
  { apply iff.intro,
    repeat { cc } },
  apply iff.intro,
  { cc},
  intro h2,
  repeat { linarith },
end

lemma size1_if_complete : complete t → size1 t = 2 ^height t :=
begin
  induction t with a l r l_ih r_ih,
  { simp [complete, height, size1] },
  simp [complete, height, size1 ],
  intros,
  simp *,
  ring,
end

lemma size_if_complete: complete t → size t = (2 ^ height t) - 1 :=
begin
 intro,
 calc
  size t = size1 t - 1 : by simp [size1_size] 
  ... = 2 ^ height t - 1: by simp [*, size1_if_complete]
end