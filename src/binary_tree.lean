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

namespace btree

#check node empty a empty   

end btree

#check node a nil nil

def height : tree α → ℕ
| nil := 0
| (node a l r) := max (height l) (height r) + 1

def min_height: tree α → ℕ 
| nil := 0
| (node a l r) := min (min_height l) (min_height r) + 1

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
  have h_4: min_height r <= height r, from min_height_le_height r,
  have h_3: min_height l <= height l, from min_height_le_height l,
  split_ifs,
  { apply iff.intro,
    { cc },
    intro h2,
    apply and.intro,
    { have h5: height l <= min_height r, from eq.subst h2 h,
      have h6: height l <= height r, from trans h5 h_4,
      exact le_antisymm h6 h_1, },
    apply and.intro,
    { assumption },
    have h3: height r <= min_height l, from eq.subst h2.symm h_1,
    have h4: height r <= min_height r, from trans h3 h,
    exact le_antisymm h_4 h4 },
  { apply iff.intro,
    repeat { cc} },
  { apply iff.intro,
    repeat { cc } },
  apply iff.intro,
  { cc},
  intro h2,
  apply and.intro,
  { have h3: min_height r <= min_height l, from le_of_not_le h,
    have h4: height r <= min_height l, from eq.subst h2 h3,
    have h5: height r <= height l, from le_trans h4 h_3,
    cc },
  apply and.intro,
  { have h3: ¬ min_height l <= height r, from eq.subst h2 h,
    have h4: height r >= height l, from le_of_not_le h_1 ,
    have h5: min_height l >= height r, from le_of_not_le h3,
    have h6: min_height l >= height l, from ge_trans h5 h4,
    exact le_antisymm h_3 h6 },
  exact h2
end