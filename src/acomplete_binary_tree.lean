import complete_binary_tree


set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true

open tree

variable {α : Type}
variable a: α 
variables s t: tree α 

/-
# Almost Complete Binary Trees

## Definition
-/

def acomplete : tree α → Prop
| t := height t - min_height t <= 1

#check @acomplete 

/-
Lemma 4.6 from __Functional Algorithms, Verified!__
-/
lemma acomplete_optimal :acomplete s ∧ size s <= size t → height s <= height t :=
begin
  intro h1,
  have h2: 2 <= 2, by trivial,
  by_cases complete s,
  { have h3: 2 ^ height s <= 2 ^height t, from calc
      2 ^ height s = size1 s : by simp [size1_if_complete s, *] 
      ... <= size1 t : by simp [*, size1_size]
      ... <= 2 ^height t : by simp [size1_height],
    simp [iff.elim_left (nat.pow_le_iff_le_right h2) h3] },
  have h3: 2 ^ min_height s < 2 ^ height t, from calc
    2 ^ min_height s < size1 s : by simp [min_height_size1_if_incomplete s, *] 
    ... <= size1 t : by simp [*, size1_size]
    ... <= 2 ^ height t: by simp [size1_height],
  have: min_height s < height t, from iff.elim_left (nat.pow_lt_iff_lt_right h2) h3,
  rw acomplete at h1,
  have: height s - min_height s ≤ 1 , from h1.left,
  have: ¬ min_height s = height s, from iff.elim_left (iff_false_left h) (complete_iff_height s), 
  have: min_height s <= height s, from min_height_le_height s,
  have: min_height s < height s, by simp [has_le.le.lt_of_ne, *],
  have: 0 < height s - min_height s, by simp [*, nat.sub_pos_of_lt],
  have: height s - min_height s = 1, by linarith,
  have: min_height s + 1 = height s, by linarith,
  linarith,
end
