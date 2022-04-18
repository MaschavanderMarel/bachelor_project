import utilities

open list
open multiset
open set
open nat

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variable x: α 
variable xs: list α  

/- 
# Insertion sort

The two functions insort and isort from __Functional Algorithms, Verified!__ are defined in Lean 
as ordered_insert and insertion_sort respectively and are reused.

## Functional Correctness
 -/

lemma mset_insort [decidable_rel r] : (ordered_insert r x xs: multiset α) = {x} + ↑xs :=
begin
  induction' xs, 
  { refl },
  { simp,
    split_ifs, 
      refl, 
      simp [← multiset.cons_coe, ih] }
end

lemma mset_isort [decidable_rel r] : (insertion_sort r xs: multiset α) = ↑xs :=
begin
  induction' xs,
  { refl },
  { simp [mset_insort, ih],
    refl }
end 

lemma set_insort [decidable_rel r] : (ordered_insert r x xs).to_set  = {x} ∪ xs.to_set  :=
begin
  simp [set.insert_def, ← set_mset_mset, mset_insort, multiset.to_set],
end

lemma sorted_insort [decidable_rel r] [is_linear_order α r] : sorted' r (ordered_insert r x xs) = sorted' r xs :=
begin
  -- By using fixing the trans and total_of functions work without writing the is_total and is_trans instances explicitly.
  induction' xs fixing *, 
  { simp [sorted'],
    intros,
    exact false.elim H },
  { simp only [ordered_insert],
    split_ifs,
    { simp [sorted', list.to_set],
      intros h1 h2,
      apply and.intro h,
      intros y h3, 
      have h4: y ∈ xs.to_set → r hd y, from h1 y,
      have h5: r hd y, from h4 h3,
      exact trans h h5 }, 
    { simp [sorted', list.to_set, ih, set_insort],
      intros h1 h2,
      exact or.resolve_right (total_of r hd x) h } }
end

lemma sorted_isort [decidable_rel r] [is_linear_order α r]: sorted' r (insertion_sort r xs) :=
begin
  induction' xs,
  repeat { simp [sorted_insort, *] }
end

/- 
## Time Complexity
We count the number of function calls.
 -/

def T_insort [decidable_rel r] : α → list α → nat 
| x [] := 1
| x (y::ys) := if  r x y  then 0 else T_insort x ys + 1 

def T_isort [decidable_rel r] : list α → nat 
| [] := 1
| (x::xs) := T_isort xs + T_insort r x (insertion_sort r xs) + 1

lemma T_insort_length [decidable_rel r]: T_insort r x xs <= xs.length + 1 :=
begin
  induction' xs,
  repeat { simp [T_insort] },
  split_ifs,
  repeat { simp *},
end

lemma length_insort [decidable_rel r] : (ordered_insert r x xs).length = xs.length + 1 :=
begin
  induction' xs,
  repeat { simp [ordered_insert] },
  split_ifs,
  repeat { simp *},
end

lemma length_isort [decidable_rel r] : (insertion_sort r xs).length = xs.length :=
begin
  induction' xs,
  repeat { simp [length_insort, *] }
end

/-
Lemma 2.1 from __Functional Algorithms, Verified!__
-/
lemma T_isort_length [decidable_rel r]: T_isort r xs <= (xs.length + 1) ^ 2 :=
begin
  induction' xs fixing *,
  repeat { simp [T_isort, T_insort_length, length_isort ]},
  show T_isort r xs + T_insort r hd (insertion_sort r xs) + 1 ≤ (xs.length + 1 + 1) ^ 2, by calc
  T_isort r xs + T_insort r hd (insertion_sort r xs) + 1 ≤ (xs.length + 1) ^ 2 + T_insort r hd (insertion_sort r xs) + 1 : by simp [ih]
  ... ≤ (xs.length + 1) ^ 2 + ((insertion_sort r xs).length + 1) + 1 : by simp [T_insort_length]
  ... = (xs.length + 1) ^ 2 + (xs.length + 1) + 1 : by simp [length_isort]
  ... = xs.length ^2 + 2 * xs.length + xs.length + 3 : by ring
  ... ≤ xs.length ^2 + 2 * xs.length + xs.length + xs.length + 3 : by simp 
  ... ≤ xs.length ^2 + 2 * xs.length + xs.length + xs.length + 4 : by simp 
  ... = (xs.length + 1 + 1) ^ 2 : by ring,
end
