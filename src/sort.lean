import data.list.sort
import data.multiset
import data.set
import tactic.induction
import tactic.ring

open list
open multiset
open set

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variable x: α 
variable xs: list α  

def list.to_set : list α → set α --Source: chapter 10.6 Theorem Proving in Lean.
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

-- This is predefined in Functional Algorithms Verified.
def multiset.to_set: multiset α → set α :=  
λ m: multiset α, {x: α | x ∈ m }

-- This definition follows the definition in Functional Algorithms Verified instead of using the predefined function sort in Lean.
def sorted' [is_total α r] [is_trans α r] : list α → Prop 
| [] := true
| (h::t) := (∀ y ∈ t.to_set, r h y ) ∧ sorted' t

/- 
# Insertion sort
 -/

section Insertion_sort

/- The two functions insort and isort from Functional Algorithms Verified are already defined in Lean as ordered_insert and insertion_sort respectively.
 -/

/- ## Functional Correctness
 -/

lemma mset_insort [decidable_rel r] : ((ordered_insert r x xs):multiset α ) =  {x} + ↑xs :=
begin
  induction' xs, 
  { refl },
  { simp,
    split_ifs, 
      refl, 
      simp [← multiset.cons_coe, ih] }
end

lemma mset_isort [decidable_rel r]: (↑ (list.insertion_sort r xs): multiset α ) = ↑xs :=
begin
  induction' xs,
  { refl },
  { simp [mset_insort, ih],
    refl }
end 

-- This lemma is predefined in the multiset file of Isabelle and used to prove lemma set_insort.
lemma set_mset_mset: multiset.to_set ↑xs = list.to_set xs := 
begin
  induction' xs,
  { refl},
  { simp [list.to_set,← ih, multiset.to_set, set.insert_def] }
end 

lemma set_insort [decidable_rel r]:  (ordered_insert r x xs).to_set  = {x} ∪ xs.to_set  :=
begin
  simp [set.insert_def, ← set_mset_mset, mset_insort, multiset.to_set],
end

lemma sorted_insort [decidable_rel r] [is_total α r] [is_trans α r] : sorted' r (ordered_insert r x xs) = sorted' r xs :=
begin
  induction' xs fixing *, -- by using fixing the trans and total_of functions will work without mentioning the instances explicitly
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
      have h3: r hd x ∨ r x hd, from total_of r hd x, 
      exact or.resolve_right h3 h } }
end

lemma sorted_isort [decidable_rel r] [is_trans α r] [is_total α r]: sorted' r (insertion_sort r xs) :=
begin
  induction' xs,
  { simp},
  { simp [sorted_insort, ih] }
end

/- ## Time Complexity
   We count the number of function calls
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
  { simp [T_insort] },
  { simp [T_insort],
    split_ifs,
    { simp},
    { simp [ih] } }
end

lemma length_insort [decidable_rel r] : (ordered_insert r x xs).length = xs.length + 1 :=
begin
  induction' xs,
  { simp [ordered_insert] },
  { simp,
    split_ifs,
    { simp},
    { simp [ih] } }
end

lemma length_isort [decidable_rel r] : (insertion_sort r xs).length = xs.length :=
begin
  induction' xs,
  { simp},
  { simp [length_insort, ih] }
end

lemma T_isort_length [decidable_rel r]: T_isort r xs <= (xs.length + 1) ^ 2 :=
begin
  induction' xs fixing *,
  { simp [T_isort]},
  { simp [T_isort, T_insort_length, length_isort],
    show T_isort r xs + T_insort r hd (insertion_sort r xs) + 1 ≤ (xs.length + 1 + 1) ^ 2, by calc
    T_isort r xs + T_insort r hd (insertion_sort r xs) + 1 ≤ (xs.length + 1) ^ 2 + T_insort r hd (insertion_sort r xs) + 1 : by simp [ih]
    ... ≤ (xs.length + 1) ^ 2 + ((insertion_sort r xs).length + 1) + 1 : by simp [T_insort_length]
    ... = (xs.length + 1) ^ 2 + (xs.length + 1) + 1 : by simp [length_isort]
    ... = xs.length ^2 + 2 * xs.length + xs.length + 3 : by ring
    ... ≤ xs.length ^2 + 2 * xs.length + xs.length + xs.length + 3 : by simp 
    ... ≤ xs.length ^2 + 2 * xs.length + xs.length + xs.length + 4 : by simp 
    ... = (xs.length + 1 + 1) ^ 2 : by ring,
    }
end

end Insertion_sort

/- 
# Quicksort
 -/

section Quicksort

def quicksort : list ℕ  → list ℕ    
| [] := []
| (x::xs) :=  have (list.filter (λ (y : ℕ), y < x) xs).sizeof < 1 + x + xs.sizeof, from sorry,
              have (list.filter (has_le.le x) xs).sizeof < 1 + x + xs.sizeof, from sorry,
              quicksort (xs.filter (λ y: ℕ  , y < x)) ++ [x] ++ quicksort (xs.filter (λ y: ℕ , y ≥ x))   

end Quicksort

#eval quicksort [3,2,1]
-- quicksort is defined in library
#eval list.qsort (λ m n: ℕ , m < n) [2,1]

/- 
# Top-Down Merge Sort
-/

#eval merge (λ m n: ℕ, m < n) [1,3] [2,4]
#eval merge_sort (λ m n: ℕ , m < n) [2,1,4,3]

/- The function merge in Functional Algoriths Verified! is already defined in Lean as merge. The function msort is defined but in a slightly different way. Therefore, it is defined below in the same way, so the proof structure of the book can be followed. -/

variables ys: list α 

def msort: list α → list α :=
sorry

/- 
## Functional Correctness
 -/

lemma mset_merge [d: decidable_rel r]: (↑ (merge r xs ys): multiset α)  = ↑ xs + ↑ ys :=
begin
  simp,
  induction' xs,
  { induction' ys,
    { simp [merge]},
    simp [merge] },
  induction' ys,
  { simp [merge] },
  simp [merge],
  split_ifs,
  { simp [ih] },
  simp [← list.cons_append] ,
  simp only [list.perm_cons_append_cons hd_1 (@ih_ys _ _ _ _ ih)],
end  

lemma set_merge [decidable_rel r]: (merge r xs ys).to_set = xs.to_set ∪ ys.to_set :=
begin
  simp [← set_mset_mset, mset_merge, multiset.to_set],
  refl
end

lemma mset_msort [decidable_rel r]: (↑ (merge_sort r xs):multiset α) = ↑ xs :=
begin
  simp [perm_merge_sort],
end

lemma sorted_merge [d: decidable_rel r] [t: is_total α r] [tr: is_trans α r]: 
  sorted' r (merge r xs ys) ↔ sorted' r xs ∧ sorted' r ys :=
begin
   induction' xs,
  { induction' ys,
      simp [merge],
    { simp [merge, sorted'] }},
  { induction' ys fixing *, 
    { simp [merge, sorted'] },
    { simp [merge],
      split_ifs,
      { simp [sorted', set_merge, ih, list.to_set],
        apply iff.intro,
        { intros h,
          apply and.intro,
          { apply and.intro,
            { intros,
              have h2: ∀ (a : α), a ∈ xs.to_set ∨ a ∈ ys.to_set → r hd a, from h.left.right,
              exact (h2 y) (or.inl H)},
            have h1: sorted' r xs ∧ (∀ (y : α), y ∈ ys.to_set → r hd_1 y) ∧ sorted' r ys, from h.right,
            exact h1.left},
          apply and.intro,
          { intros,
            have h3: (∀ (y : α), y ∈ ys.to_set → r hd_1 y), from h.right.right.left,
            exact h3 y H},
          exact h.right.right.right},
        intros h1,
        apply and.intro,
        { apply and.intro,
          { exact h},
          intros a h3,
          have h4: a ∈ xs.to_set → r hd a, from h1.left.left a,
          apply or.elim h3,
          { exact h4},
          intro h6,
          have h7: (∀ (y : α), y ∈ ys.to_set → r hd_1 y), from h1.right.left,
          have h8: r hd_1 a, from h7 a h6,
          exact trans h h8},
        apply and.intro,
        { exact h1.left.right},
        exact h1.right},
      { simp [sorted', set_merge, ih_ys, list.to_set, sorted'],
        apply iff.intro,
        { simp,
          intros h1 h2 h3 h4,
          apply and.intro,
          { exact and.intro h2 h3},
          apply and.intro,
          { intros,
            exact h1 y (or.inr H)},
          exact h4},
        simp,
        intros h1 h2 h3 h4,
        apply and.intro,
        { intros,
          apply or.elim H,
          { intro h5,
            apply or.elim h5,
            { intro h6,
              have h7: r hd_1 y ∨ r y hd_1, from total_of r hd_1 y,
              have h8: ¬ r y hd_1, from eq.subst h6.symm h,
              apply or.resolve_right h7 h8, },
            intro h6,
            have h7: r hd y, from h1 y h6,
            have h8: r hd_1 hd ∨ r hd hd_1, from total_of r hd_1 hd,
            have h9: r hd_1 hd, from or.resolve_right h8 h,
            exact trans h9 h7 },
          exact h3 y},
        exact and.intro (and.intro h1 h2) h4 } } } 

end


#check @total_of

#eval merge_sort (λ m n : ℕ, m ≤ n) [23,1, 12]
#eval merge_sort (λ m n : ℕ, m ≤ n) (30 ::15::[23,12])
