import utilities

open list
open nat

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variable x: α 
variable xs: list α  

/- 
# Quicksort

The qsort from the library is *not* really quicksort since it doesn't partition the elements in-place.
Therefore quicksort is defined below following the definition from Functional Algorithms Verified!.
 -/

lemma well_founded_qs [decidable_rel r]:  (list.filter (λ (y), r y x) xs).sizeof < 1 + xs.sizeof :=
  begin
    induction xs,
    { simp},
    simp [list.filter],
    split_ifs,
    {   simp [list.sizeof],
        linarith },
    simp [list.sizeof],
    linarith
  end

lemma well_founded_qs' [decidable_rel r]: (list.filter (λ (y),¬ r y x) xs).sizeof < 1 + xs.sizeof :=
begin
    induction xs,
    {   simp},
    simp [list.filter],
    split_ifs,
    {   simp [list.sizeof],
        linarith },
    simp [list.sizeof],
    linarith,
end

def quicksort [decidable_rel r]: list α → list α     
| [] := []
| (x::xs) :=  
  have (list.filter (λ (y), r y x) xs).sizeof < 1 + xs.sizeof, by apply well_founded_qs,
  have (list.filter (λ (y : α), ¬r y x) xs).sizeof < 1 + xs.sizeof, by apply well_founded_qs',
  quicksort (xs.filter (λ y: α, r y x)) ++ [x] ++ quicksort (xs.filter (λ y: α  , ¬ r y x))   

/-
## Functional Correctness
-/

lemma mset_quicksort [decidable_rel r]: 
  ∀ xs: list α,  (↑(quicksort r xs): multiset α)  = (↑xs: multiset α )
| [] := by simp only [quicksort]
| (x::xs) :=  
begin
  rw quicksort,
  repeat {rw ← multiset.coe_add} ,
  have h1: (list.filter (λ (y), r y x) xs).sizeof < 1 + xs.sizeof ∧ (list.filter (λ (y),¬ r y x) xs).sizeof < 1 + xs.sizeof , from begin
    apply and.intro,
    { apply well_founded_qs},
    apply well_founded_qs',
  end,
  cases h1,
  simp only [mset_quicksort (filter (λ (y : α), r y x) xs), mset_quicksort (filter (λ (y : α), ¬ r y x) xs), ← multiset.coe_filter, add_comm, add_assoc, multiset.filter_add_not],
  simp,
end

#check mset_quicksort

lemma set_quicksort [decidable_rel r]: (quicksort r xs).to_set = xs.to_set :=
begin
  simp [← set_mset_mset, mset_quicksort],
end

lemma sorted_quicksort [decidable_rel r] [is_trans α r] [is_total α r] : 
  ∀ xs, sorted' r (quicksort r xs)
| [] := by simp [quicksort]
| (x::xs) := 
begin
  rw quicksort,
  simp [sorted'_append],
  have h1: (list.filter (λ (y), r y x) xs).sizeof < 1 + xs.sizeof ∧ (list.filter (λ (y),¬ r y x) xs).sizeof < 1 + xs.sizeof , from begin
    apply and.intro,
    { apply well_founded_qs},
    apply well_founded_qs',
  end,
  cases h1,
  apply and.intro,
  { simp only [sorted_quicksort (filter (λ (y : α), r y x) xs)],},
  apply and.intro,
  { simp [sorted'],
    apply and.intro,
    { simp [set_quicksort],
      intros,
      simp [← set_mset_mset, multiset.to_set] at H,
      exact or.resolve_right (total_of r x y) H.right},
    simp only [sorted_quicksort (filter (λ (y : α), ¬ r y x) xs)]},
  intros,
  have h1: x_1 ∈ (↑(quicksort r (filter (λ (y : α), r y x) xs)): multiset α ), by simp [H],
  have h3: x_1 ∈ (↑ (filter (λ (y : α), r y x) xs): multiset α), from eq.subst (mset_quicksort r (filter (λ y, r y x) xs)) h1,
  simp at h3,
  apply and.intro,
  { exact h3.right},
  intros a h1,
  have h2: a ∈ (↑(quicksort r (filter (λ y, ¬ r y x) xs)): multiset α ), by simp [h1],
  have h5: a ∈ (↑ (filter (λ y, ¬ r y x) xs): multiset α), from eq.subst (mset_quicksort r (filter (λ y, ¬ r y x) xs)) h2,
  simp at h5,
  have h4: r x a , from or.resolve_left (total_of r a x) h5.right,
  exact trans h3.right h4,
end

/- 
## Time Complexity
Like in Functional Algorithms Verified the running time is not analyzed, 
because it is well known that it is quadratic in the worst case but sort of O(n lg n) on average. 
 -/
