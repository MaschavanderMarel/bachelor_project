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

The qsort from the library is *not* really quicksort since it doesn't partition the elements in-place.calc
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
  ∀ xs: list α,  ((quicksort r xs): multiset α)  = (↑xs: multiset α )
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



#check @well_founded_qs
#eval ({1,1,2}:multiset ℕ ) + {2,3}
#eval list.qsort (λ m n: ℕ , m > n) [2,1]
