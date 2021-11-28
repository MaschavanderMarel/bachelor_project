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

lemma well_founded_qs' [decidable_rel r]:  (list.filter (λ (y),¬ r y x) xs).sizeof < 1 + xs.sizeof :=
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

#eval list.sizeof [1,1] 
#eval sizeof 3

#eval list.filter (λ x: ℕ , x > 1) [2,3,1]
#check (λ x y: ℕ , x > y)
#eval quicksort (λ n m :ℕ , ¬ n < m) [3,2,1]
-- quicksort is defined in library
#eval list.qsort (λ m n: ℕ , m > n) [2,1]
