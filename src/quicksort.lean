import utilities

open list
open multiset
open set
open list.perm
open nat

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variable x: α 
variable xs: list α  

/- 
# Quicksort
 -/

def quicksort : list ℕ  → list ℕ    
| [] := []
| (x::xs) :=  
    have (list.filter (λ (y : ℕ), y < x) xs).sizeof < 1 + x + xs.sizeof, from sorry,
    have (list.filter (has_le.le x) xs).sizeof < 1 + x + xs.sizeof, from sorry,
    quicksort (xs.filter (λ y: ℕ, y < x)) ++ [x] ++ quicksort (xs.filter (λ y: ℕ , y ≥ x))   


#eval quicksort [3,2,1]
-- quicksort is defined in library
#eval list.qsort (λ m n: ℕ , m < n) [2,1]
