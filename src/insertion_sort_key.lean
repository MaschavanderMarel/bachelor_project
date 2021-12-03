import utilities

open list
open multiset
open set
open list.perm
open nat

set_option trace.simplify.rewrite true

variables {α : Type*} {κ : Type*}
variable r: κ → κ → Prop
variable x: α 
-- variable xs: list α
variable f: α → κ     

/- 
# Insertion Sort w.r.t. Keys and Stability
-/

def insort_key [decidable_rel r] : list α → list α     
| []       := [x]
| (y :: ys) := if r (f x) (f y) then x :: y :: ys else y :: insort_key ys

def isort_key [decidable_rel r]: list α → list α
| []       := []
| (x :: xs) := insort_key r x f (isort_key xs)

#check @insort_key
#eval insort_key (λ m n: ℤ  , m <= n) 2 (λ x, x+1)  [1,3]
#check @isort_key
#eval isort_key (λ m n: ℤ, m <=n) (λ x, x*-1) [2,3,1]

/-
## Functional Correctness
 -/

-- lemma mset_insort_key: 