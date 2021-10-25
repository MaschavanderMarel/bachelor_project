import data.list.sort
import data.multiset
import data.set
import data.finset
import tactic.induction

open list
open multiset
open set
open finset

set_option trace.simplify.rewrite true

variables {α : Type*} (r : ℕ  → ℕ  → Prop) [decidable_rel r]
variables x: ℕ   
variables xs: list ℕ   

lemma mset_insort : ((ordered_insert r x xs): multiset ℕ  ) =  {x} + ↑xs :=
begin
    induction' xs, 
  { refl },
  { simp,
    split_ifs, 
    refl, 
    simp [← multiset.cons_coe],
    simp [ih], 
    }
end

lemma mset_isort: ((list.insertion_sort r xs): multiset ℕ  ) = ↑xs :=
begin
  induction' xs,
  {refl},
  { simp [mset_insort],
    simp *,
    refl,
    }
end 

def list.to_set : list ℕ  → set ℕ --does this definition need to be proved?
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

instance list_to_set_coe (α : Type*) : --what is this instance used for?
  has_coe (list ℕ ) (set ℕ ) :=
⟨list.to_set⟩

lemma set_insort:  list.to_set (ordered_insert r x xs)  = {x} ∪ list.to_set xs  :=
begin
 -- rewrite mset_insort, --how to use mset_insort?
  induction' xs,
  {refl},
  simp,
  split_ifs,
  refl,
  simp [list.to_set],
  simp [ih],
  simp [insert_comm]
end





