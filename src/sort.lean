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

variables {α : Type*} (r : α → α → Prop) [decidable_rel r]
variables x: α 
variables xs: list α  

lemma mset_insort : ((ordered_insert r x xs):multiset α ) =  {x} + ↑xs :=
begin
    induction' xs, 
  { refl },
  { simp,
    split_ifs, 
    refl, 
    simp [← multiset.cons_coe, ih], 
    }
end

lemma mset_isort: ((list.insertion_sort r xs): multiset α ) = ↑xs :=
begin
  induction' xs,
  {refl},
  { simp [mset_insort],
    simp *,
    refl
    }
end 

def list.to_set : list α → set α
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

instance list_to_set_coe (α : Type*) :
  has_coe (list α) (set α) :=
⟨list.to_set⟩

lemma set_insort:  list.to_set (ordered_insert r x xs)  = {x} ∪ list.to_set xs  :=
begin
 -- rewrite mset_insort, --how to use mset_insort like in Functional algorithms verified?
  induction' xs,
  {refl},
  simp,
  split_ifs,
  refl,
  simp [list.to_set],
  simp [ih],
  simp [insert_comm]
end






