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

-- @[derive decidable_rel]
-- def r (m n : ℕ):  Prop := 
-- m ≤  n

universe variable uu
variables {α : Type uu} (r : α → α → Prop) [decidable_rel r]
variables x: α 
variables xs: list α  


lemma mset_insort : ((ordered_insert r x xs):multiset α ) =  {x} + ↑xs :=
begin
    induction' xs, 
  { refl },
  { simp,
    split_ifs, 
    refl, 
    simp [← multiset.cons_coe, *], 
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

def list_to_multiset_wo_dup (l: list α): multiset α :=
multiset.erase_dup l   

def multiset_to_finset (m: multiset ℕ ) (h: m.nodup) : finset ℕ :=
{val := m , nodup:= h}

#check list_to_multiset_wo_dup [1,2] 
#check multiset_to_finset {1,2}

lemma set_insort:  multiset.erase_dup (ordered_insert r x xs)  = {x} ∪ multiset.erase_dup xs  :=
begin
  rewrite mset_insort,
  sorry
end





