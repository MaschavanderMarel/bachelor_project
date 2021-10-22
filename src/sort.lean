import data.list.sort
import data.multiset
import tactic.induction

open list
open multiset

set_option trace.simplify.rewrite true

@[derive decidable_rel]
def r (m n : ℕ ):  Prop := 
m ≤  n

variables α : Type
variables x: ℕ 
variables xs: list ℕ 

lemma mset_insort : ↑(ordered_insert r x xs) = multiset.cons x xs :=
begin
  induction' xs, 
  { refl },
  { rewrite list.ordered_insert,
    split_ifs, 
    refl, 
    simp [← multiset.cons_coe], 
    simp only [ih],
    rewrite multiset.cons_swap,
    }
end

#check multiset.cons 0 xs

lemma mset_isort: ((list.insertion_sort r xs): multiset ℕ =   ↑xs :=
begin
  induction' xs,
  {refl},
  { simp [mset_insort],
    simp at ih,
    simp [ih],
    }
end
