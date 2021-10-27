import data.list.sort
import data.multiset
import data.set
import tactic.induction

open list
open multiset
open set

set_option trace.simplify.rewrite true

variables {α : Type*} (r : α → α → Prop) [decidable_rel r]
variables a x: α 
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

example: (ordered_insert (λ m n: ℕ , m ≤ n) 3 [2,4]:multiset ℕ)  = {3} + ↑[2,4] :=
begin
  simp only [mset_insort],
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

def list.to_set : list α → set α --does this def need to be proofed?
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

instance list_to_set_coe (α : Type*) : --what is this used for?
  has_coe (list α) (set α) :=
⟨list.to_set⟩

def multiset.to_set: multiset α → set α :=  -- is this correct? does it need to be proofed?
λ m: multiset α, {x: α | x ∈ m }

lemma set_mset_mset: multiset.to_set xs = list.to_set xs :=
begin
  induction' xs,
  {refl},
  simp [list.to_set, multiset.to_set],
  simp  [← ih],
  simp [multiset.to_set],
  simp [set.insert_def]
end 

#print set_mset_mset
#print set.insert_def
#print set.insert
#reduce multiset.to_set ({2,3,2}: multiset ℕ )
#reduce list.to_set [2,3,2]

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

lemma set_insort2:  list.to_set (ordered_insert r x xs)  = {x} ∪ list.to_set xs  :=
begin
 -- rewrite mset_insort, --how to use mset_insort like in Functional algorithms verified?
  simp,
  sorry
end

example: [2,1].sorted (λ m n: ℕ , m ≤ n) = false :=
by simp

lemma sorted_insort: (ordered_insert r a xs).sorted r = xs.sorted r:=
begin
  induction' xs,
  {simp},
  simp,
  sorry
end

