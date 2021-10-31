import data.list.sort
import data.multiset
import data.set
import tactic.induction

open list
open multiset
open set

set_option trace.simplify.rewrite true

--universe variable uu
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

lemma set_insort:  (ordered_insert r x xs).to_set  = {x} ∪ xs.to_set  :=
begin
  simp,
  simp [set.insert_def],
  simp [← set_mset_mset],
  simp [mset_insort],
  simp [multiset.to_set]
end

variables  [is_total α r] [is_trans α r]

def is_sorted : list α → Prop 
| [] := true
| (h::t) := (∀ y ∈ t.to_set, r h y ) ∧ is_sorted t

lemma sorted_insort: is_sorted r (ordered_insert r x xs) = is_sorted r xs :=
begin
induction' xs,
{ simp [is_sorted],
  intros,
  exact false.elim H},
{ simp only [ordered_insert],
  split_ifs,
  { simp [is_sorted, list.to_set],
    intros h1 h2,
    apply and.intro h,
    intros b h3, 
    have h4: b ∈ xs.to_set → r hd b, from h1 b,
    have h5: r hd b, from h4 h3,
    --exact trans h h5, --why does trans fail?,
    sorry
    },
  { simp [is_sorted, list.to_set, ih, set_insort],
    intros h1 h2,
    have h3: r hd x ∨ r x hd, from sorry, -- why does total_of r fail?
    exact or.resolve_right h3 h}}
end

lemma sorted_isort: is_sorted r (insertion_sort r xs) :=
begin
  induction' xs,
  { simp},
  { simp [sorted_insort, ih]}
end

