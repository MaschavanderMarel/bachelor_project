import data.list.sort
import data.multiset
import data.set
import tactic.induction

open list
open multiset
open set

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r:α → α → Prop
variable x: α 
variable xs: list α  

lemma mset_insort [decidable_rel r] : ((ordered_insert r x xs):multiset α ) =  {x} + ↑xs :=
begin
  induction' xs, 
  { refl },
  { simp,
    split_ifs, 
      refl, 
      simp [← multiset.cons_coe, ih] }
end

lemma mset_isort [decidable_rel r]: ((list.insertion_sort r xs): multiset α ) = ↑xs :=
begin
  induction' xs,
  { refl },
  { simp [mset_insort, *],
    refl }
end 

def list.to_set : list α → set α --Source: chapter 10.6 Theorem Proving in Lean.
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

-- This is predefined in Functional Algorithms Verified.
def multiset.to_set: multiset α → set α :=  
λ m: multiset α, {x: α | x ∈ m }

-- This lemma is predefined in the multiset file of Isabelle and used to prove lemma set_insort.
lemma set_mset_mset: multiset.to_set ↑xs = list.to_set xs := 
begin
  induction' xs,
  { refl},
  { simp [list.to_set,← ih, multiset.to_set, set.insert_def] }
end 

lemma set_insort [decidable_rel r]:  (ordered_insert r x xs).to_set  = {x} ∪ xs.to_set  :=
begin
  simp [set.insert_def, ← set_mset_mset, mset_insort, multiset.to_set],
end

-- This definition follows the definition in Functional Algorithms Verified.
def is_sorted [is_total α r] [is_trans α r] : list α → Prop 
| [] := true
| (h::t) := (∀ y ∈ t.to_set, r h y ) ∧ is_sorted t

lemma sorted_insort [decidable_rel r] [is_total α r] [is_trans α r] : is_sorted r (ordered_insert r x xs) = is_sorted r xs :=
begin
  induction' xs,
  { simp [is_sorted],
    intros,
    exact false.elim H },
  { simp only [ordered_insert],
    split_ifs,
    { simp [is_sorted, list.to_set],
      intros h1 h2,
      apply and.intro h,
      intros y h3, 
      have h4: y ∈ xs.to_set → r hd y, from h1 y,
      have h5: r hd y, from h4 h3,
      clear h4 h1 h2 _inst_1 _inst_2 ih h3 xs,
      exact @trans α r _inst_3 x hd y h h5 }, --why is _inst_3 not found by Lean without naming it explicitly even after clearing all other hypotheses?
    { simp [is_sorted, list.to_set, ih, set_insort],
      intros h1 h2,
      have h3: r hd x ∨ r x hd, from @total_of α r _inst_2 hd x, 
      exact or.resolve_right h3 h } }
end

lemma sorted_isort [decidable_rel r] [is_trans α r] [is_total α r]: is_sorted r (insertion_sort r xs) :=
begin
  induction' xs,
  { simp},
  { simp [sorted_insort, ih] }
end

example (a b c: α ) [decidable_rel r] [is_trans α r] [is_total α r] [is_linear_order α r]: r a b ∧ r b c → r a c :=
begin
intro h1,
have h2: r a b, from h1.left,
have h3: r b c, from h1.right,
exact @trans α r _ a b c h2 h3,
-- exact trans h2 h3
end

example (a b : α ) [is_linear_order α r] : r a b ∨ r b a :=
begin
exact total_of r a b
end


