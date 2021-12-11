import data.list.sort
import data.list.basic
import data.multiset
import data.set
import tactic.induction
import tactic.ring
import algebra.order.field
import tactic.linarith

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variables xs ys: list α 
variable x: α 

/-
This files contains some functions that are predefined in __Function Algorithms, Verified!__, 
but not in Lean
-/

def list.to_set : list α → set α --Source: chapter 10.6 Theorem Proving in Lean.
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

def multiset.to_set: multiset α → set α :=  
λ m: multiset α, {x: α | x ∈ m }

lemma member_list_set : x ∈ xs ↔ x ∈ xs.to_set :=
begin
  induction' xs,
  { simp [list.to_set], },
  simp [list.to_set, ih],
end

/-
This definition follows the definition in __Functional Algorithms, Verified!__ 
instead of using the predefined function sorted in Lean.
-/
def sorted' [is_total α r] [is_trans α r] : list α → Prop 
| [] := true
| (h::t) := (∀ y ∈ t.to_set, r h y ) ∧ sorted' t

lemma set_mset_mset: multiset.to_set ↑xs = list.to_set xs := 
begin
  induction' xs,
  { refl},
  { simp [list.to_set,← ih, multiset.to_set, set.insert_def] }
end 

lemma mset_append : (↑ (xs ++ ys): multiset α) = ↑ xs + ↑ ys :=
begin
  simp,
end

lemma set_append: (xs ++ ys).to_set = xs.to_set ∪ ys.to_set:=
begin
  simp [← set_mset_mset, multiset.to_set],
  refl,
end

lemma sorted'_append [is_trans α r] [is_total α r] : 
  sorted' r (xs ++ ys) ↔ sorted' r xs ∧ sorted' r ys ∧ (∀ (x ∈ xs), ∀ (y ∈ ys), r x y) :=
begin
  induction' xs fixing *,
  { simp [sorted']},
  simp [sorted', ih, set_append],
  apply iff.intro,
  { intro h,
    apply and.intro,
    { apply and.intro,
      { 
        intros,
        exact h.left y (or.inl H), },
      exact h.right.left},
    apply and.intro,
    { exact h.right.right.left},
    apply and.intro,
    { intros,
      have h2: y ∈ ys.to_set, from iff.elim_left (member_list_set ys y) H,
      exact  h.left y (or.inr h2), },
    exact h.right.right.right},
  intro h,
  apply and.intro,
  { intros,
    apply or.elim H,
    { exact h.left.left y },
    intro h1,
    have h2: y ∈ ys, from iff.elim_right (member_list_set ys y) h1,
    exact h.right.right.left y h2 },
  apply and.intro,
  { exact h.left.right},
  apply and.intro,
  { exact h.right.left},
  exact h.right.right.right
end
