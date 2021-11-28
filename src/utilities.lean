import data.list.sort
import data.multiset
import data.set
import tactic.induction
import tactic.ring
import algebra.order.field
import tactic.linarith
import algebra.group_power.order
-- import algebra.group_power.lemmas

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variable xs: list α 

/-
This files contains some functions that are predefined in Function Algorithms Verified, 
but not in Lean
-/

def list.to_set : list α → set α --Source: chapter 10.6 Theorem Proving in Lean.
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

def multiset.to_set: multiset α → set α :=  
λ m: multiset α, {x: α | x ∈ m }

/-
This definition follows the definition in Functional Algorithms Verified 
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

