import utilities

open list
open multiset
open set
open list.perm
open nat

set_option trace.simplify.rewrite true

variables {α : Type*} {κ : Type*}
variable r: κ → κ → Prop
variables (x: α) (k: κ ) 
variable xs: list α
variable f: α → κ 
variable P: α → Prop    

/- 
# Insertion Sort w.r.t. Keys and Stability
-/

def insort_key [decidable_rel r] [is_linear_order κ r] : list α → list α     
| []       := [x]
| (y :: ys) := if r (f x) (f y) then x :: y :: ys else y :: insort_key ys

def isort_key [decidable_rel r] [is_linear_order κ r]: list α → list α
| []       := []
| (x :: xs) := insort_key r x f (isort_key xs)

/-
## Functional Correctness
 -/

lemma mset_insort_key [decidable_rel r] [is_linear_order κ r]:
  ((insort_key r x f xs): multiset α) = {x} + ↑ xs :=
begin
  induction' xs,
  { refl},
  simp [insort_key],
  split_ifs,
  { refl},
  simp [← multiset.cons_coe, ih],
end

lemma mset_isort_key [decidable_rel r] [is_linear_order κ r]: (↑ (isort_key r f xs): multiset α) = ↑ xs :=
begin
  induction' xs,
  { refl},
  simp [mset_insort_key, isort_key, ih],
  refl,
end

lemma set_insort_key [decidable_rel r] [is_linear_order κ r]: (insort_key r x f xs).to_set = {x} ∪ xs.to_set:=
begin
  simp [← set_mset_mset, mset_insort_key, multiset.to_set],
  refl
end

lemma set_isort_key [decidable_rel r] [is_linear_order κ r]: (isort_key r f xs).to_set = xs.to_set :=
begin
  simp [← set_mset_mset, mset_isort_key],
end

lemma sorted_insort_key [decidable_rel r] [is_linear_order κ r]: 
  sorted' r ((insort_key r x f xs).map f) = sorted' r (xs.map f) :=
begin
  induction' xs fixing *,
  { simp [insort_key, sorted'],
    intros,
    exact false.elim H},
  simp [insort_key],
  split_ifs,
  { simp [sorted', list.to_set],
    intros h1 h2,
    apply and.intro h,
    intros k h3,
    exact trans h (h1 k h3) },
  simp [sorted', ih],
  intros h1,
  simp [← set_mset_mset, ← multiset.coe_map, mset_insort_key, multiset.to_set],
  intros h2,
  exact or.resolve_left (total_of r (f x) (f hd)) h
end

lemma sorted_isort_key [decidable_rel r] [is_linear_order κ r] : 
  sorted' r (map f (isort_key r f xs)) :=
begin
  induction' xs,
  { simp [isort_key] },
  simp [isort_key, sorted_insort_key, ih]
end

/-
## Stability
-/

lemma insort_is_Cons [decidable_rel r] [is_linear_order κ r]: 
  (∀ a ∈ xs.to_set, r (f x) (f a)) → insort_key r x f xs = (x:: xs):=
begin
  cases xs,
  { simp [insort_key] },
  simp [list.to_set, insort_key],
  intros h h1 h2,
  cc,
end 

lemma filter_insort_key_neg [decidable_rel r] [is_linear_order κ r] [decidable_pred P]:
  ¬ P x → (insort_key r x f xs).filter P = xs.filter P :=
begin
  induction xs,
  { simp [insort_key],
    intro h,
    simp * },
  simp [insort_key],
  split_ifs,
  { intro h1,
    simp * },
  intro h1,
  simp [list.filter, xs_ih h1],
end

#check @filter_insort_key_neg

lemma filter_insort_key_pos [decidable_rel r] [is_linear_order κ r] [decidable_pred P]:
  sorted' r (xs.map f) ∧ P x → (insort_key r x f xs).filter P = insort_key r x f (xs.filter P) :=
begin
  induction xs,
  { intro,
    simp [insort_key, *] },
  simp [sorted', list.filter, insort_key],
  split_ifs,
  { intros,
    simp [insort_key, *] },
  { have h5: (∀ a ∈ (list.filter P xs_tl).to_set, r (f x) (f a)) → insort_key r x f (filter P     xs_tl) = (x:: (filter P xs_tl)), from insort_is_Cons r x (filter P xs_tl) f,
    simp [ ← member_list_set] at h5 |-,
    intros h2 h3 h4,
    have h6: ∀ (a : α), a ∈ xs_tl → P a → r (f x) (f a), from begin
      intros a h7 h8,
      exact trans_of r h (h2 a h7),
    end,
    simp [*, h5 h6] },
  { intros,
    simp [list.filter, *, insort_key] },
  intros,
  simp [list.filter, *],
end

/-
Lemma 2.9 from __Functional Algorithms Verified!__
-/
lemma sort_key_stable [decidable_rel r] [is_linear_order κ r] [decidable_pred (λ y, f y = k)]: 
  (isort_key r f xs).filter (λ y, f y = k) = xs.filter (λ y, f y = k):=
begin
  induction xs,
  { simp [isort_key] },
  simp [list.filter],
  split_ifs,
  { simp [isort_key, *, filter_insort_key_pos, sorted_isort_key, ← member_list_set],
    have h1: (∀ a ∈ (list.filter (λ (y : α), f y = k) xs_tl).to_set, r (f _) (f a)) → insort_key r _ f _ = (_:: _) , from insort_is_Cons r xs_hd (filter (λ (y : α), f y = k) xs_tl) f,
    have h3: ∀ (a : α), a ∈ (list.filter (λ (y : α), f y = k) xs_tl).to_set → r (f xs_hd) (f a), from begin
      intros,
      simp [← member_list_set, *] at *,
      exact refl_of r k,
    end,
    exact h1 h3 },
  simp [isort_key, filter_insort_key_neg, *],
end

