import utilities

open list
open multiset
open set
open list.perm
open nat

set_option trace.simplify.rewrite true

variable {α : Type*}
variable r: α → α → Prop
variable x: α 
variable xs: list α  

/- 
# Top-Down Merge Sort
-/

#eval merge (λ m n: ℕ, m < n) [1,3] [2,4]
#eval merge_sort (λ m n: ℕ , m < n) [2,1,4,3]

/- 
The function merge from Functional Algoriths Verified! is already defined in Lean as merge. 
The function msort is defined as merge_sort but in a different way. 
Therefore, it is defined below in the same way making use of the length of the list and drop/take functions, so the proof structure of the book can be followed. 
-/

variable ys: list α 

def msort [decidable_rel r]: list α → list α
| xs := begin
  apply if h: 0 < xs.length/2 then
  have (take (xs.length / 2) xs).length < xs.length, from 
    begin
      simp,
      calc
        xs.length/2 < xs.length /2 + xs.length/ 2  : nat.lt_add_of_pos_left h
        ... =  (xs.length / 2) * 2 : by ring
        ... <=  xs.length : by apply nat.div_mul_le_self,
    end,
  have (drop (xs.length / 2) xs).length < xs.length, from  
    begin 
      simp,
      have h1: 0 < xs.length, from calc
        0 < xs.length/2 : h
        ... <= xs.length : nat.div_le_self' xs.length 2,
      exact nat.sub_lt h1 h 
    end,
  merge r (msort (take (xs.length/2) xs)) (msort (drop (xs.length/2) xs))
  else xs
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

/- 
## Functional Correctness
 -/

lemma mset_merge [d: decidable_rel r]: (↑ (merge r xs ys): multiset α)  = ↑ xs + ↑ ys :=
begin
  simp,
  induction' xs,
  { induction' ys,
    { simp [merge]},
    simp [merge] },
  induction' ys,
  { simp [merge] },
  simp [merge],
  split_ifs,
  { simp [ih] },
  simp [← list.cons_append] ,
  simp only [list.perm_cons_append_cons hd_1 (@ih_ys _ _ _ _ ih)],
end  

lemma set_merge [decidable_rel r]: (merge r xs ys).to_set = xs.to_set ∪ ys.to_set :=
begin
  simp [← set_mset_mset, mset_merge, multiset.to_set],
  refl
end

lemma mset_msort [decidable_rel r]: ∀ xs: list α, (↑ (msort r xs):multiset α) = ↑ xs 
| xs := begin
  rw msort,
  split_ifs,
  { have h1: (take (xs.length / 2) xs).length < xs.length ∧ (drop (xs.length / 2) xs).length < xs.length, from 
    begin
      apply and.intro,
      { simp,
        calc
          xs.length/2 < xs.length /2 + xs.length/ 2  : nat.lt_add_of_pos_left h
          ... =  (xs.length / 2) * 2 : by ring
          ... <=  xs.length : by apply nat.div_mul_le_self },
      simp,
      have h1: 0 < xs.length, from calc
        0 < xs.length/2 : h
        ... <= xs.length : nat.div_le_self' xs.length 2,
      exact nat.sub_lt h1 h, 
    end,
    rw mset_merge,
    cases h1,
    simp only [mset_msort (take (xs.length/2) xs)],
    simp  [mset_msort (drop (xs.length/2) xs)] }, 
  refl,
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

lemma sorted_merge [d: decidable_rel r] [t: is_total α r] [tr: is_trans α r]: 
  sorted' r (merge r xs ys) ↔ sorted' r xs ∧ sorted' r ys :=
begin
  induction' xs,
  {  induction' ys,
    { simp [merge] },
    simp [merge, sorted'], },
  induction' ys fixing *,
  { simp [merge, sorted'], },
  simp [merge],
  split_ifs,
  { simp  [sorted', ih, set_merge, and_assoc],
    intros h1 h2 h3,
    apply iff.intro,
    { intros h4 y H,
      exact h4 y (or.inl H)},
    intros h4 y H,
    apply or.elim H,
    { exact h4 y },
    intro h5,
    simp [list.to_set] at h5,
    apply or.elim h5,
    { intro h6,
      exact eq.subst h6.symm h },
    intro h6,
    exact trans h (h2 y h6)},
  simp [sorted', ih_ys, and.assoc, set_merge, and.comm],
  simp [and_comm (sorted' r ys), and.assoc ],
  intros h1 h2 h3,
  apply iff.intro,
  { intros h4 _ _,
    exact h4 y (or.inr H)},
  intros h4 _ _,
  apply or.elim H,
  { simp [list.to_set],
    intro h5,
    have h6: r hd_1 y ∨ r y hd_1, from total_of r hd_1 y,
    apply or.elim h5,
    { intro h7,
      apply or.resolve_right h6,
      exact eq.subst h7.symm h},
    intro h7,
    have h8: r hd_1 hd ∨ r hd hd_1, from total_of r hd_1 hd,
    exact trans (or.resolve_right h8 h) (h2 y h7)},
  exact h4 y,
end

lemma div_two_eq_zero_or_one {n: ℕ } (h: n/2 = 0): n = 0 ∨  n = 1 :=
begin
  apply classical.by_contradiction,
  intro h1,
  have h2: ¬ n = 0, from (iff.elim_left not_or_distrib h1).left,
  have h3: ¬ n = 1, from (iff.elim_left not_or_distrib h1).right,
  have h4: 0 < 2, by simp,
  have h5: n/2 = 0 ↔ n <= 1, by calc
    n / 2 = 0 ↔ n < 2 : nat.div_eq_zero_iff h4
    ... ↔  n + 1 <= 1 + 1 : by ring
    ... ↔  n <= 1 : by simp,
  have h6: n <=1, from iff.elim_left h5 h,
  have h7: n < 1, from nat.lt_of_le_and_ne h6 h3,
  simp at *,
  contradiction,
end

lemma sorted_msort [decidable_rel r] [is_total α r] [is_trans α r]:
  ∀ xs: list α, sorted' r (msort r xs)
| xs := 
begin
  rw msort,
  split_ifs,
  { have h1: (take (xs.length / 2) xs).length < xs.length ∧ (drop (xs.length / 2) xs).length < xs.length, from 
    begin
      apply and.intro,
      { simp,
        calc
          xs.length/2 < xs.length /2 + xs.length/ 2  : nat.lt_add_of_pos_left h
          ... =  (xs.length / 2) * 2 : by ring
          ... <=  xs.length : by apply nat.div_mul_le_self },
      simp,
      have h1: 0 < xs.length, from calc
        0 < xs.length/2 : h
        ... <= xs.length : nat.div_le_self' xs.length 2,
      exact nat.sub_lt h1 h, 
    end,
    cases h1,
    simp [sorted_merge],
    simp only [sorted_msort (take (xs.length/2) xs)],
    simp [sorted_msort (drop (xs.length/2) xs)] }, 
  have h2: 0 = xs.length/2 ∨ xs.length/2 < 0 , from nat.eq_or_lt_of_not_lt h,
  simp at h2,
  have h1: xs.length = 0 ∨ xs.length = 1, from div_two_eq_zero_or_one h2.symm,
  apply or.elim h1,
  { intro h2,
    have h3: xs = list.nil, from list.eq_nil_of_length_eq_zero h2,
    simp [h3] },
  intro h2,
  have h3: ∃ (a : α), xs = [a], from iff.elim_left list.length_eq_one h2,
  apply exists.elim h3,
  intros a h4,
  simp [h4, sorted'],
  intros,
  simp [list.to_set] at H,
  exact false.elim H
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

#eval nat.div 4 2

#eval merge_sort (λ m n : ℕ, m ≤ n) [23,1, 12]
#eval msort (λ m n : ℕ, m ≤ n) (30 ::15::[23,12])
