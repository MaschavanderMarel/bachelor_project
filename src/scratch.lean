import data.list.sort
import data.multiset
import data.set
import tactic.induction
import tactic.ring
import algebra.order.field

open list
open multiset
open set
open list.perm
open nat
set_option trace.simplify.rewrite true


def div : ℕ → ℕ → ℕ
| x y :=
  if h : 0 < y ∧ y ≤ x then
    have x - y < x,
      from sorry,
    div (x - y) y + 1
  else
    0

-- BEGIN
example (x y : ℕ) :
  div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
by rw [div]

example (x y : ℕ) (h : 0 < y ∧ y ≤ x) :
  div x y = div (x - y) y + 1 :=
begin
  rw div,
  rw if_pos h
end

#check nat.div_def


example (n: ℕ ) (h: n/2 = 0): n < 2 :=
begin
  apply classical.by_contradiction,
  intro h1,
  have h2: n = 2 ∨ 2 < n, by simp [nat.eq_or_lt_of_not_lt h1],
  apply or.elim h2,
  { intro h3,
    simp [h3] at h,
    contradiction },
  intro h3,
  simp at *,
  have h4: 0 < 2, by simp,
  have h7: n / 2 = 0 ↔ n < 2, from nat.div_eq_zero_iff h4,
  have h8: n < 2, from iff.elim_left h7 h,
  exact nat.le_lt_antisymm h1 h8,
end

lemma list_nil_or_singleton (n: ℕ ) (h: n/2 = 0): n = 0 ∨  n = 1 :=
begin
  apply classical.by_contradiction,
  intro h1,
  have h2: ¬ n = 0 ∧ ¬ n = 1, from iff.elim_left not_or_distrib h1,
  have h3: ¬ n = 0, from h2.left,
  have h4: ¬ n = 1, from h2.right,
  have h5: 0 < n, from nat.pos_of_ne_zero h3,
  have h6: 0 < 2, by simp,
  have h7: n / 2 = 0 ↔ n < 2, from nat.div_eq_zero_iff h6,
  have h8: n < 2, from iff.elim_left h7 h,
  have h10: n + 1 <= 2, by simp [nat.succ_le_of_lt h8],
  have h14: n <= 1, by simp only [nat.le_of_add_le_add_right h10],
  have h11: n < 1, from nat.lt_of_le_and_ne h14 h4,
  have h12: n + 1 <= 1, by simp [nat.succ_le_of_lt h11], 
  have h13: n <= 0, by simp only [nat.le_of_add_le_add_right h12],
  simp at h13,
  contradiction
end


example (n: ℕ ) (h: n = 0 ∨ n = 1): n < 2 :=
begin
  apply or.elim h,
  { intro h1,
    simp [h1]},
  intro h1,
  simp [h1],
end