import complete_binary_tree
import data.nat.log
import analysis.special_functions.log

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true

open tree

variable {α : Type}
variable a: α 
variables s t: tree α 

/-
# Almost Complete Binary Trees

## Definition
-/

def acomplete : tree α → Prop
| t := height t - min_height t <= 1

/-
Lemma 4.6 from __Functional Algorithms, Verified!__
-/
lemma acomplete_optimal :acomplete s ∧ size s <= size t → height s <= height t :=
begin
  intro h1,
  have h2: 2 <= 2, by trivial,
  by_cases complete s,
  { have h3: 2 ^ height s <= 2 ^height t, from calc
      2 ^ height s = size1 s : by simp [size1_if_complete s, *] 
      ... <= size1 t : by simp [*, size1_size]
      ... <= 2 ^height t : by simp [size1_height],
    simp [iff.elim_left (nat.pow_le_iff_le_right h2) h3] },
  have h3: 2 ^ min_height s < 2 ^ height t, from calc
    2 ^ min_height s < size1 s : by simp [min_height_size1_if_incomplete s, *] 
    ... <= size1 t : by simp [*, size1_size]
    ... <= 2 ^ height t: by simp [size1_height],
  have: min_height s < height t, from iff.elim_left (nat.pow_lt_iff_lt_right h2) h3,
  rw acomplete at h1,
  have: height s - min_height s ≤ 1 , from h1.left,
  have: ¬ min_height s = height s, from iff.elim_left (iff_false_left h) (complete_iff_height s), 
  have: min_height s <= height s, from min_height_le_height s,
  have: min_height s < height s, by simp [has_le.le.lt_of_ne, *],
  have: 0 < height s - min_height s, by simp [*, nat.sub_pos_of_lt],
  have: height s - min_height s = 1, by linarith,
  have: min_height s + 1 = height s, by linarith,
  linarith,
end

/-
Lemma 4.7 from __Functional Algorithms, Verified!__
-/

lemma test {a n : ℕ}: (2 ^ a < n) → a < nat.clog 2 n :=
begin
  intro h,
  induction n with n ih,
  { simp * at * },
  have h1: 2 ^ a <= n, from nat.le_of_lt_succ h,
  cases lt_or_eq_of_le h1,
  { simp [h_1] at ih,
    have h2: n <= n.succ, from nat.le_succ n,
    calc
      a < nat.clog 2 n : ih
      ... <= nat.clog 2 n.succ : nat.clog_le_clog_of_le 2 h2 },
  have h2: nat.clog 2 (2 ^ a) <= nat.clog 2 n, from nat.clog_le_clog_of_le 2 h1,
  simp [nat.clog_pow] at h2,
  have h3: 1 <= 2 ^ a, by simp [ nat.one_le_two_pow],
  rw h_1 at h3,
  have h4: 1 <= 2 ^ a, from nat.one_le_two_pow a,
  have h5: 1 < n.succ, from nat.lt_succ_of_le h3,
  rw nat.clog,
  have h6: 1 < 2, by simp,
  have h7: nat.clog 2 (2 ^ a) = a , from nat.clog_pow 2 a h6,
  rewrite h_1 at h7,
  have h8:  (1 < 2 ∧ 1 < n.succ), from and.intro h6 h5,
  -- simp only [ if_pos h8 ],
  simp *,

  sorry,
end


/- 
private lemma add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1)/b < n :=
begin
  rw [nat.div_lt_iff_lt_mul _ _ (zero_lt_one.trans hb), ←succ_le_iff, ←pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))],
  exact add_le_mul hn hb,
end

/--`clog b` and `pow b` form a Galois connection. -/
lemma le_pow_iff_clog_le' {b : ℕ} (hb : 1 < b) {x y : ℕ} :
  x ≤ b^y ↔ clog b x ≤ y :=
begin
  induction x using nat.strong_induction_on with x ih generalizing y,
  cases y,
  { rw [pow_zero],
    refine ⟨λ h, (clog_of_right_le_one h b).le, _⟩,
    simp_rw ←not_lt,
    contrapose!,
    exact clog_pos hb },
  have b_pos : 0 < b := zero_lt_two.trans_le hb,
  rw clog, split_ifs,
  { rw [succ_eq_add_one, add_le_add_iff_right, ←ih ((x + b - 1)/b) (add_pred_div_lt hb h.2),
      nat.div_le_iff_le_mul_add_pred b_pos,
      ← pow_succ, add_tsub_assoc_of_le (nat.succ_le_of_lt b_pos), add_le_add_iff_right] },
  { exact iff_of_true ((not_lt.1 (not_and.1 h hb)).trans $ succ_le_of_lt $ pow_pos b_pos _)
    (zero_le _) }
end
 -/
/- 
lemma test2 {x y : ℕ}: (2 ^ y < x) → y < nat.clog 2 x :=
begin
  induction x using nat.strong_induction_on  generalizing y,
  cases y,
  { intro h,
    simp at h,
    have h1: 1 < 2, by simp, 
    have h2: 2 <= x_n, by linarith,
    simp [*, nat.clog_pos ] },
  intro h,
  simp * at x_ᾰ,
  have ih': x_n < x_n → ∀ {y_1 : ℕ}, 2 ^ y_1 < x_n → y_1 < clog 2 x_n, from  x_ᾰ x_n,
  sorry
end
 -/

lemma test3 {a n : ℕ}: (2 ^ a < n) → a < nat.clog 2 n :=
begin
  have: 1 < 2, by simp,
  have: 0 < 2, by simp,
  induction' a,
  { intro h,
    have: 2 <= n, by linarith,
    simp [* , nat.clog_pos] },
  intro h,
  have h4: 2 ^ a.succ = 2 * 2 ^ a, by ring,
  rw h4 at h,
  have h0: 2 ^ a > 0, by simp,
  have h6: 2 ^ a ≤ (n-1)/2 ↔ 2 ^ a * 2 ≤ (n-1), from nat.le_div_iff_mul_le (2 ^ a) (n-1) this,
  have h7: 2 ^ a * 2 ≤ n - 1, from calc
    2 ^ a * 2 = 2 * 2 ^ a : by apply mul_comm
    ... <= n - 1 : by sorry,
  have h1: 2 ^ a < (n+1) / 2, by sorry,
  have ih': 2 ^ a < ((n+1)/2) → a < nat.clog 2 ((n+1) / 2), from ih ,
  rw nat.clog,
  -- simp [← nat.add_one] at h,
  have h2: 2 < n, by linarith,
  have h3: 1 < n, by linarith,
  simp [*, ← nat.add_one],
end

example (a b: ℕ ): a < b → a <= b.pred :=
begin
  induction' a,
  { simp *},
  simp [nat.succ_eq_add_one],
  intro h,
  simp [nat.pred],
  have h1 : a < b.pred, by sorry,
  sorry
end


/- 
lemma test' {a: ℕ}: ∀ n: ℕ, (2 ^ a < n) → a < nat.clog 2 n 
| n:= begin
  rw nat.clog,
  split_ifs,
  { intro h1,
    have h3: 1 < 2, by simp,
    have h4: 1 < n, from h.right,
    -- rw ← nat.clog_of_two_le h3 h4,
    have h2: (n + 2 - 1)/2 < n := add_pred_div_lt h.1 h.2,
    have h3: 2 ^ a < (n + 2 - 1) /2 ,from sorry,
    calc
      a < nat.clog 2 ((n + 2 - 1) / 2) : by apply test' ((n + 2 - 1) / 2) h3
      ... < nat.clog 2 ((n + 2 - 1) / 2) + 1 : by sorry },
  intro h1,
  rw decidable.not_and_distrib at h,
  simp at h,
  have h2: 1 <= 2 ^ a , from nat.one_le_two_pow a,
  have h3: n <= 2 ^ a, by linarith,
  have h4: 2 ^ a > n, by linarith,
  have: false, by linarith,
  exact false.elim this,
end
 -/


/-
This lemma is not verified in Isabelle.
-/
lemma acomplete_height :acomplete t → height t = nat.clog 2 (size1 t) :=
begin
  by_cases complete t,
  { have: size1 t = 2 ^height t, from size1_if_complete t h,
    simp [*, nat.clog_pow] },
  intro h1,
  rw acomplete at h1,
  have: min_height t <= height t, from min_height_le_height t,
  have: ¬ min_height t = height t, from iff.elim_left (iff_false_left h) (complete_iff_height t), 
  have: min_height t < height t, by simp [has_le.le.lt_of_ne, *],
  have h2: height t = min_height t + 1, by linarith,
  have h3: size1 t <= 2 ^ height t, from size1_height t,
  rw h2 at h3,
  simp [nat.le_pow_iff_clog_le] at h3,
  have h4: 2 ^ min_height t < size1 t, from min_height_size1_if_incomplete t h,
  have h6: min_height t < nat.clog 2 (size1 t), from test h4,
  linarith,
end


#eval nat.clog 2 9
