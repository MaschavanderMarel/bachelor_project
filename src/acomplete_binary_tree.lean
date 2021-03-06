import complete_binary_tree
import data.nat.log

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
Used for lemma 4.7
-/
lemma lt_le_sub_one {a b: ℕ }: a < b → a <= b - 1 :=
begin
  cases b,
  { simp *},
  intro h,
  have h1: a.succ ≤ b.succ, from nat.succ_le_of_lt h,
  apply nat.le_of_succ_le_succ h1,
end

/-
Used for lemma 4.7
-/
lemma sub_one_div_add_eq_add_one_div {n : ℕ }: 
  ¬ n = 0 →  ((n-1)/2) + 1 = (n + 1) / 2 :=
begin
  have h1: 0 < 2, by simp,
  cases n,
  { simp * at *},
  intro h,
  simp [nat.succ_eq_add_one],
  apply eq.symm,
  calc
    (n + 1 + 1) / 2 = (n + 2 * 1) / 2 : by ring
    ... = n / 2  + 1: by apply nat.add_mul_div_left n 1 h1
end

/-
Used for lemma 4.7
-/
lemma lt_clog_of_pow_lt {m n : ℕ}: 2 ^ m < n → m < nat.clog 2 n :=
begin
  intro h,
  have h1: 0 < 2, by simp,
  induction' m,
  { have: 2 <= n, by linarith,
    simp [* , nat.clog_pos] },
  have h2: 2 ^ m.succ = 2 ^ m * 2, by ring,
  rw h2 at h,
  have : 2 ^ m > 0, by simp,
  have h3: 2 ^ m ≤ (n-1)/2 ↔ (2 ^ m) * 2 ≤ (n-1), from nat.le_div_iff_mul_le (2 ^ m) (n-1) h1,
  have h4: 2 ^ m * 2 ≤ n - 1, from lt_le_sub_one h,
  have : 1 < n, by linarith,
  have h5: ¬ n = 0, by linarith,
  have : 2 ^ m < (n+1) / 2, by calc
    2 ^ m <= (n-1) / 2: iff.elim_right h3 h4
    ... < ((n-1) / 2) + 1 : by simp
    ... = (n+1) / 2 : sub_one_div_add_eq_add_one_div h5,
  have ih': 2 ^ m < ((n+1)/2) → m < nat.clog 2 ((n+1) / 2), from ih ,
  rw nat.clog,
  simp [*, ← nat.add_one],
end

/-
Lemma 4.7 from __Functional Algorithms, Verified!__
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
  have : min_height t < nat.clog 2 (size1 t), from lt_clog_of_pow_lt h4,
  linarith,
end

/-
Used for lemma 4.8
-/
lemma gt_log_of_lt_pow {m n: ℕ } (h: 1 <= n) : n < 2 ^ m → m > nat.log 2 n :=
begin
  induction' m,
  { intro,
    linarith },
  intro h1,
  have h2: n / 2 < 2 ^ m, from begin
    have h3: n < 2 ^ m * 2, by calc
      n < 2 ^ m.succ: h1
      ... = 2 ^ m * 2 : by ring,
    have h4: 0 < 2, by simp,
    have: n / 2 < 2 ^ m ↔ n < 2 ^ m * 2, from nat.div_lt_iff_lt_mul n (2 ^ m) h4,
    exact iff.elim_right this h3,
  end,
  rw nat.log,
  split_ifs,
  { have : 2 <= n, from h_1.left,
    have h3: 1 <= n/2, from begin
      have h1: 0 < 2, by simp,
      have h2: 1 ≤ n / 2 ↔ 1 * 2 ≤ n, from nat.le_div_iff_mul_le 1 n h1,
      simp at h2,
      cc,
    end,
    have ih': m > nat.log 2 (n/2), from ih h3 h2,
    simp only [nat.succ_eq_add_one],
    linarith },
  simp,
end

/-
Lemma 4.8 from __Functional Algorithms, Verified!__
This lemma is not verified in Isabelle.
-/
lemma acomplete_min_height: acomplete t → min_height t = nat.log 2 (size1 t) :=
begin
  by_cases complete t,
  { have: size1 t = 2 ^height t, from size1_if_complete t h,
    have: min_height t = height t, from iff.elim_left (complete_iff_height t) h,
    simp [*, nat.log_pow] },
  intro h1,
  rw acomplete at h1,
  have: min_height t <= height t, from min_height_le_height t,
  have: ¬ min_height t = height t, from iff.elim_left (iff_false_left h) (complete_iff_height t), 
  have: min_height t < height t, by simp [has_le.le.lt_of_ne, *],
  have h2: height t = min_height t + 1, by linarith,
  have h3: 2 ^ min_height t <= size1 t, from min_height_size1 t,
  have h4: nat.log 2 (2 ^ min_height t) <= nat.log 2 (size1 t), from nat.log_le_log_of_le h3,
  have : 1 < 2, by simp,
  have h5: size1 t <= 2 ^ height t, from size1_height t,
  have h6: nat.log 2 (size1 t) <= nat.log 2 (2 ^ height t), from nat.log_le_log_of_le h5,
  simp [*, nat.log_pow] at h4 h6,
  have h7: size1 t < 2 ^ height t, by apply has_le.le.lt_of_ne h5 (iff.elim_left (iff_false_left h) (complete_iff_size1 t)),
  have: nat.log 2 (size1 t) < height t, from gt_log_of_lt_pow (trans (nat.one_le_two_pow (min_height t)) h3) h7,
  linarith ,
end
