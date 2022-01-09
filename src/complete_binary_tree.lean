import binary_tree

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true

open tree

variable {α : Type}
variable a: α 
variable t: tree α 

/-
# Complete Binary Trees

## Definition
-/
def complete : tree α → Prop
| nil := true
| (node a l r ) := height l = height r ∧ complete l ∧ complete r

/-
## Lemmas

Lemma 4.1 from __Functional Algorithms, Verified!__
-/
lemma complete_iff_height: complete t ↔ min_height t = height t :=
begin
  induction t with a l r l_ih r_ih,
  { simp [complete, min_height, height] },
  simp [complete, min_height, height, min_def, max_def, *],
  have: min_height r <= height r, from min_height_le_height r,
  have: min_height l <= height l, from min_height_le_height l,
  split_ifs,
  { apply iff.intro,
    { cc },
    intro h2,
    apply and.intro,
    repeat { linarith },
    apply and.intro,
    repeat { linarith } },
  { apply iff.intro,
    repeat { cc} },
  { apply iff.intro,
    repeat { cc } },
  apply iff.intro,
  { cc},
  intro h2,
  repeat { linarith },
end

/-
Lemma 4.2 from __Functional Algorithms, Verified!__
-/
lemma size1_if_complete : complete t → size1 t = 2 ^height t :=
begin
  induction t with a l r l_ih r_ih,
  repeat { simp [complete, height, size1] },
  intros,
  simp *,
  ring,
end

lemma size_if_complete: complete t → size t = (2 ^ height t) - 1 :=
begin
 intro,
 calc
  size t = size1 t - 1 : by simp [size1_size] 
  ... = 2 ^ height t - 1: by simp [*, size1_if_complete]
end

/-
Lemma 4.3 from  __Functional Algorithms, Verified!__
-/
lemma size1_height_if_incomplete: ¬ complete t → size1 t < 2 ^ height t :=
begin
  induction t with a l r l_ih r_ih,
  repeat {simp [complete, size1, height, max_def]},
  intro h1,
  have h2: 2 <= 2, by trivial,
  by_cases h3: height l = height r,
  { simp * at h1,
    cases (not_or_of_imp h1),
    { simp [*, pow_ite] at * ,
      calc
        size1 l + size1 r < 2 ^ height l + size1 r : by simp *
        ... <= 2 ^ height l + 2 ^ height r : by simp [size1_height] 
        ... = 2 ^ (height r + 1) :by {simp *, ring} },
    simp [*, pow_ite] at *,
    calc
      size1 l + size1 r < size1 l + 2 ^ height r : by simp *
      ... <= 2 ^ height l + 2 ^ height r : by simp [size1_height] 
      ... = 2 ^ (height r + 1) :by {simp *, ring} },
  cases (ne.lt_or_lt h3),
  { have h3: ¬ height r <= height l, by linarith,
    have h4: 2 ^ height l < 2 ^ height r, from iff.elim_right (nat.pow_lt_iff_lt_right h2) h,
    simp [*, pow_ite],
    calc 
      size1 l + size1 r <= size1 l + 2 ^ height r: by simp [size1_height]
      ... <= 2 ^ height l + 2 ^ height r : by simp [size1_height]
      ... < 2 ^ height r + 2 ^ height r : by simp *
      ... = 2 ^ (height r + 1) : by ring},
  have h3: height r <= height l, by linarith,
  have h4: 2 ^ height r < 2 ^ height l, from iff.elim_right (nat.pow_lt_iff_lt_right h2) h,
  simp [*, pow_ite],
  calc 
      size1 l + size1 r <= size1 l + 2 ^ height r: by simp [size1_height]
      ... <= 2 ^ height l + 2 ^ height r : by simp [size1_height]
      ... < 2 ^ height l + 2 ^ height l : by simp *
      ... = 2 ^ (height l + 1) : by ring,
end

/-
Lemmma 4.4 from __Functional Algorithms, Verified!__ 
-/
lemma min_height_size1_if_incomplete: ¬ complete t → 2 ^ min_height t < size1 t :=
begin
  induction t with a l r l_ih r_ih,
  repeat { simp [complete, size1, min_height, min_def]},
  intro h1,
  have h2: 2 <= 2, by trivial,
  by_cases h3: min_height l = min_height r,
  { simp *,
    by_cases complete l ∧ complete r,
    { have h4: min_height l = height l, from iff.elim_left (complete_iff_height l) h.left,
      have h5: min_height r = height r, from iff.elim_left (complete_iff_height r) h.right,
      have h6: height l = height r, by cc,
      simp * at *, },
    rw [not_and_distrib] at h,
    cases h,
    { calc
        2 ^ (min_height r + 1) = 2 ^ min_height r + 2 ^ min_height r : by ring
        ... = 2 ^ min_height l + 2 ^ min_height r: by simp *
        ... <= 2 ^ min_height l + size1 r: by simp [min_height_size1]
        ... < size1 l + size1 r : by simp [l_ih h] }, 
    calc
      2 ^ (min_height r + 1) = 2 ^ min_height r + 2 ^ min_height r : by ring
      ... = 2 ^ min_height l + 2 ^ min_height r: by simp *
      ... <= size1 l + 2 ^ min_height r: by simp [min_height_size1]
      ... < size1 l + size1 r : by simp [r_ih h]},
  cases (ne.lt_or_lt h3),
  { have h4: min_height l <= min_height r, by linarith,
    simp [*, pow_ite],
    calc 
      2 ^ (min_height l + 1) = 2 ^ min_height l + 2 ^ min_height l : by ring
      ... < 2 ^ min_height l + 2 ^ min_height r : by simp [iff.elim_right (nat.pow_lt_iff_lt_right h2) h]
      ... <= 2 ^ min_height l + size1 r: by simp [min_height_size1 l, min_height_size1 r]
      ... <= size1 l + size1 r: by simp [min_height_size1]},
  have h4: ¬ min_height l <= min_height r, by linarith,
  simp [*, pow_ite],
  calc 
    2 ^ (min_height r + 1) = 2 ^ min_height r + 2 ^ min_height r : by ring
    ... < 2 ^ min_height l + 2 ^ min_height r : by simp [iff.elim_right (nat.pow_lt_iff_lt_right h2) h]
    ... <= 2 ^ min_height l + size1 r: by simp [min_height_size1 l, min_height_size1 r]
    ... <= size1 l + size1 r: by simp [min_height_size1]
end

lemma complete_if_size1_height: size1 t = 2 ^ height t → complete t :=
begin
  have h: ¬ size1 t < 2 ^ height t → complete t, from not.imp_symm (size1_height_if_incomplete t),
  intro h1,
  simp *,
end

lemma complete_if_size1_min_height: size1 t = 2 ^ min_height t → complete t :=
begin
  have h: ¬ 2 ^ min_height t < size1 t → complete t, from not.imp_symm (min_height_size1_if_incomplete t),
  intro h1,
  simp *,
end

/-
Corollary 4.5 from __Functional Algorithms, Verified!__ 
-/
lemma complete_iff_size1: complete t ↔ size1 t = 2 ^ height t :=
begin
  apply iff.intro,
  { exact size1_if_complete t },
  exact complete_if_size1_height t
end
