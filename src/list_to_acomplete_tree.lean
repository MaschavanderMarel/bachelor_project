import acomplete_binary_tree
import data.nat.log

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true
set_option eqn_compiler.zeta true

open tree

variable {α : Type} 
variables {n: ℕ} 
variables xs zs: list α 
variable a: α 
variables t: tree α 

/-
# Converting a List into an Almost Complete Tree
Section 4.3.1 from __Functional Algorithms, Verified!__. 
This section is not included in the Isabelle file.

## Definitions
-/

def bal [inhabited α]: ℕ → list α → tree α × list α
| n xs := 
  if h: n ≠ 0 then let 
    m := n /2, 
    (l, ys) := 
    have m < n, begin 
      have h1: 0 < n, from nat.pos_of_ne_zero h,
      have h2: 1 < 2, by simp,
      exact nat.div_lt_self h1 h2,
    end,
    bal m xs,
    (r, zs) := 
    have n - 1 - m < n, begin
      have h1: 0 < (1 + m), by simp [nat.add_one_ne_zero m, nat.add_comm, nat.pos_of_ne_zero],
      have: m < n, by simp [nat.div_lt_self, nat.pos_of_ne_zero, *],
      have h2: 1 + m <= n, by linarith,
      rw nat.sub_sub n 1 m,
      exact nat.sub_lt_of_pos_le (1 + m) n h1 h2,
    end,
    bal (n - 1 - m) (ys.tail) in 
    ((node ys.head l r), zs)
  else (nil, xs)

/-
Including nested let expressions in the definition of bal does not seem to work when using the definition in proofs. 
Therefore, an alternative, but similar definition bal' without let expression, 
is made and used in the proofs.
-/
def bal' [inhabited α]: ℕ → list α → tree α × list α
| n xs := begin
  apply if h: n ≠ 0 then  
  have n - 1 - n /2 < n, begin
    have h1: 0 < (1 + n /2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    have: n / 2 < n, by simp [nat.div_lt_self, nat.pos_of_ne_zero, *],
    have h2: 1 + n /2 <= n, by linarith,
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n /2) n h1 h2,
  end,
  have n/2 < n, begin 
    have h1: 0 < n, from nat.pos_of_ne_zero h,
    have h2: 1 < 2, by simp,
    exact nat.div_lt_self h1 h2,
  end,
  ((node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd)
  else (nil, xs)
end

def bal_list [inhabited α]: ℕ → list α → tree α 
| n xs := (bal' n xs).fst

def balance_list [inhabited α]: list α → tree α 
| xs := bal_list xs.length xs

def bal_tree [inhabited α]: ℕ → tree α → tree α 
| n t := bal_list n (inorder t)

def balance_tree [inhabited α]: tree α → tree α 
| t := bal_tree (size t) t 

/-
## Correctness

Lemma 4.9 from __Functional Algorithms, Verified!__
-/
lemma bal_prefix_suffix [inhabited α]: 
  n <= xs.length ∧ bal' n xs = (t, zs) → xs = inorder t ++ zs ∧ size t = n :=
begin
  induction n using nat.strong_induction_on with n ih generalizing t zs xs,
  intro h,
  cases h,
  by_cases n=0,
  { have h2: bal' 0 xs = (t, zs), from eq.subst h h_right,
    have h3: bal' 0 xs = (nil, xs) := begin
      rw [bal', if_neg],
      simp,
    end,
    apply and.intro,
    { have: t = nil, by cc,
      simp [inorder, *],
      cc },
    simp *,
    cc },
  let l := (bal' (n/2) xs).fst,
  let ys := (bal' (n/2) xs).snd,
  let r := (bal' (n - 1 - n/2) ys.tail).fst,
  let as := (bal' (n - 1 - n/2) ys.tail).snd,
  have h1: 0 < n, from nat.pos_of_ne_zero h,
  have h1': 1 <= n, by linarith,
  have h1'': 1 < 2, by simp,
  have h2: n/2 < n, begin
    exact nat.div_lt_self h1 h1'',
  end,  
  have h3': n/2 <= n, from le_of_lt h2,
  have h4': n/2 <= n - 1, by linarith,
  have h2' : 1 <= n - n/2, by by simp [add_le_of_le_tsub_right_of_le, le_tsub_of_add_le_left, *],
  have h3: n - 1 - n/2 < n, begin
    have h1: 0 < (1 + n/2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    have h2: 1 + n/2 <= n, from iff.elim_left (le_tsub_iff_right h3') h2',
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n/2) n h1 h2,
  end,
  have : bal' n xs = ((node ys.head l r), as) := by rw [bal', if_pos h],
  have h14: t = (node ys.head l r), by cc,
  have h13: zs = as, by cc,
  simp at ih,
  have h4: n/2 <= xs.length, from trans h3' h_left,
  have h5: bal' (n/2) xs = (l, ys), by simp,
  have ih': xs = inorder l ++ ys ∧ size l = n/2, from ih (n/2) h2 l ys xs h4 h5,
  cases ih',
  have h8: n <= ys.length + n/2, from calc
    n <= (xs).length : h_left
    ... = (inorder l ++ ys).length : by cc
    ... = n/2 + ys.length: by simp [list.length, ih'_right]
    ...= ys.length + n/2 : by ring,
  have h5': n - n/2 <= ys.length, by simp [h8],
  have h6: ys.length - 1 = ys.tail.length, by simp,
  have h7: 1 <= ys.length, from trans h2' h5',
  have h15: 0 < ys.length, by simp [nat.lt_of_succ_le, h7],
  have : ys.length = ys.tail.length + 1, from iff.elim_left (nat.sub_eq_iff_eq_add h7) h6,
  have h10: n - n/2 <= ys.tail.length + 1, by calc
    n - n/2 <= ys.length: by simp only [tsub_le_iff_right, h8]
    ... = ys.tail.length + 1: by cc,
  have h11: n - n/2 -1 <= ys.tail.length, by simp only [tsub_le_iff_right, h10],
  rw nat.sub.right_comm n (n/2) 1 at h11,
  have h12: bal' (n - 1 - n / 2) ys.tail = (r, zs), by simp [h13],
  have ih'':  ys.tail = inorder r ++ zs ∧ size r = n - 1 - n/2, from ih (n - 1 - n/2) h3 r zs ys.tail h11 h12,
  cases ih'',
  apply and.intro,
  { simp [h14, inorder],
    rw ← ih''_left,
    rw list.cons_head_tail,
    { exact ih'_left },
    exact list.ne_nil_of_length_pos h15 },
  simp  [h14, size, ih'_right, ih''_right],
  calc
    n / 2 + (n - 1 - n / 2) + 1 = n - 1 + 1: by rw add_tsub_cancel_of_le h4'
    ... = n : by rw tsub_add_cancel_of_le h1'
end

lemma inorder_bal_list_eq_take [inhabited α ] : 
  n <= xs.length → inorder (bal_list n xs) = list.take n xs :=
begin
  intro h,
  rw [bal_list, bal'],
  split_ifs,
  { let l := (bal' (n/2) xs).fst,
    let ys := (bal' (n/2) xs).snd,
    let r := (bal' (n - 1 - n/2) ys.tail).fst,
    let zs := (bal' (n - 1 - n/2) ys.tail).snd,
    have h1: bal' n xs = ((node ys.head l r), zs) := 
    begin
      rw [bal', if_pos h_1],
    end,
    have h2:  n <= xs.length ∧ bal' n xs = (node ys.head l r,
 zs) → xs = inorder (node ys.head l r) ++ zs ∧ size (node ys.head l r) = n, from bal_prefix_suffix _ _ _ ,
    simp [h, h1] at h2,
    cases h2,
    have h3: (inorder (node ys.head l r)).length = n, by simp only [length_inorder, h2_right],
    have h4: list.take n xs = list.take n (inorder (node ys.head l r) ++ zs), from congr_arg (list.take n) h2_left,
    rw h4,
    rw list.take_left' h3 },
  simp at h_1,
  rw h_1,
  simp [list.take_zero]
end

lemma inorder_balance_list_eq_list [inhabited α] : inorder (balance_list xs) = xs :=
begin
  rw balance_list,
  simp [*, inorder_bal_list_eq_take],
end

lemma inorder_bal_tree_eq_take_inorder [inhabited α]:
  n <= size t → inorder (bal_tree n t) = list.take n (inorder t) :=
begin
  intro h,
  rw [bal_tree],
  simp [*, inorder_bal_list_eq_take],
end

lemma inorder_balance_tree_eq_inorder [inhabited α]: inorder (balance_tree t) = inorder t:=
begin
  rw balance_tree,
  simp [*, inorder_bal_tree_eq_take_inorder, ← length_inorder],
end

/-
This lemma is used in lemma 4.10 and 4.11
-/
lemma bal_length [inhabited α]: 
  n <= xs.length ∧ bal' n xs = (t, zs) → xs.length = zs.length + n :=
begin
  intro h,
  have : xs = inorder t ++ zs ∧ size t = n, by simp [bal_prefix_suffix xs zs t h],
  simp [*, add_comm],
end

/-
Lemma 4.10 from __Functional Algorithms, Verified!__
-/
lemma bal_height [inhabited α] :
  n <= xs.length ∧ bal' n xs = (t, zs) → height t = nat.clog 2 (n + 1):=
begin
  induction n using nat.strong_induction_on with n ih generalizing t zs xs,
  intro h,
  cases h,
  by_cases n=0,
  { simp *,
    have : bal' 0 xs = (nil, xs) := begin
      rw [bal', if_neg],
      simp,
    end,
    cc },
  have h1: 0 < n, from nat.pos_of_ne_zero h,
  have h2 : 1 <= n, by simp [nat.add_one_le_iff, h1],
  have h3: n/2 < n, by simp [nat.div_lt_self h1],  
  have h5: 1 + n/2 <= n, by simp [nat.one_add_le_iff, h3], 
  have h6: n - 1 - n/2 < n, begin
    have h7: 0 < (1 + n/2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n/2) n h7 h5,
  end,
  let l := (bal' (n/2) xs).fst,
  let ys := (bal' (n/2) xs).snd,
  let r := (bal' (n - 1 - n/2) ys.tail).fst,
  let as := (bal' (n - 1 - n/2) ys.tail).snd,
  have : bal' n xs = ((node ys.head l r), as), by rw [bal', if_pos h],
  have h8: t = (node ys.head l r), by cc,
  have h9: zs = as, by cc,
  simp at ih,
  have h10: n/2 <= xs.length, from le_of_lt (lt_of_lt_of_le h3 h_left),
  have h11: bal' (n/2) xs = (l, ys), by simp,
  have ih': height l = nat.clog 2 (n/2 + 1), from ih (n/2) h3 l ys xs h10 h11,
  have h12: xs.length = ys.length + n/2, from bal_length xs ys l ⟨ h10, h11⟩ ,
  have h13: n - 1 - n/2 <= ys.tail.length, from calc
    n - 1 - n/2 = n - (1 + n/2): by rw nat.sub_sub n 1 (n/2)
    ... <= xs.length - (1 + n/2) : nat.sub_le_sub_right h_left (1 + n/2)
    ... = ys.length + n/2 - (1 + n/2): by rw h12
    ...= ys.length + n/2 - 1 - n/2: by rw ← nat.sub_sub (ys.length + n/2) 1 (n/2)
    ... = ys.length + n/2 - n/2 - 1: by rw nat.sub.right_comm (ys.length + n/2) 1 (n/2)
    ... = ys.length - 1: by simp
    ... = ys.tail.length: by simp,
  have h14: bal' (n - 1 - n / 2) ys.tail = (r, as), by simp [-tsub_le_iff_right],
  have ih'': height r = nat.clog 2 ((n - 1 - n/2) + 1), from ih (n - 1 - n/2) h6 r as ys.tail h13 h14,
  have h15: nat.clog 2 (n - 1 - n / 2 + 1) <= nat.clog 2 (n/2 + 1), begin
    apply nat.clog_le_clog_of_le,
    simp,
    ring,
    have h16: n < ( n / 2) * 2 + 2, by simp [nat.lt_div_mul_add],
    rw mul_comm,
    rw nat.lt_add_one_iff at h16,
    exact h16
  end,
  rw [← ih', ← ih''] at h15,
  have h17: 2 <= n + 1, by simp [nat.add_le_add_right h2 1],
  have h18: nat.clog 2 (n + 1) = nat.clog 2 ((n+1 + 2 - 1)/2) + 1, by simp [nat.clog_of_two_le _ h17],
  have h19: (n + 1 + 2 - 1)/2 = n / 2 + 1 := begin
    calc
    (n + 1 + 2 - 1)/2 = ( n + 2) /2 : by ring
    ... = n/2 + 1: by simp
  end,
  rw h19 at h18,
  calc
    height t = max (height l) (height r) + 1: by simp [h8, height]
    ... = height l + 1: by {simp, exact h15}
    ... = nat.clog 2 (n/2 + 1) + 1 : by rw ih' 
    ... = nat.clog 2 (n + 1): by rw ← h18
end

lemma eq_div2_add_div2 {n:ℕ }: (n + 1) / 2 + n /2 = n :=
begin
  induction n with n ih,
  { ring},
  simp [nat.succ_eq_add_one],
  ring,
  simp [nat.succ_eq_add_one],
  rw add_comm (n/2 + 1),
  rw ← add_assoc,
  simp [nat.add_one] at *,
  exact ih,
end

/-
Lemma 4.11 from __Functional Algorithms, Verified!__
-/
lemma bal_min_height [inhabited α] :
  n <= xs.length ∧ bal' n xs = (t, zs) → min_height t = nat.log 2 (n + 1):=
begin
  induction n using nat.strong_induction_on with n ih generalizing t zs xs,
  intro h,
  cases h,
  by_cases n=0,
  { simp *,
    have : bal' 0 xs = (nil, xs) := begin
      rw [bal', if_neg],
      simp,
    end,
    rw h at h_right,
    have h1: t = nil, by cc,
    simp [min_height, *] },
  have h1: 0 < n, from nat.pos_of_ne_zero h,
  have h2 : 1 <= n, by simp [nat.add_one_le_iff, h1],
  have h3: n/2 < n, by simp [nat.div_lt_self h1],  
  have h5: 1 + n/2 <= n, by simp [nat.one_add_le_iff, h3], 
  have h6: n - 1 - n/2 < n, begin
    have h7: 0 < (1 + n/2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n/2) n h7 h5,
  end,
  let l := (bal' (n/2) xs).fst,
  let ys := (bal' (n/2) xs).snd,
  let r := (bal' (n - 1 - n/2) ys.tail).fst,
  let as := (bal' (n - 1 - n/2) ys.tail).snd,
  have : bal' n xs = ((node ys.head l r), as), by rw [bal', if_pos h],
  have h8: t = (node ys.head l r), by cc,
  have h9: zs = as, by cc,
  simp at ih,
  have h10: n/2 <= xs.length, from le_of_lt (lt_of_lt_of_le h3 h_left),
  have h11: bal' (n/2) xs = (l, ys), by simp,
  have ih': min_height l = nat.log 2 (n/2 + 1), from ih (n/2) h3 l ys xs h10 h11,
  have h12: xs.length = ys.length + n/2, from bal_length xs ys l ⟨ h10, h11⟩ ,
  have h13: n - 1 - n/2 <= ys.tail.length, from calc
    n - 1 - n/2 = n - (1 + n/2): by rw nat.sub_sub n 1 (n/2)
    ... <= xs.length - (1 + n/2) : nat.sub_le_sub_right h_left (1 + n/2)
    ... = ys.length + n/2 - (1 + n/2): by rw h12
    ...= ys.length + n/2 - 1 - n/2: by rw ← nat.sub_sub (ys.length + n/2) 1 (n/2)
    ... = ys.length + n/2 - n/2 - 1: by rw nat.sub.right_comm (ys.length + n/2) 1 (n/2)
    ... = ys.length - 1: by simp
    ... = ys.tail.length: by simp,
  have h14: bal' (n - 1 - n / 2) ys.tail = (r, as), by simp [-tsub_le_iff_right],
  have ih'': min_height r = nat.log 2 ((n - 1 - n/2) + 1), from ih (n - 1 - n/2) h6 r as ys.tail h13 h14,
  have h15: nat.log 2 (n - 1 - n / 2 + 1) <= nat.log 2 (n/2 + 1), begin
    apply nat.log_le_log_of_le,
    simp,
    ring,
    have h16: n < ( n / 2) * 2 + 2, by simp [nat.lt_div_mul_add],
    rw mul_comm,
    rw nat.lt_add_one_iff at h16,
    exact h16
  end,
  rw [← ih', ← ih''] at h15,
  have h17: 2 <= n + 1, by simp [nat.add_le_add_right h2 1],
  have h17': 1 < 2, by simp,
  have h18: nat.log 2 (n + 1) = nat.log 2 ((n+1)/2) + 1, by simp [nat.log_of_one_lt_of_le h17' h17],
  have h19: (n + 1) / 2 = n - 1 - n/2 + 1 := begin
    have h21: n / 2 <= n, from le_of_lt h3,
    have h22: 1 <= n - n / 2, by {rw le_tsub_iff_right h21, exact h5},
    rw [nat.sub.right_comm n 1 (n/2), tsub_add_cancel_of_le h22 ],
    apply symm,
    rw nat.sub_eq_iff_eq_add h21,
    exact eq_div2_add_div2.symm,
  end,
  rw h19 at h18,
  calc
    min_height t = min (min_height l) (min_height r) + 1: by simp [h8, min_height]
    ... = min_height r + 1: by {simp, exact h15}
    ... = nat.log 2 (n - 1 - n / 2 + 1) + 1 : by rw ih''
    ... = nat.log 2 (n + 1): by rw ← h18
end

/-
This lemma is not proofed in  __Functional Algorithms, Verified!__,
but is needed for corollary 4.12
-/
lemma clog_sub_log_le_one {n: ℕ } : nat.clog 2 n - nat.log 2 n <= 1 :=
begin
  have h: 1 < 2, by simp,
  cases n,
  { simp },
  have h1: 0 < n.succ, by simp, 
  have h2: 2 ^ nat.log 2 n.succ ≤ n.succ, from (nat.pow_log_le_self h ( nat.succ_pos n)),
  have h3: n.succ ≤ 2 ^ nat.clog 2 n.succ , from nat.le_pow_clog h n.succ,
  have h4: n.succ < 2 ^ (nat.log 2 n.succ).succ, from nat.lt_pow_succ_log_self h h1,
  have h5: 1 <= n.succ, by linarith,
  cases h5.lt_or_eq,
  { have h6: 2 ^ (nat.clog 2 n.succ).pred < n.succ, from nat.pow_pred_clog_lt_self h h_1,
    have h7: 2 ^ (nat.clog 2 n.succ).pred <  2 ^ (nat.log 2 n.succ).succ, from h6.trans h4,
    rw nat.pow_lt_iff_lt_right _ at h7,
    simp [tsub_le_iff_right, add_comm 1, nat.le_of_pred_lt h7] },
  rw ← h_1,
  simp,
end

/-
Corollary 4.12 from __Functional Algorithms, Verified!__
-/
lemma bal_acomplete [inhabited α ]: n <= xs.length ∧ bal' n xs = (t, zs) → acomplete t:=
begin
  intro h,
  rw acomplete,
  have h1: height t = nat.clog 2 (n + 1), from bal_height xs zs t h,
  have h2: min_height t = nat.log 2 (n + 1), from bal_min_height xs zs t h,
  rw [h1, h2],
  exact clog_sub_log_le_one,
end
