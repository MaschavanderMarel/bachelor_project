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
Section 4.3.1 from __Functional Algorithms, Verified!__. This section is not included in the Isabelle file.

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

example [inhabited α] (h: n ≠ 0) : bal' n xs = ((node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd) :=
begin
  rw [bal'],
  rw  [if_pos h],
end

example [inhabited α] (h: n ≠ 0) : bal n xs = ((node (bal (n/2) xs).snd.head (bal (n/2) xs).fst (bal (n - 1 - n/2) ((bal (n/2) xs).snd.tail)).fst), (bal (n - 1 - n/2) ((bal (n/2) xs).snd.tail)).snd) :=
begin
    have: n/2 < n, begin 
    have h1: 0 < n, from nat.pos_of_ne_zero h,
    have h2: 1 < 2, by simp,
    exact nat.div_lt_self h1 h2,
  end,
  have: n - 1 - n/2 < n, begin
    have h1: 0 < (1 + n/2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    have: n/2 < n, by simp [nat.div_lt_self, nat.pos_of_ne_zero, *],
    have h2: 1 + n/2 <= n, by linarith,
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n/2) n h1 h2,
  end,
  rw [bal, dif_pos h],
  simp,
  sorry,
end

example [inhabited α] (h: n ≠ 0) : 
  let (l, ys) :=  bal (n/2) xs, 
  (r, zs) := bal (n - 1 - (n/2)) (ys.tail)
 in
  bal n xs = ((node ys.head l r), zs)
 :=
begin
  rw [bal],
  split_ifs,
  { sorry},
  simp [_example._match_2, _example._match_1],
  sorry
end


#eval bal 0 ([]:list ℕ ) 
#eval bal 2 [1,2,3]
#eval bal' 3 [1,2,3]

/-
## Correctness

Lemma 4.9 from __Functional Algorithms, Verified!__
-/
lemma bal_prefix_suffix [inhabited α]: n <= xs.length ∧ bal n xs = (t, zs) → xs = inorder t ++ zs ∧ size t = n :=
begin
  induction n using nat.strong_induction_on with n ih generalizing t zs,
  intro h1,
  cases h1,
  by_cases n=0,
  { have h2: bal 0 xs = (t, zs), from eq.subst h h1_right,
    have h3: bal 0 xs = (nil, xs) := begin
      rw [bal, dif_neg],
      simp,
    end,
    apply and.intro,
    { have: t = nil, by cc,
      simp [inorder, *],
      cc },
    simp *,
    cc },
  let m: ℕ  := n/2,
  let m':= n - 1 - m,
  have h2: m < n, begin
    have h1: 0 < n, from nat.pos_of_ne_zero h,
    have h2: 1 < 2, by simp,
    exact nat.div_lt_self h1 h2,
  end,  
  have h3: m' < n, begin
    have h1: 0 < (1 + m), by simp [nat.add_one_ne_zero m, nat.add_comm, nat.pos_of_ne_zero],
    have: m < n, by simp [nat.div_lt_self, nat.pos_of_ne_zero, *],
    have h2: 1 + m <= n, by linarith,
    simp [m'],
    rw nat.sub_sub n 1 m,
    exact nat.sub_lt_of_pos_le (1 + m) n h1 h2,
  end,
  set l: tree α := (bal m xs).fst with l',
  set ys:= (bal m xs).snd with ys',
  set r:= (bal m' ys.tail).fst with r',
  have : bal n xs = ((node ys.head l r), zs), begin
    rw [bal, dif_pos h],
    simp *,
    sorry,
  end,
  have : t = (node ys.head l r), by cc,
  simp at ih,
  have h4: m <= xs.length, by linarith,
  have h5: bal m xs = (l, ys), begin
    sorry,
  end,
  have ih': xs = inorder l ++ ys ∧ size l = m, from ih m h2 l ys h4 h5,
  cases ih',
  -- have h6: 0 < ys.length, from sorry,
  have h8: n <= m + ys.length, from calc
    n <= xs.length : h1_left
    ... = (inorder l ++ ys).length : by rw [ih'_left]
    ... = m + ys.length: by simp [list.length, ih'_right],
  have: n - m <= ys.length, by sorry,
  sorry
end

lemma bal_prefix_suffix' [inhabited α]: 
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
  have h1: 0 < n, from nat.pos_of_ne_zero h,
  have : 1 <= n, by linarith,
  have h1': 1 < 2, by simp,
  have h2: n/2 < n, begin
    exact nat.div_lt_self h1 h1',
  end,  
  have h3': n/2 <= n, from le_of_lt h2,
  have : n/2 <= n - 1, by linarith,
  have h2' : 1 <= n - n/2, by by simp [add_le_of_le_tsub_right_of_le, le_tsub_of_add_le_left, *],
  have h3: n - 1 - n/2 < n, begin
    have h1: 0 < (1 + n/2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    have h2: 1 + n/2 <= n, from iff.elim_left (le_tsub_iff_right h3') h2',
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n/2) n h1 h2,
  end,
  have : bal' n xs = ((node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd) := by rw [bal', if_pos h],
  have h14: t = (node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), by cc,
  have h13: zs = (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd, by cc,
  simp at ih,
  have h4: n/2 <= xs.length, from trans h3' h_left,
  have h5: bal' (n/2) xs = ((bal' (n/2) xs).fst, (bal' (n/2) xs).snd), by simp,
  have ih': xs = inorder (bal' (n/2) xs).fst ++ (bal' (n/2) xs).snd ∧ size (bal' (n/2) xs).fst = n/2, from ih (n/2) h2 (bal' (n/2) xs).fst (bal' (n/2) xs).snd xs h4 h5,
  cases ih',
  have h8: n <= (bal' (n/2) xs).snd.length + n/2, from calc
    n <= (xs).length : h_left
    ... = (inorder (bal' (n/2) xs).fst ++ (bal' (n/2) xs).snd).length : by cc
    ... = n/2 + (bal' (n/2) xs).snd.length: by simp [list.length, ih'_right]
    ...= (bal' (n/2) xs).snd.length + n/2 : by ring,
  have h5': n - n/2 <= (bal' (n/2) xs).snd.length, by simp *,
  have h6: (bal' (n/2) xs).snd.length - 1 = (bal' (n/2) xs).snd.tail.length, by simp,
  have h7: 1 <= (bal' (n/2) xs).snd.length, from trans h2' h5',
  have h15: 0 < (bal' (n/2) xs).snd.length, by simp [nat.lt_of_succ_le, h7],
  have : (bal' (n/2) xs).snd.length = (bal' (n/2) xs).snd.tail.length + 1, from iff.elim_left (nat.sub_eq_iff_eq_add h7) h6,
  have h10: n - n/2 <= (bal' (n/2) xs).snd.tail.length + 1, by calc
    n - n/2 <= (bal' (n/2) xs).snd.length: by simp only [tsub_le_iff_right, h8]
    ... = (bal' (n/2) xs).snd.tail.length + 1: by cc,
  have h11: n - n/2 -1 <= (bal' (n/2) xs).snd.tail.length, by simp only [tsub_le_iff_right, h10],
  rw nat.sub.right_comm n (n/2) 1 at h11,
  have h12: bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail = ((bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).fst, zs), by simp [h13],
  have ih'':  (bal' (n/2) xs).snd.tail = inorder (bal' (n - 1 - n/2) (bal' (n/2) xs).snd.tail).fst ++ zs ∧ size (bal' (n - 1 - n/2) (bal' (n/2) xs).snd.tail).fst = n - 1 - n/2, from ih (n - 1 - n/2) h3 (bal' (n - 1 - n/2) (bal' (n/2) xs).snd.tail).fst zs (bal' (n/2) xs).snd.tail h11 h12,
  cases ih'',
  apply and.intro,
  { simp [h14, inorder],
    rw ← ih''_left,
    rw list.cons_head_tail,
    { exact ih'_left },
    exact list.ne_nil_of_length_pos h15 },
  simp [*, size, nat.sub_add_cancel],
end

lemma inorder_bal_list_eq_take [inhabited α ] : 
  n <= xs.length → inorder (bal_list n xs) = list.take n xs :=
begin
  intro h,
  rw [bal_list, bal'],
  split_ifs,
  { have h1: bal' n xs = ((node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal'   (n/2) xs).snd.tail)).fst), (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd) := 
    begin
      rw [bal', if_pos h_1],
    end,
    have h2:  n <= xs.length ∧ bal' n xs = (node (bal' (n / 2) xs).snd.head (bal' (n / 2) xs).fst (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).fst,
 (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).snd) → xs = inorder (node (bal' (n / 2) xs).snd.head (bal' (n / 2) xs).fst (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).fst) ++ (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).snd ∧ size (node (bal' (n / 2) xs).snd.head (bal' (n / 2) xs).fst (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).fst) = n, from bal_prefix_suffix' _ _ _ ,
    simp [h, h1] at h2,
    cases h2,
    have h3: (inorder (node (bal' (n / 2) xs).snd.head (bal' (n / 2) xs).fst (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).fst)).length = n, by simp *,
    have h4: list.take n xs = list.take n (
  inorder
      (node (bal' (n / 2) xs).snd.head (bal' (n / 2) xs).fst (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).fst) ++
    (bal' (n - 1 - n / 2) (bal' (n / 2) xs).snd.tail).snd), from congr_arg (list.take n) h2_left,
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

lemma bal_length [inhabited α]: 
  n <= xs.length ∧ bal' n xs = (t, zs) → xs.length = zs.length + n :=
begin
  intro h,
  have : xs = inorder t ++ zs ∧ size t = n, by simp [bal_prefix_suffix' xs zs t h],
  simp [*, add_comm],
end

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
    sorry
  end,
  rw h19 at h18,
  calc
    min_height t = min (min_height l) (min_height r) + 1: by simp [h8, min_height]
    ... = min_height r + 1: by {simp, exact h15}
    ... = nat.log 2 (n - 1 - n / 2 + 1) + 1 : by rw ih''
    ... = nat.log 2 (n + 1): by rw ← h18
end

#check @nat.log_of_one_lt_of_le
#check max

