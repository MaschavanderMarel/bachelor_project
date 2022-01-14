import acomplete_binary_tree
import data.nat.log

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true
set_option eqn_compiler.zeta true

open tree

variable {α : Type} 
variables n: ℕ 
variables xs zs: list α 
variable a: α 
variables t: tree α 

/-
# Converting a List into an Almost Complete Tree
Section 4.3.1 from __Functional Algorithms, Verified!__. This section is not included in the Isabelle file.

## Definition
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

example [inhabited α] (h: n ≠ 0) : bal' n xs = ((node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd) :=
begin
  rw [bal', if_pos h],
end

#eval bal 0 ([]:list ℕ ) 
#eval bal' 1 [1,2,3]

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
  let l: tree α := (bal m xs).fst,
  let ys:= (bal m xs).snd,
  let r:= (bal m' ys.tail).fst,
  have : bal n xs = ((node ys.head l r), zs), begin
    rw [bal, dif_pos h],
    simp *,
    -- simp [@bal._match_2 α _inst_1 n h (λ (ys : list α) (this : n - 1 - n / 2 < n), bal (n - 1 - n / 2) ys.tail) ],
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

lemma bal_prefix_suffix' [inhabited α]: n <= xs.length ∧ bal' n xs = (t, zs) → xs = inorder t ++ zs ∧ size t = n :=
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
  have : n/2 <= n - 1, by linarith,
  have h2' : 1 <= n - n/2, by by simp [add_le_of_le_tsub_right_of_le, le_tsub_of_add_le_left, *],
  have h3: n - 1 - n/2 < n, begin
    have h1: 0 < (1 + n/2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
    have h2: 1 + n/2 <= n, by linarith,
    rw nat.sub_sub n 1 (n/2),
    exact nat.sub_lt_of_pos_le (1 + n/2) n h1 h2,
  end,
  have : bal' n xs = ((node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd) := begin
    rw [bal', if_pos h],
  end,
  have h14: t = (node (bal' (n/2) xs).snd.head (bal' (n/2) xs).fst (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).fst), by cc,
  have h13: zs = (bal' (n - 1 - n/2) ((bal' (n/2) xs).snd.tail)).snd, by cc,
  simp at ih,
  have h4: n/2 <= xs.length, by linarith,
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

#check @trans
#check @iff.elim_right
#check list.length
#check list.length_tail
