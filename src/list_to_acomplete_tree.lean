import acomplete_binary_tree
import data.nat.log

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true

open tree

variable {α : Type} 
variables n m: ℕ 
variables xs zs: list α 
variable a: α 
variables t: tree α 

/-
# Converting a List into an Almost Complete Tree
Section 4.3.1 from __Functional Algorithms, Verified!__. This section is not coded in the Isabelle file.

## Definition
-/

def bal [inhabited α]: ℕ → list α → tree α × list α
| n xs := begin
  apply if h: n ≠ 0 then let 
    m := n /2, 
    (l, ys) := 
    have m < n, begin 
      have h1: 0 < n, from nat.pos_of_ne_zero h,
      have h2: 1 < 2, by simp,
      exact nat.div_lt_self h1 h2,
    end,
    bal m xs,
    (r, zs) := 
    have n - 1 - n /2 < n, begin
      have h1: 0 < (1 + n /2), by simp [nat.add_one_ne_zero (n/2), nat.add_comm, nat.pos_of_ne_zero],
      have: n / 2 < n, by simp [nat.div_lt_self, nat.pos_of_ne_zero, *],
      have h2: 1 + n /2 <= n, by linarith,
      rw nat.sub_sub n 1 (n/2),
      exact nat.sub_lt_of_pos_le (1 + n /2) n h1 h2,
    end,
    bal (n - 1 - m) (ys.tail) in 
    ((node ys.head l r), zs)
    else (nil, xs)
end

/-
## Correctness

Lemma 4.9 from __Functional Algorithms, Verified!__
-/
lemma bal_prefix_suffix [inhabited α]: n <= xs.length ∧ bal n xs = (t, zs) → xs = inorder t ++ zs ∧ size t = n :=
begin
  induction n using nat.strong_induction_on with n1 ih,
  by_cases n1=0,
  { intro h1,
    cases h1,
    have h2: bal 0 xs = (t, zs), from eq.subst h h1_right,
    have h3: bal 0 xs = (nil, xs) :=
        begin
          rw [bal],
          simp [dite],
          refl
        end,
    apply and.intro,
    { have: t = nil, by cc,
      simp [inorder, *],
      cc },
    simp *,
    cc },
  sorry
end

example (n : nat) : n * 2 = n + n :=
begin
  induction n using nat.strong_induction_on with n1 ih ,
  have ih': n1 < n1 → (λ (n : ℕ), n * 2 = n + n) n1, from ih n1,
  have h: n1 <= n1, by simp,
  have h1: n1 < n1 ∨ n1 = n1, by sorry,
  cases h1,
  { simp *,},
  sorry,
end

example {p : nat → Prop} (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
begin
  have h1: (∀ (m : ℕ), m < n → p m) → p n, from h n,
  sorry
end

#check (λ (n : ℕ), n + 0 = n)

#check nat.strong_induction_on