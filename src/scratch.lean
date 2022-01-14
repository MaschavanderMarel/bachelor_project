import utilities

open list
open nat

set_option trace.simplify.rewrite true
-- set_option eqn_compiler.zeta true

variable {α : Type*}
variable r: α → α → Prop
variable x: α 
variables xs zs: list α 
variable q: ℕ × ℕ  

example (h: 0 < xs.length) : xs.length = 1 + xs.tail.length:=
begin
  simp [*,list.length, nat.sub_one, add_comm 1, nat.add_one, nat.succ_pred_eq_of_pos],
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

#reduce (λ (n : ℕ), n + 0 = n) 

#check nat.strong_induction_on

def bar1 : ℕ × ℕ → ℕ
| (m, n) := m + n

#print bar1._main
#eval bar1 (1,2)

def bar2 (p : ℕ × ℕ) : ℕ :=
match p with (m, n) := m + n end

#print bar2._match_1
#eval bar2 (1,2)

def bar3 : ℕ × ℕ → ℕ :=
λ ⟨m, n⟩, m + n

#print bar3._match_1

def bar4 (p : ℕ × ℕ) : ℕ :=
let ⟨m, n⟩ := p in m + n

def bar5 (p : ℕ × ℕ) : ℕ :=
let q:= 1 in
let (m, n) := p in m + n


#eval bar5 (1,2)
#print bar5

def bar6 (p : ℕ × ℕ) : ℕ :=
p.fst + p.snd

#eval bar6 (1,2)
#print bar6

example (n m: ℕ ) : bar5 (n,m) = n + m :=
begin
  rw [bar5],
  simp [bar5._match_1],
end

example : ∃ x, x = 5 :=
begin
  let u:= 5, 
  let v:= 6,
  apply exists.intro u,
  refl,
end

example : ∃ x, x = 5 :=
  let u:= 5 in
  let v:=6 in 
  exists.intro u begin
    refl
  end

lemma aux {n: ℕ } (h: ¬ n = 0): n / 2 + (n - 1 - n / 2 ) + 1 = n :=
begin
  have h1: 0 < n, from nat.pos_of_ne_zero h,
  have : 1 <= n, by linarith,
  have : n < n + n, from nat.lt_add_of_pos_left h1,
  have h2: n < n * 2, by linarith,
  have h3: 0 < 2, by linarith,
  have : n/2 < n , from iff.elim_right (nat.div_lt_iff_lt_mul n n h3) h2,
  have h4: n/2 <= n - 1, by linarith,
  calc
    n / 2 + (n - 1 - n / 2 ) + 1 = 1 + (n/2 + (n - 1 - n/2)) : by ring
    ... = n : by simp [nat.add_sub_of_le h4, *],
end  

lemma aux2 {m n: ℕ } (h: ¬ n = 0) (h1: n <= m + n/2): 1 <= m :=
begin
  have : 0 < n, from nat.pos_of_ne_zero h,
  have : 1 <= n, by linarith,
  have : n/2 < n , from sorry,
  have : n/2 <= n - 1, by linarith,
  have : 1 <= n - n/2, by by simp [add_le_of_le_tsub_right_of_le, le_tsub_of_add_le_left, *],
  have: n - n/2 <= m, by simp *,
  linarith
end

example {n: ℕ } (h: ¬ n = 0) :n - 1 + 1 = n :=
begin
  have h1: 0 < n, from nat.pos_of_ne_zero h,
  have : 1 <= n, by linarith,
  simp [*,nat.sub_add_cancel]
end

#check @tsub_le_iff_right

namespace hidden
open nat

def div : ℕ → ℕ → ℕ
| x y :=
  if h : 0 < y ∧ y ≤ x then
    have x - y < x,
      from nat.sub_lt (lt_of_lt_of_le h.left h.right) h.left,
    div (x - y) y + 1
  else
    0

example (x y : ℕ) :
  div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
by rw [div]

example (x y : ℕ) (h : 0 < y ∧ y ≤ x) :
  div x y = div (x - y) y + 1 :=
begin
  rw [div],
  sorry
end

end hidden