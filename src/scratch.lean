import utilities
import data.nat.log
import data.nat.parity

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

example (x : ℕ) (h : x = 3)  : x + x + x = 9 :=
begin
  set y := x with h_xy,
  sorry
end

example {n:ℕ} (h:¬ n = 0): n - 1 - n / 2  ≤ n / 2  :=
begin
  have h1: 2 * n - 2 - n <= n, from sorry,
  have: (2*n - 2 - n)/2 <= n/2, from nat.div_le_div_right h1,
  have: (2 * n - 2 - n) / 2 = n - 1 - n/2, by calc
    (2 * n - 2 - n) / 2 = (2 * n - n - 2) / 2: by rw nat.sub.right_comm (2 * n) 2 n
    ... = n - 1 - n/2: by sorry,
  sorry
end

example {n:ℕ} : n - 1 - n / 2 + 1 ≤ n / 2 + 1  :=
begin
  simp,
  ring,
  have h2: n < ( n / 2) * 2 + 2, by simp [nat.lt_div_mul_add],
  rw mul_comm,
  rw nat.lt_add_one_iff at h2,
  exact h2
end

lemma eq_div2_add_div2 {n:ℕ }: (n + 1) / 2 + n /2 = n :=
begin
  induction n with n ih,
  { ring},
  simp [succ_eq_add_one],
  ring,
  simp [succ_eq_add_one],
  rw add_comm (n/2 + 1),
  rw ← add_assoc,
  simp [add_one] at *,
  exact ih,
end



#check add_assoc

example (n:ℕ ) : (n + 1) / 2 = n - 1 - n/2 + 1 := begin
  rw nat.sub.right_comm n 1 (n/2),
  have  h1: 1 <= n - n/2, from sorry, --al gedaan
  rw tsub_add_cancel_of_le h1,
  have h2: n/2 <= n, from sorry, --al gedaan
  apply symm,
  rw nat.sub_eq_iff_eq_add h2,
  exact eq_div2_add_div2.symm
end

#check @nat.div

example (n:ℕ ) (h: ¬ n = 0): (n + 1) / 2 = n - 1 - n/2 + 1 := 
begin
  rw nat.sub.right_comm n 1 (n/2),
  have  h1: 1 <= n - n/2, from sorry,
  rw tsub_add_cancel_of_le h1,
  have h2: n/2 <= n, from sorry,
  apply symm,
  rw nat.sub_eq_iff_eq_add h2,
  cases nat.mod_two_eq_zero_or_one n,
  { rw nat.succ_div,
    split_ifs,
    { 
      sorry},
    sorry},
  rw nat.succ_div,
  split_ifs,
  { sorry},
  sorry
end

example {n:ℕ } (h: 1 + n /2 <= n) (h1: n/2 <=n): 1 <= n - n / 2 :=
begin
  rw le_tsub_iff_right h1,
  exact h
end
