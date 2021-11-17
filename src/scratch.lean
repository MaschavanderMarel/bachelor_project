namespace hidden

inductive nat : Type
| zero : nat
| succ : nat → nat

namespace nat

def add : nat → nat → nat
| m zero     := m
| m (succ n) := succ (add m n)

local infix ` + ` := add

-- BEGIN
theorem zero_add: ∀ n, zero + n = n
| zero     := by simp [add]
| (succ n) := begin
  have h: zero + (n+ n ) = n + n, from zero_add (n+n),
  simp [add, zero_add n]
end


example: ∀ n, zero + n = n :=
begin
intros,
induction n ,
simp [add], 
simp [add],
simp [n_ih]
end

example: ∀ n, zero + n = n :=
assume n,
n.rec_on sorry sorry





end nat
end hidden