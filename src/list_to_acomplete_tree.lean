import acomplete_binary_tree
import data.nat.log

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true

open tree

variable {α : Type}
variable a: α 
variables s t: tree α 

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
      have h2: 1 < 2, by linarith,
      exact nat.div_lt_self h1 h2,
    end,
    bal m xs,
    (r, zs) := 
    have n - 1 - n /2 < n, begin
      have h0: 1 + n/2 ≠ 0, by simp [nat.add_one_ne_zero (n/2), nat.add_comm],
      have h1: 0 < (1 + n /2), from nat.pos_of_ne_zero h0,
      have h2: 1 + n /2 <= n, by sorry,
      calc
        n - 1 - n /2 = n - ( 1 + n / 2) : nat.sub_sub n 1 (n/2)
        ... < n: nat.sub_lt_of_pos_le (1 + n /2) n h1 h2, 
    end,
    bal (n - 1 - m) (ys.tail) in 
    ((node ys.head l r), zs)
    else (nil, xs)
end


#eval bal 2 [1, 2, 3, 4]
#check @measure_wf

#eval nat.div 5 2