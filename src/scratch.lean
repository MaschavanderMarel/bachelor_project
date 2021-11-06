import data.list.sort
import data.list.perm
import data.multiset
import tactic.induction

open list
open int

set_option trace.simplify.rewrite true

def l: list ℕ  :=
[2,4,5,5,3] 

#eval l

def s: set ℕ :=
{2,3,1}


@[derive decidable_rel]
def r (m n : ℕ ):  Prop := 
m ≤  n

#eval list.insertion_sort r l

#eval ordered_insert r 3 (insertion_sort r l)
#check list.ordered_insert r 3 l

#eval multiset.cons 5 {3,4}
#eval append [4] [2,3]

#check [3,4,5]
#print insertion_sort
#check insertion_sort

#check l
#check multiset

def m: multiset ℕ :=
{3,4,5,5,2}

#check multiset.cons 4 m
#eval multiset.cons 4 m

#eval m

lemma is: 3=3 :=
by refl


namespace fol_17

-- The following problem asks you to do a calculational proof. Some of these facts will be useful:
#check @add_assoc
#check @add_comm
#check @add_zero
#check @zero_add
#check @mul_assoc
#check @mul_comm
#check @mul_one
#check @one_mul
#check @left_distrib
#check @right_distrib
#check @add_left_neg
#check @add_right_neg
#check @sub_eq_add_neg
-- (You may want to comment these lines if there is too much information to the right.)


variables x y z : int

-- For example, we could prove the following fact:
theorem t1 : x - x = 0 :=
begin
  show x -x =0, by 
-- calc
sorry
-- x - x = x + -x : by rw sub_eq_add_neg
--     ... = 0      : by rw add_right_neg
end

-- Or this one:
theorem t2 (h : x + y = x + z) : y = z :=
calc
y     = 0 + y        : by rw zero_add
    ... = (-x + x) + y : by rw add_left_neg
    ... = -x + (x + y) : by rw add_assoc
    ... = -x + (x + z) : by rw h
    ... = (-x + x) + z : by rw add_assoc
    ... = 0 + z        : by rw add_left_neg
    ... = z            : by rw zero_add

-- Your job is to prove this. Replace the sorry statements with the facts listed above.
theorem fol_17 (h : x + y = z + y) : x = z :=
calc
x     = x + 0          : by rw add_zero
    ... = x + (y + -y) : by rw add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = (z + y) + -y : by rw h
    ... = z + (y + -y) : by rw add_assoc
    ... = z + 0        : by rw add_right_neg
    ... = z            : by rw add_zero

end fol_17