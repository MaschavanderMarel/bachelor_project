import data.list.sort
import data.list.perm
import data.multiset
import tactic.induction

open list

set_option trace.simplify.rewrite true

def l: list ℕ  :=
[2,4,5,5,3] 

#eval l.length

@[derive decidable_rel]
def r (m n : ℕ ):  Prop := 
m ≤  n

#eval list.insertion_sort r l

#eval ordered_insert r 3 (insertion_sort r l)
#check list.ordered_insert r 3 l

#eval multiset.cons 5 ({3,4})
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

variables α : Type
variables x: ℕ 
variables xs: list ℕ 

#check multiset.cons x xs
#check list.ordered_insert r x xs

lemma mset_insort : ↑(ordered_insert r x xs) = multiset.cons x xs :=
begin
  induction' xs, 
  { refl },
  { rewrite list.ordered_insert,
    split_ifs, 
    refl, 
    simp [←multiset.cons_coe], 
    simp only [ih],
    rewrite multiset.cons_swap,
    }
end

lemma mul_zero' (n : ℕ) :
  nat.mul 0 n = 0 :=
begin
  induction' n,
  { refl },
  { simp [*] at * }
end

/-- `ordered_insert a l` inserts `a` into `l` at such that
  `ordered_insert a l` is sorted if `l` is. -/
@[simp] def my_ordered_insert (a : ℕ ) : list ℕ  → list ℕ 
| []       := [a]
| (b :: l) := if a ≤ b then a :: b :: l else b :: my_ordered_insert l


lemma my_mset_insort : ↑(my_ordered_insert x xs) = multiset.cons x xs :=
begin
  induction' xs, 
  { refl },
  { simp [*, ite (x ≤ hd) (x :: hd :: xs) (hd :: my_ordered_insert x xs)] at * },
end
