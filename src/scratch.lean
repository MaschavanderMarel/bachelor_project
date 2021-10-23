import data.list.sort
import data.list.perm
import data.multiset
import tactic.induction

open list

set_option trace.simplify.rewrite true

def l: list ℕ  :=
[2,4,5,5,3] 

#eval l

def s: set ℕ :=
{2,3,1}

#eval s

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

variables α : Type
variables x: ℕ 
variables xs: list ℕ 

#check multiset.cons x xs
#check list.ordered_insert r x xs

