import data.list.sort
import data.multiset
import data.set
import tactic.induction
import tactic.ring

open list
open multiset
open set

set_option trace.simplify.rewrite true

/- Insertion sort
 -/

section Insertion_sort

-- Functional Correctness

variable {α : Type*}
variable r:α → α → Prop
variable x: α 
variable xs: list α  

lemma mset_insort [decidable_rel r] : ((ordered_insert r x xs):multiset α ) =  {x} + ↑xs :=
begin
  induction' xs, 
  { refl },
  { simp,
    split_ifs, 
      refl, 
      simp [← multiset.cons_coe, ih] }
end

lemma mset_isort [decidable_rel r]: (↑ (list.insertion_sort r xs): multiset α ) = ↑xs :=
begin
  induction' xs,
  { refl },
  { simp [mset_insort, ih],
    refl }
end 

def list.to_set : list α → set α --Source: chapter 10.6 Theorem Proving in Lean.
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

-- This is predefined in Functional Algorithms Verified.
def multiset.to_set: multiset α → set α :=  
λ m: multiset α, {x: α | x ∈ m }

-- This lemma is predefined in the multiset file of Isabelle and used to prove lemma set_insort.
lemma set_mset_mset: multiset.to_set ↑xs = list.to_set xs := 
begin
  induction' xs,
  { refl},
  { simp [list.to_set,← ih, multiset.to_set, set.insert_def] }
end 

lemma set_insort [decidable_rel r]:  (ordered_insert r x xs).to_set  = {x} ∪ xs.to_set  :=
begin
  simp [set.insert_def, ← set_mset_mset, mset_insort, multiset.to_set],
end

-- This definition follows the definition in Functional Algorithms Verified.
def is_sorted [is_total α r] [is_trans α r] : list α → Prop 
| [] := true
| (h::t) := (∀ y ∈ t.to_set, r h y ) ∧ is_sorted t

lemma sorted_insort [decidable_rel r] [is_total α r] [ t: is_trans α r]  : is_sorted r (ordered_insert r x xs) = is_sorted r xs :=
begin
  induction' xs,
  { simp [is_sorted],
    intros,
    exact false.elim H },
  { simp only [ordered_insert],
    split_ifs,
    { simp [is_sorted, list.to_set],
      intros h1 h2,
      apply and.intro h,
      intros y h3, 
      have h4: y ∈ xs.to_set → r hd y, from h1 y,
      have h5: r hd y, from h4 h3,
      clear h4 h1 h2 _inst_1 _inst_2 ih h3 xs,
      exact @trans _ _ t _ _ _ h h5 }, --why is t not found by Lean without mentioning it explicitly, but it is in example below?
    { simp [is_sorted, list.to_set, ih, set_insort],
      intros h1 h2,
      have h3: r hd x ∨ r x hd, from @total_of α r _inst_2 hd x, 
      exact or.resolve_right h3 h } }
end

lemma sorted_isort [decidable_rel r] [is_trans α r] [is_total α r]: is_sorted r (insertion_sort r xs) :=
begin
  induction' xs,
  { simp},
  { simp [sorted_insort, ih] }
end

example (a b c: α ) [decidable_rel r] [is_trans α r] [is_total α r] [is_linear_order α r]: r a b ∧ r b c → r a c :=
begin
intro h1,
have h2: r a b, from h1.left,
have h3: r b c, from h1.right,
exact @trans α r _ a b c h2 h3,
-- exact trans h2 h3
end

example (a b : α ) {s: α → α → Prop} [is_linear_order α s] : s a b ∨ s b a :=
begin
  exact total_of s a b
end

/- Time Complexity
   We count the number of function calls
 -/

def T_insort [decidable_rel r] : α → list α → nat 
| x [] := 1
| x (y::ys) := if  r x y  then 0 else T_insort x ys + 1 

def T_isort [decidable_rel r] : list α → nat 
| [] := 1
| (x::xs) := T_isort xs + T_insort r x (insertion_sort r xs) + 1

lemma T_insort_length [decidable_rel r]: T_insort r x xs <= xs.length + 1 :=
begin
  induction' xs,
  { simp [T_insort] },
  { simp [T_insort],
    split_ifs,
    { simp},
    { simp [ih] } }
end

lemma length_insort [decidable_rel r] : (ordered_insert r x xs).length = xs.length + 1 :=
begin
  induction' xs,
  { simp [ordered_insert] },
  { simp,
    split_ifs,
    { simp},
    { simp [ih] } }
end

lemma length_isort [decidable_rel r] : (insertion_sort r xs).length = xs.length :=
begin
  induction' xs,
  { simp},
  { simp [length_insort, ih] }
end

lemma T_isort_length [d: decidable_rel r]: T_isort r xs <= (xs.length + 1) ^ 2 :=
begin
  induction' xs,
  { simp [T_isort]},
  { simp [T_isort, T_insort_length, length_isort],
    show @T_isort _ _ _ xs + @T_insort _ _ _ hd (@insertion_sort _ _ _ xs) + 1 ≤ (xs.length + 1 + 1) ^ 2, by calc
    @T_isort _ _ d xs + @T_insort _ _ d hd (@insertion_sort _ _ d xs) + 1 ≤ (xs.length + 1) ^ 2 + @T_insort _ _ d hd (@insertion_sort _ _ d xs) + 1 : by simp [ih]
    ... ≤ (xs.length + 1) ^ 2 + ((@insertion_sort _ _ d xs).length + 1) + 1 : by simp [T_insort_length]
    ... = (xs.length + 1) ^ 2 + (xs.length + 1) + 1 : by simp [length_isort]
    ... = xs.length ^2 + 2 * xs.length + xs.length + 3 : by ring
    ... ≤ xs.length ^2 + 2 * xs.length + xs.length + xs.length + 3 : by simp 
    ... ≤ xs.length ^2 + 2 * xs.length + xs.length + xs.length + 4 : by simp 
    ... = (xs.length + 1 + 1) ^ 2 : by ring,
    }
end

end Insertion_sort

/- Quicksort
 -/

section Quicksort

def quicksort : list ℕ  → list ℕ    
| [] := []
| (x::xs) :=  have (list.filter (λ (y : ℕ), y < x) xs).sizeof < 1 + x + xs.sizeof, from sorry,
              have (list.filter (has_le.le x) xs).sizeof < 1 + x + xs.sizeof, from sorry,
              quicksort (xs.filter (λ y: ℕ  , y < x)) ++ [x] ++ quicksort (xs.filter (λ y: ℕ , y ≥ x))   

end Quicksort

#eval quicksort [3,2,1]

/- Top-Down Merge Sort-/

#eval merge (λ m n: ℕ, m < n) [1,3] [2,4]
#eval merge_sort (λ m n: ℕ , m < n) [2,1,4,3]

-- Functional Correctness

variable {α : Type*}
variable r: α → α → Prop
variables xs ys: list α 

lemma mset_merge [decidable_rel r]: (↑ (merge r xs ys): multiset α)  = ↑ xs + ↑ ys :=
begin
  simp,
  induction' xs,
  { induction' ys,
    { simp [merge]},
    simp [merge] },
  induction' ys,
  { simp [merge] },
  simp [merge],
  split_ifs,
  { simp [ih] },
  have h1: (∀ (r : α → α → Prop) (ys : list α) [_inst_1 : decidable_rel r], @merge _ r _inst_1 xs ys ~ xs ++ ys) → @merge _ r _inst_1 (hd :: xs) ys ~ hd :: xs ++ ys, from  @ih_ys r _inst_1 hd xs,  
  have h2: @merge _ r _inst_1 (hd :: xs) ys ~ (hd :: xs) ++ ys, from h1 ih, 
  simp [← list.cons_append] ,
  simp only [list.perm_cons_append_cons hd_1 h2],
end  
