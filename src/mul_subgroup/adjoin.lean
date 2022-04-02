import mul_subgroup.basic

/-! Adjoining an element to a multiplicative subgroup. -/

variables {K : Type*} [field K]

namespace mul_subgroup

inductive adjoin_is_unit_carrier (T : mul_subgroup K) (x : K) (hx : is_unit x) : set K
| base (a : K) : a ∈ T → adjoin_is_unit_carrier a 
| of : adjoin_is_unit_carrier x 
| mul (a b : K) : adjoin_is_unit_carrier a → adjoin_is_unit_carrier b → adjoin_is_unit_carrier (a * b)
| inv (a : K) : adjoin_is_unit_carrier a → adjoin_is_unit_carrier (a⁻¹)

def adjoin_is_unit (T : mul_subgroup K) (x : K) (hx : is_unit x) : mul_subgroup K :=
{ carrier := T.adjoin_is_unit_carrier x hx,
  mul_mem' := λ a b ha hb, adjoin_is_unit_carrier.mul _ _ ha hb,
  inv_mem' := λ a ha, adjoin_is_unit_carrier.inv _ ha,
  one_mem' := adjoin_is_unit_carrier.base _ T.one_mem,
  is_unit' := begin
    intros a ha,
    induction ha, 
    { apply T.is_unit_of_mem, assumption },
    { assumption },
    { apply is_unit.mul, assumption' },
    { rw is_unit_iff_ne_zero at *, apply inv_ne_zero, assumption } 
  end }

def adjoin_ne_zero (T : mul_subgroup K) (x : K) (hx : x ≠ 0) : mul_subgroup K :=
T.adjoin_is_unit x (is_unit.mk0 _ hx)

lemma mem_adjoin_is_unit_of_mem (T : mul_subgroup K) (x : K) (hx : is_unit x) (a : K) (ha : a ∈ T) : 
  a ∈ T.adjoin_is_unit x hx := adjoin_is_unit_carrier.base _ ha 

lemma mem_adjoin_is_unit_self (T : mul_subgroup K) (x : K) (hx : is_unit x) :
  x ∈ T.adjoin_is_unit x hx := adjoin_is_unit_carrier.of

lemma mem_adjoin_ne_zero_of_mem (T : mul_subgroup K) (x : K) (hx : x ≠ 0) (a : K) (ha : a ∈ T) : 
  a ∈ T.adjoin_ne_zero x hx := T.mem_adjoin_is_unit_of_mem _ _ _ ha

lemma mem_adjoin_ne_zero_self (T : mul_subgroup K) (x : K) (hx : x ≠ 0) :
  x ∈ T.adjoin_ne_zero x hx := T.mem_adjoin_is_unit_self _ _

lemma le_adjoin_is_unit (T : mul_subgroup K) (x : K) (hx : is_unit x) : 
  T ≤ T.adjoin_is_unit x hx := T.mem_adjoin_is_unit_of_mem _ _

lemma le_adjoin_ne_zero (T : mul_subgroup K) (x : K) (hx : x ≠ 0) :
  T ≤ T.adjoin_ne_zero x hx := T.mem_adjoin_ne_zero_of_mem _ _

lemma adjoin_ne_zero_eq_of_mem (T : mul_subgroup K) (x : K) (hx : x ≠ 0) 
  (h : x ∈ T) : T.adjoin_ne_zero x hx = T := 
begin
  ext t,
  split,
  { intro h, induction h, assumption, assumption, apply mul_mem, assumption', 
    apply inv_mem, assumption },
  { intros h, apply adjoin_is_unit_carrier.base, assumption }
end

lemma adjoin_ne_zero_le (T H : mul_subgroup K) (x : K) (hx : x ≠ 0) :
  T ≤ H → x ∈ H → T.adjoin_ne_zero x hx ≤ H := 
begin
  intros h1 h2 t ht,
  induction ht, 
  apply h1, assumption,
  assumption,
  apply H.mul_mem, assumption',
  apply H.inv_mem, assumption
end

inductive adjoin_carrier (T : mul_subgroup K) (S : set K) (hS : ∀ (s : K) (hs : s ∈ S), is_unit s) : set K
| base (a : K) : a ∈ T → adjoin_carrier a 
| of (s : K) (hs : s ∈ S) : adjoin_carrier s 
| mul (a b : K) : adjoin_carrier a → adjoin_carrier b → adjoin_carrier (a * b)
| inv (a : K) : adjoin_carrier a → adjoin_carrier (a⁻¹)

def adjoin (T : mul_subgroup K) (S : set K) (hS : ∀ (s : K) (hs : s ∈ S), is_unit s) : mul_subgroup K := 
{ carrier := T.adjoin_carrier S hS,
  mul_mem' := λ x y hx hy, adjoin_carrier.mul _ _ hx hy,
  inv_mem' := λ x hx, adjoin_carrier.inv _ hx,
  one_mem' := adjoin_carrier.base _ T.one_mem,
  is_unit' := begin
    intros x hx, induction hx,
    { apply T.is_unit_of_mem, assumption },
    { apply hS, assumption },
    { apply is_unit.mul, assumption' },
    { rw is_unit_iff_ne_zero at *, apply inv_ne_zero, assumption }
  end }

def adjoin0 (T : mul_subgroup K) (S : set K) (hS : ∀ (s : K) (hs : s ∈ S), s ≠ 0) :
  mul_subgroup K :=
T.adjoin S $ λ s h, is_unit_iff_ne_zero.mpr (hS _ h)


end mul_subgroup