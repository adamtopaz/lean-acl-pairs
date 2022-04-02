import ring_theory.subring.basic
import mul_subgroup.adjoin
import ring_theory.ideal.local_ring
import ring_theory.integral_domain

structure valuation_subring (K : Type*) [field K] extends subring K :=
(mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier)

namespace valuation_subring

variables {K : Type*} [field K]

instance : set_like (valuation_subring K) K := 
{ coe := λ R, R.carrier,
  coe_injective' := begin
    intros R S h,
    cases R with R _, cases S with S _, 
    congr,
    ext x,
    dsimp at h,
    change (x ∈ R.carrier ↔ x ∈ S.carrier),
    rw h,
  end }

lemma one_mem (R : valuation_subring K) : (1 : K) ∈ R := 
R.to_subring.one_mem

lemma zero_mem (R : valuation_subring K) : (0 : K) ∈ R := 
R.to_subring.zero_mem

lemma neg_mem (R : valuation_subring K) {x : K} (hx : x ∈ R) : -x ∈ R := 
R.to_subring.neg_mem hx

lemma sub_mem (R : valuation_subring K) {x y : K} (hx : x ∈ R) (hy : y ∈ R) : 
  x - y ∈ R := 
R.to_subring.sub_mem hx hy

lemma mul_mem (R : valuation_subring K) {x y : K} (hx : x ∈ R) (hy : y ∈ R) : 
  x * y ∈ R := 
R.to_subring.mul_mem hx hy

lemma mem_or_inv_mem (R : valuation_subring K) (x : K) : 
  x ∈ R ∨ x⁻¹ ∈ R := 
R.mem_or_inv_mem' x

instance (R : valuation_subring K) : comm_ring R := 
show comm_ring R.to_subring, by apply_instance

instance (R : valuation_subring K) : is_domain R :=
show is_domain R.to_subring, by apply_instance

def units (R : valuation_subring K) : set Kˣ := 
{ u | (u : K) ∈ R ∧ (u⁻¹ : K) ∈ R }

lemma neg_mem_units (R : valuation_subring K) {x : Kˣ} (hx : x ∈ R.units) : 
  -x ∈ R.units := 
begin
  split, convert R.neg_mem hx.1, convert R.neg_mem hx.2, field_simp,
end

lemma one_mem_units (R : valuation_subring K) : (1 : Kˣ) ∈ R.units := 
begin
  split,
  exact R.one_mem,
  convert R.one_mem, simp,
end

lemma mul_mem_units (R : valuation_subring K) {x y : Kˣ} 
  (hx : x ∈ R.units) (hy : y ∈ R.units) :
  x * y ∈ R.units := 
begin
  split, push_cast, apply R.mul_mem hx.1 hy.1,
  simp only [units.coe_mul], rw mul_inv₀, apply R.mul_mem hx.2 hy.2, 
end

def nonunits (R : valuation_subring K) : set K :=
{ x | x ∈ R ∧ x ∉ (coe : Kˣ → K) '' R.units }

def principal_units (R : valuation_subring K) : set Kˣ := 
{ u | (u : K) - 1 ∈ R.nonunits }

end valuation_subring