import ring_theory.subring.basic
import mul_subgroup.adjoin
import ring_theory.ideal.local_ring
import ring_theory.integral_domain
import ring_theory.valuation.valuation_subring

namespace valuation_subring

variables {K : Type*} [field K]

lemma sub_mem (R : valuation_subring K) {x y : K} (hx : x ∈ R) (hy : y ∈ R) : 
  x - y ∈ R := 
R.to_subring.sub_mem hx hy

def units (R : valuation_subring K) : set Kˣ := 
{ u | (u : K) ∈ R ∧ (u⁻¹ : K) ∈ R }

lemma neg_mem_units (R : valuation_subring K) {x : Kˣ} (hx : x ∈ R.units) : 
  -x ∈ R.units := 
begin
  split, convert R.neg_mem _ hx.1, convert R.neg_mem _ hx.2, field_simp,
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
  split, push_cast, apply R.mul_mem _ _ hx.1 hy.1,
  simp only [units.coe_mul], rw mul_inv, apply R.mul_mem _ _ hx.2 hy.2, 
end

def nonunits (R : valuation_subring K) : set K :=
{ x | x ∈ R ∧ x ∉ (coe : Kˣ → K) '' R.units }

def principal_units (R : valuation_subring K) : set Kˣ := 
{ u | (u : K) - 1 ∈ R.nonunits }

end valuation_subring