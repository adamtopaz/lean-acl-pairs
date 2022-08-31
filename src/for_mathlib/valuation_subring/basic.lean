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

lemma neg_mem_units (R : valuation_subring K) {x : Kˣ} (hx : x ∈ R.unit_group) : 
  -x ∈ R.unit_group := 
begin
  change R.valuation _ = _,
  change R.valuation _ = _ at hx,
  simpa only [units.coe_hom_apply, units.coe_neg, valuation.map_neg] using hx,
end

lemma mem_unit_group_iff_mem_and_inv_mem (R : valuation_subring K) (u : Kˣ) : 
  u ∈ R.unit_group ↔ (u : K) ∈ R ∧ (u⁻¹ : K) ∈ R := 
begin
  split,
  { rintros (h : R.valuation u = 1), split, 
    rw ← valuation_subring.valuation_le_one_iff, apply le_of_eq, assumption,
    rw ← valuation_subring.valuation_le_one_iff, apply le_of_eq, simpa },
  { intros hh, sorry }
end

lemma mem_nonunits_iff_mem_and_nmem (R : valuation_subring K) (x : K) : 
  x ∈ R.nonunits ↔ x ∈ R ∧ x ∉ (coe : Kˣ → K) '' R.unit_group := sorry

lemma mem_principal_unit_group_iff_mem (R : valuation_subring K) (x : Kˣ) :
  x ∈ R.principal_unit_group ↔ (x : K) - 1 ∈ R.nonunits := sorry

end valuation_subring