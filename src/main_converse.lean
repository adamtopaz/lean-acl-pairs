import recover

-- We are given two fields, `K` and `F`
variables {K F : Type*} [field K] [field F] 

open module finite_dimensional 
open_locale tensor_product

/-
NOTE: This introduces notation `[a]ₘ` for `a : Kˣ`, where `[a]ₘ` is the element of
the base-change `F ⊗[ℤ] (additive Kˣ)` corresponding to `a`. 
-/
notation `[`:max a`]ₘ`:max := 1 ⊗ₜ (additive.of_mul a)

lemma one_tmul_mul (a b : Kˣ) : ([a * b]ₘ : F ⊗[ℤ] additive Kˣ) = 
  [a]ₘ + [b]ₘ := 
tensor_product.tmul_add _ _ _

lemma one_tmul_inv (a : Kˣ) : ([a⁻¹]ₘ : F ⊗[ℤ] additive Kˣ) = - [a]ₘ :=
tensor_product.tmul_neg _ _

/-
We consider the weak topology on `dual F (F ⊗[ℤ] additive Kˣ)`. 
This is just the pointwise convergence topology, i.e. the topology
induced by the product topology on the type of functions `F ⊗[ℤ] additive Kˣ → F` 
where `F` is given the discrete topology.
-/
def module.dual.weak_topology : 
  topological_space (dual F (F ⊗[ℤ] additive Kˣ)) := 
topological_space.induced (λ e a, e a) $ 
(@Pi.topological_space (F ⊗[ℤ] additive Kˣ) (λ _, F) $ λ a, ⊥)

/-
We only activate this topological space instance for this file.
-/
local attribute [instance] 
  module.dual.weak_topology

/- 
The converse to the main theorem about alternating pairs. 
This is a simple result, and we prove it without many dependencies from the imports.
-/
theorem valuation_implies_alternating
  -- Given submodules `I` and `D` of `dual F (F ⊗[ℤ] additive Kˣ)` 
  (D I : submodule F (dual F (F ⊗[ℤ] additive Kˣ))) 
  -- which are closed with respect to the topology mentioned above,
  (hDclosed : is_closed (D : set (dual F (F ⊗[ℤ] additive Kˣ))))
  (hIclosed : is_closed (I : set (dual F (F ⊗[ℤ] additive Kˣ))))
  -- and a valuation ring of `K`
  (R : valuation_subring K)
  -- satisfying (1) `I ≤ D`;
  (le : I ≤ D)
  -- (2) the elements of `D` act trivially on `-1 : Kˣ`;
  (hnegone : ∀ (f : dual F (F ⊗[ℤ] additive Kˣ)) (hf : f ∈ D), f [-1]ₘ = 0) 
  -- (3) the elements of `I` act trivially on the units of `R`;
  (units : ∀ (u : Kˣ) (hu : u ∈ R.unit_group) 
    (f : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ I), f [u]ₘ = 0)
  -- (4) the elements of `D` act trivially on the principal units of `R`;
  (punits : ∀ (u : Kˣ) (hu : u ∈ R.principal_unit_group) 
    (f : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ D), f [u]ₘ = 0)
  -- (5) `D/I` is finite dimensional;
  (fd : finite_dimensional F (↥D ⧸ I.comap D.subtype))
  -- (6) and `I` has codimension at most `1` in `D`,
  (codim : finrank F (↥D ⧸ I.comap D.subtype) ≤ 1) :
  -- then any pair of elements of `D` satisfies the alternating condition.
  ∀ (u v : Kˣ) (huv : (u : K) + v = 1) 
    (f g : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ D) (hg : g ∈ D), 
    f [u]ₘ * g [v]ₘ = f [v]ₘ * g [u]ₘ := 
begin
  intros u v huv f g hf hg,
  resetI, rw finrank_le_one_iff at codim,
  obtain ⟨⟨e,he⟩,hhe⟩ := codim, 
  let f' : D := ⟨f,hf⟩,
  let g' : D := ⟨g,hg⟩,
  obtain ⟨cf,hcf⟩ := hhe (submodule.mkq _ f'),
  obtain ⟨cg,hcg⟩ := hhe (submodule.mkq _ g'),
  simp only [submodule.quotient.quot_mk_eq_mk, ← submodule.mkq_apply] at hcf hcg,
  rw [← sub_eq_zero, ← linear_map.map_smul, ← linear_map.map_sub,
    submodule.mkq_apply, submodule.quotient.mk_eq_zero] at hcf hcg,
  simp only [submodule.mem_comap, submodule.coe_subtype, submodule.coe_sub, 
    submodule.coe_smul_of_tower, submodule.coe_mk] at hcg hcf,
  have hfI : ∀ (t : Kˣ) (ht : t ∈ R.unit_group), f [t]ₘ = cf • e [t]ₘ, 
  { intros t ht, symmetry, rw ← sub_eq_zero, 
    rw [← linear_map.smul_apply, ← linear_map.sub_apply], exact units t ht _ hcf },
  have hgI : ∀ (t : Kˣ) (ht : t ∈ R.unit_group), 
    g [t]ₘ = cg • e [t]ₘ, 
  { intros t ht, symmetry, rw ← sub_eq_zero, 
    rw [← linear_map.smul_apply, ← linear_map.sub_apply], exact units t ht _ hcg },
  by_cases hunituv : u ∈ R.unit_group ∧ v ∈ R.unit_group,
  { cases hunituv with huu hvu,
    rw [hfI _ huu, hgI _ huu, hfI _ hvu, hgI _ hvu],
    simp_rw [smul_eq_mul], ring },
  push_neg at hunituv,
  by_cases huu : u ∈ R.unit_group,
  { have hvu : u ∈ R.principal_unit_group, 
    { rw valuation_subring.mem_principal_unit_group_iff_mem,
      rw valuation_subring.mem_nonunits_iff_mem_and_nmem,
      rw valuation_subring.mem_unit_group_iff_mem_and_inv_mem at huu,
      split, exact R.sub_mem huu.1 R.one_mem,
      intro c, apply hunituv _, 
      swap, rwa valuation_subring.mem_unit_group_iff_mem_and_inv_mem,
      obtain ⟨w,hw⟩ := c, convert R.neg_mem_units hw.1, 
      ext, push_cast, rw hw.2, rw neg_sub, convert (congr_arg (λ e : K, e - u) huv), ring },
    rw [punits u hvu f hf, punits u hvu g hg, zero_mul, mul_zero] },
  rw valuation_subring.mem_unit_group_iff_mem_and_inv_mem at huu, push_neg at huu,
  by_cases huR : (u : K) ∈ R, 
  { have hvu : v ∈ R.principal_unit_group, 
    { rw valuation_subring.mem_principal_unit_group_iff_mem,
      rw valuation_subring.mem_nonunits_iff_mem_and_nmem,
      split, convert R.neg_mem _ huR, rwa [sub_eq_iff_eq_add, eq_neg_add_iff_add_eq],
      intro c, apply huu huR, obtain ⟨w,hw⟩ := c, 
      have := (R.neg_mem_units hw.1), rw valuation_subring.mem_unit_group_iff_mem_and_inv_mem at this,
      convert this.2,
      ext, push_cast, rwa [hw.2, neg_sub, eq_sub_iff_add_eq] },
    rw [punits v hvu f hf, punits v hvu g hg, zero_mul, mul_zero] },
  { have huu : (u : K)⁻¹ ∈ R, 
    { cases R.mem_or_inv_mem (u : K), contradiction, assumption },
    have huz : (u : K) ≠ 0, 
    { intro c, apply huR, rw c, apply R.zero_mem },
    have huv' : -(u⁻¹ * v) ∈ R.principal_unit_group, 
    { rw valuation_subring.mem_principal_unit_group_iff_mem,
      rw valuation_subring.mem_nonunits_iff_mem_and_nmem,
      split, push_cast, rw ← neg_add', apply R.neg_mem, 
      have : (u : K) + v ∈ R, rw huv, apply R.one_mem,
      convert R.mul_mem _ _ huu this, field_simp, ring,
      intro c, apply huR, 
      obtain ⟨w,hw1,hw2⟩ := c, push_cast at hw2, field_simp at hw2,
      rw [← neg_add', add_comm, huv] at hw2,
      have : (w : K) * u ∈ R, rw hw2, apply R.neg_mem, apply R.one_mem,
      erw valuation_subring.mem_unit_group_iff_mem_and_inv_mem at hw1,
      convert R.mul_mem _ _ this hw1.2, field_simp [w.ne_zero], ring },
    have hfuv : f [u]ₘ = f [v]ₘ, 
    { symmetry, rw [← sub_eq_zero, ← f.map_sub, sub_eq_add_neg, ← one_tmul_inv,
        ← one_tmul_mul, mul_comm],
      have := punits _ huv' f hf, 
      rwa [neg_eq_neg_one_mul, one_tmul_mul, f.map_add, hnegone f hf, zero_add] at this },
    have hguv : g [u]ₘ = g [v]ₘ, 
    { symmetry, rw [← sub_eq_zero, ← g.map_sub, sub_eq_add_neg, ← one_tmul_inv,
        ← one_tmul_mul, mul_comm],
      have := punits _ huv' g hg, 
      rwa [neg_eq_neg_one_mul, one_tmul_mul, g.map_add, hnegone g hg, zero_add] at this },
    simp only [hfuv, hguv, mul_comm] }
end