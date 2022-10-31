import bridge_char
import rigid_elements.main
import for_mathlib.valuation_subring.basic

noncomputable theory
open_locale tensor_product
open_locale classical

open module

variables {K F : Type*} [field K] [field F] --[is_prime_field F]

open finite_dimensional

namespace main_theorem_mul_setup

lemma mk_rigid_pair 
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  rigid_pair (mul_subgroup.mk' T.restrict) (mul_subgroup.mk' T.nonrig.restrict) :=
begin
  let T' := mul_subgroup.mk' T.restrict,
  let H' := mul_subgroup.mk' T.nonrig.restrict,
  have hle' : T' ≤ H', 
  { intros t ht, 
    use T'.is_unit_of_mem ht,
    apply T.le_nonrig, 
    obtain ⟨u,hu⟩ := ht,
    exact hu },
  apply rigid_pair.mk_of_le T' H' hle',
  { refine ⟨(-1 : Kˣ).is_unit, _⟩,
    change _ ∈ T,
    rw [← T.dual_annihilator_dual_annihilator_comap, 
      submodule.mem_dual_annihilator_comap_iff],
    intros φ hφ,
    have := hT.neg_one φ hφ,
    convert this, ext, refl },
  { intros x hx hx', 
    have hx'' := hx',
    contrapose! hx',
    use is_unit.mk0 x hx,
    change _ ∈ T.nonrig, 
    dsimp [submodule.nonrig],
    rw submodule.mem_sup,
    refine ⟨0, T.zero_mem, (units.mk0 x hx).as, _, _⟩,
    { apply submodule.subset_span,  
      refine ⟨units.mk0 x hx,_,rfl⟩,
      dsimp [submodule.nonrig_condition],
      split,
      { contrapose! hx'',
        apply hle', use (is_unit.mk0 x hx), dsimp [submodule.restrict], 
        change _ ∈ T, convert hx'', ext, refl },
      { intros y hy, 
        rw ← hy at hx',
        have : ((units.mk0 x hx)⁻¹ : K) * y = x⁻¹ + 1,
        { field_simp [hy], },
        rw ← this at hx',
        cases hx' with hx'1 hx'2,
        split,
        { contrapose! hx'1, 
          use y.is_unit, change _ ∈ T, convert hx'1, ext, refl },
        { contrapose! hx'2, 
          use (units.mk0 x hx)⁻¹.is_unit.mul y.is_unit, 
          change _ ∈ T, convert hx'2, ext, refl } } },
    { rw zero_add, congr' 1, ext, refl } },
end

lemma mk_rigid_pair_char_two
  [is_prime_field F]
  (htwo : (2 : F) = 0)
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  rigid_pair (mul_subgroup.mk' T.restrict) (mul_subgroup.mk' T.restrict) :=
begin
  let T' := mul_subgroup.mk' T.restrict,
  have hneg1 : (-1 : K) ∈ T', 
  { refine ⟨(-1 : Kˣ).is_unit, _⟩,
    change _ ∈ T,
    rw [← T.dual_annihilator_dual_annihilator_comap, 
      submodule.mem_dual_annihilator_comap_iff],
    intros φ hφ,
    have := hT.neg_one φ hφ,
    convert this, ext, refl },
  apply rigid_pair.mk_of_le T' T' (le_refl _) hneg1,
  { intros x hx1 hx2,
    let y : Kˣ := units.mk0 x hx1,
    let z : Kˣ := units.mk0 (1 + x) _,
    have hh := submodule.dependent_of_acl _ hT (-y) z _,
    rw fintype.not_linear_independent_iff at hh,
    obtain ⟨g,h1,i,h2⟩ := hh,
    simp only [fin.sum_univ_succ, submodule.mkq_apply, matrix.cons_val_zero, 
      fintype.univ_of_subsingleton, fin.mk_zero, 
      matrix.cons_val_succ, finset.sum_singleton, fin.succ_zero_eq_one] at h1,
    let a := g 0,
    let b := g 1, 
    change a • _ + b • _ = _ at h1,
    cases eq_zero_or_one_of_is_prime_field_of_two _ htwo a with ha ha;
    cases eq_zero_or_one_of_is_prime_field_of_two _ htwo b with hb hb,
    { fin_cases i; contradiction, },
    { simp only [ha,hb, zero_smul, zero_add, one_smul, 
        submodule.quotient.mk_eq_zero] at h1, 
      left, rw submodule.dual_annihilator_dual_annihilator_comap at h1,
      use z.is_unit, change _ ∈ T, convert h1, ext, refl },
    { simp only [ha,hb, zero_smul, add_zero, one_smul, 
        submodule.quotient.mk_eq_zero] at h1, 
      exfalso,
      apply hx2, 
      rw submodule.dual_annihilator_dual_annihilator_comap at h1,
      rw (show x = (-1 : K) * (-x), by ring), apply T'.mul_mem hneg1,
      use (-y).is_unit, change _ ∈ T, convert h1, ext, refl },
    { simp only [ha,hb, one_smul, ← submodule.mkq_apply,
        ← linear_map.map_add, ← units.as_mul] at h1, 
      simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero,
        submodule.dual_annihilator_dual_annihilator_comap] at h1,
      right,
      have : (2 : F) • y.as = (0 : mul_base_change K F), 
      { rw [htwo, zero_smul], },
      rw [← sub_zero (-y * z).as,← this,(show (2 : F) = 1 + 1, by ring),
        add_smul, one_smul, ← units.as_mul, sub_eq_add_neg,
        ← units.as_inv, ← units.as_mul] at h1,
      rw (show (x⁻¹ + 1) = (-1) * (-(x⁻¹ + 1)), by ring),
      apply T'.mul_mem hneg1,
      have : -(x⁻¹ + 1) = ↑(-y * z * (y * y)⁻¹), 
      { push_cast, field_simp, 
        dsimp [z], ring },
      rw this,
      use (-y * z * (y * y)⁻¹).is_unit, change _ ∈ T, convert h1, ext, refl },
    { dsimp [y,z], ring, },
    { intro c, rw add_eq_zero_iff_neg_eq at c, rw c at hneg1,
      exact hx2 hneg1 } }
end

end main_theorem_mul_setup

theorem main_theorem_mul_char_ne_two 
  [is_prime_field F]
  (htwo : (2 : F) ≠ 0)
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  ∃ (R : valuation_subring K)
    (H : submodule F (mul_base_change K F))
    (hTH : T ≤ H)
    (units : ∀ u : Kˣ, u ∈ R.unit_group → u.as ∈ H)
    (principal_units : ∀ u : Kˣ, u ∈ R.principal_unit_group → u.as ∈ T)
    (fd : finite_dimensional F (↥H ⧸ T.comap H.subtype)),
    finrank F (↥H ⧸ T.comap H.subtype) ≤ 1 := 
begin
  let T' := mul_subgroup.mk' T.restrict,
  let H' := mul_subgroup.mk' T.nonrig.restrict,
  let P : rigid_pair T' H' := main_theorem_mul_setup.mk_rigid_pair T hT,
  obtain ⟨t,ht1,ht2,ht3⟩ := P.exists_preadditive,
  let t' : Kˣ := units.mk0 t ht1,
  let E := T.nonrig ⊔ (submodule.span F ({t'.as} : set (mul_base_change K F))),
  have hE : E = T.nonrig,
  { suffices : (submodule.span F ({t'.as} : set (mul_base_change K F))) ≤ T.nonrig,
    { dsimp [E], exact sup_eq_left.mpr this, },
    rw [submodule.span_le, set.singleton_subset_iff],
    change t'.as ∈ T.nonrig,
    suffices : (2 : F) • t'.as ∈ T.nonrig,
    { convert T.nonrig.smul_mem ((2 : F)⁻¹) this using 1,
      rw [← mul_smul, inv_mul_cancel htwo, one_smul] },
    rw [(show (2 : F) = 1 + 1, by ring), add_smul, one_smul, ← units.as_mul],
    obtain ⟨u,hu⟩ := ht2, convert hu, ext, refl },
  let P' : rigid_pair T' (H'.adjoin_ne_zero t ht1) := _,
  change rigid_pair.preadditive P' at ht3,
  let R := ht3.valuation_subring,
  use [R, T.nonrig, T.le_nonrig],
  refine ⟨_,_,_,_⟩,
  { intros u hu, 
    rw ← hE,
    suffices : H'.adjoin_ne_zero t ht1 ≤ mul_subgroup.mk' E.restrict,
    { have hh := ht3.mem_of_mem_units u hu,
      change u ∈ E.restrict,
      suffices : (u : K) ∈ mul_subgroup.mk' E.restrict,
      { obtain ⟨h1,h2⟩ := this, 
        convert h2, ext, refl },
      exact this hh, },
    apply mul_subgroup.adjoin_ne_zero_le,
    { intros u hu,  
      use H'.is_unit_of_mem hu,
      apply submodule.mem_sup_left,
      obtain ⟨v,hv⟩ := hu,
      exact hv },
    { use is_unit.mk0 t ht1, 
      apply submodule.mem_sup_right,
      convert submodule.mem_span_singleton_self _, ext, refl } },
  { intros u hu, 
    have := ht3.mem_of_mem_principal_units u hu,
    obtain ⟨v,hv⟩ := this, 
    convert hv, ext, refl },
  { apply bridge_finite_dimensional _ hT },
  { apply bridge_codim _ hT },
end

theorem main_theorem_mul_char_two 
  [is_prime_field F]
  (htwo : (2 : F) = 0)
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  ∃ (R : valuation_subring K)
    (H : submodule F (mul_base_change K F))
    (hTH : T ≤ H)
    (units : ∀ u : Kˣ, u ∈ R.unit_group → u.as ∈ H)
    (principal_units : ∀ u : Kˣ, u ∈ R.principal_unit_group → u.as ∈ T)
    (fd : finite_dimensional F (↥H ⧸ T.comap H.subtype)),
    finrank F (↥H ⧸ T.comap H.subtype) ≤ 1 := 
begin
  let T' := mul_subgroup.mk' T.restrict,
  let P : rigid_pair T' T' := 
    main_theorem_mul_setup.mk_rigid_pair_char_two htwo T hT,
  obtain ⟨t,ht1,ht2,ht3⟩ := P.exists_preadditive,
  let t' : Kˣ := units.mk0 t ht1,
  let P' : rigid_pair T' (T'.adjoin_ne_zero t ht1) := _,
  change rigid_pair.preadditive P' at ht3,
  let R := ht3.valuation_subring, use R,
  let H := T ⊔ (submodule.span F ({t'.as} : set (mul_base_change K F))),
  have hfd : finite_dimensional F (↥H ⧸ (T.comap H.subtype)), 
  { let e := (T.comap H.subtype).mkq.comp (submodule.of_le (le_sup_right : _ ≤ T ⊔ _)),
    have he : function.surjective e, 
    { apply submodule.mkq_comp_sup_mod_surjective },
    apply e.finite_dimensional_of_surjective, rwa linear_map.range_eq_top },
  use [H, le_sup_left],
  refine ⟨_,_,_,_⟩,
  { intros u hu,
    have hh := ht3.mem_of_mem_units u hu,
    suffices : T'.adjoin_ne_zero t ht1 ≤ mul_subgroup.mk' H.restrict,
    { replace hh := this hh, 
      obtain ⟨v,hv⟩ := hh,
      convert hv, ext, refl },
    apply mul_subgroup.adjoin_ne_zero_le,
    { intros u hu, use T'.is_unit_of_mem hu, change _ ∈ H,
      apply submodule.mem_sup_left, obtain ⟨v,hv⟩ := hu, exact hv },
    { use t'.is_unit,
      apply submodule.mem_sup_right,
      convert submodule.mem_span_singleton_self _, ext, refl } },
  { intros u hu, 
    have := ht3.mem_of_mem_principal_units u hu,
    obtain ⟨v,hv⟩ := this,
    convert hv, ext, refl },
  { exact hfd },
  { by_cases htT : t ∈ T', 
    { have : H = T, 
      { erw [sup_eq_left],
        rw submodule.span_singleton_le_iff_mem, obtain ⟨v,hv⟩ := htT, convert hv, ext, refl },
      rw this at hfd ⊢, resetI, rw finrank_le_one_iff, use 0, rintros ⟨w,hw⟩, use 0,
      symmetry,
      simp, },
    apply submodule.finrank_le_one_of_not_linear_independent T {t'.as} t'.as 
      (set.mem_singleton (units.as t')), 
    { contrapose! htT, 
      use t'.is_unit, change _ ∈ T, convert htT, ext, refl },
    { rintros v (rfl : v = t'.as), 
      rw fintype.not_linear_independent_iff, use ![1,-1],
      split, { simp [fin.sum_univ_succ] }, { use 0, norm_num } } },
end

theorem main_theorem_mul
  [is_prime_field F]
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  ∃ (R : valuation_subring K)
    (H : submodule F (mul_base_change K F))
    (hTH : T ≤ H)
    (units : ∀ u : Kˣ, u ∈ R.unit_group → u.as ∈ H)
    (principal_units : ∀ u : Kˣ, u ∈ R.principal_unit_group → u.as ∈ T)
    (fd : finite_dimensional F (↥H ⧸ T.comap H.subtype)),
    finrank F (↥H ⧸ T.comap H.subtype) ≤ 1 := 
begin
  by_cases htwo : (2 : F) = 0,
  apply main_theorem_mul_char_two, assumption',
  apply main_theorem_mul_char_ne_two, assumption'
end

theorem main_theorem_mul_char
  (p ℓ : ℕ)
  [fact (nat.prime p)]
  (HH : p ≠ ℓ)
  [char_p K p]
  [char_p F ℓ]
  (htwo : (2 : F) ≠ 0)
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  ∃ (R : valuation_subring K)
    (H : submodule F (mul_base_change K F))
    (hTH : T ≤ H)
    (units : ∀ u : Kˣ, u ∈ R.unit_group → u.as ∈ H)
    (principal_units : ∀ u : Kˣ, u ∈ R.principal_unit_group → u.as ∈ T)
    (fd : finite_dimensional F (↥H ⧸ T.comap H.subtype)),
    finrank F (↥H ⧸ T.comap H.subtype) ≤ 1 := 
begin
  let T' := mul_subgroup.mk' T.restrict,
  let H' := mul_subgroup.mk' T.nonrig.restrict,
  let P : rigid_pair T' H' := main_theorem_mul_setup.mk_rigid_pair T hT,
  obtain ⟨t,ht1,ht2,ht3⟩ := P.exists_preadditive,
  let t' : Kˣ := units.mk0 t ht1,
  let E := T.nonrig ⊔ (submodule.span F ({t'.as} : set (mul_base_change K F))),
  have hE : E = T.nonrig,
  { suffices : (submodule.span F ({t'.as} : set (mul_base_change K F))) ≤ T.nonrig,
    { dsimp [E], exact sup_eq_left.mpr this, },
    rw [submodule.span_le, set.singleton_subset_iff],
    change t'.as ∈ T.nonrig,
    suffices : (2 : F) • t'.as ∈ T.nonrig,
    { convert T.nonrig.smul_mem ((2 : F)⁻¹) this using 1,
      rw [← mul_smul, inv_mul_cancel htwo, one_smul] },
    rw [(show (2 : F) = 1 + 1, by ring), add_smul, one_smul, ← units.as_mul],
    obtain ⟨u,hu⟩ := ht2, convert hu, ext, refl },
  let P' : rigid_pair T' (H'.adjoin_ne_zero t ht1) := _,
  change rigid_pair.preadditive P' at ht3,
  let R := ht3.valuation_subring,
  use [R, T.nonrig, T.le_nonrig],
  refine ⟨_,_,_,_⟩,
  { intros u hu, 
    rw ← hE,
    suffices : H'.adjoin_ne_zero t ht1 ≤ mul_subgroup.mk' E.restrict,
    { have hh := ht3.mem_of_mem_units u hu,
      change u ∈ E.restrict,
      suffices : (u : K) ∈ mul_subgroup.mk' E.restrict,
      { obtain ⟨h1,h2⟩ := this, 
        convert h2, ext, refl },
      exact this hh, },
    apply mul_subgroup.adjoin_ne_zero_le,
    { intros u hu,  
      use H'.is_unit_of_mem hu,
      apply submodule.mem_sup_left,
      obtain ⟨v,hv⟩ := hu,
      exact hv },
    { use is_unit.mk0 t ht1, 
      apply submodule.mem_sup_right,
      convert submodule.mem_span_singleton_self _, ext, refl } },
  { intros u hu, 
    have := ht3.mem_of_mem_principal_units u hu,
    obtain ⟨v,hv⟩ := this, 
    convert hv, ext, refl },
  { apply bridge_char_finite_dimensional p ℓ HH _ hT },
  { apply bridge_char_codim p ℓ HH _ hT },
end