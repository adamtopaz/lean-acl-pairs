import bridge
import algebra.char_zero
import algebra.char_p

noncomputable theory
open_locale tensor_product
open_locale classical

open module

variables {K F : Type*} [field K] [field F] 
variables (p ℓ : ℕ) [fact (nat.prime p)] 

theorem bridge_char
  [char_p K p]
  [char_p F ℓ]
  (HH : p ≠ ℓ)
  (H : submodule F (mul_base_change K F))
  (hH : H.dual_annihilator.acl)
  (u v : Kˣ)
  (hu : u.as ∉ H) (hv : v.as ∉ H)
  (hu₁ : ∀ y : Kˣ, (y : K) = 1 + u → y.as ∉ H)
  (hu₂ : ∀ y : Kˣ, (y : K) = 1 + u → (u⁻¹ * y).as ∉ H)
  (hv₁: ∀ y : Kˣ, (y : K) = 1 + v → y.as ∉ H)
  (hv₂ : ∀ y : Kˣ, (y : K) = 1 + v → (v⁻¹ * y).as ∉ H) : 
  ¬ linear_independent F ![H.mkq u.as, H.mkq v.as] := 
begin
  intro c,
  let S : bridge.setup H hH := ⟨u,v,hu,hv,hu₁,hu₂,hv₁,hv₂,c⟩,
  let E := S.make,
  --obtain ⟨m,n,hn,hh⟩ := is_prime_field.cond (1 - S.A),
  have key := E.main_theorem_char (p+1) (by simp),
  push_cast at key,
  have : (p : K) = 0 := char_p.cast_eq_zero _ _, 
  simp only [this, zero_add, sub_self, one_mul] at key,
  rw S.φ_map_u at key,
  replace key := projectivization.affine_embedding_injective _ _ key,
  simp only [prod.mk.inj_iff, self_eq_add_left, nat.cast_eq_zero, eq_self_iff_true, and_true] at key,
  apply HH,
  erw char_p.cast_eq_zero_iff F ℓ at key,
  by_cases hℓ : ℓ = 0,
  { rw hℓ at key, simp only [zero_dvd_iff] at key, rwa hℓ },
  { have : nat.prime ℓ, 
    { cases char_p.char_is_prime_or_zero F ℓ, { exact h }, exact false.elim (hℓ h) },
    rw nat.dvd_prime at key, cases key,
    { have := nat.prime.ne_one this, exact false.elim (this key) },
    { exact key.symm },
    exact fact.out _ },
end

lemma bridge_char_finite_dimensional
  [char_p K p]
  [char_p F ℓ]
  (HH : p ≠ ℓ)
  (T : submodule F (mul_base_change K F))
  (hT : T.dual_annihilator.acl) : 
  finite_dimensional F (T.nonrig ⧸ T.comap T.nonrig.subtype) := 
begin
  by_cases hh : ∃ (u : Kˣ), T.nonrig_condition u,
  swap, 
  { push_neg at hh, 
    have : set_of T.nonrig_condition = ∅,
    { rw set.eq_empty_iff_forall_not_mem,  
      exact hh },
    dsimp [submodule.nonrig],
    rw [this, set.image_empty],
    have he := submodule.mkq_comp_sup_mod_surjective (submodule.span F ∅) T,
    let e : _ →ₗ[_] _ := _, change function.surjective e at he,
    haveI : finite_dimensional F (submodule.span F (∅ : set (mul_base_change K F))), 
    { apply finite_dimensional.span_of_finite, exact set.finite_empty },
    apply e.finite_dimensional_of_surjective,
    rwa linear_map.range_eq_top },
  obtain ⟨u,hu⟩ := hh,
  apply T.finite_dimensional_of_not_linear_independent 
    (units.as '' set_of T.nonrig_condition) u.as ⟨u,hu,rfl⟩ hu.1,
  rintros a ⟨a,ha,rfl⟩,
  apply bridge_char p ℓ HH T hT a u ha.1 hu.1 
    (λ y hy, (ha.2 y hy).1)
    (λ y hy, (ha.2 y hy).2)
    (λ y hy, (hu.2 y hy).1)
    (λ y hy, (hu.2 y hy).2)
end

theorem bridge_char_codim 
  [char_p K p]
  [char_p F ℓ]
  (HH : p ≠ ℓ)
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  finite_dimensional.finrank F (T.nonrig ⧸ T.comap T.nonrig.subtype) ≤ 1 := 
begin
  have fd : finite_dimensional F (T.nonrig ⧸ T.comap T.nonrig.subtype) := 
    bridge_char_finite_dimensional p ℓ HH T hT,
  by_cases hh : ∃ (u : Kˣ), T.nonrig_condition u,
  swap,
  { push_neg at hh, 
    have : set_of T.nonrig_condition = ∅,
    { rw set.eq_empty_iff_forall_not_mem,  
      exact hh },
    dsimp [submodule.nonrig] at *,
    rw [this, set.image_empty] at *,
    have he := submodule.mkq_comp_sup_mod_surjective (submodule.span F ∅) T,
    resetI,
    rw finrank_le_one_iff,
    use 0, rintros ⟨w,hw⟩, use 0, rw submodule.mem_sup at hw,
    obtain ⟨y,hy,z,hz,rfl⟩ := hw,
    simp only [submodule.span_empty, submodule.mem_bot] at hz,
    symmetry,
    simpa only [hz, add_zero, submodule.quotient.quot_mk_eq_mk, smul_zero, 
      submodule.quotient.mk_eq_zero] },
  obtain ⟨u,hu⟩ := hh,
  apply T.finrank_le_one_of_not_linear_independent 
    (units.as '' set_of T.nonrig_condition) u.as ⟨u,hu,rfl⟩ hu.1,
  rintros a ⟨a,ha,rfl⟩,
  apply bridge_char p ℓ HH T hT a u ha.1 hu.1 
    (λ y hy, (ha.2 y hy).1)
    (λ y hy, (ha.2 y hy).2)
    (λ y hy, (hu.2 y hy).1)
    (λ y hy, (hu.2 y hy).2)
end