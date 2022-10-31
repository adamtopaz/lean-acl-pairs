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

