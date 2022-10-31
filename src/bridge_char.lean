import bridge
import algebra.char_zero
import algebra.char_p

noncomputable theory
open_locale tensor_product
open_locale classical

open module

variables {K F : Type*} [field K] [field F] 
variables (p : ℕ) [fact (nat.prime p)] 

theorem bridge_char
  [char_zero F]
  [char_p K p]
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
  exact (fact.out (nat.prime p)).ne_zero key,
end

