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

-- We give ourselves to natural numbers, `p` and `ℓ`, with `p` being prime.
variables (p ℓ : ℕ) [fact (nat.prime p)]
-- Assume that `K` has characteristic `p`.
variable [char_p K p]
-- Assume that `F` satisfies `[char_p F ℓ]`.
-- NB: If `ℓ = 0`, this is *weaker* than the assumption that `F` has characteristic zero.
-- See the docstring for the `char_p` for more information.
variable [char_p F ℓ]

/- The main theorem of alternating pairs (positive characteristic case). -/
theorem main_alternating_theorem_pos_char 
  -- Assume that `p` and `ℓ` are different
  (HH : p ≠ ℓ)
  -- and that 2 is invertible in `F`.
  (htwo : (2 : F) ≠ 0)
  -- Given a submodule `D` of `dual F (F ⊗[ℤ] additive Kˣ)`,
  (D : submodule F (dual F (F ⊗[ℤ] additive Kˣ))) 
  -- which is: (1) closed with respect to the topology introduced above; 
  (h1 : is_closed (D : set (dual F (F ⊗[ℤ] additive Kˣ))))
  -- (2) every element of `D` maps `[(-1 : Kˣ)]ₘ` to zero;
  (h2 : ∀ (f : dual F (F ⊗[ℤ] additive Kˣ)) (hf : f ∈ D), f [-1]ₘ = 0) 
  -- (3) satisfies the alternating condition, i.e. whenever `u v : Kˣ` satisfy
  -- `(u : K) + v = 1`, then `f [u]ₘ * g [v]ₘ = f [v]ₘ * g [u]ₘ`.
  (h3 : ∀ (u v : Kˣ) (huv : (u : K) + v = 1) 
    (f g : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ D) (hg : g ∈ D), 
    f [u]ₘ * g [v]ₘ = f [v]ₘ * g [u]ₘ) : 
  -- Then there exists a valuation subring `R` of `K`, 
  ∃ (R : valuation_subring K)
  -- and another submodule `I` of `dual F (F ⊗[ℤ] additive Kˣ)` 
    (I : submodule F (dual F (F ⊗[ℤ] additive Kˣ)))
    -- which is closed, and such that the following hold:
    (Iclosed : is_closed (I : set (dual F (F ⊗[ℤ] additive Kˣ))))
    -- (1) `I` is contained in `D`;
    (le : I ≤ D)
    -- (2) the elements `f` of `I` satisfy `f [u]ₘ = 0` for `R`-units;
    (units : ∀ (u : Kˣ) (hu : u ∈ R.unit_group) 
      (f : dual F (F ⊗[ℤ] additive Kˣ))
      (hf : f ∈ I), f [u]ₘ = 0)
    -- (3) the elements `f` of `D` satisfy `f [u]ₘ = 0` for `R`-principal-units;
    (punits : ∀ (u : Kˣ) (hu : u ∈ R.principal_unit_group) 
      (f : dual F (F ⊗[ℤ] additive Kˣ))
      (hf : f ∈ D), f [u]ₘ = 0)
    -- (4) the quotient `D / I` is finite dimensional;
    (fd : finite_dimensional F (↥D ⧸ I.comap D.subtype)),
    -- and `I` has codimension at most one in `D`.
    finrank F (↥D ⧸ I.comap D.subtype) ≤ 1 := 
begin
  rw submodule.is_closed_iff at h1,
  let T := D.dual_annihilator_comap,
  have hTD : T.dual_annihilator = D,
  { dsimp only [T],
    exact h1.dual_comap_dual },
  have hacl : D.acl,
  { refine ⟨h1, h3, h2⟩ },
  have hacl' : T.dual_annihilator.acl, 
  { convert hacl },
  obtain ⟨R,H,le,units,principal_units,fd,codim⟩ := 
    main_theorem_mul_char p ℓ HH htwo T hacl',
  let I := H.dual_annihilator,
  obtain ⟨e⟩ : nonempty ((↥D ⧸ submodule.comap D.subtype I) ≃ₗ[F] 
    (dual F (↥H ⧸ T.comap H.subtype))), 
  { dsimp [I],
    rw ← hTD, 
    have e := submodule.dual_mod_comap_iso T H le,
    apply nonempty.intro,
    exact e },
  refine ⟨R, I, _, _, _, _, _, _⟩,
  { rw submodule.is_closed_iff, apply submodule.is_closed_dual_annihilator },
  { intros f hf, rw [← hTD, submodule.mem_dual_annihilator], 
    intros w hw,
    dsimp [I] at hf,
    erw submodule.mem_dual_annihilator at hf,
    apply hf, apply le, assumption },
  { intros u hu, 
    rw ← submodule.mem_dual_annihilator_comap_iff,
    dsimp [I], rw submodule.dual_annihilator_dual_annihilator_comap,
    apply units, assumption },
  { intros u hu,
    rw ← submodule.mem_dual_annihilator_comap_iff,
    apply principal_units, assumption },
  { resetI, apply e.symm.finite_dimensional },
  { resetI, rwa [e.finrank_eq, subspace.dual_finrank_eq] },
end
