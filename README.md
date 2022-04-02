# Valuations and `acl`-pairs.

This repository contains a formalization of the relationship between so-called `acl`-pairs and valuation rings. The formal statement (reproduced below) of the main theorem, and its formal proof, can be found in `src/main_theorem.lean` and its imported files.

```lean
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

-- We now assume that `F` is a prime field.
-- The is defined as saying that every element `a : F` can be expressed as 
-- `m/n` for some `m : ℤ` and some `n : ℕ` such that `(n : F) ≠ 0`.
variable [is_prime_field F]

example : is_prime_field ℚ := infer_instance
example (p : ℕ) [fact (nat.prime p)] : is_prime_field (zmod p) := infer_instance

/- The main theorem of `acl`-pairs. -/
theorem main_acl_theorem 
  -- Given a submodule `D` of `dual F (F ⊗[ℤ] additive Kˣ)`,
  (D : submodule F (dual F (F ⊗[ℤ] additive Kˣ))) 
  -- which is: (1) closed with respect to the topology introduced above; 
  (h1 : is_closed (D : set (dual F (F ⊗[ℤ] additive Kˣ))))
  -- (2) every element of `D` maps `[(-1 : Kˣ)]ₘ` to zero;
  (h2 : ∀ (f : dual F (F ⊗[ℤ] additive Kˣ)) (hf : f ∈ D), f [-1]ₘ = 0) 
  -- (3) satisfies the `acl`-condition, i.e. whenever `u v : Kˣ` satisfy
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
    (units : ∀ (u : Kˣ) (hu : u ∈ R.units) 
      (f : dual F (F ⊗[ℤ] additive Kˣ))
      (hf : f ∈ I), f [u]ₘ = 0)
    -- (3) the elements `f` of `D` satisfy `f [u]ₘ = 0` for `R`-principal-units;
    (punits : ∀ (u : Kˣ) (hu : u ∈ R.principal_units) 
      (f : dual F (F ⊗[ℤ] additive Kˣ))
      (hf : f ∈ D), f [u]ₘ = 0)
    -- (4) the quotient `D / I` is finite dimensional;
    (fd : finite_dimensional F (↥D ⧸ I.comap D.subtype)),
    -- and `I` has codimension at most one in `D`.
    finrank F (↥D ⧸ I.comap D.subtype) ≤ 1 := 
...
```

The converse of the above theorem is much easier to prove, and holds without the additional hypothesis that `F` is a prime field.
It is also formalized in the same file, with the following statement.
```lean
/- 
The converse to the main theorem about `acl`-pairs. 
This is a simple result, and we prove it without many dependencies from the imports.
-/
theorem main_acl_converse
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
  (units : ∀ (u : Kˣ) (hu : u ∈ R.units) 
    (f : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ I), f [u]ₘ = 0)
  -- (4) the elements of `D` act trivially on the principal units of `R`;
  (punits : ∀ (u : Kˣ) (hu : u ∈ R.principal_units) 
    (f : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ D), f [u]ₘ = 0)
  -- (5) `D/I` is finite dimensional;
  (fd : finite_dimensional F (↥D ⧸ I.comap D.subtype))
  -- (6) and `I` has codimension at most `1` in `D`,
  (codim : finrank F (↥D ⧸ I.comap D.subtype) ≤ 1) :
  -- then any pair of elements of `D` satisfies the `acl`-condition.
  ∀ (u v : Kˣ) (huv : (u : K) + v = 1) 
    (f g : dual F (F ⊗[ℤ] additive Kˣ))
    (hf : f ∈ D) (hg : g ∈ D), 
    f [u]ₘ * g [v]ₘ = f [v]ₘ * g [u]ₘ := 
...
```

## References
The arguments formalized in this repository are based on the following references.

- Arason, R. Elman, and B. Jacob, *Rigid elements, valuations, and realization of Witt rings*, J. Algebra 110 (1987), no. 2, 449–467.
- F. A. Bogomolov and Y. Tschinkel, *Commuting elements of Galois groups of function fields*, Motives, polylogarithms and Hodge theory, Part I (Irvine, CA, 1998), 2002, pp. 75–120.
- I. Efrat, *Construction of valuations from K-theory*, Math. Res. Lett. 6 (1999), no. 3-4, 335–343.
- J. Koenigsmann, *From p-rigid elements to valuations (with a Galois-characterization of p-adic fields)*, J. Reine Angew. Math. 465 (1995), 165–182.
- A. Topaz, *Commuting-liftable subgroups of Galois groups II*, J. Reine Angew. Math. 730 (2017), 65–133.