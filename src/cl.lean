import main_induction_step
import for_mathlib.base_change
import for_mathlib.basis
import for_mathlib.duality

.

open_locale tensor_product
open_locale classical

variables (K F : Type*) [field K] [field F]

open module

abbreviation mul_base_change := F ⊗[ℤ] additive Kˣ

variables {K F}

def units.as (x : Kˣ) : mul_base_change K F :=
1 ⊗ₜ additive.of_mul x

namespace units

@[simp]
lemma as_mul (u v : Kˣ) : ((u * v).as : mul_base_change K F) = u.as + v.as := 
tensor_product.tmul_add _ _ _

@[simp]
lemma as_one : ((1 : Kˣ).as : mul_base_change K F) = 0 := 
tensor_product.tmul_zero _ _

@[simp]
lemma as_inv (u : Kˣ) : (u⁻¹.as : mul_base_change K F) = - u.as := 
tensor_product.tmul_neg _ _

lemma as_div (u v : Kˣ) : ((u / v).as : mul_base_change K F) = u.as - v.as := 
tensor_product.tmul_sub _ _ _

end units

namespace submodule

def restrict (T : submodule F (mul_base_change K F)) : 
  subgroup Kˣ :=
{ carrier := { u | u.as ∈ T },
  mul_mem' := λ u v hu hv, begin
    dsimp at hu hv ⊢,
    rw units.as_mul,
    apply T.add_mem hu hv,
  end,
  one_mem' := begin
    dsimp, rw units.as_one, exact T.zero_mem,
  end,
  inv_mem' := begin
    intros u hu,
    dsimp at hu ⊢,
    rw units.as_inv,
    apply T.neg_mem hu,
  end }

--instance : topological_space (dual F (mul_base_change K F)) := 
--module.dual.pointwise_convergence_topology

structure acl (H : submodule F (dual F (mul_base_change K F))) : Prop := 
(closed : H.closed)
(alternating : 
  ∀ (u v : Kˣ) (h : (u : K) + v = 1) (f g : dual F (mul_base_change K F))
    (hf : f ∈ H) (hg : g ∈ H), f u.as * g v.as = f v.as * g u.as) 
(neg_one : ∀ (f : dual F (mul_base_change K F)) (hf : f ∈ H), f ((-1 : Kˣ).as) = 0)

noncomputable theory

lemma neg_one_mem_of_acl (H : submodule F (dual F (mul_base_change K F))) (h : H.acl) :
  (-1 : Kˣ).as ∈ H.dual_annihilator_comap :=
begin
  rw mem_dual_annihilator_comap_iff,
  intros f hf,
  apply h.neg_one _ hf,
end

lemma dependent_of_acl (H : submodule F (dual F (mul_base_change K F))) (h : H.acl)
  (u v : Kˣ) (huv : (u : K) + v = 1) : 
  ¬ linear_independent F 
    ![H.dual_annihilator_comap.mkq u.as, 
      H.dual_annihilator_comap.mkq v.as] :=
begin
  --let T := H.dual_annihilator_comap
  let e := ![(H.dual_annihilator_comap.mkq) u.as, 
    (H.dual_annihilator_comap.mkq) v.as],
  let E := equiv_to_dual_mod_of_is_closed H h.1,
  intro c,
  let β := basis.sum_extend c,
  let f : dual F _ := β.coord (sum.inl 0),
  let g : dual F _ := β.coord (sum.inl 1),
  let f' := E.symm f,
  let g' := E.symm g,
  have HH := h.2 u v huv f' g' f'.2 g'.2,
  dsimp only [f',g', E] at HH,
  simp only [equiv_to_dual_mod_of_is_closed_symm_apply_apply H h.1] at HH,
  have he0 : e 0 = (H.dual_annihilator_comap.mkq u.as) := rfl, 
  have he1 : e 1 = (H.dual_annihilator_comap.mkq v.as) := rfl,
  simp only [← he0, ← he1] at HH,
  dsimp only [e,f,g,β] at HH,
  simp only [
      ← basis.sum_extend_extends _ c 0, 
      ← basis.sum_extend_extends _ c 1] at HH, 
  dsimp at HH,
  simp only [basis.repr_self, finsupp.single_apply] at HH,
  simp_rw [if_pos rfl] at HH,
  rw [if_neg, if_neg] at HH,
  { apply (one_ne_zero : (1 : F) ≠ 0),
    simpa using HH },
  all_goals { norm_num }
end

end submodule
