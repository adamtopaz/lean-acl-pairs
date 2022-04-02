import linear_algebra.projective_space.basic
import tactic.field_simp

variables (K V W : Type*) [field K] [add_comm_group V] [module K V]
  [add_comm_group W] [module K W]

namespace projectivization 

def affine_embedding : V → ℙ K (K × V) :=
λ v, mk _ (1,v) (by simp)

lemma affine_embedding_injective : function.injective (affine_embedding K V) :=
begin
  intros a b h,
  erw mk_eq_mk_iff at h,
  obtain ⟨u,h⟩ := h,
  simp only [prod.smul_mk, prod.mk.inj_iff] at h,
  have : u = 1,
  { ext, convert h.1, rw [units.smul_def], simp },
  have h2 := h.2,
  rw this at h2,
  simpa using h2.symm
end

lemma ne_of_leading_one_of_leading_zero (v w : V) (h : w ≠ 0) :
  (mk K (1,v) (by simp) : ℙ K (K × V)) ≠ mk K (0,w) (by simpa) := 
begin
  intro c,
  rw mk_eq_mk_iff at c,
  obtain ⟨u,hu⟩ := c,
  simpa using hu,
end

def affine_embedding_of_nonzero (u : K) (hu : u ≠ 0) : V → ℙ K (K × V) :=
λ v, mk _ (u,v) (by simpa)

lemma affine_embedding_of_nonzero_injective (u : K) (hu : u ≠ 0) : 
  function.injective (affine_embedding_of_nonzero K V u hu) := 
begin
  intros a b h,
  erw mk_eq_mk_iff at h,
  obtain ⟨t,ht⟩ := h,
  simp only [prod.smul_mk, prod.mk.inj_iff] at ht,
  cases ht with h1 h2,
  have : t = 1,
  { change (t : K) * u = u at h1, apply_fun (λ e, e * u⁻¹) at h1, 
    field_simp at h1, exact h1 },
  rw this at h2,
  simpa using h2.symm,
end

lemma ne_of_leading_nonzero_of_leading_zero (v w : V) (h : w ≠ 0)
  (a : K) (ha : a ≠ 0) :
  (mk K (a,v) (by simpa) : ℙ K (K × V)) ≠ mk K (0,w) (by simpa) := 
begin
  intro c,
  rw mk_eq_mk_iff at c,
  obtain ⟨t,ht⟩ := c,
  simp only [prod.smul_mk, smul_zero, prod.mk.inj_iff] at ht,
  exact ha (ht.1.symm)
end

end projectivization