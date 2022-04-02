import linear_algebra.dual


variables {K V : Type*} [field K] [add_comm_group V] [module K V]

open module

namespace submodule

def map_to_dual_mod (H : submodule K (dual K V)) : 
  H →ₗ[K] dual K (V ⧸ H.dual_annihilator_comap) :=
{ to_fun := λ h, submodule.liftq _ (h : dual K V) (λ x hx, begin
    rw mem_dual_annihilator_comap_iff at hx,
    apply hx _ h.2,
  end),
  map_add' := by tidy,
  map_smul' := by tidy }

@[simp]
lemma map_to_dual_mod_apply (H : submodule K (dual K V)) (f : H) (v : V) :
  H.map_to_dual_mod f (H.dual_annihilator_comap.mkq v) = (f : dual K V) v := rfl

lemma map_to_dual_mod_injective (H : submodule K (dual K V)) : 
  function.injective H.map_to_dual_mod := 
begin
  intros f g h,
  ext v,
  apply_fun (λ e, e (H.dual_annihilator_comap.mkq v)) at h,
  exact h
end

section finite_dimensional

open finite_dimensional

variables [finite_dimensional K V]

lemma finrank_dual_mod (H : submodule K (dual K V)) : 
  finrank K (dual K (V ⧸ H.dual_annihilator_comap)) = finrank K H := 
begin
  let J : subspace K (dual K V) := H,
  rw [subspace.dual_finrank_eq],
  have := H.dual_annihilator_comap.finrank_quotient_add_finrank,
  rw ← J.finrank_add_finrank_dual_annihilator_comap_eq at this,
  exact nat.add_right_cancel this, 
end

noncomputable
def equiv_to_dual_mod (H : submodule K (dual K V)) : 
  H ≃ₗ[K] dual K (V ⧸ H.dual_annihilator_comap) := 
H.map_to_dual_mod.linear_equiv_of_injective H.map_to_dual_mod_injective H.finrank_dual_mod.symm

@[simp]
lemma equiv_to_dual_mod_apply_apply (H : submodule K (dual K V)) (h : H) (v : V) : 
  H.equiv_to_dual_mod h (H.dual_annihilator_comap.mkq v) = (h : dual K V) v := rfl

@[simp]
lemma equiv_to_dual_mod_symm_apply_apply (H : submodule K (dual K V)) 
  (f : dual K (V ⧸ H.dual_annihilator_comap)) (v : V) : 
(H.equiv_to_dual_mod.symm f : dual K V) v = f (H.dual_annihilator_comap.mkq v) := 
begin
  rw ← equiv_to_dual_mod_apply_apply, simp,
end

@[simp]
lemma equiv_to_dual_mod_symm_apply (H : submodule K (dual K V))
  (f : dual K (V ⧸ H.dual_annihilator_comap)) : 
  (H.equiv_to_dual_mod.symm f : dual K V) = linear_map.comp f H.dual_annihilator_comap.mkq :=
by { ext, simp }

lemma mem_iff_dual_annihilator_comap (H : submodule K (dual K V)) 
  (f : dual K V) : f ∈ H ↔ ∀ (a : V) (ha : a ∈ H.dual_annihilator_comap), f a = 0 :=
begin
  split, 
  { intros hf a ha, rw mem_dual_annihilator_comap_iff at ha, exact ha _ hf, },
  { intros h, 
    let g : dual K (V ⧸ H.dual_annihilator_comap) := H.dual_annihilator_comap.liftq f h,
    let e := H.equiv_to_dual_mod.symm g,
    convert e.2, ext, simp }
end

end finite_dimensional

end submodule
