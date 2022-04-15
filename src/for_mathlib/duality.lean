import linear_algebra.basis
import for_mathlib.fd_duality
import for_mathlib.basis
import topology.constructions

variables {V K : Type*} [field K] [add_comm_group V] [module K V]

namespace module

def dual.pointwise_convergence_topology : 
  topological_space (dual K V) := 
let e : (dual K V) → (V → K) := λ f, f in 
topological_space.induced e (@Pi.topological_space V (λ _, K) (λ _, ⊥))

end module

namespace submodule

open module

def closed (H : submodule K (dual K V)) : Prop := 
∀ (f : dual K V), (∀ (a : V) (ha : a ∈ H.dual_annihilator_comap), f a = 0) → f ∈ H

section
local attribute [instance] dual.pointwise_convergence_topology

theorem is_closed_iff (H : submodule K (dual K V)) :
  is_closed (H : set (dual K V)) ↔ H.closed := 
begin
  letI : topological_space V := ⊥,
  letI : topological_space K := ⊥,
  let e : dual K V → V → K := λ f, f,
  have he : inducing e := ⟨rfl⟩,
  split,
  { intros h f hf,
    rw he.is_closed_iff at h,
    obtain ⟨T,hT1,hT2⟩ := h,
    change f ∈ (H : set (dual K V)), rw ← hT2,
    rw is_closed_iff_nhds at hT1,
    apply hT1,
    intros U hU,
    rw [nhds_pi, filter.mem_pi] at hU,
    obtain ⟨I,hI1,hI2,hI3,hI4⟩ := hU,
    simp_rw [nhds_discrete, filter.mem_pure] at hI3,
    let W : submodule K V := submodule.span K I,
    haveI : finite_dimensional K W,
    { apply finite_dimensional.span_of_finite, exact hI1 },
    let F : dual K V →ₗ[K] dual K W :=  dual.transpose W.subtype,
    let H' := H.map F,
    suffices : F f ∈ H', 
    { obtain ⟨g,hg1,hg2⟩ := this,
      use g,
      split,
      { apply hI4, rw set.mem_pi, intros i hi,
        have : g i = f i, 
        { let j : W := ⟨i, submodule.subset_span hi⟩,
          change F g j = F f j, rw hg2 },
        rw this, 
        apply hI3 },
      { change g ∈ e ⁻¹' T, rw hT2, apply hg1 } },
    rw mem_iff_dual_annihilator_comap,
    intros a ha,
    rw mem_dual_annihilator_comap_iff at ha,
    apply hf,
    dsimp, rw mem_dual_annihilator_comap_iff,
    intros g hg,
    apply ha (F g), refine ⟨g,hg,rfl⟩ },
  { intros h,
    have : (H : set (dual K V)) = 
      ⋂ (a : V) (ha : a ∈ H.dual_annihilator_comap), { g | a ∈ g.ker },
    { ext f, 
      split,
      { intros hf,  
        rw set.mem_Inter, intros a, rw set.mem_Inter, intros ha, 
        rw mem_dual_annihilator_comap_iff at ha,
        exact ha _ hf },
      { intros hf, 
        apply h,
        intros a ha,
        rw set.mem_Inter at hf, specialize hf a,
        rw set.mem_Inter at hf, specialize hf ha,
        apply hf } },
    rw this,
    apply is_closed_Inter, intros a,
    apply is_closed_Inter, intros ha,
    rw he.is_closed_iff,
    use (λ (e : V → K), e a) ⁻¹' ({0} : set K),
    refine ⟨_, rfl⟩,
    apply is_closed.preimage, exact continuous_apply a, 
    constructor, trivial }
end
end

lemma mem_iff_dual_annihilator_comap_of_closed (H : submodule K (dual K V))
  (hH : H.closed) (f : dual K V) : 
  f ∈ H ↔ (∀ (a : V) (ha : a ∈ H.dual_annihilator_comap), f a = 0) := 
begin
  split,
  { intros hf a ha, 
    rw mem_dual_annihilator_comap_iff at ha,
    exact ha _ hf },
  { intro hf, 
    apply hH _ hf }
end

noncomputable
def equiv_to_dual_mod_of_is_closed (H : submodule K (dual K V)) 
  (hH : H.closed) : 
  H ≃ₗ[K] dual K (V ⧸ H.dual_annihilator_comap) :=
linear_equiv.of_bijective H.map_to_dual_mod H.map_to_dual_mod_injective 
begin
  intros f, 
  let g : dual K V := f.comp H.dual_annihilator_comap.mkq,
  use g,
  swap, { ext, refl },
  rw mem_iff_dual_annihilator_comap_of_closed _ hH,
  intros a ha,
  dsimp [g],
  convert f.map_zero using 2, 
  simpa only [quotient.mk_eq_zero],
end

@[simp]
lemma equiv_to_dual_mod_of_is_closed_apply_apply 
  (H : submodule K (dual K V)) (hH : H.closed) 
  (f : H) (v : V) : 
  H.equiv_to_dual_mod_of_is_closed hH f (H.dual_annihilator_comap.mkq v) = f v := 
rfl

@[simp]
lemma equiv_to_dual_mod_of_is_closed_symm_apply_apply 
  (H : submodule K (dual K V)) (hH : H.closed) 
  (f : dual K (V ⧸ H.dual_annihilator_comap)) (v : V) : 
  ((H.equiv_to_dual_mod_of_is_closed hH).symm f : dual K V) v = 
    f (H.dual_annihilator_comap.mkq v) :=
begin
  erw ← H.equiv_to_dual_mod_of_is_closed_apply_apply hH,
  simp,
end
  
lemma is_closed_dual_annihilator (T : submodule K V) :
  T.dual_annihilator.closed := 
begin
  intros f hf,
  rw mem_dual_annihilator,
  intros w hw,
  apply hf,
  rw mem_dual_annihilator_comap_iff,
  intros g hg,
  rw mem_dual_annihilator at hg,
  apply hg,
  assumption
end

lemma exists_functional_of_nonzero (v : V) (hv : v ≠ 0) : 
  ∃ φ : dual K V, φ v ≠ 0 :=
begin
  have : linear_independent K ![v], 
  { by_contra c,
    rw fintype.not_linear_independent_iff at c, 
    obtain ⟨g,h1,i,h2⟩ := c,
    apply h2,
    simp only [fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk, fin.mk_zero, matrix.cons_val_fin_one, finset.sum_singleton,
      smul_eq_zero] at h1,
    fin_cases i, cases h1, assumption,
    contradiction },
  let β := basis.sum_extend this,
  use β.coord (sum.inl 0),
  change β.coord (sum.inl 0) (![v] 0) ≠ 0,
  dsimp only [β],
  have := basis.sum_extend_extends _ this 0,
  rw ← this,
  dsimp,
  classical,
  simp only [basis.repr_self, finsupp.single_apply, if_pos rfl],
  exact one_ne_zero,
end

@[simp]
lemma dual_annihilator_dual_annihilator_comap (T : submodule K V) : 
  T.dual_annihilator.dual_annihilator_comap = T := 
begin
  ext t,
  split,
  { intros ht,  
    rw mem_dual_annihilator_comap_iff at ht,
    by_contra c,
    have : ∃ (φ : dual K (V ⧸ T)), φ (T.mkq t) ≠ 0, 
    { apply exists_functional_of_nonzero, simpa },
    obtain ⟨φ, hφ⟩ := this,
    apply hφ,
    let ψ := φ.comp T.mkq, apply ht ψ,
    rw mem_dual_annihilator,
    intros v hv,
    dsimp only [ψ, linear_map.comp_apply],
    convert φ.map_zero,
    simpa },
  { intros ht,  
    rw mem_dual_annihilator_comap_iff,
    intros φ hφ,
    rw mem_dual_annihilator at hφ,
    apply hφ,
    assumption }
end

lemma closed.dual_comap_dual {T : submodule K (dual K V)} 
  (hT : T.closed) : T.dual_annihilator_comap.dual_annihilator = T := 
begin
  ext t,
  split,
  { intros ht, 
    rw mem_dual_annihilator at ht,
    rwa mem_iff_dual_annihilator_comap_of_closed _ hT },
  { intros ht, 
    rw mem_dual_annihilator, 
    rwa ← mem_iff_dual_annihilator_comap_of_closed _ hT, },
end

def quotient_dual_dual_equiv (T : submodule K V) :
  (V ⧸ T.dual_annihilator.dual_annihilator_comap) ≃ₗ[K] 
  (V ⧸ T) := 
{ inv_fun := T.liftq (submodule.mkq _) (by simp),
  left_inv := by { rintro ⟨t⟩, refl },
  right_inv := by { rintro ⟨t⟩, refl },
  ..(submodule.liftq T.dual_annihilator.dual_annihilator_comap T.mkq (by simp)) }

@[simp]
lemma quotient_dual_dual_equiv_apply (T : submodule K V) (v : V) : 
  T.quotient_dual_dual_equiv (submodule.mkq _ v) = T.mkq v := rfl

@[simp]
lemma quotient_dual_dual_equiv_symm_apply (T : submodule K V) (v : V) : 
  T.quotient_dual_dual_equiv.symm (submodule.mkq _ v) = submodule.mkq _ v := rfl

def mod_to_dual_mod (T H : submodule K V) : 
  (↥(T.dual_annihilator) ⧸ (H.dual_annihilator.comap T.dual_annihilator.subtype)) →ₗ[K] 
  (dual K (H ⧸ T.comap H.subtype)) := 
(H.dual_annihilator.comap T.dual_annihilator.subtype).liftq 
({ to_fun := λ e, (T.comap H.subtype).liftq ((e : dual K V).comp H.subtype) begin
    rintros ⟨x,hx⟩ hhx,
    simp only [mem_comap, coe_subtype, coe_mk] at hhx,
    cases e with e he,
    rw mem_dual_annihilator at he,
    apply he, exact hhx,
  end,
  map_add' := begin
    rintros ⟨x,hx⟩ ⟨y,hy⟩, ext ⟨t,ht⟩, 
    refl,
  end,
  map_smul' := begin
    rintros c ⟨x,hx⟩, ext ⟨t,ht⟩,
    refl,
  end }) $
begin
  rintros ⟨x,hx⟩ hhx,
  simp only [mem_comap, coe_subtype, coe_mk, mem_dual_annihilator] at hhx,
  rw mem_dual_annihilator at hx, rw linear_map.mem_ker, dsimp,
  ext ⟨t,ht⟩, 
  simp only [liftq_mkq, linear_map.coe_comp, coe_subtype, function.comp_app, coe_mk, 
    linear_map.zero_comp, linear_map.zero_apply],
  apply hhx, exact ht,
end

@[simp]
lemma mod_to_dual_mod_apply (T H : submodule K V) (e : T.dual_annihilator) (h : H) : 
  mod_to_dual_mod T H (submodule.mkq _ e) (submodule.mkq _ h) = e h := rfl

noncomputable
def dual_mod_comap_iso (T H : submodule K V) (le : T ≤ H) : 
  (↥(T.dual_annihilator) ⧸ (H.dual_annihilator.comap T.dual_annihilator.subtype)) ≃ₗ[K]
  (dual K (↥H ⧸ T.comap H.subtype)) :=
linear_equiv.of_bijective 
(mod_to_dual_mod T H)
begin
  rintros ⟨f⟩ ⟨g⟩ h,
  simp only [quotient.quot_mk_eq_mk] at h,
  simp only [quotient.quot_mk_eq_mk],
  rw ← sub_eq_zero at h ⊢,
  simp only [← submodule.mkq_apply, ← linear_map.map_sub] at h ⊢,
  simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero],
  simp only [mem_comap, coe_subtype, add_subgroup_class.coe_sub, 
    mem_dual_annihilator, linear_map.sub_apply],
  intros v hv,
  let t : H := ⟨v,hv⟩,
  apply_fun (λ e, e (submodule.mkq _ t)) at h,
  exact h,
end 
begin
  intros e,
  let g : dual K H := e.comp (submodule.mkq _),
  obtain ⟨f,hf⟩ := subspace.dual_restrict_surjective g,
  have hfT : f ∈ T.dual_annihilator,
  { rw mem_dual_annihilator,  
    intros v hv,
    let u : H := ⟨v, le hv⟩,
    change dual_restrict _ f u = _,
    rw hf,
    dsimp [g], rw ← submodule.mkq_apply,
    have : ((comap H.subtype T).mkq) u = 0,
    { simpa only [mkq_apply, quotient.mk_eq_zero, mem_comap, coe_subtype, coe_mk] },
    simp [this] },
  let t : T.dual_annihilator := ⟨f,hfT⟩,
  use submodule.mkq _ t,
  ext, dsimp only [linear_map.comp_apply, mod_to_dual_mod_apply, t],
  change dual_restrict _ f x = _, rw hf, refl,
end

end submodule
