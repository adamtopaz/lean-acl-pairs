import linear_algebra.finite_dimensional
import linear_algebra.basic

variables {K V : Type*} [field K] [add_comm_group V] [module K V]

open submodule finite_dimensional

lemma submodule.mkq_comp_sup_mod_surjective (S T : submodule K V) :
  function.surjective ((T.comap (T ⊔ S).subtype).mkq.comp 
    (submodule.of_le (le_sup_right : _ ≤ T ⊔ S))) :=
begin
  rintro ⟨t,ht⟩, rw submodule.mem_sup at ht,
  obtain ⟨y,hy,z,hz,rfl⟩ := ht,
  use [z,hz],
  simp only [linear_map.coe_comp, function.comp_app, mkq_apply, quotient.quot_mk_eq_mk],
  rw [← sub_eq_zero, ← submodule.mkq_apply, ← submodule.mkq_apply,
    ← linear_map.map_sub, submodule.mkq_apply, submodule.quotient.mk_eq_zero],
  simp only [mem_comap, submodule.coe_subtype, add_subgroup_class.coe_sub, coe_of_le, coe_mk],
  convert (T.neg_mem hy), abel,
end

lemma submodule.finrank_le_one_of_not_linear_independent_aux (T : submodule K V)
  (S : set V) (v : V) (hv : v ∈ S) (hv' : v ∉ T)
  (h : ∀ (a : V) (ha : a ∈ S), ¬ linear_independent K ![T.mkq a, T.mkq v]) 
  (z : V) (hz : z ∈ span K S) : 
  ∃ (c : K) (t : V) (ht : t ∈ T), z = c • v + t := 
begin
  apply span_induction hz,
  { intros x hx, 
    specialize h x hx,
    rw fintype.not_linear_independent_iff at h,
    obtain ⟨g,h1,i,h2⟩ := h,
    simp only [fin.sum_univ_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons] at h1,
    have hg0 : g 0 ≠ 0,
    { intro c, simp only [c, zero_smul, zero_add, smul_eq_zero] at h1, 
      cases h1, fin_cases i; contradiction, apply hv', simpa using h1 },
    apply_fun (λ e, (g 0)⁻¹ • e) at h1,
    simp only [smul_add, ← mul_smul, inv_mul_cancel hg0, one_smul, smul_zero,
      ← linear_map.map_smul, ← linear_map.map_add] at h1,
    rw [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1,
    refine ⟨-((g 0)⁻¹ * g 1), x + ((g 0)⁻¹ * g 1) • v, h1,_⟩, 
    simp only [neg_smul], abel },
  { use [0,0,T.zero_mem, by simp] },
  { rintros u v ⟨c,t,ht,rfl⟩ ⟨d,s,hs,rfl⟩,
    use [(c + d),(t + s), T.add_mem ht hs],
    simp only [add_smul], abel },
  { rintros a v ⟨c,t,ht,rfl⟩, use [a * c, a • t, T.smul_mem a ht],
    simp only [mul_smul, smul_add] }
end

lemma submodule.surjective_of_not_linear_independent (T : submodule K V) 
  (S : set V) (v : V) (hv : v ∈ S) (hv' : v ∉ T)
  (h : ∀ (a : V) (ha : a ∈ S), ¬ linear_independent K ![T.mkq a, T.mkq v]) : 
let e1 : span K ({v} : set V) →ₗ[K] span K S := of_le (span_mono $ by simpa),
    e2 : (span K S) →ₗ[K] ↥(T ⊔ span K S) := of_le le_sup_right,
    e3 : ↥(T ⊔ span K S) →ₗ[K] (↥(T ⊔ span K S) ⧸ T.comap (T ⊔ span K S).subtype) := 
      submodule.mkq _ in 
function.surjective ((e3.comp e2).comp e1) := 
begin
  dsimp, rintros ⟨x,hx⟩,
  rw submodule.mem_sup at hx,
  obtain ⟨y,hy,z,hz,rfl⟩ := hx,
  obtain ⟨c,t,ht,rfl⟩ := T.finrank_le_one_of_not_linear_independent_aux S v hv hv' h z hz,
  dsimp,
  refine ⟨⟨c • v, _⟩, _⟩,
  { rw submodule.mem_span_singleton, 
    refine ⟨c,rfl⟩ },
  rw [← sub_eq_zero, ← submodule.mkq_apply, ← submodule.mkq_apply, ← linear_map.map_sub,
    submodule.mkq_apply, submodule.quotient.mk_eq_zero],
  simp only [mem_comap, submodule.coe_subtype, add_subgroup_class.coe_sub, coe_of_le, coe_mk],
  convert T.add_mem (T.neg_mem ht) (T.neg_mem hy),
  abel,
end

lemma submodule.finite_dimensional_of_not_linear_independent (T : submodule K V) 
  (S : set V) (v : V) (hv : v ∈ S) (hv' : v ∉ T)
  (h : ∀ (a : V) (ha : a ∈ S), ¬ linear_independent K ![T.mkq a, T.mkq v]) :
  finite_dimensional K (↥(T ⊔ span K S) ⧸ T.comap (T ⊔ span K S).subtype) := 
begin
  let e1 : span K ({v} : set V) →ₗ[K] span K S := of_le (span_mono $ by simpa),
  let e2 : (span K S) →ₗ[K] ↥(T ⊔ span K S) := of_le le_sup_right,
  let e3 : ↥(T ⊔ span K S) →ₗ[K] (↥(T ⊔ span K S) ⧸ T.comap (T ⊔ span K S).subtype) :=  
    submodule.mkq _,
  let e := (e3.comp e2).comp e1,
  apply e.finite_dimensional_of_surjective,
  rw linear_map.range_eq_top,
  apply T.surjective_of_not_linear_independent,
  assumption',
end


lemma submodule.finrank_le_one_of_not_linear_independent (T : submodule K V)
  (S : set V) (v : V) (hv : v ∈ S) (hv' : v ∉ T)
  (h : ∀ (a : V) (ha : a ∈ S), ¬ linear_independent K ![T.mkq a, T.mkq v]) :
  finrank K (↥(T ⊔ span K S) ⧸ T.comap (T ⊔ span K S).subtype) ≤ 1 := 
begin
  haveI : finite_dimensional K (↥(T ⊔ span K S) ⧸ T.comap (T ⊔ span K S).subtype) := 
    T.finite_dimensional_of_not_linear_independent S v hv hv' h,
  rw finrank_le_one_iff,
  let e1 : span K ({v} : set V) →ₗ[K] span K S := of_le (span_mono $ by simpa),
  let e2 : (span K S) →ₗ[K] ↥(T ⊔ span K S) := of_le le_sup_right,
  let e3 : ↥(T ⊔ span K S) →ₗ[K] (↥(T ⊔ span K S) ⧸ T.comap (T ⊔ span K S).subtype) :=  
    submodule.mkq _,
  let e := e3.comp e2,
  let v' : span K S := ⟨v, subset_span hv⟩,
  use e v',
  rintros ⟨w,hw⟩, rw submodule.mem_sup at hw, obtain ⟨y,hy,z,hz,rfl⟩ := hw,
  dsimp,
  dsimp only [← submodule.mkq_apply],
  let y' : ↥(T ⊔ span K S) := ⟨y,_⟩,
  let z' : ↥(T ⊔ span K S) := ⟨z,_⟩,
  change ∃ c, _ = submodule.mkq _ (y' + z'),
  have : (T.comap (T ⊔ span K S).subtype).mkq y' = 0, 
  { simpa },
  simp only [linear_map.map_add, this, zero_add],
  obtain ⟨c,t,ht,hh⟩ := 
    submodule.finrank_le_one_of_not_linear_independent_aux T S v hv hv' h z hz,
  use c,
  dsimp,
  dsimp only [← submodule.mkq_apply],
  rw [← linear_map.map_smul, ← sub_eq_zero, ← linear_map.map_sub,
    submodule.mkq_apply, submodule.quotient.mk_eq_zero],
  simp only [mem_comap, submodule.coe_subtype, add_subgroup_class.coe_sub, 
    coe_smul_of_tower, coe_of_le, subtype.coe_mk],
  rw hh, simpa,
  exact mem_sup_right hz,
  exact mem_sup_left hy,
end