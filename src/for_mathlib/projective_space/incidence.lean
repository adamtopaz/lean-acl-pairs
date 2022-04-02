import linear_algebra.projective_space.basic
import data.fintype.card
import linear_algebra.linear_independent
import linear_algebra.finite_dimensional
import lemmas.matrix
import tactic

variables {K V : Type*} 
  [field K] 
  [add_comm_group V]
  [module K V]

namespace projectivization

inductive independent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i, f i ≠ 0) (h : linear_independent K f) :
    independent (λ i : ι, projectivization.mk _ (f i) (hf i))

lemma independent_iff_rep {ι : Type*} (f : ι → ℙ K V) :
  independent f ↔ 
  linear_independent K (projectivization.rep ∘ f) :=
begin
  split,
  { rintro ⟨g,hg,h⟩,
    have : ∀ i, ∃ (a : Kˣ), a • g i = (mk K (g i) (hg i)).rep,
    { intro i, apply exists_smul_eq_mk_rep },
    choose e he using this,
    have : projectivization.rep ∘ (λ i, mk K (g i) (hg i)) = (λ i, e i • g i),
    { ext, rw he },
    rw this,
    exact linear_independent.units_smul h e },
  { intros h, 
    have := independent.mk _ _ h,
    swap, { intros i, apply rep_nonzero },
    convert this,
    ext, simp only [mk_rep] }
end

inductive dependent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i, f i ≠ 0) (h : ¬ linear_independent K f) :
    dependent (λ i : ι, projectivization.mk _ (f i) (hf i))

lemma dependent_iff_rep {ι : Type*} (f : ι → ℙ K V) :
  dependent f ↔ 
  ¬ linear_independent K (projectivization.rep ∘ f) :=
begin
  split,
  { rintro ⟨g,hg,h⟩, 
    intro c, apply h,
    have : ∀ i, ∃ (a : Kˣ), a • g i = (mk K (g i) (hg i)).rep,
    { intro i, apply exists_smul_eq_mk_rep },
    choose e he using this,
    have : projectivization.rep ∘ (λ i, mk K (g i) (hg i)) = (λ i, e i • g i),
    { ext, rw he },
    rw this at c,
    convert linear_independent.units_smul c e⁻¹,
    ext, simp },
  { intros h, 
    have := dependent.mk _ _ h,
    swap, { intros i, apply rep_nonzero },
    convert this,
    ext, simp only [mk_rep] }
end

@[simp]
lemma dependent_iff_not_independent { ι : Type*} (f : ι → ℙ K V) :
  ¬ independent f ↔ dependent f :=
by rw [independent_iff_rep, dependent_iff_rep]

@[simp]
lemma not_dependent_iff_independent {ι : Type*} (f : ι → ℙ K V) :
  ¬ dependent f ↔ independent f :=
by rw [← dependent_iff_not_independent, not_not]

lemma eq_iff_dependent (p q : ℙ K V) : p = q ↔ dependent ![p,q] := 
begin
  split,
  { rintro rfl, rw [dependent_iff_rep, fintype.linear_independent_iff],
    push_neg, use ![1,-1], refine ⟨by simp [fin.sum_univ_succ], 0, by simp⟩ },
  { intro h, rw [dependent_iff_rep, fintype.linear_independent_iff] at h, 
    push_neg at h, obtain ⟨g,h1,i,h2⟩ := h,
    rw [← mk_rep p, ← mk_rep q, mk_eq_mk_iff],
    simp only [fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero, 
      fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk,
      fin.mk_zero, matrix.cons_val_succ, finset.sum_singleton, fin.succ_zero_eq_one] at h1,
    fin_cases i, 
    { have : g 1 ≠ 0, 
      { intro c, apply h2, simp only [c, zero_smul, add_zero, smul_eq_zero] at h1, 
        cases h1, { exact h1, }, { exfalso, apply p.rep_nonzero h1 } },
      use (is_unit.mk0 _ h2).unit⁻¹ * -(is_unit.mk0 _ this).unit,
      rw [mul_smul, inv_smul_eq_iff, units.smul_def, units.smul_def],
      dsimp [is_unit.unit], rwa [neg_smul, neg_eq_iff_add_eq_zero, add_comm] },
    { have : g 0 ≠ 0, 
      { intro c, apply h2, simp only [c, zero_smul, zero_add, smul_eq_zero] at h1, 
        cases h1, { exact h1, }, { exfalso, apply q.rep_nonzero h1 } },
      use (is_unit.mk0 _ this).unit⁻¹ * -(is_unit.mk0 _ h2).unit,
      rw [mul_smul, inv_smul_eq_iff, units.smul_def, units.smul_def],
      dsimp [is_unit.unit], rwa [neg_smul, neg_eq_iff_add_eq_zero, add_comm] } }
end

lemma ne_iff_independent (p q : ℙ K V) : p ≠ q ↔ independent ![p,q] := 
by rw [← not_dependent_iff_independent, not_iff_not, eq_iff_dependent] 

lemma dependent_iff_rep₃ (u v w : ℙ K V) : dependent ![u,v,w] ↔
  ∃ (a b c : K) (hh : ![a,b,c] ≠ 0), a • u.rep + b • v.rep + c • w.rep = 0 := 
begin
  split,
  { intro h, 
    rw [dependent_iff_rep, fintype.linear_independent_iff] at h,
    push_neg at h,
    obtain ⟨g,h1,h2⟩ := h,
    use [g 0, g 1, g 2],
    refine ⟨_, by simpa [fin.sum_univ_succ, add_assoc] using h1⟩, 
    intro c, obtain ⟨i,h2⟩ := h2, apply h2, 
    convert congr_fun c i, fin_cases i; refl },
  { rintro ⟨a,b,c,h1,h2⟩, 
    rw [dependent_iff_rep, fintype.linear_independent_iff],
    push_neg, use ![a,b,c],
    refine ⟨by simpa [fin.sum_univ_succ, add_assoc] using h2, _⟩,
    by_contra c, push_neg at c,
    apply h1, ext i, apply c }
end

lemma independent_mk_iff₃ (u v w : V) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
  independent ![mk K u hu, mk K v hv, mk K w hw] ↔ 
  linear_independent K ![u,v,w] := 
begin
  split,
  { intros h, 
    rw independent_iff_rep at h,
    rw comp_matrix_eq_matrix₃ at h,
    choose e he using λ i : fin 3, exists_smul_eq_mk_rep K (![u,v,w] i) 
      (by fin_cases i; assumption),
    have := h.units_smul e⁻¹,
    convert this,
    ext i,
    fin_cases i,
    { specialize he 0, dsimp at he, simp [← he] },
    { specialize he 1, simp only [matrix.cons_val_one, matrix.head_cons] at he, simp [← he], },
    { specialize he 2, 
      simp only [matrix.cons_vec_bit0_eq_alt0, matrix.cons_append, matrix.empty_append, 
        matrix.cons_vec_alt0, matrix.empty_vec_alt0,
        matrix.cons_val_one, matrix.head_cons] at he, 
      simp [← he] } },
  { intro h, convert independent.mk _ _ h,  
    { ext i, fin_cases i; simp },
    { intro i, fin_cases i; assumption } }
end

lemma independent_mk_iff₂ (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
  independent ![mk K u hu, mk K v hv] ↔ 
  linear_independent K ![u,v] := 
begin
  split,
  { intros h, 
    rw independent_iff_rep at h,
    rw comp_matrix_eq_matrix₂ at h,
    choose e he using λ i : fin 2, exists_smul_eq_mk_rep K (![u,v] i) 
      (by fin_cases i; assumption),
    have := h.units_smul e⁻¹,
    convert this,
    ext i,
    fin_cases i,
    { specialize he 0, dsimp at he, simp [← he] },
    { specialize he 1, simp only [matrix.cons_val_one, matrix.head_cons] at he, simp [← he], } },
  { intro h, convert independent.mk _ _ h,  
    { ext i, fin_cases i; simp },
    { intro i, fin_cases i; assumption } }
end

lemma dependent_mk_iff₃ (u v w : V) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
  dependent ![mk K u hu, mk K v hv, mk K w hw] ↔ 
  ¬ linear_independent K ![u,v,w] := 
by rw [← dependent_iff_not_independent, not_iff_not, independent_mk_iff₃]

lemma dependent_mk_iff₂ (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
  dependent ![mk K u hu, mk K v hv] ↔ 
  ¬ linear_independent K ![u,v] := 
by rw [← dependent_iff_not_independent, not_iff_not, independent_mk_iff₂]

lemma independent_swap₃ (a b c : ℙ K V) : 
  independent ![a,b,c] → independent ![a,c,b] := 
begin
  rintros h, 
  rw [independent_iff_rep, fintype.linear_independent_iff] at *,
  intros g hg i,
  specialize h ![g 0, g 2, g 1] _,
  { simp only [fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero, 
    matrix.cons_val_succ, fintype.univ_of_subsingleton,
    fin.mk_eq_subtype_mk, fin.mk_zero, fin.succ_zero_eq_one, 
    finset.sum_singleton, fin.succ_one_eq_two] at *,  
    rwa add_comm (g 1 • _) at hg },
  fin_cases i, exacts [h 0, h 2, h 1],
end

lemma independent_rotate₃ (a b c : ℙ K V) :
  independent ![a,b,c] → independent ![b,c,a] := 
begin
  rintros h, 
  rw [independent_iff_rep, fintype.linear_independent_iff] at *,
  intros g hg i,
  specialize h ![g 2, g 0, g 1] _,
  { simp only [fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero, 
    matrix.cons_val_succ, fintype.univ_of_subsingleton,
    fin.mk_eq_subtype_mk, fin.mk_zero, fin.succ_zero_eq_one, 
    finset.sum_singleton, fin.succ_one_eq_two] at *,  
    rwa [add_comm, add_assoc, add_comm, add_assoc] at hg, },
  fin_cases i, exacts [h 1, h 2, h 0],
end

lemma dependent_swap₃ (a b c : ℙ K V) :
  dependent ![a,b,c] → dependent ![a,c,b] := 
begin
  simp_rw ← dependent_iff_not_independent,
  rw not_imp_not,
  exact independent_swap₃ _ _ _,
end

lemma dependent_rotate₃ (a b c : ℙ K V) :
  dependent ![a,b,c] → dependent ![b,c,a] := 
begin
  simp_rw ← dependent_iff_not_independent,
  rw not_imp_not,
  intros h,
  apply independent_rotate₃, 
  exact independent_rotate₃ _ _ _ h, 
end

lemma independent_swap₂ (a b : ℙ K V) : 
  independent ![a,b] → independent ![b,a] := 
begin
  simp only [← ne_iff_independent],
  intros h, exact h.symm
end

lemma dependent_swap₂ (a b : ℙ K V) : 
  dependent ![a,b] → dependent ![b,a] := 
begin
  simp only [← eq_iff_dependent],
  intros h, exact h.symm,
end
  
def span₂ (a b : ℙ K V) : submodule K V :=
a.submodule ⊔ b.submodule

def span₃ (a b c : ℙ K V) : submodule K V :=
a.submodule ⊔ b.submodule ⊔ c.submodule

lemma span_eq_span₂ (a b : ℙ K V) : 
  span₂ a b = submodule.span K ({a.rep, b.rep} : set V) := 
begin
  dsimp [span₂], simp only [submodule_eq], 
  rw [sup_comm, ← submodule.span_union], simp,
end

lemma span_eq_span₃ (a b c : ℙ K V) :
  span₃ a b c = submodule.span K ({a.rep, b.rep, c.rep} : set V) := 
begin
  dsimp [span₃], 
  rw [sup_comm, (sup_comm : a.submodule ⊔ _ = _), ← sup_assoc],
  simp only [submodule_eq, ← submodule.span_union, set.union_singleton],
end

lemma span_swap₃ (a b c : ℙ K V) : 
  span₃ a b c = span₃ a c b := 
begin
  dsimp [span₃],
  simp only [sup_assoc],
  congr' 1, apply sup_comm,
end

lemma span_rotate₃ (a b c : ℙ K V ) : 
  span₃ a b c = span₃ b c a := 
begin
  dsimp [span₃],
  rw [sup_assoc, sup_comm],
end

lemma span_swap₂ (a b : ℙ K V) : 
  span₂ a b = span₂ b a := 
begin
  dsimp [span₂], rw sup_comm,
end

open finite_dimensional

section

variables [finite_dimensional K V]
open_locale classical

lemma finrank_span_of_independent₃ (a b c : ℙ K V) :
  independent ![a,b,c] → finrank K (span₃ a b c) = 3 := 
begin
  intros h, rw [independent_iff_rep] at h,
  rw [span_eq_span₃, ← set.range_matrix_eq₃, ← comp_matrix_eq_matrix₃],
  exact finrank_span_eq_card h,
end

lemma finrank_span_of_independent₂ (a b : ℙ K V) :
  independent ![a,b] → finrank K (span₂ a b) = 2 := 
begin
  intros h, rw [independent_iff_rep] at h,
  rw [span_eq_span₂, ← set.range_matrix_eq₂, ← comp_matrix_eq_matrix₂],
  exact finrank_span_eq_card h,
end

lemma finrank_span_lt_of_dependent₃ (a b c : ℙ K V) :
  dependent ![a,b,c] → finrank K (span₃ a b c) < 3 := 
begin
  intro h,
  rw dependent_iff_rep at h,
  rw [span_eq_span₃, ← set.range_matrix_eq₃, ← comp_matrix_eq_matrix₃],
  rw linear_independent_iff_card_eq_finrank_span at h,
  change ¬ (3 = _) at h,
  apply lt_of_le_of_ne,
  refine le_trans (finrank_span_le_card _) _, 
  { simp only [set.to_finset_range], 
    apply finset.card_image_le },
  exact ne.symm h,
end

instance nontrivial_span₂ (a b : ℙ K V) : nontrivial (span₂ a b) :=
begin
  use 0, use a.rep, apply submodule.mem_sup_left, 
  rw submodule_eq, apply submodule.mem_span_singleton_self,
  intro c,
  apply a.rep_nonzero,
  exact congr_arg coe c.symm
end

instance nontrivial_span₃ (a b c : ℙ K V) : nontrivial (span₃ a b c) :=
begin
  use 0, use a.rep, dsimp [span₃], rw sup_assoc, apply submodule.mem_sup_left,
  rw submodule_eq, apply submodule.mem_span_singleton_self,
  intro c,
  apply a.rep_nonzero,
  exact congr_arg coe c.symm
end

lemma finrank_span_pos₃ (a b c : ℙ K V) : 
  0 < finrank K (span₃ a b c) := 
finrank_pos

lemma fingrank_span_pos₂ (a b : ℙ K V) :
  0 < finrank K (span₂ a b) := 
finrank_pos

lemma span₂_le_span₃ (a b c : ℙ K V) : 
  span₂ a b ≤ span₃ a b c := 
le_sup_left

lemma finrank_span_of_independent_of_dependent₃ (a b c : ℙ K V) :
  independent ![a,b] → dependent ![a,b,c] → finrank K (span₃ a b c) = 2 := 
begin
  intros h1 h2,
  have : finrank K (span₃ a b c) < 3 := finrank_span_lt_of_dependent₃ _ _ _ h2,
  have h : finrank K (span₂ a b) = 2 := finrank_span_of_independent₂ _ _ h1,
  have : 2 ≤ finrank K (span₃ a b c),
  { rw ← h,
    apply submodule.finrank_mono,
    exact le_sup_left },
  linarith
end

lemma dependent_iff_span (a b c : ℙ K V) (h : independent ![a,b]) : 
  dependent ![a,b,c] ↔ c.submodule ≤ span₂ a b := 
begin
  split,
  { intros h, 
    rw [dependent_iff_rep, fintype.not_linear_independent_iff] at h, 
    rw [span_eq_span₂, submodule_eq],
    rw submodule.span_singleton_le_iff_mem,
    obtain ⟨g,h1,i,hi⟩ := h,
    simp only [fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero, 
      matrix.cons_val_succ, fin.succ_zero_eq_one, fintype.univ_of_subsingleton, 
      fin.mk_eq_subtype_mk, fin.mk_zero, finset.sum_singleton, 
      fin.succ_one_eq_two] at h1,
    have hh : g 2 ≠ 0, 
    { intros c, 
      rw [independent_iff_rep, fintype.linear_independent_iff] at h,
      specialize h ![g 0, g 1] (by simpa [c, fin.sum_univ_succ] using h1),
      apply hi,
      fin_cases i,
      exacts [h 0, h 1, c] },
    apply_fun (λ e, (g 2)⁻¹ • e) at h1,
    simp only [smul_add, smul_zero, ← mul_smul, inv_mul_cancel hh, one_smul,
      ← add_assoc, add_eq_zero_iff_neg_eq] at h1,
    rw ← h1,
    let E := submodule.span K ({a.rep, b.rep} : set V),
    apply E.neg_mem, apply E.add_mem; apply E.smul_mem; apply submodule.subset_span,
    { simp only [set.mem_insert_iff, eq_self_iff_true, true_or] }, 
    { simp only [set.mem_insert_iff, set.mem_singleton, or_true] } },
  { intro hh, 
    dsimp [span₂] at hh, simp only [submodule_eq] at hh,
    rw [submodule.span_singleton_le_iff_mem, submodule.mem_sup] at hh,
    obtain ⟨u,hu,v,hv,hh⟩ := hh,
    simp only [submodule.mem_span_singleton] at hu hv,
    obtain ⟨i,rfl⟩ := hv,
    obtain ⟨j,rfl⟩ := hu,
    rw [dependent_iff_rep, fintype.not_linear_independent_iff],
    use ![j,i,-1],
    split,
    { simp only [fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero, matrix.cons_val_succ, 
        fintype.univ_of_subsingleton, matrix.cons_val_fin_one, neg_smul, one_smul, 
        finset.sum_const, finset.card_singleton],  
      simpa only [← add_assoc, add_neg_eq_zero] },
    { use 2, simp, } }
end

variables (K V)
structure configuration (a b c u v : ℙ K V) :=
(Iabc : independent ![a,b,c])
(Dabu : dependent ![a,b,u])
(Dacv : dependent ![a,c,v])
(Iau : independent ![a,u])
(Ibu : independent ![b,u])
(Iav : independent ![a,v])
(Icv : independent ![c,v])
variables {K V}

namespace configuration

variables {a b c u v : ℙ K V} (C : configuration K V a b c u v)

include C

lemma Icu : independent ![c,u] := 
begin
  rw ← ne_iff_independent,
  intro cc,
  have h1 := C.Iabc,
  have h2 := C.Dabu,
  rw cc at *,
  rw ← not_dependent_iff_independent at h1,
  apply h1, exact h2
end

lemma Ibv : independent ![b,v] :=
begin
  rw ← ne_iff_independent,
  intro cc,
  have h1 := independent_swap₃ _ _ _ C.Iabc,
  have h2 := C.Dacv,
  rw cc at *,
  rw ← not_dependent_iff_independent at h1,
  apply h1, exact h2
end

lemma Iab : independent ![a,b] := 
begin
  have := C.Iabc,
  simp only [independent_iff_rep, fintype.linear_independent_iff] at this ⊢,
  intros g hg i,
  specialize this ![g 0, g 1, 0] (by simpa [fin.sum_univ_succ] using hg),
  fin_cases i, exacts [this 0, this 1],
end

lemma Iac : independent ![a,c] :=
begin
  have := C.Iabc,
  simp only [independent_iff_rep, fintype.linear_independent_iff] at this ⊢,
  intros g hg i,
  specialize this ![g 0, 0, g 1] (by simpa [fin.sum_univ_succ] using hg),
  fin_cases i, exacts [this 0, this 2],
end

def M := span₃ a b c 
def L₁ := span₂ u c
def L₂ := span₂ v b

lemma M_eq : C.M = C.L₁ ⊔ C.L₂ :=
begin
  dsimp [span₃, span₂, L₁, L₂, M], 
  apply le_antisymm,
  { apply sup_le _ _; try { apply sup_le _ _ },
    rw [sup_comm, sup_assoc],
    apply le_trans _ le_sup_right,
    rw ← sup_assoc, apply le_trans _ le_sup_left,
    erw ← dependent_iff_span,
    apply dependent_rotate₃, exact C.Dabu, exact C.Ibu,
    apply le_trans le_sup_right le_sup_right,
    apply le_trans le_sup_right le_sup_left },
  { apply sup_le _ _; apply sup_le _ _,
    apply le_trans _ le_sup_left,
    erw ← dependent_iff_span, exact C.Dabu, exact C.Iab,
    exact le_sup_right,
    rw [(sup_comm : (a.submodule ⊔ _ = _)), sup_assoc],   
    apply le_trans _ le_sup_right,
    erw ← dependent_iff_span, exact C.Dacv, exact C.Iac,
    apply le_trans le_sup_right le_sup_left },
end

lemma finrank_M : finrank K C.M = 3 := 
begin
  apply finrank_span_of_independent₃, exact C.Iabc,
end

lemma finrank_L₁ : finrank K C.L₁ = 2 := 
begin
  apply finrank_span_of_independent₂, apply independent_swap₂, exact C.Icu
end

lemma finrank_L₂ : finrank K C.L₂ = 2 := 
begin
  apply finrank_span_of_independent₂, apply independent_swap₂, exact C.Ibv
end

def Q := C.L₁ ⊓ C.L₂

lemma finrank_Q : finrank K C.Q = 1 := 
begin
  have := submodule.dim_sup_add_dim_inf_eq C.L₁ C.L₂,
  dsimp [Q],
  rw [← C.M_eq, C.finrank_M, C.finrank_L₁, C.finrank_L₂] at this,
  linarith,
end

end configuration

theorem exists_unique_of_configuration (a b c u v : ℙ K V)
  (C : configuration K V a b c u v) : 
  ∃! q : ℙ K V, dependent ![u,c,q] ∧ dependent ![v,b,q] :=
begin
  use mk'' C.Q C.finrank_Q,
  refine ⟨⟨_,_⟩,_⟩,
  { erw dependent_iff_span, simp only [submodule_mk''],
    refine le_trans inf_le_left (le_of_eq rfl),
    apply independent_swap₂,
    exact C.Icu },
  { erw dependent_iff_span, simp only [submodule_mk''],
    refine le_trans inf_le_right (le_of_eq rfl),
    apply independent_swap₂,
    exact C.Ibv },
  { intros y hy, 
    rw ← mk''_submodule y, congr' 1,
    apply eq_of_le_of_finrank_eq,
    { apply le_inf _ _,
      { erw ← dependent_iff_span, exact hy.1,
        apply independent_swap₂, exact C.Icu },
      { erw ← dependent_iff_span, exact hy.2, 
        apply independent_swap₂, exact C.Ibv } },
    { rw [finrank_submodule, C.finrank_Q] } }
end

lemma eq_of_config (a b c u v q₁ q₂ : ℙ K V) 
  (C : configuration K V a b c u v) :
  dependent ![u,c,q₁] → 
  dependent ![v,b,q₁] →
  dependent ![u,c,q₂] → 
  dependent ![v,b,q₂] → q₁ = q₂ :=
begin
  obtain ⟨q,h1,h2⟩ := exists_unique_of_configuration _ _ _ _ _ C,
  intros e1 e2 e3 e4,
  have eq1 : q₁ = q, 
  { apply h2, exact ⟨e1,e2⟩ },
  have eq2 : q₂ = q,
  { apply h2, exact ⟨e3,e4⟩ },
  rw [eq1, ← eq2],
end

end
section 

/-! incidence is preserved by linear equivalences. TODO: generalize -/

variables {W : Type*} [add_comm_group W] [module K W]
variable (E : V ≃ₗ[K] W)

lemma map_mk_eq_mk' (E : V →ₗ[K] W) (hE : function.injective E) 
  (u : V) (hu : u ≠ 0) : 
  map E hE (mk K u hu) = mk _ (E u) (by { rw ← E.map_zero, exact hE.ne hu }) := rfl

lemma map_mk_eq_mk (u : V) (hu : u ≠ 0) : 
  map E.to_linear_map E.injective (mk K u hu) = 
  mk _ (E u) (E.map_ne_zero_iff.mpr hu) := 
rfl

lemma independent_map_comp_of_independent {ι : Type*} 
  (e : ι → ℙ K V) : 
  independent e → independent (map E.to_linear_map E.injective ∘ e) := 
begin
  intro h, induction h with f hf h, 
  refine independent.mk _ _ (h.map (_ : disjoint _ E.to_linear_map.ker)),
  convert disjoint_bot_right,
  rw linear_map.ker_eq_bot, exact E.injective
end

lemma independent_map_comp_iff {ι : Type*} 
  (e : ι → ℙ K V) : 
  independent e ↔ independent (map E.to_linear_map E.injective ∘ e) := 
begin
  refine ⟨independent_map_comp_of_independent _ _, _⟩,
  intros h, 
  convert independent_map_comp_of_independent E.symm _ h,
  ext, rw [← function.comp.assoc, ← map_comp], 
  dsimp,
  change id (e x) = _, apply congr_fun, symmetry, convert map_id,
  ext, simp,
end

lemma independent_iff_independent₂ (u v : ℙ K V) : 
  independent ![u,v] ↔ 
  independent ![map E.to_linear_map E.injective u, map E.to_linear_map E.injective v] := 
by rw [independent_map_comp_iff E, comp_matrix_eq_matrix₂]

lemma independent_iff_independent₃ (u v w : ℙ K V) : 
  independent ![u, v, w] ↔ 
  independent ![map E.to_linear_map E.injective u, 
    map E.to_linear_map E.injective v,
    map E.to_linear_map E.injective w] := 
by rw [independent_map_comp_iff E, comp_matrix_eq_matrix₃]

lemma dependent_map_comp_iff {ι : Type*} 
  (e : ι → ℙ K V) : 
  dependent e ↔ dependent (map E.to_linear_map E.injective ∘ e) := 
begin
  simp only [← dependent_iff_not_independent, not_iff_not],
  apply independent_map_comp_iff,
end

lemma dependent_iff_dependent₂ (u v : ℙ K V) : 
  dependent ![u,v] ↔ 
  dependent ![map E.to_linear_map E.injective u, map E.to_linear_map E.injective v] := 
by rw [dependent_map_comp_iff E, comp_matrix_eq_matrix₂]

lemma dependent_iff_dependent₃ (u v w : ℙ K V) : 
  dependent ![u, v, w] ↔ 
  dependent ![map E.to_linear_map E.injective u, 
    map E.to_linear_map E.injective v,
    map E.to_linear_map E.injective w] := 
by rw [dependent_map_comp_iff E, comp_matrix_eq_matrix₃]

end

end projectivization