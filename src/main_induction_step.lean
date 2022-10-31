import for_mathlib.projective_space.incidence
import for_mathlib.projective_space.affine_embedding

open projectivization

notation `mk₀` x := (mk _ x (by simp))
notation `mk[` F `]` x := (mk F (x : F × F × F) (by simp))

variables {K F : Type*} [field K] [field F]

section configurations

meta def helper₃ := `[
  rw [independent_mk_iff₃, fintype.linear_independent_iff],
  intros g hg,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
    mul_one, mul_zero, matrix.cons_val_succ, fin.succ_zero_eq_one, fintype.univ_of_subsingleton, 
    fin.mk_zero, finset.sum_singleton, fin.succ_one_eq_two, prod.mk_add_mk, add_zero, 
    zero_add, prod.mk_eq_zero] at hg,
  rcases hg with ⟨h1,h2,h3⟩ ]

meta def helper₂ := `[
  rw [independent_mk_iff₂, fintype.linear_independent_iff],
  intros g hg,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
    mul_one, mul_zero, matrix.cons_val_succ, fin.succ_zero_eq_one, fintype.univ_of_subsingleton, 
    fin.mk_zero, finset.sum_singleton, fin.succ_one_eq_two, prod.mk_add_mk, add_zero, 
    zero_add, prod.mk_eq_zero] at hg,
  rcases hg with ⟨h1,h2,h3⟩ ]

variables (F K)
def one_add_x_add_y_config : projectivization.configuration F (F × F × F)
  (mk[F] (1,0,0)) -- (φ 1) 
  (mk[F] (0,1,0)) -- (φ (1 + x)) 
  (mk[F] (0,0,1))-- (φ (1 + y)) 
  (mk[F] (1,1,0)) -- (φ x) 
  (mk[F] (1,0,1)) -- (φ y) 
  := 
{ Iabc := begin
    helper₃,
    intros i, fin_cases i; assumption
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    refine ⟨![1,1,-1], by simp [fin.sum_univ_succ], 0, by norm_num⟩,
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    refine ⟨![1,1,-1], by simp [fin.sum_univ_succ], 0, by norm_num⟩,
  end,
  Iau := begin
    rw [← ne_iff_independent], 
    apply (affine_embedding_injective _ _).ne,
    norm_num,
  end,
  Ibu := begin
    rw [← ne_iff_independent],
    apply ne.symm,
    apply ne_of_leading_one_of_leading_zero,
    norm_num
  end,
  Iav := begin
    rw [← ne_iff_independent],
    apply (affine_embedding_injective _ _).ne,
    norm_num,
  end,
  Icv := begin
    rw [← ne_iff_independent], 
    apply ne.symm,
    apply ne_of_leading_one_of_leading_zero,
    norm_num
  end }

def two_add_x_add_y_config : configuration F (F × F × F)
  (mk[F] (1,0,1)) -- (φ y) 
  (mk[F] (1,1,1)) -- (φ (1 + x + y)) 
  (mk[F] (0,0,1)) -- (φ (1 + y)) 
  (mk[F] (0,1,0)) -- (φ (1 + x)) 
  (mk[F] (1,0,0)) -- (φ 1) 
  :=
{ Iabc := begin
    helper₃,
    intros i, fin_cases i,
    { simpa [h2] using h1 },
    { exact h2 },
    { rw [h2, add_zero] at h1, simpa [h2,h1] using h3 },
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    refine ⟨![1,-1,1], by simp [fin.sum_univ_succ], 0, by norm_num⟩,
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    refine ⟨![-1,1,1], by simp [fin.sum_univ_succ], 0, by norm_num⟩,
  end,
  Iau := begin
    rw [← ne_iff_independent],
    apply ne_of_leading_one_of_leading_zero,
    norm_num
  end,
  Ibu := begin
    rw [← ne_iff_independent],
    apply ne_of_leading_one_of_leading_zero,
    norm_num
  end,
  Iav := begin
    rw [← ne_iff_independent],
    apply (affine_embedding_injective _ _).ne,
    norm_num
  end,
  Icv := begin
    rw [← ne_iff_independent],
    apply ne.symm,
    apply ne_of_leading_one_of_leading_zero,
    norm_num
  end }

def frac_config (n : ℕ) : configuration F (F × F × F)
  (mk[F] (n-1,1,0))
  (mk[F] (1,0,0))
  (mk[F] (1,0,1))
  (mk[F] (n,1,0))
  (mk[F] (n,1,1)) :=
{ Iabc := begin
    helper₃,
    intros i, fin_cases i,
    { exact h2 },
    { simpa [h2,h3] using h1 },
    { exact h3 },
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, 
        algebra.id.smul_eq_mul, one_mul, mul_one, mul_zero,
        matrix.cons_val_succ, fintype.univ_of_subsingleton, fin.mk_zero, 
        matrix.cons_val_fin_one, neg_smul, prod.neg_mk, finset.sum_const, finset.card_singleton, 
        nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, zero_add, add_zero, add_right_neg, 
        prod.mk_eq_zero, eq_self_iff_true, and_true], 
      ring },
    use 1, norm_num,
  end, 
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
        one_mul, mul_one, mul_zero, matrix.cons_val_succ, fintype.univ_of_subsingleton, 
        fin.mk_zero, matrix.cons_val_fin_one, neg_smul, prod.neg_mk, 
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true], 
      ring },
    use 1, norm_num,
  end,
  Iau := begin
    helper₂,
    have : g 0 * ((n : F) - 1) + g 1 * n = n * (g 0 + g 1) - g 0, by ring, 
    rw [this,h2, mul_zero, zero_sub, neg_eq_zero] at h1,
    rw [h1, zero_add] at h2,
    intros i, fin_cases i,
    exacts [h1, h2]
  end,
  Ibu := begin
    helper₂,
    intros i, fin_cases i,
    { simpa [h2] using h1 },
    { exact h2 }
  end,
  Iav := begin
    helper₂,
    intros i, fin_cases i,
    { simpa [h3] using h2 },
    { exact h3 }
  end,
  Icv := begin
    helper₂,
    intros i, fin_cases i,
    { simpa [h2] using h3 },
    { exact h2 }
  end }

def frac_config' (n : ℕ) : configuration F (F × F × F)
  (mk[F] (n,1,1))
  (mk[F] (0,0,1))
  (mk[F] (1,0,0))
  (mk[F] (n,1,0))
  (mk[F] (n+1,1,1)) := 
{ Iabc := begin
    helper₃,
    simp only [h2, zero_mul, zero_add] at h1 h3,
    intros i, fin_cases i, assumption',
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num }
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num }
  end,
  Iau := begin
    helper₂,
    simp only [h3, zero_add] at h2,
    intros i, fin_cases i, assumption',
  end,
  Ibu := begin
    helper₂,
    intros i, fin_cases i, assumption',
  end,
  Iav := begin
    helper₂,
    rw (show g 0 * ↑n + g 1 * (↑n + 1) = (g 0 + g 1) * n + g 1, by ring) at h1,
    simp only [h2, zero_mul, zero_add] at h1,
    simp only [h1, add_zero] at h2,
    intros i, fin_cases i, assumption'
  end,
  Icv := begin
    helper₂,
    simp only [h2, zero_mul, add_zero] at h1,
    intro i, fin_cases i, assumption',
  end }

def frac_config_horizontal (n m : ℕ) (hn : (n : F) ≠ 0) : configuration F (F × F × F)
  (mk F (n,m-1,0) (λ c, hn (congr_arg prod.fst c)))
  (mk[F] (0,1,0)) 
  (mk[F] (0,1,1)) 
  (mk F (n,m,0) (λ c, hn (congr_arg prod.fst c))) 
  (mk F (n,m,1) (λ c, hn (congr_arg prod.fst c))) := 
{ Iabc := begin
    helper₃,
    apply_fun (λ e, e * (n : F)⁻¹) at h1, 
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1,h3,zero_mul,zero_add,add_zero] at h2,
    intros i, fin_cases i, assumption'
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
        one_mul, mul_zero, matrix.cons_val_succ, mul_one, fintype.univ_of_subsingleton, 
        fin.mk_zero, matrix.cons_val_fin_one, neg_smul, prod.neg_mk, 
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_zero, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true, true_and],
      ring },
    use 0, norm_num
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
        one_mul, mul_zero, matrix.cons_val_succ, mul_one, fintype.univ_of_subsingleton, 
        fin.mk_zero, matrix.cons_val_fin_one, neg_smul, prod.neg_mk, 
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_zero, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true, true_and],
      ring },
    use 1, norm_num,
  end,
  Iau := begin
    helper₂,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [add_mul, mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    have : g 0 * (↑m - 1) + g 1 * ↑m = (g 0 + g 1) * (m : F) - g 0, by ring, 
    rw [this, h1, zero_mul, zero_sub, neg_eq_zero] at h2,
    rw [h2, zero_add] at h1,
    intros i, fin_cases i, assumption'
  end,
  Ibu := begin
    helper₂,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1, zero_mul, add_zero] at h2,
    intros i, fin_cases i, assumption'
  end,
  Iav := begin
    helper₂,
    simp only [h3, zero_mul, add_zero] at h1,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [zero_mul, add_zero, mul_assoc, mul_inv_cancel hn, mul_one] at h1,
    intros i, fin_cases i, assumption'
  end,
  Icv := begin
    helper₂,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1, add_zero] at h3,
    intros i, fin_cases i, assumption',
  end }

def frac_config_horizontal' (n m : ℕ) (hn : (n : F) ≠ 0) : configuration F (F × F × F)
  (mk F (n,m,1) (λ c, hn (congr_arg prod.fst c)))
  (mk[F] (0,1,0))
  (mk[F] (0,0,1))
  (mk[F] (n,m+1,1))
  (mk F (n,m,0) (λ c, hn (congr_arg prod.fst c)))
  :=
{ Iabc := begin
    helper₃,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1, zero_add, zero_mul] at h2 h3,
    intros i, fin_cases i, assumption'
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num },
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num },
  end,
  Iau := begin
    rw ← ne_iff_independent,
    apply (affine_embedding_of_nonzero_injective _ _ _ hn).ne,
    norm_num,
  end,
  Ibu := begin
    rw ← ne_iff_independent, apply ne.symm,
    apply ne_of_leading_nonzero_of_leading_zero,
    norm_num, assumption
  end,
  Iav := begin
    rw ← ne_iff_independent, apply ne.symm,
    apply (affine_embedding_of_nonzero_injective _ _ _ hn).ne,
    norm_num,
  end,
  Icv := begin
    rw ← ne_iff_independent, apply ne.symm,
    apply ne_of_leading_nonzero_of_leading_zero,
    norm_num, assumption
  end }

/-
def neg_frac_config (n : ℕ) : configuration F (F × F × F)
  (mk[F] (n-1,-1,0))
  (mk[F] (1,0,0))
  (mk[F] (1,0,1))
  (mk[F] (n,-1,0))
  (mk[F] (n,-1,1)) :=
{ Iabc := begin
    helper₃,
    simp only [mul_neg, mul_one, neg_eq_zero] at h2,
    intros i, fin_cases i,
    { exact h2 },
    { simpa [h2,h3] using h1 },
    { exact h3 },
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, 
        algebra.id.smul_eq_mul, one_mul, mul_one, mul_zero,
        matrix.cons_val_succ, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk, fin.mk_zero, 
        matrix.cons_val_fin_one, neg_smul, prod.neg_mk, finset.sum_const, finset.card_singleton, 
        nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, zero_add, add_zero, add_right_neg, 
        prod.mk_eq_zero, eq_self_iff_true, and_true], 
      ring },
    use 1, norm_num,
  end, 
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
        one_mul, mul_one, mul_zero, matrix.cons_val_succ, fintype.univ_of_subsingleton, 
        fin.mk_eq_subtype_mk, fin.mk_zero, matrix.cons_val_fin_one, neg_smul, prod.neg_mk, 
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true], 
      ring },
    use 1, norm_num,
  end,
  Iau := begin
    helper₂,
    simp only [mul_neg, mul_one, neg_eq_zero, ← neg_add] at h2,
    have : g 0 * ((n : F) - 1) + g 1 * n = n * (g 0 + g 1) - g 0, by ring, 
    rw [this,h2, mul_zero, zero_sub, neg_eq_zero] at h1,
    rw [h1, zero_add] at h2,
    intros i, fin_cases i,
    exacts [h1, h2]
  end,
  Ibu := begin
    helper₂,
    simp only [mul_neg, mul_one, neg_eq_zero] at h2,
    intros i, fin_cases i,
    { simpa [h2] using h1 },
    { exact h2 }
  end,
  Iav := begin
    helper₂,
    intros i, fin_cases i,
    { simpa [h3] using h2 },
    { exact h3 }
  end,
  Icv := begin
    helper₂,
    simp only [mul_neg, mul_one, neg_eq_zero] at h2,
    intros i, fin_cases i,
    { simpa [h2] using h3 },
    { exact h2 }
  end }

def neg_frac_config' (n : ℕ) : configuration F (F × F × F)
  (mk[F] (n,-1,1))
  (mk[F] (0,0,1))
  (mk[F] (1,0,0))
  (mk[F] (n,-1,0))
  (mk[F] (n+1,-1,1)) := 
{ Iabc := begin
    helper₃,
    simp only [mul_neg, mul_one, neg_eq_zero] at h2,
    simp only [h2, zero_mul, zero_add] at h1 h3,
    intros i, fin_cases i, assumption',
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num }
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num }
  end,
  Iau := begin
    helper₂,
    rw [← add_mul, mul_neg, mul_one, neg_eq_zero] at h2,
    simp only [h3, zero_add] at h2,
    intros i, fin_cases i, assumption',
  end,
  Ibu := begin
    helper₂,
    simp only [mul_neg, mul_one, neg_eq_zero] at h2,
    intros i, fin_cases i, assumption',
  end,
  Iav := begin
    helper₂,
    rw [← add_mul, mul_neg, mul_one, neg_eq_zero] at h2,
    rw (show g 0 * ↑n + g 1 * (↑n + 1) = (g 0 + g 1) * n + g 1, by ring) at h1,
    simp only [h2, zero_mul, zero_add] at h1,
    simp only [h1, add_zero] at h2,
    intros i, fin_cases i, assumption'
  end,
  Icv := begin
    helper₂, 
    simp only [mul_neg, mul_one, neg_eq_zero] at h2,
    simp only [h2, zero_mul, add_zero] at h1,
    intro i, fin_cases i, assumption',
  end }

def neg_frac_config_horizontal (n m : ℕ) (hn : (n : F) ≠ 0) : configuration F (F × F × F)
  (mk F (n,1-m,0) (λ c, hn (congr_arg prod.fst c)))
  (mk[F] (0,1,0)) 
  (mk[F] (0,-1,1)) 
  (mk F (n,-m,0) (λ c, hn (congr_arg prod.fst c))) 
  (mk F (n,-m,1) (λ c, hn (congr_arg prod.fst c))) := 
{ Iabc := begin
    helper₃,
    apply_fun (λ e, e * (n : F)⁻¹) at h1, 
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1,h3,zero_mul,zero_add,add_zero] at h2,
    intros i, fin_cases i, assumption'
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
        one_mul, mul_zero, matrix.cons_val_succ, mul_one, fintype.univ_of_subsingleton, 
        fin.mk_eq_subtype_mk, fin.mk_zero, matrix.cons_val_fin_one, neg_smul, prod.neg_mk, 
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_zero, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true, true_and],
      refine ⟨_,_,_⟩; ring },
    use 0, norm_num
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, 
        one_mul, mul_zero, matrix.cons_val_succ, mul_one, fintype.univ_of_subsingleton, 
        fin.mk_eq_subtype_mk, fin.mk_zero, matrix.cons_val_fin_one, neg_smul, prod.neg_mk, 
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_zero, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true, true_and],
      ring },
    use 1, norm_num,
  end,
  Iau := begin
    helper₂,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [add_mul, mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    have : g 0 * (1 - ↑m) + g 1 * (-↑m) = (g 0 + g 1) * -(m : F) + g 0, by ring, 
    rw [this, h1, zero_mul, zero_add] at h2,
    rw [h2, zero_add] at h1,
    intros i, fin_cases i, assumption'
  end,
  Ibu := begin
    helper₂,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1, zero_mul, add_zero] at h2,
    intros i, fin_cases i, assumption'
  end,
  Iav := begin
    helper₂,
    simp only [h3, zero_mul, add_zero] at h1,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [zero_mul, add_zero, mul_assoc, mul_inv_cancel hn, mul_one] at h1,
    intros i, fin_cases i, assumption'
  end,
  Icv := begin
    helper₂,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1, add_zero] at h3,
    intros i, fin_cases i, assumption',
  end }

def neg_frac_config_horizontal' (n m : ℕ) (hn : (n : F) ≠ 0) : configuration F (F × F × F)
  (mk F (n,-m,1) (λ c, hn (congr_arg prod.fst c)))
  (mk[F] (0,1,0))
  (mk[F] (0,0,1))
  (mk[F] (n,-m-1,1))
  (mk F (n,-m,0) (λ c, hn (congr_arg prod.fst c)))
  :=
{ Iabc := begin
    helper₃,
    apply_fun (λ e, e * (n : F)⁻¹) at h1,
    simp only [mul_assoc, mul_inv_cancel hn, mul_one, zero_mul] at h1,
    simp only [h1, zero_add, zero_mul] at h2 h3,
    intros i, fin_cases i, assumption'
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num },
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num },
  end,
  Iau := begin
    rw ← ne_iff_independent,
    apply (affine_embedding_of_nonzero_injective _ _ _ hn).ne,
    simp only [ne.def, prod.mk.inj_iff, eq_self_iff_true, and_true],
    rw (show (-(m : F) - 1) = -(m+1), by ring),
    norm_num,
  end,
  Ibu := begin
    rw ← ne_iff_independent, apply ne.symm,
    apply ne_of_leading_nonzero_of_leading_zero,
    norm_num, assumption
  end,
  Iav := begin
    rw ← ne_iff_independent, apply ne.symm,
    apply (affine_embedding_of_nonzero_injective _ _ _ hn).ne,
    norm_num,
  end,
  Icv := begin
    rw ← ne_iff_independent, apply ne.symm,
    apply ne_of_leading_nonzero_of_leading_zero,
    norm_num, assumption
  end }
-/

def neg_config : configuration F (F × F × F)
  (mk[F] (1,1,1))
  (mk[F] (0,1,0)) 
  (mk[F] (0,1,1)) 
  (mk[F] (1,0,1)) 
  (mk[F] (1,0,0)) :=
{ Iabc := begin
    helper₃,
    simp only [h1, zero_add] at h3,
    simp only [h1, h3, add_zero, zero_add] at h2,
    intros i, fin_cases i, assumption'
  end,
  Dabu := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num }
  end,
  Dacv := begin
    rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num }
  end,
  Iau := begin
    rw ← ne_iff_independent,
    apply (affine_embedding_injective _ _).ne,
    norm_num,
  end,
  Ibu := begin
    rw ← ne_iff_independent,
    apply ne.symm,
    apply ne_of_leading_one_of_leading_zero,
    norm_num,
  end,
  Iav := begin
    rw ← ne_iff_independent,
    apply (affine_embedding_injective _ _).ne,
    norm_num,
  end,
  Icv := begin
    rw ← ne_iff_independent,
    apply ne.symm,
    apply ne_of_leading_one_of_leading_zero,
    norm_num,
  end }

variables {F K}
end configurations

structure setup (φ : K → ℙ F (F × F × F)) (x y : K) :=
(map_zero : φ 0 = mk₀ (1,0,0))
(map_one : φ 1 = mk₀ (1,0,0))
(map_x : φ x = mk₀ (1,1,0))
(map_y : φ y = mk₀ (1,0,1))
(map_one_add_x : φ (1+x) = mk₀ (0,1,0))
(map_one_add_y : φ (1+y) = mk₀ (0,0,1))
(map_neg : ∀ u : K, φ (-u) = φ u)
(dependent_pos : ∀ u v : K, dependent ![φ u, φ v, φ (u + v)])
(dependent_neg : ∀ u v : K, dependent ![φ u, φ v, φ (u - v)]) .

namespace setup

variables {φ : K → ℙ F (F × F × F)} {x y : K} (C : setup φ x y)
include C


lemma map_one_add_x_add_y : φ (1 + x + y) = mk₀ (1,1,1) :=
begin
  apply eq_of_config _ _ _ _ _ _ _ (one_add_x_add_y_config F),
  all_goals { simp only [← C.map_one, ← C.map_x, ← C.map_y, ← C.map_one_add_x, ← C.map_one_add_y] },
  rw (show (1 + x + y) = x + (1 + y), by ring),
  apply C.dependent_pos,
  rw (show (1 + x + y) = y + (1 + x), by ring),
  apply C.dependent_pos,
  { rw [C.map_x, C.map_one_add_y, dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 1, simp } },
  { rw [C.map_y, C.map_one_add_x, dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 1, simp } },
end



lemma map_two_add_x_add_y : φ (2 + x + y) = mk₀ (0,1,1) :=
begin
  apply eq_of_config _ _ _ _ _ _ _ (two_add_x_add_y_config F),
  all_goals 
  { simp only [← C.map_y, ← C.map_one_add_x_add_y, ← C.map_one_add_y, 
      ← C.map_one_add_x, ← C.map_one] },
  { rw (show (2 + x + y) = (1 + x) + (1 + y), by ring), 
    apply C.dependent_pos },
  { rw (show (2 + x + y) = 1 + (1 + x + y), by ring), 
    apply C.dependent_pos },
  { rw [C.map_one_add_x, C.map_one_add_y, dependent_mk_iff₃, fintype.not_linear_independent_iff], 
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, simp } },
  { rw [C.map_one, C.map_one_add_x_add_y, dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, simp } },
end

lemma map_two_add_x : φ (2 + x) = mk[F] (1,-1,0) := 
begin
  apply eq_of_config _ _ _ _ _ _ _ (neg_config F),
  all_goals { simp only [← C.map_two_add_x_add_y, ← C.map_y,  
    ← C.map_one, ← C.map_one_add_x] },
  { nth_rewrite 1 (show (2 + x) = (-y) + (2 + x + y), by ring), 
    rw ← C.map_neg y,
    apply C.dependent_pos },
  { rw (show (2 + x) = 1 + (1 + x), by ring), 
    apply C.dependent_pos },
  { simp only [C.map_y, C.map_two_add_x_add_y, dependent_mk_iff₃, 
      fintype.not_linear_independent_iff], 
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num } },
  { simp only [C.map_one, C.map_one_add_x, dependent_mk_iff₃, 
      fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num } },
end

lemma map_to_frac (n : ℕ) : 
  (φ ((2 - n) + x + y) = mk[F] (n,1,1)) ∧ 
  (φ ((1 - n) + x) = mk[F] (n,1,0)) :=
begin
  induction n with n hn,
  { simp only [nat.cast_zero, sub_zero],
    refine ⟨C.map_two_add_x_add_y, C.map_one_add_x⟩ },
  cases hn with h1 h2,
  have key : φ ((2 - (↑n+1)) + x + y) = mk[F] (↑n+1,1,1), 
  { apply eq_of_config _ _ _ _ _ _ _ (frac_config F n),
    { rw [← h2, ← C.map_y],
      rw (show 2 - (↑n + 1) + x + y = (1 - ↑n + x) + y, by ring),
      apply C.dependent_pos },
    { rw [← h1, ← C.map_one],  
      convert C.dependent_neg _ _, ring },
    { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],  
      use ![1,1,-1], split,
      { simp [fin.sum_univ_succ] },
      { use 0, norm_num } },
    { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],  
      use ![1,1,-1], split,
      { simp [fin.sum_univ_succ] },
      { use 0, norm_num } } },
  refine ⟨_, _⟩,
  { exact_mod_cast key },
  apply eq_of_config _ _ _ _ _ _ _ (frac_config' F n),
  { rw [← h2, ← C.map_one],  
    convert C.dependent_neg _ _, 
    push_cast, ring },
  { rw [← key, ← C.map_one_add_y],
    convert C.dependent_neg _ _,
    push_cast, ring },
  { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num } },
  { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp only [fin.sum_univ_succ, nat.cast_succ, matrix.cons_val_zero, prod.smul_mk, 
        algebra.id.smul_eq_mul, one_mul, mul_one, matrix.cons_val_succ, neg_smul, 
        mul_zero, prod.neg_mk, neg_zero, fintype.univ_of_subsingleton,
        fin.mk_zero, matrix.cons_val_fin_one, neg_add_rev, finset.sum_const, 
        finset.card_singleton, smul_add, nsmul_eq_mul, nat.cast_one, prod.mk_add_mk, 
        zero_add, add_zero, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true], 
      ring },
    { use 0, norm_num } },
end

lemma map_to_frac_horizontal (n m : ℕ) (hn : (n : F) ≠ 0) (hm : m ≠ 0) :
  (φ ((1 + m - n) + m * x + y) = mk[F] (n,m,1)) ∧ 
  (φ ((m-n) + m * x) = projectivization.mk F (n,m,0) (λ c, hn (congr_arg prod.fst c))) := 
begin
  cases m, { exfalso, exact hm rfl },
  induction m with m H,
  { convert (C.map_to_frac n) using 3, 
    { push_cast, ring },
    { exact_mod_cast rfl },
    { push_cast, ring },
    { exact_mod_cast rfl } },
  specialize H (m.succ_ne_zero),
  have key : 
    φ (1 + m + 2 - n + (m + 2) * x + y) = 
    projectivization.mk F (n, m + 1 + 1, 1) (λ c, hn (congr_arg prod.fst c)), 
  { apply eq_of_config _ _ _ _ _ _ _ (frac_config_horizontal F n (m + 1) hn),
    { rw [← H.2, ← C.map_two_add_x_add_y],
      convert C.dependent_pos _ _ using 5,
      push_cast, ring },
    { erw [← H.1, ← C.map_one_add_x],
      convert C.dependent_pos _ _ using 5,
      push_cast, ring },
    { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],  
      use ![1,1,-1], split,
      { simp only [fin.sum_univ_succ, nat.cast_add, nat.cast_one, matrix.cons_val_zero, 
          prod.smul_mk, algebra.id.smul_eq_mul, one_mul, mul_zero, matrix.cons_val_succ, 
          mul_one, fintype.univ_of_subsingleton, fin.mk_zero,
          matrix.cons_val_fin_one, neg_smul, prod.neg_mk, neg_add_rev, finset.sum_const, 
          finset.card_singleton, nsmul_eq_mul, prod.mk_add_mk, zero_add, add_right_neg, 
          prod.mk_eq_zero, eq_self_iff_true, and_true, true_and], 
        ring },
      { use 0, norm_num } },
    { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
      use ![1,1,-1], split,
      { simp only [fin.sum_univ_succ, nat.cast_add, nat.cast_one, matrix.cons_val_zero, 
          prod.smul_mk, algebra.id.smul_eq_mul, one_mul, mul_zero, matrix.cons_val_succ, 
          mul_one, fintype.univ_of_subsingleton, fin.mk_zero,
          matrix.cons_val_fin_one, neg_smul, prod.neg_mk, neg_add_rev, finset.sum_const, 
          finset.card_singleton, nsmul_eq_mul, prod.mk_add_mk, zero_add, add_right_neg, 
          prod.mk_eq_zero, eq_self_iff_true, and_true, true_and], 
        ring },
      { use 0, norm_num } } },
  split, { exact_mod_cast key },
  push_cast at H,
  apply eq_of_config _ _ _ _ _ _ _ (frac_config_horizontal' F n (m + 1) hn),
  { push_cast, rw [← key, ← C.map_one_add_y],
    convert C.dependent_neg _ _ using 5, ring },
  { push_cast, rw [← H.2, ← C.map_one_add_x],
    convert C.dependent_pos _ _ using 5, ring },
  { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,-1,-1], split,
    { simp only [fin.sum_univ_succ, nat.cast_add, nat.cast_one, nat.cast_succ, 
        matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, one_mul, 
        mul_one, matrix.cons_val_succ, neg_smul, mul_zero, prod.neg_mk, neg_zero,
        fintype.univ_of_subsingleton, fin.mk_zero, 
        matrix.cons_val_fin_one, neg_add_rev, finset.sum_const, finset.card_singleton, 
        nsmul_eq_mul, mul_neg, smul_add, smul_zero, prod.mk_add_mk, zero_add, add_zero, 
        add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true, true_and], 
      simp only [nat.cast_zero, zero_add, one_mul, prod.mk_add_mk, add_zero, 
        add_right_neg, prod.mk_eq_zero, eq_self_iff_true,
        and_true, true_and], 
      ring },
    { use 0, norm_num } },
  { rw [dependent_mk_iff₃, fintype.not_linear_independent_iff],
    use ![1,1,-1], split,
    { simp only [fin.sum_univ_succ, nat.cast_add, nat.cast_one, nat.cast_succ, 
        matrix.cons_val_zero, prod.smul_mk, algebra.id.smul_eq_mul, one_mul, 
        mul_zero, matrix.cons_val_succ, mul_one, fintype.univ_of_subsingleton,
        fin.mk_zero, matrix.cons_val_fin_one, neg_smul, 
        prod.neg_mk, neg_add_rev, neg_zero, finset.sum_const, finset.card_singleton, 
        nsmul_eq_mul, mul_neg, smul_add, smul_zero, prod.mk_add_mk, zero_add,
        add_neg_cancel_left, add_zero, add_right_neg, prod.mk_eq_zero, eq_self_iff_true, 
        and_true, true_and, ne.def],
      simp only [nat.cast_zero, zero_add, one_mul, prod.mk_add_mk, add_neg_cancel_left, 
        add_right_neg, prod.mk_eq_zero, eq_self_iff_true, and_true, true_and],
      ring },
    { use 0, norm_num } },
end

/-! 

Now we use the symmetry of the situation.

-/

omit C

variable (F)

@[simps]
def negate_snd_equiv : (F × F × F) ≃ₗ[F] (F × F × F) := 
{ to_fun := λ a, ⟨a.1, -a.2.1, a.2.2⟩,
  map_add' := by { intros x y, ext; simp; ring },
  map_smul' := by { intros r x, ext; dsimp; simp; ring },
  inv_fun := λ a, ⟨a.1, -a.2.1, a.2.2⟩,
  left_inv := by { intros x, ext; simp },
  right_inv := by { intros x, ext; simp } }

@[simp]
lemma negate_snd_equiv_negate_snd_equiv_apply (x : F × F × F) : 
  negate_snd_equiv F (negate_snd_equiv F x) = x :=
begin
  cases x, dsimp, simp,
end

@[simp]
lemma negate_snd_equiv_comp_negate_snd_equiv : 
  (negate_snd_equiv F).to_linear_map.comp (negate_snd_equiv F).to_linear_map = linear_map.id := 
by { apply fun_like.ext, dsimp, simp }

variable {F}
include C

def negate_snd : setup (map (negate_snd_equiv F).to_linear_map (negate_snd_equiv F).injective ∘ φ)
  (-2 - x) y :=
{ map_zero := begin
    dsimp,
    rw [C.map_zero, map_mk_eq_mk],
    dsimp, simp only [neg_zero], 
  end,
  map_one := begin
    dsimp,
    rw [C.map_one, map_mk_eq_mk],
    dsimp, simp only [neg_zero], 
  end,
  map_x := begin
    dsimp,
    rw [(show -2 - x = -(2+x), by ring), C.map_neg, C.map_two_add_x, map_mk_eq_mk],
    dsimp, simp only [neg_neg],
  end,
  map_y := begin
    dsimp,
    rw [C.map_y, map_mk_eq_mk],
    dsimp, simp only [neg_zero], 
  end,
  map_one_add_x := begin
    dsimp,
    rw [(show 1 + (-2 - x) = -(1 + x), by ring), C.map_neg, C.map_one_add_x, map_mk_eq_mk],
    dsimp, rw mk_eq_mk_iff, use (-1), norm_num,
  end,
  map_one_add_y := begin
    dsimp, rw [C.map_one_add_y, map_mk_eq_mk],
    dsimp, simp only [neg_zero],
  end,
  map_neg := begin
    intros u, dsimp, rw [C.map_neg],
  end,
  dependent_pos := begin
    intros u v,
    rw ← dependent_iff_dependent₃, apply C.dependent_pos,
  end,
  dependent_neg := begin
    intros u v,
    rw ← dependent_iff_dependent₃, apply C.dependent_neg,
  end }

theorem main_theorem (m : ℤ) (n : ℕ) (h : ((n : F), (m : F), (0 : F)) ≠ 0) : 
  ∃ (t : K), φ t = projectivization.mk F ((n : F), (m : F), 0) h :=
begin
  induction m,
  { cases m, 
    { have H : ((n : F), (0 : F), (0 : F)) ≠ 0, by simpa using h,
      simp only [nat.nat_zero_eq_zero, int.of_nat_eq_coe, int.coe_nat_zero, int.cast_zero],
      use 1, symmetry, rw [C.map_one, mk_eq_mk_iff],
      simp only [ne.def, prod.mk_eq_zero, eq_self_iff_true, and_true] at H,
      use (is_unit.mk0 _ H).unit, simp [units.smul_def] },
    simp only [int.of_nat_eq_coe, int.coe_nat_succ, int.cast_add, int.cast_coe_nat, int.cast_one],
    by_cases hn : (n : F) = 0,
    { use 1 + x, 
      have H : (m : F) + 1 ≠ 0, by simpa [hn] using h,
      simp only [hn], rw C.map_one_add_x, symmetry, rw mk_eq_mk_iff,
      use (is_unit.mk0 ((m : F) + 1) H).unit, simp [units.smul_def] },
    { have := (C.map_to_frac_horizontal n (m + 1) hn (by norm_num)).2, 
      push_cast at this,
      refine ⟨_, this⟩ } },
  { let H := h, --push_cast at H, 
    by_cases hn : (n : F) = 0, 
    { simp only [hn, int.cast_neg_succ_of_nat, neg_add_rev, ne.def, prod.mk_eq_zero, 
        eq_self_iff_true, and_true, true_and] at H ⊢,  
      use 1 + x,
      symmetry, rw [C.map_one_add_x, mk_eq_mk_iff],
      use (is_unit.mk0 _ H).unit, simp [units.smul_def] },
    { have := (C.negate_snd.map_to_frac_horizontal n (m + 1) hn (by norm_num)).2,
      push_cast at this ⊢,
      let E := negate_snd_equiv F,
      apply_fun (map E.to_linear_map E.injective) at this,
      dsimp [map_mk_eq_mk] at this,
      change ((map E.to_linear_map E.injective) ∘ (map E.to_linear_map E.injective)) _ = _ at this, 
      rw ← map_comp at this,
      conv_lhs at this 
      { congr, erw negate_snd_equiv_comp_negate_snd_equiv },
      erw map_id at this, dsimp [id] at this,
      refine ⟨_, by exact_mod_cast this⟩, } }
end


--lemma map_to_frac_horizontal (n m : ℕ) (hn : (n : F) ≠ 0) (hm : m ≠ 0) :
--  (φ ((1 + m - n) + m * x + y) = mk[F] (n,m,1)) ∧ 
theorem main_theorem_char (m : ℕ) (hm : m ≠ 0) : 
  (φ ((m-1) + m * x) = mk[F] (1,m,0)) := 
by convert (map_to_frac_horizontal C 1 m _ hm).2; norm_num

end setup