import cl
import for_mathlib.projective_space.affine_embedding
import for_mathlib.finite_dimensional
import data.zmod.algebra

noncomputable theory
open_locale tensor_product
open_locale classical

open module

variables {K F : Type*} [field K] [field F] 

class is_prime_field (F : Type*) [field F] :=
(cond [] : ∀ a : F, ∃ (m : ℤ) (n : ℕ) (hn : (n : F) ≠ 0), a = m/n)

lemma eq_zero_or_one_of_is_prime_field_of_two (F : Type*) [field F] 
  [is_prime_field F] (htwo : (2 : F) = 0) (a : F) :
  a = 0 ∨ a = 1 := 
begin
  obtain ⟨m,n,hnz,rfl⟩ := is_prime_field.cond a,
  have : (2 : ℤ) * (m / 2) + (m % 2) = m := int.div_add_mod m 2,
  rw ← this,
  field_simp,
  have : 2 * (n/2) + (n % 2) = n := nat.div_add_mod n 2,
  rw ← this at ⊢ hnz,
  push_cast at hnz, simp [(show (1 : F) + 1 = 2, by ring), htwo] at hnz,
  push_cast, simp [htwo, (show (1 : F) + 1 = 2, by ring)],
  cases int.mod_two_eq_zero_or_one m with hm hm;
  cases nat.mod_two_eq_zero_or_one n with hn hn;
  simp [hn,hm],
  apply hnz, 
  rw hn, push_cast,
end

instance : is_prime_field ℚ := 
begin
  constructor, intros a, 
  rcases a with ⟨m,n,h1,h2⟩,
  refine ⟨m,n,_,_⟩,
  { intro c, norm_cast at c, rw c at h1, exact nat.lt_asymm h1 h1 },
  { norm_cast, exact rat.num_denom', }
end

instance (p : ℕ) [fact (nat.prime p)] : is_prime_field (zmod p) :=
begin
  constructor, intros a, 
  refine ⟨a.val, 1, _, _⟩,
  { push_cast, simp },
  { simp },
end

namespace bridge

structure setup
  (H : submodule F (mul_base_change K F)) 
  (hH : (H.dual_annihilator : submodule F _).acl) :=
(u v : Kˣ)
(hu : u.as ∉ H) (hv : v.as ∉ H)
(hu₁ : ∀ y : Kˣ, (y : K) = 1 + u → y.as ∉ H)
(hu₂ : ∀ y : Kˣ, (y : K) = 1 + u → (u⁻¹ * y).as ∉ H)
(hv₁: ∀ y : Kˣ, (y : K) = 1 + v → y.as ∉ H)
(hv₂ : ∀ y : Kˣ, (y : K) = 1 + v → (v⁻¹ * y).as ∉ H)
(li : linear_independent F ![H.mkq u.as, H.mkq v.as])

namespace setup

variables 
  {H : submodule F (mul_base_change K F)}
  {hH : H.dual_annihilator.acl} 
  (S : setup H hH)

def e := ![H.mkq S.u.as, H.mkq S.v.as]

include S
lemma mkq_neg_one : H.mkq (-1 : Kˣ).as = 0 :=
begin
  simp,
  have := hH.neg_one,
  rw ← H.dual_annihilator_dual_annihilator_comap,
  rw submodule.mem_dual_annihilator_comap_iff,
  exact this,
end

lemma mkq_neg (u : Kˣ) : H.mkq (-u).as = H.mkq u.as :=
begin
  have : -u = (-1) * u, by simp only [neg_mul, one_mul],
  simp only [this, units.as_mul, linear_map.map_add, S.mkq_neg_one, zero_add],
end

lemma exists_of_one_add_u (y : Kˣ) (hy : (y : K) = 1 + S.u) :
  ∃ (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1), 
  H.mkq y.as = a • H.mkq S.u.as := 
begin
  have := submodule.dependent_of_acl _ hH (-S.u) y _,
  swap, { push_cast, rwa [neg_add_eq_iff_eq_add, add_comm] },
  rw fintype.not_linear_independent_iff at this,
  obtain ⟨g,h1,i,h2⟩ := this,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, 
    fintype.univ_of_subsingleton, 
    fin.mk_zero, matrix.cons_val_succ, finset.sum_singleton, 
    fin.succ_zero_eq_one] at h1,
  apply_fun H.quotient_dual_dual_equiv at h1,
  simp only [linear_equiv.map_add,
    linear_equiv.map_smul, linear_equiv.map_zero, 
    H.quotient_dual_dual_equiv_apply, S.mkq_neg] at h1,
  have hg1 : g 1 ≠ 0,
  { intro c, 
    fin_cases i, swap, { contradiction },
    simp only [c, zero_smul, add_zero, zero_add, smul_eq_zero] at h1, 
    cases h1, { contradiction },
    simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1,
    exact S.hu h1 },
  have hg0 : g 0 ≠ 0,
  { intro c, 
    fin_cases i, { contradiction },
    simp only [c, zero_smul, add_zero, zero_add, smul_eq_zero] at h1,
    cases h1, { contradiction },
    simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1,
    exact S.hu₁ y hy h1 },
  use (- g 0 / g 1),
  refine ⟨_,_,_⟩,
  { field_simp, assumption },
  { field_simp,  
    intro c, rw ← c at h1,
    simp only [neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_eq_zero] at h1,
    cases h1, { contradiction },
    rw [sub_eq_zero] at h1, replace h1 := h1.symm, 
    rw ← sub_eq_zero at h1,
    rw [← H.mkq.map_sub, submodule.mkq_apply, 
      submodule.quotient.mk_eq_zero, ← units.as_div] at h1,
    apply S.hu₂ y hy, convert h1 using 2,
    rw [mul_comm, div_eq_mul_inv] },
  { apply_fun (λ e, (g 1)⁻¹ • e) at h1,
    simp only [smul_add, smul_zero, ← mul_smul, inv_mul_cancel hg1,
      one_smul, add_eq_zero_iff_neg_eq, ← neg_smul] at h1,
    convert h1.symm using 3, field_simp },
end

lemma exists_of_one_add_v (y : Kˣ) (hy : (y : K) = 1 + S.v) :
  ∃ (b : F) (hb0 : b ≠ 0) (ha1 : b ≠ 1), 
  H.mkq y.as = b • H.mkq S.v.as := 
begin
  have := submodule.dependent_of_acl _ hH (-S.v) y _,
  swap, { push_cast, rwa [neg_add_eq_iff_eq_add, add_comm] },
  rw fintype.not_linear_independent_iff at this,
  obtain ⟨g,h1,i,h2⟩ := this,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, 
    fintype.univ_of_subsingleton, 
    fin.mk_zero, matrix.cons_val_succ, finset.sum_singleton, 
    fin.succ_zero_eq_one] at h1,
  apply_fun H.quotient_dual_dual_equiv at h1,
  simp only [linear_equiv.map_add,
    linear_equiv.map_smul, linear_equiv.map_zero, 
    H.quotient_dual_dual_equiv_apply, S.mkq_neg] at h1,
  have hg1 : g 1 ≠ 0,
  { intro c, 
    fin_cases i, swap, { contradiction },
    simp only [c, zero_smul, add_zero, zero_add, smul_eq_zero] at h1, 
    cases h1, { contradiction },
    simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1,
    exact S.hv h1 },
  have hg0 : g 0 ≠ 0,
  { intro c, 
    fin_cases i, { contradiction },
    simp only [c, zero_smul, add_zero, zero_add, smul_eq_zero] at h1,
    cases h1, { contradiction },
    simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1,
    exact S.hv₁ y hy h1 },
  use (- g 0 / g 1),
  refine ⟨_,_,_⟩,
  { field_simp, assumption },
  { field_simp,  
    intro c, rw ← c at h1,
    simp only [neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_eq_zero] at h1,
    cases h1, { contradiction },
    rw [sub_eq_zero] at h1, replace h1 := h1.symm, 
    rw ← sub_eq_zero at h1,
    rw [← H.mkq.map_sub, submodule.mkq_apply, 
      submodule.quotient.mk_eq_zero, ← units.as_div] at h1,
    apply S.hv₂ y hy, convert h1 using 2,
    rw [mul_comm, div_eq_mul_inv] },
  { apply_fun (λ e, (g 1)⁻¹ • e) at h1,
    simp only [smul_add, smul_zero, ← mul_smul, inv_mul_cancel hg1,
      one_smul, add_eq_zero_iff_neg_eq, ← neg_smul] at h1,
    convert h1.symm using 3, field_simp },
end



def basis := basis.sum_extend S.li
def f : dual F (mul_base_change K F ⧸ H) := S.basis.coord (sum.inl 0)
def g : dual F (mul_base_change K F ⧸ H) := S.basis.coord (sum.inl 1)

@[simp] lemma f_map_u : S.f (H.mkq S.u.as) = 1 := 
begin
  change S.f (S.e 0) = 1,
  dsimp only [f,e],
  rw ← basis.sum_extend_extends _ S.li 0,
  dsimp [basis],
  simp only [basis.repr_self, finsupp.single_apply, if_pos rfl],
end

@[simp] lemma f_map_v : S.f (H.mkq S.v.as) = 0 := 
begin
  change S.f (S.e 1) = 0,
  dsimp only [f,e],
  rw ← basis.sum_extend_extends _ S.li 1,
  dsimp [basis],
  simp only [basis.repr_self, finsupp.single_apply],
  rw if_neg, norm_num
end

@[simp] lemma g_map_u : S.g (H.mkq S.u.as) = 0 := 
begin
  change S.g (S.e 0) = 0,
  dsimp only [g,e],
  rw ← basis.sum_extend_extends _ S.li 0,
  dsimp [basis],
  simp only [basis.repr_self, finsupp.single_apply],
  rw if_neg, norm_num
end

@[simp] lemma g_map_v : S.g (H.mkq S.v.as) = 1 := 
begin
  change S.g (S.e 1) = 1,
  dsimp only [g,e],
  rw ← basis.sum_extend_extends _ S.li 1,
  dsimp [basis],
  simp only [basis.repr_self, finsupp.single_apply, if_pos rfl],
end

def ψₗ : (mul_base_change K F ⧸ H) →ₗ[F] (F × F) := 
{ to_fun := λ t, (S.f t, S.g t),
  map_add' := λ x y, by ext; simp, 
  map_smul' := λ c x, by ext; simp } 

.

def ψₗ' : (mul_base_change K F) →ₗ[F] (F × F) := S.ψₗ.comp H.mkq

def ψ : Kˣ → F × F := λ x, S.ψₗ (H.mkq x.as)

lemma ψ_apply' (x : Kˣ) : S.ψ x = S.ψₗ' x.as := rfl
lemma ψ_apply (x : Kˣ) : S.ψ x = S.ψₗ (H.mkq x.as) := rfl

@[simp]
lemma ψ_map_mul (x y : Kˣ) : S.ψ (x * y) = S.ψ x + S.ψ y :=
by simp only [S.ψ_apply', units.as_mul, linear_map.map_add]

@[simp]
lemma ψ_map_one : S.ψ 1 = 0 := 
by simp only [S.ψ_apply', units.as_one, linear_map.map_zero]

@[simp]
lemma ψ_map_inv (x : Kˣ) : S.ψ x⁻¹ = - S.ψ x := 
by simp only [S.ψ_apply', units.as_inv, linear_map.map_neg]

@[simp]
lemma ψ_map_neg_one : S.ψ (-1 : Kˣ) = 0 :=
begin
  have := submodule.neg_one_mem_of_acl _ hH,
  rw S.ψ_apply, rw submodule.dual_annihilator_dual_annihilator_comap at this,
  have : H.mkq (-1 : Kˣ).as = 0, 
    simpa only [submodule.mkq_apply, submodule.quotient.mk_eq_zero],
  simp [this]
end

@[simp]
lemma ψ_map_neg (x : Kˣ) : S.ψ (-x) = S.ψ x := 
begin
  rw neg_eq_neg_one_mul,
  simp only [S.ψ_map_mul, S.ψ_map_neg_one, zero_add],
end

lemma ψ_dep (x y : Kˣ) (hxy : (x : K) + y = 1) :
  ¬ linear_independent F ![S.ψ x, S.ψ y] := 
begin
  have h := submodule.dependent_of_acl _ hH x y hxy,
  simp only [fintype.not_linear_independent_iff] at h ⊢,
  obtain ⟨g,h1,h2⟩ := h,
  refine ⟨g,_,h2⟩,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, fintype.univ_of_subsingleton, 
    fin.mk_zero, matrix.cons_val_succ, finset.sum_singleton, 
    fin.succ_zero_eq_one] at h1 ⊢,
  simp only [S.ψ_apply, ← linear_map.map_smul, ← linear_map.map_add] at 
    h1 ⊢,
  have : (H.mkq) (g 0 • x.as + g 1 • y.as) = 0,
  { simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1 ⊢,
    rwa [submodule.dual_annihilator_dual_annihilator_comap] at h1 },
  simp [this]
end

lemma ψ_dep' (x y : Kˣ) (hxy : (x : K) - y = 1) :
  ¬ linear_independent F ![S.ψ x, S.ψ y] := 
begin
  have h := submodule.dependent_of_acl _ hH x (-y) _,
  rw ← S.ψ_map_neg y,
  simp only [fintype.not_linear_independent_iff] at h ⊢,
  obtain ⟨g,h1,h2⟩ := h,
  refine ⟨g,_,h2⟩,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, fintype.univ_of_subsingleton, 
    fin.mk_zero, matrix.cons_val_succ, finset.sum_singleton, 
    fin.succ_zero_eq_one] at h1 ⊢,
  simp only [S.ψ_apply, ← linear_map.map_smul, ← linear_map.map_add] at 
    h1 ⊢,
  have : (H.mkq) (g 0 • x.as + g 1 • (-y).as) = 0,
  { simp only [submodule.mkq_apply, submodule.quotient.mk_eq_zero] at h1 ⊢,
    rwa [submodule.dual_annihilator_dual_annihilator_comap] at h1 },
  simp [this], 
  convert hxy, push_cast, ring,
end

@[simp]
lemma ψ_map_u :
  S.ψ S.u = (1,0) := 
begin
  ext, exact S.f_map_u, exact S.g_map_u,
end

@[simp]
lemma ψ_map_v : 
  S.ψ S.v = (0,1) := 
begin
  ext, exact S.f_map_v, exact S.g_map_v,
end

lemma one_add_u_ne_zero : (1 : K) + S.u ≠ 0 :=
begin
  intro c, rw add_eq_zero_iff_neg_eq at c,
  have hh : (-1 : Kˣ) = S.u, ext, exact c,
  have := S.ψ_map_u, rw [← hh, S.ψ_map_neg_one] at this,
  apply (zero_ne_one : ((0 : F) ≠ 1)),
  exact congr_arg prod.fst this
end

lemma one_sub_u_ne_zero : (1 : K) - S.u ≠ 0 :=
begin
  intro c, rw sub_eq_zero at c, have hh : S.u = 1, by { ext, exact c.symm },
  have := S.ψ_map_u, rw [hh, S.ψ_map_one] at this,
  apply (zero_ne_one : (0 : F) ≠ 1),
  exact congr_arg prod.fst this
end

lemma one_add_v_ne_zero : (1 : K) + S.v ≠ 0 :=
begin
  intro c, rw add_eq_zero_iff_neg_eq at c,
  have hh : (-1 : Kˣ) = S.v, ext, exact c,
  have := S.ψ_map_v, rw [← hh, S.ψ_map_neg_one] at this,
  apply (zero_ne_one : ((0 : F) ≠ 1)),
  exact congr_arg prod.snd this
end

lemma one_sub_v_ne_zero : (1 : K) - S.v ≠ 0 :=
begin
  intro c, rw sub_eq_zero at c, have hh : S.v = 1, by { ext, exact c.symm },
  have := S.ψ_map_v, rw [hh, S.ψ_map_one] at this,
  apply (zero_ne_one : (0 : F) ≠ 1),
  exact congr_arg prod.snd this
end

lemma ψ_exists_of_one_add_u (y : Kˣ) (hy : (y : K) = 1 + S.u) : 
  ∃ (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1), S.ψ y = (a,0) := 
begin
  obtain ⟨a,ha0,ha1,ha⟩ := S.exists_of_one_add_u y hy,
  use [a,ha0,ha1],
  rw [S.ψ_apply, ha, linear_map.map_smul, ← S.ψ_apply, S.ψ_map_u],
  simp,
end

lemma ψ_exists_of_one_add_v (y : Kˣ) (hy : (y : K) = 1 + S.v) : 
  ∃ (b : F) (hb0 : b ≠ 0) (hb1 : b ≠ 1), S.ψ y = (0,b) := 
begin
  obtain ⟨a,ha0,ha1,ha⟩ := S.exists_of_one_add_v y hy,
  use [a,ha0,ha1],
  rw [S.ψ_apply, ha, linear_map.map_smul, ← S.ψ_apply, S.ψ_map_v],
  simp,
end

def one_add_u : Kˣ := units.mk0 _ S.one_add_u_ne_zero 
def one_add_v : Kˣ := units.mk0 _ S.one_add_v_ne_zero

def A : F := 
(S.ψ_exists_of_one_add_u (units.mk0 _ S.one_add_u_ne_zero) 
  (by { dsimp, ring })).some

def B : F := 
(S.ψ_exists_of_one_add_v (units.mk0 _ S.one_add_v_ne_zero) 
  (by { dsimp, ring })).some

lemma A_ne_zero : S.A ≠ 0 := 
(S.ψ_exists_of_one_add_u (units.mk0 _ S.one_add_u_ne_zero) 
  (by { dsimp, ring })).some_spec.some

lemma B_ne_zero : S.B ≠ 0 := 
(S.ψ_exists_of_one_add_v (units.mk0 _ S.one_add_v_ne_zero) 
  (by { dsimp, ring })).some_spec.some

def A' : Fˣ := units.mk0 S.A S.A_ne_zero
def B' : Fˣ := units.mk0 S.B S.B_ne_zero

lemma A_ne_one : S.A ≠ 1 := 
(S.ψ_exists_of_one_add_u (units.mk0 _ S.one_add_u_ne_zero) 
  (by { dsimp, ring })).some_spec.some_spec.some

lemma B_ne_one : S.B ≠ 1 := 
(S.ψ_exists_of_one_add_v (units.mk0 _ S.one_add_v_ne_zero) 
  (by { dsimp, ring })).some_spec.some_spec.some

def A'_sub_one : Fˣ := units.mk0 (S.A - 1) 
  (λ c, S.A_ne_one $ by rwa sub_eq_zero at c)

def B'_sub_one : Fˣ := units.mk0 (S.B - 1)
  (λ c, S.B_ne_one $ by rwa sub_eq_zero at c)

lemma ψ_map_one_add_u : 
  S.ψ S.one_add_u = (S.A,0) :=
(S.ψ_exists_of_one_add_u (units.mk0 _ S.one_add_u_ne_zero) 
  (by { dsimp, ring })).some_spec.some_spec.some_spec

lemma ψ_map_one_add_v : 
  S.ψ S.one_add_v = (0,S.B) := 
(S.ψ_exists_of_one_add_v (units.mk0 _ S.one_add_v_ne_zero) 
  (by { dsimp, ring })).some_spec.some_spec.some_spec

def transform : 
  (F × F × F) →ₗ[F] (F × F × F) :=
{ to_fun := λ x, ⟨
    x.1 * S.A * S.B - x.2.1 * S.B - x.2.2 * S.A, 
    x.2.1 * S.B * (S.A - 1),
    x.2.2 * S.A * (S.B - 1)⟩,
  map_add' := λ x y, begin
    ext; dsimp; ring
  end,
  map_smul' := λ c x, begin
    ext; dsimp; ring
  end }

lemma transform_injective : 
  function.injective S.transform := 
begin
  rintros ⟨x₁,x₂,x₃⟩ ⟨y₁,y₂,y₃⟩ h,
  dsimp [transform] at h,
  simp only [prod.mk.inj_iff, mul_eq_mul_right_iff] at h,
  rcases h with ⟨h1,h2,h3⟩,
  cases h3, swap, { exfalso, apply S.B_ne_one, rwa [sub_eq_zero] at h3 },
  cases h3, swap, { exfalso, exact S.A_ne_zero h3 },
  cases h2, swap, { exfalso, apply S.A_ne_one, rwa [sub_eq_zero] at h2 },
  cases h2, swap, { exfalso, exact S.B_ne_zero h2 },
  simp only [h2, h3, sub_left_inj, mul_eq_mul_right_iff] at h1,
  cases h1, swap, { exfalso, exact S.B_ne_zero h1 },
  cases h1, swap, { exfalso, exact S.A_ne_zero h1 },
  ext, assumption'
end

def transform_equiv : 
  (F × F × F) ≃ₗ[F] (F × F × F) := 
S.transform.linear_equiv_of_injective S.transform_injective (by simp)

def φ : K → ℙ F (F × F × F) :=
λ x, if hx : x = 0 then mk[F] (1,0,0) else 
projectivization.map S.transform S.transform_injective $
projectivization.affine_embedding _ _ (S.ψ (units.mk0 x hx))

open projectivization

lemma φ_map_zero : S.φ 0 = (mk[F] (1,0,0)) := 
by { dsimp [φ], rw dif_pos rfl }

lemma φ_map_one : S.φ 1 = mk[F] (1,0,0) := 
begin
  dsimp [φ], rw dif_neg (one_ne_zero : (1 : K) ≠ 0),
  simp only [units.mk0_one, ψ_map_one],
  dsimp [affine_embedding],
  rw map_mk_eq_mk',
  dsimp [transform],
  rw mk_eq_mk_iff,
  use S.A' * S.B',
  simp [A', B', units.smul_def],
end

lemma φ_map_u : S.φ S.u = mk[F] (1,1,0) := 
begin
  dsimp [φ], rw dif_neg S.u.ne_zero,
  have : units.mk0 _ (S.u.ne_zero) = S.u, by { ext, refl }, rw this, clear this,
  rw S.ψ_map_u,
  dsimp [affine_embedding, map_mk_eq_mk', transform],
  rw mk_eq_mk_iff,
  simp,
  use S.B' * S.A'_sub_one,
  split,
  { dsimp [B', A'_sub_one, units.smul_def], ring },
  { dsimp [B', A'_sub_one, units.smul_def], ring }
end

lemma φ_map_v : S.φ S.v = mk[F] (1,0,1) := 
begin
  dsimp [φ], rw dif_neg S.v.ne_zero,
  have : units.mk0 _ (S.v.ne_zero) = S.v, by { ext, refl }, rw this, clear this,
  rw S.ψ_map_v,
  dsimp [affine_embedding, map_mk_eq_mk', transform],
  rw mk_eq_mk_iff,
  simp,
  use S.A' * S.B'_sub_one,
  split,
  { dsimp [A', B'_sub_one, units.smul_def], ring },
  { dsimp [A', B'_sub_one, units.smul_def], ring }
end

lemma φ_map_one_add_u : S.φ (1 + S.u) = mk[F] (0,1,0) := 
begin
  dsimp [φ], rw dif_neg S.one_add_u_ne_zero, 
  have : units.mk0 _ S.one_add_u_ne_zero = S.one_add_u := rfl, rw this, clear this,
  rw S.ψ_map_one_add_u,
  dsimp [affine_embedding, map_mk_eq_mk', transform],
  rw mk_eq_mk_iff,
  simp,
  use S.A' * S.B' * S.A'_sub_one,
  dsimp [A', B', A'_sub_one, units.smul_def], ring,
end

lemma φ_map_one_add_v : S.φ (1 + S.v) = mk[F] (0,0,1) := 
begin
  dsimp [φ], rw dif_neg S.one_add_v_ne_zero, 
  have : units.mk0 _ S.one_add_v_ne_zero = S.one_add_v := rfl, rw this, clear this,
  rw S.ψ_map_one_add_v,
  dsimp [affine_embedding, map_mk_eq_mk', transform],
  rw mk_eq_mk_iff,
  simp, split, { ring },
  use S.A' * S.B' * S.B'_sub_one,
  dsimp [A', B', B'_sub_one, units.smul_def], ring,
end

lemma φ_map_neg (x : K) : S.φ (-x) = S.φ x := 
begin
  by_cases hx : x = 0, { rw [hx, neg_zero] },
  dsimp [φ],
  rw [dif_neg (neg_ne_zero.mpr hx), dif_neg hx],
  have : units.mk0 (-x) (neg_ne_zero.mpr hx) = - (units.mk0 x hx), by { ext, refl },
  rw [this, S.ψ_map_neg],
end

lemma φ_dependent_pos (x y : K) :
  dependent ![S.φ x, S.φ y, S.φ (x + y)] := 
begin
  by_cases hx : x = 0,
  { simp only [hx, zero_add], rw [dependent_iff_rep, fintype.not_linear_independent_iff], 
    use ![0,1,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 1, norm_num } },
  by_cases hy : y = 0,
  { simp only [hy, add_zero], rw [dependent_iff_rep, fintype.not_linear_independent_iff], 
    use ![1,0,-1], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num } },
  by_cases hxy : x + y = 0,
  { rw add_eq_zero_iff_eq_neg at hxy, 
    simp only [hxy, S.φ_map_neg, add_left_neg],
    rw [dependent_iff_rep, fintype.not_linear_independent_iff], 
    use ![1,-1,0], split,
    { simp [fin.sum_univ_succ] },
    { use 0, norm_num } },
  dsimp [φ],
  rw [dif_neg hx, dif_neg hy, dif_neg hxy],
  dsimp [map_mk_eq_mk', affine_embedding],
  rw [dependent_mk_iff₃, ← comp_matrix_eq_matrix₃],

  let x' := units.mk0 x hx,
  let y' := units.mk0 y hy,
  let xy' := units.mk0 (x + y) hxy,

  suffices : ¬ linear_independent F ![((1 : F),S.ψ x'), (1, S.ψ y'), (1, S.ψ xy')],
  { intro c, 
    apply this, apply linear_independent.of_comp _ c },

  rw fintype.not_linear_independent_iff,
  let r := y' * x'⁻¹,
  let s := xy' * x'⁻¹,
  have hrs : (s : K) = 1 + r,
  { dsimp [r,s,x', units.mk0], field_simp },
  have HH := S.ψ_dep (-r) s _,
  swap, { rw hrs, push_cast, ring },
  rw S.ψ_map_neg at HH,
  dsimp [r,s] at HH,
  simp only [S.ψ_apply, units.as_mul, units.as_inv, 
    linear_map.map_add, linear_map.map_neg] at HH,
  simp only [← S.ψ_apply, fintype.not_linear_independent_iff] at HH,
  obtain ⟨g,h1,i,h2⟩ := HH,
  simp only [fin.sum_univ_succ, matrix.cons_val_zero, smul_add, smul_neg, 
    fintype.univ_of_subsingleton, 
    fin.mk_zero, matrix.cons_val_succ, finset.sum_singleton, 
    fin.succ_zero_eq_one] at h1,
  use ![- g 0 - g 1, g 0, g 1],
  split,
  { simp only [fin.sum_univ_succ, matrix.cons_val_zero, prod.smul_mk, 
      algebra.id.smul_eq_mul, mul_one, matrix.cons_val_succ, 
      fintype.univ_of_subsingleton, fin.mk_zero, 
      matrix.cons_val_fin_one, finset.sum_const, finset.card_singleton, 
      nsmul_eq_mul, nat.cast_one, one_mul, prod.mk_add_mk, sub_add_add_cancel, 
      add_left_neg, prod.mk_eq_zero, eq_self_iff_true, true_and],
    rw ← h1, ext; dsimp [smul_eq_mul]; ring },
  { fin_cases i, use 1, use 2 }
end

lemma φ_dependent_neg (x y : K) :
  dependent ![S.φ x, S.φ y, S.φ (x - y)] := 
begin
  rw [← S.φ_map_neg y, sub_eq_add_neg],
  apply φ_dependent_pos,
end

def make : _root_.setup S.φ S.u S.v :=  
{ map_zero := S.φ_map_zero,
  map_one := S.φ_map_one, 
  map_x := S.φ_map_u,
  map_y := S.φ_map_v,
  map_one_add_x := S.φ_map_one_add_u,
  map_one_add_y := S.φ_map_one_add_v,
  map_neg := S.φ_map_neg,
  dependent_pos := S.φ_dependent_pos, 
  dependent_neg := S.φ_dependent_neg }

end setup

end bridge

theorem bridge 
  [is_prime_field F]
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
  obtain ⟨m,n,hn,hh⟩ := is_prime_field.cond (1 - S.A),
  have := E.main_theorem m n (λ c, hn (congr_arg prod.fst c)), 
  obtain ⟨t,ht⟩ := this,
  have hm : (m : F) ≠ 0,
  { intro c, simp only [c, zero_div] at hh, 
    apply S.A_ne_one, rw sub_eq_zero at hh, exact hh.symm },
  have htz : t ≠ 0,
  { intro c, 
    rw [c, E.map_zero] at ht,
    replace ht := ht.symm,
    rw projectivization.mk_eq_mk_iff at ht,
    obtain ⟨u,hu⟩ := ht,
    simp only [prod.smul_mk, smul_zero, prod.mk.inj_iff, 
      eq_self_iff_true, and_true, units.smul_def, smul_eq_mul, mul_one, 
      mul_zero] at hu,
    exact hm hu.2.symm },
  dsimp [bridge.setup.φ] at ht,
  rw dif_neg htz at ht,
  dsimp [projectivization.affine_embedding, projectivization.map_mk_eq_mk'] at ht,
  rw projectivization.mk_eq_mk_iff at ht,
  obtain ⟨a,ha⟩ := ht,
  dsimp [bridge.setup.transform] at ha,
  simp only [smul_zero, one_mul, prod.mk.inj_iff, zero_eq_mul, mul_eq_zero] at ha,
  rcases ha with ⟨h1,h2,h3⟩,
  cases h3, swap, { apply S.B_ne_one, rwa sub_eq_zero at h3 },
  cases h3, swap, { exact S.A_ne_zero h3 },
  rw [h3, zero_mul, sub_zero] at h1,
  have : S.A - 1 = (-m) / n, 
  { field_simp at ⊢ hh, rw ← hh, ring },
  rw this at h2, dsimp [units.smul_def] at h2, field_simp at h2,
  --apply_fun (λ e, e / (m : F)) at h2, field_simp [hm] at h2,
  rw (show (a : F) * m * n = m * (a * n), by ring) at h2,
  rw (show -((S.ψ (units.mk0 t htz)).fst * S.B * m) = 
    m * (-(S.ψ (units.mk0 t htz)).fst * S.B), by ring) at h2,
  apply_fun (λ e, (m : F)⁻¹ * e) at h2,
  simp only [← mul_assoc, inv_mul_cancel hm, one_mul] at h2,
  dsimp [units.smul_def, smul_eq_mul] at h1,
  rw h2 at h1,
  replace h1 := h1.symm,
  rw sub_eq_iff_eq_add at h1,
  simp only [neg_mul, add_left_neg, mul_eq_zero] at h1,
  cases h1, 
  { apply S.A_ne_zero h1 },
  { apply S.B_ne_zero h1 }
end

def submodule.nonrig_condition (T : submodule F (mul_base_change K F)) 
  (x : Kˣ) : Prop := 
x.as ∉ T ∧ 
∀ (y : Kˣ) (hy : (y : K) = 1 + x), y.as ∉ T ∧ (x⁻¹ * y).as ∉ T

def submodule.nonrig (T : submodule F (mul_base_change K F)) : 
  submodule F (mul_base_change K F) := 
T ⊔ (submodule.span _ $ units.as '' set_of T.nonrig_condition)

lemma submodule.le_nonrig (T : submodule F (mul_base_change K F)) : 
  T ≤ T.nonrig := le_sup_left

lemma bridge_finite_dimensional
  [is_prime_field F]
  (T : submodule F (mul_base_change K F))
  (hT : T.dual_annihilator.acl) : 
  finite_dimensional F (T.nonrig ⧸ T.comap T.nonrig.subtype) := 
begin
  by_cases hh : ∃ (u : Kˣ), T.nonrig_condition u,
  swap, 
  { push_neg at hh, 
    have : set_of T.nonrig_condition = ∅,
    { rw set.eq_empty_iff_forall_not_mem,  
      exact hh },
    dsimp [submodule.nonrig],
    rw [this, set.image_empty],
    have he := submodule.mkq_comp_sup_mod_surjective (submodule.span F ∅) T,
    let e : _ →ₗ[_] _ := _, change function.surjective e at he,
    haveI : finite_dimensional F (submodule.span F (∅ : set (mul_base_change K F))), 
    { apply finite_dimensional.span_of_finite, exact set.finite_empty },
    apply e.finite_dimensional_of_surjective,
    rwa linear_map.range_eq_top },
  obtain ⟨u,hu⟩ := hh,
  apply T.finite_dimensional_of_not_linear_independent 
    (units.as '' set_of T.nonrig_condition) u.as ⟨u,hu,rfl⟩ hu.1,
  rintros a ⟨a,ha,rfl⟩,
  apply bridge T hT a u ha.1 hu.1 
    (λ y hy, (ha.2 y hy).1)
    (λ y hy, (ha.2 y hy).2)
    (λ y hy, (hu.2 y hy).1)
    (λ y hy, (hu.2 y hy).2)
end

theorem bridge_codim 
  [is_prime_field F] 
  (T : submodule F (mul_base_change K F)) 
  (hT : T.dual_annihilator.acl) : 
  finite_dimensional.finrank F (T.nonrig ⧸ T.comap T.nonrig.subtype) ≤ 1 := 
begin
  have fd : finite_dimensional F (T.nonrig ⧸ T.comap T.nonrig.subtype) := 
    bridge_finite_dimensional T hT,
  by_cases hh : ∃ (u : Kˣ), T.nonrig_condition u,
  swap,
  { push_neg at hh, 
    have : set_of T.nonrig_condition = ∅,
    { rw set.eq_empty_iff_forall_not_mem,  
      exact hh },
    dsimp [submodule.nonrig] at *,
    rw [this, set.image_empty] at *,
    have he := submodule.mkq_comp_sup_mod_surjective (submodule.span F ∅) T,
    resetI,
    rw finrank_le_one_iff,
    use 0, rintros ⟨w,hw⟩, use 0, rw submodule.mem_sup at hw,
    obtain ⟨y,hy,z,hz,rfl⟩ := hw,
    simp only [submodule.span_empty, submodule.mem_bot] at hz,
    symmetry,
    simpa only [hz, add_zero, submodule.quotient.quot_mk_eq_mk, smul_zero, 
      submodule.quotient.mk_eq_zero] },
  obtain ⟨u,hu⟩ := hh,
  apply T.finrank_le_one_of_not_linear_independent 
    (units.as '' set_of T.nonrig_condition) u.as ⟨u,hu,rfl⟩ hu.1,
  rintros a ⟨a,ha,rfl⟩,
  apply bridge T hT a u ha.1 hu.1 
    (λ y hy, (ha.2 y hy).1)
    (λ y hy, (ha.2 y hy).2)
    (λ y hy, (hu.2 y hy).1)
    (λ y hy, (hu.2 y hy).2)
end
  

