import rigid_elements.valuation_subring_of_preadditive

variables {K : Type*} [field K] {T H : mul_subgroup K} (rp : rigid_pair T H)

open rigid_pair

-- Prop 2.12
lemma rigid_pair.preadditive_of_exists_UU (u : K)
  (hu : u ∈ rp.UU) (hu' : u ∉ T) : rp.preadditive := 
begin
  rw preadditive_iff,
  intros x y hx hy,
  by_cases hxz : -x = 0, { rw neg_eq_zero at hxz, simp [hxz, T.one_mem] },
  have H1 := rp.neg _ hx.1 (1 + x) (1 + y) hx.2 hy.2 hxz,
  have hxu : u⁻¹ * x ∈ rp.OO_m,
  { apply hu.2.2, assumption },
  have huy : u * y ∈ rp.OO_m,
  { apply hu.1.2, assumption },
  have z1 : - (x * u) ≠ 0, 
  { simp only [ne.def, neg_eq_zero, mul_eq_zero, inv_eq_zero], 
    push_neg, split, swap,
    { apply rp.UU_ne_zero_of_mem u hu },
    { simpa using hxz } },
  have H2 := rp.neg _ hxu.1 _ _ hxu.2 huy.2 _,
  cases H1; cases H2,
  { convert H1, ring },
  { convert H1, ring },
  { convert H2, 
    field_simp [rp.UU_ne_zero_of_mem u hu], ring },
  { exfalso,
    have := T.mul_mem (T.inv_mem H1) H2,
    apply hu', convert this,
    have aux : ((-(u⁻¹ * x))⁻¹ * (1 + u⁻¹ * x) + (1 + u * y)) = 
      u * ((-x)⁻¹ * (1 + x) + (1 + y)),
    field_simp [rp.UU_ne_zero_of_mem u hu], ring,
    rw [aux, ← mul_assoc, mul_comm _ u, mul_assoc, inv_mul_cancel, mul_one], 
    exact T.ne_zero_of_mem H1 },
  simp only [ne.def, neg_eq_zero, mul_eq_zero, inv_eq_zero],
  push_neg, split, exact rp.UU_ne_zero_of_mem u hu, simpa using hxz,
end

-- Lemma 2.13
lemma rigid_pair.OO_p_mem_of_mem_nmem_nmem (u : K) :
  u ∈ H → u ∉ T → 1 - u⁻¹ ∉ T → u ∈ rp.OO_p :=
begin
  intros h1 h2 h3,
  by_cases hu : u - 1 = 0, 
  { rw sub_eq_zero at hu, rw hu, apply rp.OO_p_one_mem },
  have : u - 1 ∈ H,
  { by_contra c, have := rp.pos _ c 1 1 T.one_mem T.one_mem hu, 
  cases this, { apply h2, convert this, ring },
  apply h3, 
  rw ← inv_inv (1 - u⁻¹), apply T.inv_mem,
  convert this, field_simp [H.ne_zero_of_mem h1] },
  refine ⟨h1, _⟩, intros x hx,
  have hux : u * x ∉ H,
  { intro c, apply hx.1, convert H.mul_mem (H.inv_mem h1) c,
    field_simp [H.ne_zero_of_mem h1], ring },
  have hux' : (u - 1) * x ∉ H,
  { intro c, apply hx.1, convert H.mul_mem (H.inv_mem this) c,
    field_simp [H.ne_zero_of_mem this], ring },
  by_cases huxz : u * x = 0, { rw huxz, apply rp.OO_m_zero_mem },
  have aux1 := rp.pos _ hux 1 1 T.one_mem T.one_mem huxz,
  simp only [mul_one, mul_assoc] at aux1,
  by_cases huxz' : (u - 1) * x = 0, 
  { rw [sub_mul, one_mul, sub_eq_zero] at huxz', rw huxz', exact hx },
  have aux2 := rp.pos _ hux' (1 + x) 1 hx.2 T.one_mem huxz',
  cases aux1; cases aux2,
  { exact ⟨hux, aux1⟩ },
  { exact ⟨hux, aux1⟩ },
  { refine ⟨hux, _⟩, convert aux2 using 1, ring },
  exfalso, apply h3,
  have : (1 - u⁻¹) * (((u - 1) * x)⁻¹ * (1 + x) + 1) = 
    (u * x)⁻¹ + 1, 
  { field_simp [H.ne_zero_of_mem h1], ring },
  convert T.mul_mem aux1 (T.inv_mem aux2), rw ← this,
  rw [mul_assoc, mul_inv_cancel, mul_one],
  apply T.ne_zero_of_mem aux2
end .

-- Prop 2.14
lemma rigid_pair.preadditive_of_nmem_of_neg_not_rigid (a : K) :
  a ≠ 0 → 
  a ∉ T → 
  ¬ (T.rigid (-a)) → rp.preadditive := 
begin
  intros ha haT nrig,
  have haH : a ∈ H,
  { by_contra c, 
    apply nrig,
    exact rp.neg _ c }, 
  dsimp [mul_subgroup.rigid] at nrig,
  push_neg at nrig,
  obtain ⟨s,t,hs,ht,ha',h1,h2⟩ := nrig,
  let z : K := s⁻¹ * t,
  have hz : z ∈ T := T.mul_mem (T.inv_mem hs) ht,
  replace h1 : (1 : K) - a * z ∉ T,
  { intros c, apply h1, convert T.mul_mem hs c, dsimp [z],
    field_simp [T.ne_zero_of_mem hs], ring },
  replace h2 : z - a⁻¹ ∉ T,
  { intros c, apply h2, convert T.mul_mem hs c, dsimp [z], 
    field_simp [T.ne_zero_of_mem hs, H.ne_zero_of_mem haH], ring },
  let u := a * z,
  have huT : u ∉ T,
  { intros c, apply haT, dsimp [u,z] at c,
    convert T.mul_mem (T.mul_mem c hs) (T.inv_mem ht),
    field_simp [T.ne_zero_of_mem hs, T.ne_zero_of_mem ht] },
  have huH : u ∈ H,
  { dsimp [u,z], 
    convert H.mul_mem haH (H.mul_mem (H.inv_mem _) _),
    exact rp.le hs, exact rp.le ht },
  have key : u ∈ rp.UU,
  { split, 
    { apply rp.OO_p_mem_of_mem_nmem_nmem, 
      assumption, assumption, dsimp [u], intros c, apply h2,
      convert T.mul_mem hz c,
      field_simp [H.ne_zero_of_mem haH, T.ne_zero_of_mem hz], ring },
    { apply rp.OO_p_mem_of_mem_nmem_nmem,
      exact H.inv_mem huH, intros c, apply huT, convert T.inv_mem c, rw inv_inv,
      rw inv_inv, exact h1 } },
  exact rp.preadditive_of_exists_UU u key huT,
end
