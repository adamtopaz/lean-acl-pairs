import for_mathlib.valuation_subring.basic
import rigid_elements.rigid_pair

variables {K : Type*} [field K] {T H : mul_subgroup K} {rp : rigid_pair T H}

open rigid_pair

lemma rigid_pair.preadditive.mul_mem (h : rp.preadditive) :
  ∀ (x y : K), x ∈ rp.OO → y ∈ rp.OO → x * y ∈ rp.OO :=
begin
  suffices : ∀ a b : K, a ∈ rp.OO_m → b ∈ rp.OO_m → a * b ∈ rp.OO,
  { rintros a b (ha|ha) (hb|hb), 
    { apply this, assumption' },
    { left, rw mul_comm, apply hb.2, assumption },
    { left, apply ha.2, assumption },
    { right, apply rp.OO_p_mul_mem, assumption' } },
  intros x y hx hy,
  by_cases hxy : x * y ∈ H, 
  { right, apply h.mul_mem_of_mem, assumption' },
  left, refine ⟨hxy,_⟩,
  rw (show (1 + x * y = 1 - ((-1) * x) * y), by ring),
  apply (rp.preadditive_iff.mp h) _ _ _ hy,
  apply h.neg_one_mem.2 _ hx,
end

lemma rigid_pair.preadditive.one_mem (h : rp.preadditive) :
  (1 : K) ∈ rp.OO := or.inr $ rp.OO_p_one_mem 

lemma rigid_pair.preadditive.zero_mem (h : rp.preadditive) :
  (0 : K) ∈ rp.OO := or.inl $ rp.OO_m_zero_mem

lemma rigid_pair.preadditive.neg_mem (h : rp.preadditive) :
  ∀ (x : K), x ∈ rp.OO → -x ∈ rp.OO :=
begin
  intros x hx,
  rw (show -x = (-1) * x, by ring),
  apply h.mul_mem _ _ _ hx,
  exact or.inr h.neg_one_mem,
end

lemma rigid_pair.preadditive.one_plus_mem (h : rp.preadditive) :
  ∀ (x : K), x ∈ rp.OO → 1 + x ∈ rp.OO :=
begin
  intros z hz,
  by_cases hzz : z = -1, { rw hzz, simp [h.zero_mem] },
  have hzz' : 1 + z ≠ 0, 
  { intro c, apply hzz,  
    rwa [← add_eq_zero_iff_eq_neg, add_comm] },
  by_cases hz1 : z ∈ rp.OO_p,
  swap, 
  { right, apply h, cases hz, assumption, contradiction },
  have hh : 1 - (1 + z) ∈ rp.OO_p, 
  { rw (show 1 - (1 + z) = (-1) * z, by ring),
    apply rp.OO_p_mul_mem h.neg_one_mem hz1 },
  have aux : ∀ y : K, y ∈ rp.OO_m → 1 + (1 + z) * y ∈ T ∧ 1 + (1 + z) * y ∈ rp.OO_p,
  { intros y hy,
    have := h.one_sub_mul_mem (-(1+z)) y _ _ hy, 
    { convert this, ring, ring },
    { contrapose! hzz, simp at hzz, rwa neg_add_eq_zero at hzz },
    { simpa using hh } },
  by_cases hz2 : (1 + z) ∈ H, 
  { right, refine ⟨hz2, _⟩,  
    intros y hy, refine ⟨_, (aux y hy).1⟩,
    intros c, apply hy.1, 
    convert H.mul_mem (H.inv_mem hz2) c,
    field_simp, ring },
  have : 1 + (1 + z) * (-1 * (1 + z)⁻¹) ∉ T,
  { convert T.zero_nmem, field_simp, ring },
  have : (-1) * (1 + z)⁻¹ ∉ rp.OO_m,
  { intro c, apply this, exact (aux _ c).1 },
  rw (show (-1) * (1 + z)⁻¹ = (- (1 + z))⁻¹, by rw [inv_neg, ← neg_eq_neg_one_mul]) at this,
  rw ← rp.OO_m_mem_iff_inv_nmem at this,
  rw (show 1 + z = (-1) * (-(1+z)), by ring), 
  apply h.mul_mem, apply h.neg_mem, apply h.one_mem, left, assumption, rwa neg_ne_zero,
  intro c, apply hz2,
  rw (show 1 + z = (-1) * (-(1 + z)), by ring), 
  apply H.mul_mem _ c, apply rp.neg_one_mem,
end

lemma rigid_pair.preadditive.mem_or_inv_mem (h : rp.preadditive) :
  ∀ x : K, x ∈ rp.OO ∨ x⁻¹ ∈ rp.OO :=
begin
  intros x, 
  by_cases hx : x ∈ rp.OO, { left, assumption },
  right, apply h.inv_mem_of_nmem, assumption,
end

lemma rigid_pair.preadditive.add_mem (h : rp.preadditive) :
  ∀ (x y : K), x ∈ rp.OO → y ∈ rp.OO → x + y ∈ rp.OO := 
begin
  intros x y hx hy,
  by_cases hxz : x = 0, { simpa [hxz] },
  by_cases hyz : y = 0, { simpa [hyz] },
  cases h.mem_or_inv_mem (x * y⁻¹) with hh hh,
  { replace hh := h.one_plus_mem _ hh, 
    convert h.mul_mem _ _ hy hh, field_simp, ring },
  { replace hh := h.one_plus_mem _ hh, 
    convert h.mul_mem _ _ hx hh, field_simp, ring }
end

def rigid_pair.preadditive.valuation_subring 
  (h : rp.preadditive) : valuation_subring K :=
{ carrier := rp.OO,
  mul_mem' := h.mul_mem,
  one_mem' := h.one_mem,
  add_mem' := h.add_mem,
  zero_mem' := h.zero_mem,
  neg_mem' := h.neg_mem,
  mem_or_inv_mem' := h.mem_or_inv_mem }

lemma rigid_pair.preadditive.units_eq 
  (h : rp.preadditive) (u : Kˣ) : u ∈ h.valuation_subring.units ↔ (u : K) ∈ rp.UU :=
begin
  split,
  { intros h, 
    rcases h with ⟨(h1|h1),(h2|h2)⟩,
    { rw OO_m_mem_iff_inv_nmem at h1, contradiction, exact u.ne_zero, exact h1.1 },
    { exfalso, apply h1.1, convert H.inv_mem h2.1, simp },
    { exfalso, apply h2.1, convert H.inv_mem h1.1 },
    { refine ⟨h1,h2⟩ } },
  { intros h, 
    split,
    exact or.inr h.1,
    exact or.inr h.2 }
end

lemma rigid_pair.preadditive.mem_of_mem_units
  (h : rp.preadditive) (u : Kˣ) (hu : u ∈ h.valuation_subring.units) : (u : K) ∈ H :=
begin
  rw h.units_eq at hu,
  cases hu with hu _,
  exact hu.1,
end

lemma rigid_pair.preadditive.mem_of_mem_principal_units
  (h : rp.preadditive) (u : Kˣ) (hu : u ∈ h.valuation_subring.principal_units) : 
  (u : K) ∈ T := 
begin
  change _ ∈ rp.OO ∧ _ ∉ _ at hu,
  cases hu with hu1 hu2,
  by_cases hune1 : u = 1,
  { rw hune1, simp [T.one_mem] },
  change ¬ ∃ v, _ at hu2, push_neg at hu2, 
  have husub1 : (u : K) - 1 ≠ 0, { contrapose! hune1, rw sub_eq_zero at hune1, ext, exact hune1 },
  specialize hu2 (units.mk0 _ husub1),
  have : units.mk0 _ husub1 ∉ h.valuation_subring.units,
  { intro c, exact hu2 c rfl },
  rw h.units_eq at this,
  cases hu1, convert hu1.2, ring,
  have : ((u : K) - 1)⁻¹ ∉ rp.OO_p, 
  { intro c, apply this, split, 
    exact hu1, exact c },
  obtain ⟨y,z,hy,hz,hh⟩ := rp.exists_inv_eq_mul _ (H.inv_mem hu1.1) this, rw inv_inv at hh,
  have hhneg1 : (-1 : K) ∈ rp.OO_p := h.neg_one_mem,
  replace hhneg1 := hhneg1.2 _ hy,
  convert (preadditive_iff _).mp h _ _ hhneg1 hz,
  rw [mul_assoc, ← hh], ring,
end