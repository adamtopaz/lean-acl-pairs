import rigid_elements.preadditive_conditions
import mul_subgroup.adjoin

variables {K : Type*} [field K]

open rigid_pair

def mul_subgroup.exceptional (T : mul_subgroup K) :=
(∀ x : K, ¬ (T.rigid x ∧ T.rigid (-x)) → x ∈ T ∨ -x ∈ T) ∧ 
((-1 : K) ∈ T ∨ ∀ (x y : K), x ∈ T → y ∈ T → x + y ∈ T)

theorem rigid_pair.preadditive_of_not_exceptional
  {T H : mul_subgroup K}
  (rp : rigid_pair T H)
  (H : ¬ T.exceptional) : 
  rp.preadditive :=
begin
  suffices : (∃ (a : K) (ha1 : a ≠ 0) (ha2 : a ∉ T), ¬ T.rigid (-a)),
  { obtain ⟨a,ha1,ha2,hh⟩ := this,
    exact rp.preadditive_of_nmem_of_neg_not_rigid a ha1 ha2 hh },
  by_contra c, push_neg at c,
  apply H,
  split,
  { intros x hx, rw not_and_distrib at hx, cases hx,
    { have hxz : x ≠ 0, 
      { dsimp [mul_subgroup.rigid] at hx, push_neg at hx, 
        obtain ⟨a,b,ha,hb,hx1,hx2,hx3⟩ := hx,
        assumption },
      specialize c (-x) (by simpa), 
      rw neg_neg at c,
      right, 
      by_contra cc, apply hx, apply c cc },
    { have hxz : x ≠ 0, 
      { dsimp [mul_subgroup.rigid] at hx, push_neg at hx, 
        obtain ⟨a,b,ha,hb,hx1,hx2,hx3⟩ := hx,
        simpa using hx1 },
      specialize c x hxz,
      left,
      by_contra cc, apply hx, apply c cc } },
  { by_cases hn : (-1 : K) ∈ T, { left, assumption },
    right, 
    intros x y hx hy,
    specialize c (-1) (by simp) hn, rw neg_neg at c,
    specialize c x y hx hy (by simp),
    cases c,
    { simpa using c },
    { simpa using c } }
end

-- Claim (*) on page 458
lemma rigid_pair.exists_preadditive_aux
  {T H : mul_subgroup K}
  (rp : rigid_pair T H) :
  ∀ (a b : K), a ∈ rp.OO_m → b ∈ rp.OO_m → (1 - a * b ∉ T) →
  (-a)⁻¹ * (1 - a * b) ∈ T :=
begin
  intros a b ha hb hh,
  have haz : (-a) ≠ 0,
  { intro c, apply hh, rw neg_eq_zero at c, simp [c, T.one_mem] },
  have haz' : a ≠ 0, by simpa using haz, 
  have := rp.neg a ha.1 (1+a) (1+b) ha.2 hb.2 _,
  swap, 
  { intro c, apply hh, rw neg_eq_zero at c, simp [c, T.one_mem] },
  cases this,
  { exfalso, apply hh, convert this, ring },
  convert this, field_simp, left, ring,
end

lemma rigid_pair.exists_preadditive_aux'
  {T H : mul_subgroup K}
  (rp : rigid_pair T H) :
  ∀ (a b : K), a ∈ rp.OO_m → b ∈ rp.OO_m → (1 - a * b ∉ T) →
  a * b⁻¹ ∈ T :=
begin
  intros a b ha hb hh,
  have h1 := rp.exists_preadditive_aux a b ha hb hh,
  have h2 := rp.exists_preadditive_aux b a hb ha (by rwa mul_comm),
  convert T.mul_mem (T.inv_mem h1) h2 using 1,
  have : b ≠ 0,
  { intro c, apply T.ne_zero_of_mem h2, simp [c] },
  have : a ≠ 0, 
  { intro c, apply T.ne_zero_of_mem h1, simp [c] },
  have : 1 - a * b ≠ 0,
  { intro c, apply T.ne_zero_of_mem h1, simp [c] }, 
  field_simp, ring,
end

lemma rigid_pair.OO_m_mono {T H H' : mul_subgroup K}
  (rp : rigid_pair T H) (h : H ≤ H') : 
  (rp.of_le H' h).OO_m ≤ rp.OO_m := 
begin
  rintros x ⟨h1,h2⟩,
  exact ⟨λ c, h1 (h c), h2⟩,
end

theorem rigid_pair.exists_preadditive 
  {T H : mul_subgroup K}
  (rp : rigid_pair T H) : 
  ∃ (x : K) (hx : x ≠ 0) (hxH : x * x ∈ H),
  (rp.of_le _ (H.le_adjoin_ne_zero x hx)).preadditive := 
begin
  by_cases HH : rp.preadditive,
  { use [1, one_ne_zero], split, { rw mul_one, exact H.one_mem }, 
    convert HH,
    exact H.adjoin_ne_zero_eq_of_mem 1 one_ne_zero H.one_mem },
  --have HT : T.exceptional,
  --{ by_contra c, apply HH, apply rigid_pair.preadditive_of_not_exceptional _ c },
  rw rp.preadditive_iff at HH,
  push_neg at HH,
  obtain ⟨a,b,ha,hb,HH⟩ := HH,
  have haz : a ≠ 0, 
  { intro c, apply HH, simp [c, T.one_mem] },
  use [a, haz],
  let rp' := rp.of_le _ (H.le_adjoin_ne_zero a haz),
  let H' := H.adjoin_ne_zero a haz,
  change _ ∧ rp'.preadditive,
  let t := (-a)⁻¹ * (1 - a * b),
  have aux1 : t ∈ T := rp.exists_preadditive_aux a b ha hb HH,
  have haz' : (-a) ≠ 0, { simpa },
  have h1 : 1 - a * b = (-a) * t, by { dsimp [t], field_simp, ring },
  have h2 : a * b = 1 + a * t, 
  { rw [neg_mul] at h1, apply_fun (λ e, -e) at h1, rw neg_neg at h1, rw ← h1, ring },
  have h3 := rp.pos a ha.1 1 t T.one_mem aux1 haz,
  rw ← h2 at h3,
  cases h3,
  swap, 
  { exfalso,  
    apply hb.1, apply rp.le, dsimp [t] at h3,
    convert h3, field_simp, ring },
  have hbz : b ≠ 0,
  { intro c, apply T.ne_zero_of_mem h3, simp [c] },
  split,
  { apply rp.le, 
    have := rp.exists_preadditive_aux' a b ha hb HH,
    convert T.mul_mem h3 this using 1, field_simp, ring },
  { apply rigid_pair.preadditive_of_exists_UU _ (-a),
    swap, { intro c, apply ha.1, rw ← neg_neg a, apply rp.le_neg c, },
    suffices : ∀ z : K, z ∈ rp'.OO_m → 1 - a * z ∈ T ∧ 1 - a⁻¹ * z ∈ T,
    { split,
      { split, 
        apply rp'.neg_mem_of_mem, exact H.mem_adjoin_ne_zero_self _ _,
        intros y hy,
        specialize this y hy,
        split,
        { intro c, 
          apply hy.1, rw (show y = (-a)⁻¹ * (-a * y), by field_simp; ring),
          apply mul_subgroup.mul_mem,
          apply mul_subgroup.inv_mem,
          apply rp'.neg_mem_of_mem,
          exact H.mem_adjoin_ne_zero_self _ _,
          exact c },
        { convert this.1, ring } },
      { split,
        apply mul_subgroup.inv_mem, apply rp'.neg_mem_of_mem, 
        exact H.mem_adjoin_ne_zero_self _ _,
        intros y hy,
        specialize this y hy,
        split,
        { intro c, 
          apply hy.1, rw (show y = (-a) * ((-a)⁻¹ * y), by field_simp; ring),
          apply mul_subgroup.mul_mem,
          apply rp'.neg_mem_of_mem, exact H.mem_adjoin_ne_zero_self _ _,
          exact c },
        { convert this.2, rw [inv_neg], ring } } },
    intros z hz,
    by_cases hzz : z = 0, { simp [hzz, T.one_mem] },
    split,
    { by_contra c,
      have := rp.exists_preadditive_aux' a z ha (rp.OO_m_mono _ hz) c,
      apply hz.1, replace this := rp'.le this,
      convert H'.mul_mem (H.mem_adjoin_ne_zero_self a haz) (H'.inv_mem this),
      field_simp, ring },
    have hh : 1 - b * z ∈ T,
    { by_contra c, 
      have := rp.exists_preadditive_aux' b z hb (rp.OO_m_mono _ hz) c,
      apply hz.1, replace this := rp'.le this,
      convert H'.mul_mem (_ : b ∈ H') (H'.inv_mem this),
      field_simp, ring,
      { suffices : a * b ∈ H',
        { convert H'.mul_mem this (H'.inv_mem (H.mem_adjoin_ne_zero_self a haz)), 
          field_simp, ring }, 
        apply rp'.le, exact h3 } },
    by_contra c, apply hz.1,
    have c' : ((-a) * z⁻¹)⁻¹ ∉ rp'.OO_m, 
    { dsimp [rigid_pair.OO_m], push_neg, intro _, convert c, field_simp, ring },
    rw ← rp'.OO_m_mem_iff_inv_nmem at c',
    have e1 := rp.exists_preadditive_aux (-a * z⁻¹) (-b * z) (rp.OO_m_mono _ c') _ _,
    have e2 := rp.exists_preadditive_aux a b ha hb HH,
    rw ← inv_inv z, apply mul_subgroup.inv_mem,
    apply rp'.mem_of_neg_mem, apply rp'.le,
    have : 1 - -a * z⁻¹ * (-b * z) = (1 - a * b), by field_simp; ring, rw this at e1, clear this,
    convert T.mul_mem e2 (T.inv_mem e1), 
    rw [mul_inv, mul_comm, mul_assoc, 
      mul_comm _ (1 - a * b), ← mul_assoc _ (1 - a * b), inv_mul_cancel], 
    field_simp, ring,
    { intro c, apply T.ne_zero_of_mem e2, simp [c] },
    { apply rp.OO_m_mono (H.le_adjoin_ne_zero a haz),
      split, 
      { intro c, apply hz.1, 
        convert H'.mul_mem c (H'.inv_mem (_ : -b ∈ H')), 
        have : -b ≠ 0, by simpa,
        field_simp, ring,
        apply rp'.neg_mem_of_mem,
        have : b * a⁻¹ ∈ H', 
        { apply rp'.le,
          apply rp.exists_preadditive_aux' b a hb ha (by rwa mul_comm) },
        convert H'.mul_mem this (H.mem_adjoin_ne_zero_self _ _), field_simp }, 
      { convert hh, ring } },
    { convert HH using 2, field_simp, ring },
    { simp only [ne.def, neg_eq_zero, mul_eq_zero, inv_eq_zero], push_neg, 
      exact ⟨haz, hzz⟩ },
    { intro c, apply hz.1, 
      convert H'.mul_mem (H'.inv_mem c) (_ : (-a) ∈ H'), field_simp,
      apply rp'.neg_mem_of_mem, exact H.mem_adjoin_ne_zero_self _ _ } }
end