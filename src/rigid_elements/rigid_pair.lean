import rigid_elements.basic

variables {K : Type*} [field K]
structure rigid_pair (T H : mul_subgroup K) : Prop :=
(pos [] : ∀ x : K, x ∉ H → T.rigid x)
(neg [] : ∀ x : K, x ∉ H → T.rigid (-x))

namespace rigid_pair

variables {T H : mul_subgroup K} 

lemma mk_of_le (T H : mul_subgroup K) :
  T ≤ H →
  (-1 : K) ∈ T → 
  (∀ (x : K), x ≠ 0 → x ∉ H → 1 + x ∈ T ∨ x⁻¹ + 1 ∈ T) →
  rigid_pair T H :=
begin
  intros h1 h2 h3,
  constructor,
  { intros x hx a b ha hb hh, 
    cases h3 (x * b * a⁻¹) _ _,
    left, 
    { convert T.mul_mem ha h, 
      field_simp [T.ne_zero_of_mem ha], ring },
    right, 
    { convert T.mul_mem h hb,
      field_simp [T.ne_zero_of_mem hb], ring },
    { simp only [ne.def, mul_eq_zero, inv_eq_zero], 
      push_neg,
      refine ⟨⟨hh, T.ne_zero_of_mem hb⟩, T.ne_zero_of_mem ha⟩ },
    { intro c, apply hx, 
      convert H.mul_mem (H.mul_mem c (h1 ha)) (H.inv_mem (h1 hb)),
      field_simp [T.ne_zero_of_mem ha, T.ne_zero_of_mem hb] } },
  { intros x hx a b ha hb hh,
    cases h3 (-x * b * a⁻¹) _ _,
    left, 
    { convert T.mul_mem h ha, 
      field_simp [T.ne_zero_of_mem ha] },
    right, 
    { convert T.mul_mem h hb,  
      simp only [ne.def, neg_eq_zero] at hh,
      field_simp [T.ne_zero_of_mem hb, hh], ring },
    { simp only [ne.def, neg_eq_zero, mul_eq_zero, inv_eq_zero],  
      push_neg, 
      refine ⟨⟨by simpa using hh, T.ne_zero_of_mem hb⟩, T.ne_zero_of_mem ha⟩ },
    { intro c, apply hx,  
      rw neg_eq_neg_one_mul at c,
      have : x = ((-1) * x * b * a⁻¹) * ((-1) * b⁻¹ * a),
      { field_simp [T.ne_zero_of_mem ha, T.ne_zero_of_mem hb] },
      rw this,
      apply H.mul_mem c,
      apply H.mul_mem,
      apply H.mul_mem,
      apply h1, apply h2,
      apply H.inv_mem, apply h1, apply hb,
      apply h1, apply ha } }
end

lemma of_le (rp : rigid_pair T H) 
  (H' : mul_subgroup K) (h : H ≤ H') : rigid_pair T H' :=
begin
  constructor,
  { intros x hx,  
    exact rp.pos x (λ c, hx (h c)) },
  { intros x hx, 
    exact rp.neg x (λ c, hx (h c)) }
end

lemma le (rp : rigid_pair T H) : T ≤ H :=
begin
  intros t ht,
  by_contra c,
  have hh := rp.neg t c,
  specialize hh t 1 ht T.one_mem (by simpa using T.ne_zero_of_mem ht),
  cases hh,
  { apply T.zero_nmem, convert hh, simp },
  { apply T.zero_nmem, convert hh, 
    field_simp [(show (-t) ≠ 0, by simpa using T.ne_zero_of_mem ht)] }
end

lemma le_neg (rp : rigid_pair T H) {t : K} (ht : t ∈ T) : 
  -t ∈ H :=
begin
  by_contra c,
  have hh := rp.pos (-t) c, 
  specialize hh t 1 ht T.one_mem (by simpa using T.ne_zero_of_mem ht),
  cases hh,
  { apply T.zero_nmem, convert hh, simp },
  { apply T.zero_nmem, convert hh, 
    field_simp [(show (-t) ≠ 0, by simpa using T.ne_zero_of_mem ht)] }
end

lemma neg_one_mem (rp : rigid_pair T H) : (-1 : K) ∈ H :=
rp.le_neg T.one_mem

lemma neg_mem_of_mem (rp : rigid_pair T H) (x : K) (hx : x ∈ H) : (-x) ∈ H :=
begin
  rw neg_eq_neg_one_mul,
  exact H.mul_mem rp.neg_one_mem hx,
end

lemma mem_of_neg_mem (rp : rigid_pair T H) (x : K) (hx : (-x) ∈ H) : x ∈ H :=
begin
  rw (show x = (-1) * (-x), by ring),
  exact H.mul_mem rp.neg_one_mem hx
end

def OO_m (rp : rigid_pair T H) : set K := 
{ x | x ∉ H ∧ 1 + x ∈ T }

def OO_p (rp : rigid_pair T H) : set K :=
{ x | x ∈ H ∧ ∀ y : K, y ∈ rp.OO_m → x * y ∈ rp.OO_m }

def OO (rp : rigid_pair T H) : set K := rp.OO_m ∪ rp.OO_p 

def UU (rp : rigid_pair T H) : set K := 
{ x | x ∈ rp.OO_p ∧ x⁻¹ ∈ rp.OO_p }

-- Observation 2.3 (1), part 1
lemma OO_p_one_mem (rp : rigid_pair T H) : (1 : K) ∈ rp.OO_p :=
begin
  refine ⟨H.one_mem, _⟩,
  intros y hy, rwa one_mul
end

-- Observation 2.3 (1), part 2
lemma OO_p_mul_mem (rp : rigid_pair T H) {x y : K} : x ∈ rp.OO_p → y ∈ rp.OO_p → 
  x * y ∈ rp.OO_p :=
begin
  rintros ⟨h1,h1'⟩ ⟨h2,h2'⟩,
  refine ⟨H.mul_mem h1 h2, _⟩,
  intros z hz, rw mul_assoc,
  apply h1', apply h2', exact hz
end

-- Observation 2.3 (1), part 3
lemma UU_one_mem (rp : rigid_pair T H) : (1 : K) ∈ rp.UU :=
⟨rp.OO_p_one_mem, by { rw inv_one, exact rp.OO_p_one_mem }⟩

-- Observation 2.3 (1), part 4
lemma UU_mul_mem (rp : rigid_pair T H) {x y : K} :
  x ∈ rp.UU  → y ∈ rp.UU → x * y ∈ rp.UU :=
begin
  rintros ⟨hx,hx'⟩ ⟨hy,hy'⟩,
  split,
  { exact rp.OO_p_mul_mem hx hy },
  { rw mul_inv, exact rp.OO_p_mul_mem hx' hy' },
end

-- Observation 2.3 (1), part 5
lemma UU_inv_mem (rp : rigid_pair T H) {x : K} :
  x ∈ rp.UU → x⁻¹ ∈ rp.UU :=
begin
  rintros ⟨h1,h2⟩, refine ⟨h2, by simpa⟩
end

-- Observation 2.3 (1), part 6
lemma UU_ne_zero_of_mem (rp : rigid_pair T H) (x : K) (hx : x ∈ rp.UU) : 
  x ≠ 0 :=
H.ne_zero_of_mem hx.1.1

-- Observation 2.3 (2)
lemma OO_m_zero_mem (rp : rigid_pair T H) : (0 : K) ∈ rp.OO_m :=
begin
  refine ⟨H.zero_nmem,_⟩,
  simpa using T.one_mem,
end

-- Observation 2.3 (3)
lemma OO_m_mem_iff_inv_nmem (rp : rigid_pair T H) (x : K) (hx : x ≠ 0) (hxH : x ∉ H) : 
  x ∈ rp.OO_m ↔ x⁻¹ ∉ rp.OO_m := 
begin
  split,
  { intro h, dsimp [OO_m], push_neg, intros hx' c, 
    apply hx', apply rp.le,
    have : 1 + x⁻¹ = x⁻¹ * (1 + x), by { field_simp, ring }, 
    rw this at c,
    have : 1 + x ≠ 0 := ne_zero_right (T.ne_zero_of_mem c),
    convert T.mul_mem c (T.inv_mem h.2),
    field_simp, ring },
  { intros c, dsimp [OO_m] at c, push_neg at c, specialize c _,
    { intro cc, apply hxH, rw ← inv_inv x, exact H.inv_mem cc },
    refine ⟨hxH,_⟩,
    cases rp.pos _ hxH 1 1 T.one_mem T.one_mem hx,
    { simpa using h },
    { exfalso, apply c, convert h using 1, ring } }
end

-- Observation 2.3 (4)
lemma exists_inv_eq_mul (rp : rigid_pair T H) 
  (x : K) (hx : x ∈ H) (hx' : x ∉ rp.OO_p) :
  ∃ (y z : K) (hy : y ∈ rp.OO_m) (hz : z ∈ rp.OO_m), x⁻¹ = y * z :=
begin
  dsimp [OO_p] at hx', push_neg at hx', specialize hx' hx,
  obtain ⟨y,hy1,hy2⟩ := hx',
  use [y, (x * y)⁻¹, hy1],
  have : y ≠ 0, 
  { contrapose! hy2, rw [hy2, mul_zero], exact rp.OO_m_zero_mem },
  split,
  { rw rp.OO_m_mem_iff_inv_nmem, 
    { rwa inv_inv }, 
    { apply inv_ne_zero, exact mul_ne_zero (H.ne_zero_of_mem hx) this },
    have hhy := hy1.1,
    contrapose! hhy,
    rw mul_inv at hhy,
    rw ← inv_inv y,
    apply H.inv_mem,
    convert H.mul_mem hx hhy,
    field_simp [mul_ne_zero (H.ne_zero_of_mem hx) this] },
  { field_simp [mul_ne_zero (H.ne_zero_of_mem hx) this,
      H.ne_zero_of_mem hx], rw mul_comm }
end

-- Observation 2.3 (5) -- setup
lemma OO_m_one_plus_ne_zero_of_mem (rp : rigid_pair T H) (x : K) (hx : x ∈ rp.OO_m) :
  1 + x ≠ 0 := 
T.ne_zero_of_mem $ hx.2

-- Observation 2.3 (5) 
lemma OO_m_neg_div_one_plus_mem_of_mem (rp : rigid_pair T H) (x : K) 
  (hx : x ∈ rp.OO_m) : -x * (1 + x)⁻¹ ∈ rp.OO_m :=
begin
  split,
  { intro c, apply hx.1, 
    convert H.mul_mem (rp.neg_one_mem) (H.mul_mem c (rp.le hx.2)),
    field_simp [rp.OO_m_one_plus_ne_zero_of_mem x hx] },
  { rw (show 1 + -x * (1 + x)⁻¹ = (1+x)⁻¹, 
      by field_simp [rp.OO_m_one_plus_ne_zero_of_mem x hx]),  
    apply T.inv_mem, exact hx.2 }
end

def preadditive (rp : rigid_pair T H) : Prop := 
  ∀ (x : K) (hx : x ∈ rp.OO_m), 1 + x ∈ rp.OO_p

variables {T H}

lemma preadditive_iff_aux (rp : rigid_pair T H) :
  rp.preadditive ↔ 
  (∀ (x y : K) (hx : x ∈ rp.OO_m) (hy : y ∈ rp.OO_m), 1 + (1 + x) * y ∈ T) :=
begin
  split,
  { introsI h x y hx hy,
    apply (((h x hx).2) y hy).2 },
  { intros h,
    intros x hx,
    split,
    { apply rp.le, exact hx.2 },
    { intros y hy, split, 
      { intros c, apply hy.1,
        convert H.mul_mem (H.inv_mem (rp.le hx.2)) c,
        field_simp [T.ne_zero_of_mem hx.2], ring },
      { apply h, assumption' } } }
end

-- Lemma 2.6 (1)↔(2)
lemma preadditive_iff (rp : rigid_pair T H) : 
  rp.preadditive ↔ 
  (∀ (x y : K) (hx : x ∈ rp.OO_m) (hy : y ∈ rp.OO_m), 1 - x * y ∈ T) :=
begin
  rw preadditive_iff_aux,
  split,
  { intros h x y hx hy,  
    have : 1 - x * y = (1 + y) * (1 + (1 + x) * ((-y * (1 + y)⁻¹))),
    { field_simp [rp.OO_m_one_plus_ne_zero_of_mem y hy], ring },
    rw this, clear this,
    apply T.mul_mem hy.2,
    apply h _ _ hx,
    apply rp.OO_m_neg_div_one_plus_mem_of_mem _ hy },
  { intros h x y hx hy,  
    let z := -y * (1 + y)⁻¹,
    have hz : z ∈ rp.OO_m := rp.OO_m_neg_div_one_plus_mem_of_mem _ hy,
    have : y = - z * (1 + z)⁻¹, 
    { dsimp [z], 
      field_simp [rp.OO_m_one_plus_ne_zero_of_mem z hz,   
        rp.OO_m_one_plus_ne_zero_of_mem y hy] },
    rw this, clear this,
    suffices : (1 + z) * (1 + (1 + x) * (-z * (1+z)⁻¹)) ∈ T, 
    { convert T.mul_mem this (T.inv_mem hz.2),
      field_simp [rp.OO_m_one_plus_ne_zero_of_mem z hz], ring }, 
    have : (1 + z) * (1 + (1 + x) * (-z * (1 + z)⁻¹)) = 1 - x * z, 
    { field_simp [rp.OO_m_one_plus_ne_zero_of_mem z hz], ring },
    rw this,
    apply h, assumption' }
end

-- Lemma 2.6 (3)
lemma preadditive.one_sub_mul_mem {rp : rigid_pair T H} (h : rp.preadditive) : 
  (∀ (x y : K), x ≠ 0 → 1 + x ∈ rp.OO_p → y ∈ rp.OO_m → 
    1 - x * y ∈ T ∧ 1 - x * y ∈ rp.OO_p) :=
begin
  intros x y hxz hx hy,
  have : 1 - x * y = (1 + y) * (1 + (1 + x) * (-y * (1+y)⁻¹)),
  { field_simp [rp.OO_m_one_plus_ne_zero_of_mem y hy], ring },
  rw this, clear this,
  have hy' : -y * (1 + y)⁻¹ ∈ rp.OO_m := rp.OO_m_neg_div_one_plus_mem_of_mem y hy,
  have := hx.2 _ hy',
  split,
  { apply T.mul_mem hy.2 this.2 },
  { apply rp.OO_p_mul_mem (h _ hy) (h _ this) }
end

-- Lemma 2.9 (1)
lemma preadditive.mul_mem_of_mem {rp : rigid_pair T H} (h : rp.preadditive) :
  ∀ (x y : K), x ∈ rp.OO_m → y ∈ rp.OO_m → x * y ∈ H → x * y ∈ rp.OO_p :=
begin
  intros x y hx hy hxy,
  refine ⟨hxy,_⟩,
  intros z hz, split,
  { intros c, 
    apply hz.1, convert H.mul_mem (H.inv_mem hxy) c,
    field_simp [H.ne_zero_of_mem hxy], ring },
  have : 1 - x * y ∈ T ∧ 1 - x * y ∈ rp.OO_p,
  { apply h.one_sub_mul_mem,
    { intro c, apply H.ne_zero_of_mem hxy, rw [c, zero_mul] },
    { apply h _ hx },
    { exact hy } },
  rw (show (1 + x * y * z = 1 - (- (x * y) * z)), by ring),
  apply (h.one_sub_mul_mem _ _ _ _ _).1,
  { rw neg_ne_zero, exact H.ne_zero_of_mem hxy },
  { convert this.2, ring },
  { exact hz },
end

-- Lemma 2.9 (2)
lemma preadditive.inv_mem_of_nmem {rp : rigid_pair T H} (h : rp.preadditive) :
  ∀ x : K, x ∉ rp.OO → x⁻¹ ∈ rp.OO :=
begin
  intros x hx,
  by_cases hxz : x = 0, { left, rw [hxz, inv_zero], apply rp.OO_m_zero_mem },
  by_cases hxH : x ∈ H, swap,
  { by_contra c, dsimp only [OO] at c, 
    simp only [set.mem_union] at c, push_neg at c,
    replace c := c.1,
    rw ← rp.OO_m_mem_iff_inv_nmem at c,
    { apply hx, left, exact c },
    assumption' },
  dsimp only [OO, set.mem_union] at hx, 
  push_neg at hx, cases hx with hx1 hx2,
  obtain ⟨y,z,hy,hz,hyz⟩ := rp.exists_inv_eq_mul x hxH hx2,
  rw hyz, right, apply h.mul_mem_of_mem _ _ hy hz,
  rw ← hyz, apply H.inv_mem, exact hxH
end

-- Lemma 2.9 (3)
lemma preadditive.neg_one_mem {rp : rigid_pair T H} (h : rp.preadditive) : 
  (-1 : K) ∈ rp.OO_p := 
begin
  suffices : (-1 : K) ∈ rp.OO, 
  { cases this, swap, assumption, 
    exfalso, apply this.1, apply rp.neg_one_mem },
  by_contra c, apply c,
  convert h.inv_mem_of_nmem _ c using 1,
  ring,
end

end rigid_pair