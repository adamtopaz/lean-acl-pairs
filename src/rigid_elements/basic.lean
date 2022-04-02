import mul_subgroup.basic
import tactic

variables {K : Type*} [field K]

lemma ne_zero_left {x y : K} (h : x * y ≠ 0) : x ≠ 0 := 
λ c, h $ by simp [c]

lemma ne_zero_right {x y : K} (h : x * y ≠ 0) : y ≠ 0 := 
λ c, h $ by simp [c]

def mul_subgroup.rigid (T : mul_subgroup K) (x : K) : Prop := 
∀ a b : K, a ∈ T → b ∈ T → x ≠ 0 → a + x * b ∈ T ∨ x⁻¹ * a + b ∈ T

namespace mul_subgroup.rigid

variables {T : mul_subgroup K} {x : K} 

lemma mul_left {t : K} (h : T.rigid x) (ht : t ∈ T) :
  T.rigid (t * x) :=
begin
  intros a b ha hb htx,
  cases h a (b * t) ha _ _ with hh hh,
  { left, convert hh using 1, ring },
  { right,   
    convert T.mul_mem hh (T.inv_mem ht) using 1,
    field_simp [T.ne_zero_of_mem ht, ne_zero_right htx], ring },
  { exact T.mul_mem hb ht },
  { exact ne_zero_right htx }
end

lemma mul_right {t : K} (h : T.rigid x) (ht : t ∈ T) :
  T.rigid (x * t) := 
by { rw mul_comm, apply mul_left, assumption' }

lemma of_mul_left {t : K} (h : T.rigid (t * x)) (ht : t ∈ T) :
  T.rigid x :=
begin
  convert h.mul_left (T.inv_mem ht),
  field_simp [T.ne_zero_of_mem ht], ring
end

lemma of_mul_right {t : K} (h : T.rigid (x * t)) (ht : t ∈ T) :
  T.rigid x :=
begin
  rw mul_comm at h,
  apply h.of_mul_left ht,
end

lemma mul_left_iff (t : K) (ht : t ∈ T) :
  T.rigid (t * x) ↔ T.rigid x :=
⟨λ h, h.of_mul_left ht, λ h, h.mul_left ht⟩

lemma mul_right_iff (t : K) (ht : t ∈ T) :
  T.rigid (x * t) ↔ T.rigid x :=
by { rw [mul_comm, mul_left_iff t ht] }

end mul_subgroup.rigid