import group_theory.subgroup.basic
import tactic.field_simp

variables (K : Type*) [field K]

--lemma is_unit.inv {G : Type*} [group_with_zero G] {x : G} (hx : is_unit x) : is_unit x⁻¹ := 
--⟨⟨x⁻¹,x, by field_simp [hx.ne_zero], by field_simp [hx.ne_zero]⟩, rfl⟩

structure mul_subgroup :=
(carrier : set K)
(mul_mem' : ∀ {x y : K}, x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' : ∀ {x : K}, x ∈ carrier → x⁻¹ ∈ carrier)
(one_mem' : (1 : K) ∈ carrier)
(is_unit' : ∀ {x : K}, x ∈ carrier → is_unit x)

namespace mul_subgroup
variable {K}

instance : set_like (mul_subgroup K) K :=
{ coe := carrier,
  coe_injective' := begin
    intros S T h,
    cases S, cases T, congr, assumption,
  end }

@[ext]
lemma ext (S T : mul_subgroup K) (h : ∀ x, x ∈ S ↔ x ∈ T) : 
  S = T := set_like.ext h

lemma is_unit_of_mem {x : K} (T : mul_subgroup K) : x ∈ T → is_unit x :=
begin
  intros hx, apply T.is_unit' hx,
end

lemma ne_zero_of_mem [nontrivial K] 
  {x : K} (T : mul_subgroup K) : x ∈ T → x ≠ 0 := 
λ hx, is_unit.ne_zero (T.is_unit_of_mem hx)

lemma zero_nmem [nontrivial K] (T : mul_subgroup K) : (0 : K) ∉ T := 
λ c, T.ne_zero_of_mem c rfl 

lemma mul_mem (T : mul_subgroup K) {a b : K} (ha : a ∈ T) (hb : b ∈ T) : 
  a * b ∈ T := T.mul_mem' ha hb

lemma one_mem (T : mul_subgroup K) : (1 : K) ∈ T :=
T.one_mem'

lemma inv_mem (T : mul_subgroup K) {a : K}
  (ha : a ∈ T) : a⁻¹ ∈ T := 
T.inv_mem' ha

def mk' (T : subgroup Kˣ) : mul_subgroup K := 
{ carrier := { u | ∃ (h : is_unit u), h.unit ∈ T },
  mul_mem' := begin
    rintros x y ⟨hx,hx'⟩ ⟨hy,hy'⟩, refine ⟨hx.mul hy, _⟩,
    convert T.mul_mem hx' hy',
    ext, refl,
  end,
  inv_mem' := begin
    rintros x ⟨hx,hx'⟩, refine ⟨hx.inv, _⟩,
    convert T.inv_mem hx', ext, simpa only [units.coe_inv],
  end,
  one_mem' := ⟨is_unit_one, by { convert T.one_mem, ext, refl }⟩,
  is_unit' := λ x hx, hx.some }

def subgroup (T : mul_subgroup K) : subgroup Kˣ := 
{ carrier := { u | (u : K) ∈ T },
  mul_mem' := λ a b ha hb, T.mul_mem ha hb,
  one_mem' := T.one_mem,
  inv_mem' := λ a ha, begin
    dsimp, convert T.inv_mem ha using 1, simp only [units.coe_inv],
  end }

end mul_subgroup
