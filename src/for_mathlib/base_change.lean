import linear_algebra.tensor_product

variables {A R : Type*} [add_comm_group A] [comm_ring R]

open_locale tensor_product

variable (R)
def add_monoid_hom.base_change (M : Type*) [add_comm_group M] [module R M]
  (f : A →+ M) : (R ⊗[ℤ] A) →ₗ[R] M :=
let E : R →ₗ[ℤ] A →ₗ[ℤ] M := 
{ to_fun := λ r, r • f.to_int_linear_map,
  map_add' := begin
    intros r s, simp [add_smul],
  end,
  map_smul' := begin
    intros r x,
    simp [mul_smul],
    refine (zsmul_eq_smul_cast R r (x • add_monoid_hom.to_int_linear_map f)).symm,
  end } in 
let EE := tensor_product.lift E in 
{ to_fun := EE,
  map_add' := λ x y, EE.map_add _ _,
  map_smul' := begin
    intros r x,
    apply x.induction_on,
    { simp },
    { intros t a,
      dsimp, 
      dsimp [EE], simp,
      have : r • t ⊗ₜ[ℤ] a = (r * t) ⊗ₜ[ℤ] a, by refl,
      simp [this, mul_smul] },
    { intros x y hx hy, 
      simp [smul_add, hx, hy, EE.map_add] }
  end }

.

variables {R}

@[simp]
lemma add_monoid_hom.base_change_apply_tmul {M : Type*} [add_comm_group M] [module R M]
  (f : A →+ M) (r : R) (a : A) : f.base_change R M (r ⊗ₜ[ℤ] a)= r • f a := 
by { dsimp [add_monoid_hom.base_change], simp }

variable (R)
@[simps]
def to_base_change : A →+ R ⊗[ℤ] A :=
{ to_fun := λ a, 1 ⊗ₜ[ℤ] a,
  map_zero' := tensor_product.tmul_zero _ _,
  map_add' := tensor_product.tmul_add _ }

def base_change_equiv :
  (A →+ R) ≃ₗ[R] ((R ⊗[ℤ] A) →ₗ[R] R) :=
{ to_fun := λ f, f.base_change _ _,
  map_add' := begin
    intros f g, ext x,
    apply x.induction_on,
    { simp },
    { intros x y, simp },
    { intros r a h1 h2, simp only [linear_map.map_add, h1, h2] }
  end,
  map_smul' := begin
    intros r x, ext e, 
    apply e.induction_on,
    { simp }, 
    { intros x y, simp, rw [← mul_assoc, mul_comm x, mul_assoc] },
    { intros r a h1 h2, simp only [linear_map.map_add, h1, h2] }
  end,
  inv_fun := λ f, f.to_add_monoid_hom.comp (to_base_change _),  
  left_inv := λ f, by { ext, simp, },
  right_inv := λ f, begin
    ext x, 
    apply x.induction_on,
    { simp, },
    { intros u v, simp, rw [← smul_eq_mul, ← f.map_smul], congr' 1, 
      change ((u * 1) ⊗ₜ[ℤ] v) = _, rw mul_one, }, 
    { intros r a h1 h2, simp only [h1, h2, linear_map.map_add], }, 
  end }
