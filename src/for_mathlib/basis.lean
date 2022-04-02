import linear_algebra.basis

variables {ι K M : Type*} [field K] [add_comm_group M] [module K M]

@[simp]
lemma basis.sum_extend_extends (f : ι → M) 
  (hf : linear_independent K f) (i : ι) : 
  (basis.sum_extend hf) (sum.inl i) = f i := 
begin
  dsimp [basis.sum_extend],
  simp,
end