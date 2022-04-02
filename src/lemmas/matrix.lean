import data.set
import data.matrix.notation

lemma set.range_matrix_eq₁ {α : Type*} (a : α) :
  set.range ![a] = {a} := by tidy

lemma set.range_matrix_eq₂ {α : Type*} (a b : α) :
  set.range ![a,b] = {a,b} := by tidy

lemma set.range_matrix_eq₃ {α : Type*} (a b c : α) :
  set.range ![a,b,c] = {a,b,c} := by tidy

lemma comp_matrix_eq_matrix₁ {α β : Type*} (f : α → β) 
  (a : α) : f ∘ ![a] = ![f a] := by { ext i, fin_cases i, refl }

lemma comp_matrix_eq_matrix₂ {α β : Type*} (f : α → β) 
  (a b : α) : f ∘ ![a, b] = ![f a, f b] := by { ext i, fin_cases i; refl }

lemma comp_matrix_eq_matrix₃ {α β : Type*} (f : α → β) 
  (a b c : α) : f ∘ ![a, b, c] = ![f a, f b, f c] := by { ext i, fin_cases i; refl }