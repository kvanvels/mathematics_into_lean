import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic

section

variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin
  apply iff.intro,
  intros h x xs,
  dsimp,
  have h1 : f x ∈ f '' s := mem_image_of_mem _ xs,
  have h2 := h h1,
  exact h2,
  intros h1 y h2,
  rcases h2 with ⟨x,xs,fx⟩,
  have h3 := h1 xs,
  dsimp at h3,
  rw ←fx,
  exact h3,  
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros y ⟨x,⟨h2,h3⟩⟩,
  specialize h h3,
  rw ←h,
  exact h2,  
end


example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros x ⟨h1,⟨h2,h3⟩⟩,
  dsimp at h2,
  rw h3 at h2,
  exact h2,  
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin
  intros x h1,
  specialize h x,
  cases h with y hy,
  apply exists.intro y,
  apply and.intro,
  dsimp,
  rw hy,
  exact h1,
  exact hy,
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
begin
  intros x h1,
  rcases h1 with ⟨y, ⟨hy1,hy2⟩⟩,
  apply exists.intro y,
  apply and.intro,
  exact h hy1,
  exact hy2,
end


example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x h1,
  exact (h h1),  
end


example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  dsimp,
  refl,
end

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x,⟨h1,h2⟩⟩,
  apply and.intro,
  apply exists.intro x,
  apply and.intro,
  exact h1.left,
  exact h2,
  apply exists.intro x,
  apply and.intro,
  apply h1.right,
  exact h2,  
end

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1,⟨h2,h3⟩⟩,⟨x2,⟨h5,h6⟩⟩⟩,
  have h7 : x1 = x2 := 
  begin
    apply h,
    rw h3,  
    exact h6.symm,
  end,
  apply exists.intro x1,
  apply and.intro,
  apply and.intro,
  exact h2,
  rw h7,
  exact h5,
  exact h3, 
end


example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x,⟨h1,h2⟩⟩,h3⟩,
  apply exists.intro x,
  apply and.intro,
  apply and.intro,
  exact h1,
  intro h4,
  apply h3,
  apply exists.intro x,
  apply and.intro,
  exact h4,
  exact h2,
  exact h2,  
end


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intro x,
  dsimp,
  intro h1,
  exact h1,  
end


example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  apply subset_antisymm,
  rintros y ⟨⟨x,⟨h1,h2⟩⟩,h3⟩,
  apply exists.intro x,
  apply and.intro,
  apply and.intro,
  exact h1,
  dsimp,
  rw h2,
  exact h3,
  exact h2,
  rintros y ⟨x,⟨⟨h1,h2⟩,h3⟩⟩,
  apply and.intro,
  apply exists.intro x,
  apply and.intro,
  exact h1,
  exact h3,
  rw ←h3,
  exact h2,  
end

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
begin
  rintros y ⟨x,⟨⟨h1,h2⟩,h3⟩⟩,
  apply or.inr,
  rw ←h3,
  exact h2,  
end


example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintro x ⟨h1,h2⟩,
  dsimp at h2,
  dsimp [preimage],
  apply and.intro,
  apply exists.intro x,
  apply and.intro,
  exact h1,
  refl,
  exact h2,  

end

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (h1|h2),
  apply or.inl,
  apply exists.intro x,
  apply and.intro h1,
  refl,
  apply or.inr,
  exact h2,  
end


variables {I : Type*} (A : I → set α) (B : I → set β)

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

end

section
open set real

example : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos,
  intro e,   -- log x = log y
  calc
    x   = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw e
    ... = y           : by rw exp_log ypos
end

example : range exp = { y | y > 0 } :=
begin
  ext y, split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos },
  intro ypos,
  use log y,
  rw exp_log ypos
end

example : inj_on sqrt { x | x ≥ 0 } :=
begin
  intros x x_pos y y_pos h,
  calc
    x   = (sqrt x)^2 : by rw sq_sqrt x_pos
    ... = (sqrt y)^2 : by rw h
    ... = y          : by rw sq_sqrt y_pos

  
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin
  intros x x_pos y y_pos h,
  dsimp at h,
calc
  x = sqrt (x^2) : by rw sqrt_sq x_pos
 ...= sqrt (y^2) : by rw h
... = y          : by rw sqrt_sq y_pos,  
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
    ext y, split,
    { rintros ⟨x, ⟨xnonneg, rfl⟩⟩,
      apply sqrt_nonneg },
    intro ynonneg,
    use y^2,
    dsimp at *,
    split,
    apply pow_nonneg ynonneg,
    apply sqrt_sq,
    assumption,
end

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
begin
    ext y,
    split,
    { rintros ⟨x, rfl⟩,
       dsimp at *,
       apply pow_two_nonneg },
    intro ynonneg,
    use sqrt y,
    exact sq_sqrt ynonneg,
end


end

section
variables {α β : Type*} [inhabited α]

#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

example : P (classical.some h) := classical.some_spec h

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

variable  f : α → β
open function

example : injective f ↔ left_inverse (inverse f) f  :=
begin
  apply iff.intro,
  intros h1 x,
  apply h1,
  apply inverse_spec,
  apply exists.intro x,
  refl,
  intros h1 x1 x2 h2,
  rw ←h1 x1,
  rw ←h1 x2,
  rw h2,  
end



example : surjective f ↔ right_inverse (inverse f) f :=
begin
  apply iff.intro,
  intros h1 y,
  apply inverse_spec,
  have h2 := h1 y,
  exact h2,
  intros h1 y,
  apply exists.intro ((inverse f) y),
  apply h1,
end

  

end

section
variable {α : Type*}
open function

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    from h₁,
  have h₃ : j ∉ S,
    by rwa h at h₁,
    contradiction,
end

end
