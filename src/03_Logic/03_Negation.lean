import data.real.basic

section
variables a b : ℝ

example (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  intro h1,
  cases h1 with x hx1,
  unfold fn_lb at hx1,
  specialize h x,
  cases h with y hy,
  specialize hx1 y,
  linarith,
end

example : ¬ fn_has_ub (λ x, x) :=
begin
  intro h1,
  cases h1 with x h1x,
  specialize h1x (x + 1),
  dsimp at h1x,
  linarith,
end

#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)

example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  by_contradiction h2,
  push_neg at h2,
  specialize h h2,
  linarith,
end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intro h1,
  specialize h1 h,
  linarith,
end


example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  {
    intros x1 x2 h1,
    refl,  
  },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  have h2 := @h f monof 1 0 h',
  linarith,
end

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
begin
  revert h,
  contrapose!,
  intro x_pos,
  apply exists.intro (x/2),
  apply and.intro,
  linarith,
  linarith,  
end

end

section
variables {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
begin
  intros x h1,
  apply h,
  apply exists.intro x,
  exact h1,  
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  rintro ⟨x,h1⟩,
  specialize h x,
  exact h h1,
end


example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
begin
  intro h1,
  cases h with x hx,
  specialize h1 x,
  exact hx h1,
end


open_locale classical

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contradiction h1,
  apply h,
  intros x,
  by_contradiction h2,
  apply h1,
  apply exists.intro x,
  exact h2,
end

example (h : ¬ ¬ Q) : Q :=
begin
  by_contradiction h1,
  apply h,
  exact h1,
end

example (h : Q) : ¬ ¬ Q :=
begin
  intro h1,
  exact h1 h,
end

end

open_locale classical
section
variable (f : ℝ → ℝ)

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
 intro a,
 by_contradiction h1,
 apply h,
 unfold fn_has_ub,
 apply exists.intro a,
 unfold fn_ub,
 intro aa,
 by_contradiction h2,
 apply h1,
 apply exists.intro aa,
 push_neg at h2,
 exact h2,  
end

example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
begin
  push_neg at h,
  exact h
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h
end

example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  rw monotone at h,
  push_neg at h,
  exact h,
  
end


example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h
end

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

end

section
variable a : ℕ

example (h : 0 < 0) : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

example (h : 0 < 0) : a > 37 :=
absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end

end

