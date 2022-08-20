import data.real.basic


#check ∀ x : ℝ, 0 ≤ x → abs x = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε

lemma my_lemma : ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε ε_pos ε_le1 h1 h2,
  apply or.elim (em (x = 0)),
  intro x0,
  rw [x0,zero_mul,abs_zero],
  exact ε_pos,
  intro x_pos,
  apply or.elim (em (y = 0)),
  intro y0,
  rw [y0,mul_zero,abs_zero],
  exact ε_pos,
  intro y_pos,
  rw abs_mul,
  rw ←mul_one ε,
  apply mul_lt_mul,
  exact h1,
  apply le_trans,
  exact h2.le,
  exact ε_le1,
  rw abs_pos,
  exact y_pos,
  exact ε_pos.le,
end

section
  variables a b δ : ℝ
  variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
  variables (ha : abs a < δ) (hb : abs b < δ)

  #check my_lemma a b δ
  #check my_lemma a b δ h₀ h₁
  #check my_lemma a b δ h₀ h₁ ha hb
end



def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

section
variables (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  apply add_le_add,
  apply hfa,
  apply hgb
end

example (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
sorry

example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 :=
begin
  intro x,
  have h1 := nnf x,
  have h2 := nng x,
  dsimp,
  rw ←mul_zero (0: ℝ),
  apply mul_le_mul,
  exact h1,
  exact h2,
  refl,
  exact h1,  
  
end

example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
begin
  intro x,
  dsimp,
  specialize hfa x,
  specialize hfb x,
  specialize nng x,
  apply mul_le_mul,
  exact hfa,
  exact hfb,
  exact nng,
  exact nna,    
end

end

section
variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

#check @add_le_add

def fn_ub' (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

theorem fn_ub_add {f g : α → R} {a b : R}
    (hfa : fn_ub' f a) (hgb : fn_ub' g b) :
  fn_ub' (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
end

example (f : ℝ → ℝ) (h : monotone f) :
  ∀ {a b}, a ≤ b → f a ≤ f b := h

section
variables (f g : ℝ → ℝ)

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb
end

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
λ a b aleb, add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
begin
  intros x1 x2 h1,
  exact mul_le_mul_of_nonneg_left (mf h1) nnc,
end



example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
begin
  intros x1 x2 h1,
  dsimp,
  apply mf,
  apply mg h1,
end


def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                    ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
begin
  intros x1,
  dsimp,
  specialize of x1,
  specialize og x1,
  rw [of,og],
  rw neg_mul_neg,  
end



example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
begin
  intro x1,
  dsimp,
  specialize ef x1,
  specialize og x1,
  rw [ef,og],
  exact mul_neg (f (-x1) ) (g (-x1)),
end  


example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
begin
  intro x1,
  dsimp,
  specialize og x1,
  rw og,
  specialize ef (g (-x1) ),
  rw ef,  
end


end

section
variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  intros h1 h2 x h3,
  exact h2 (h1 h3),
end

end

section

variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
begin
  intros x h1,
  specialize h x,
  specialize h h1,
  apply le_trans,
  exact h,
  exact h',  
end

end

section
open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  exact (add_left_inj c).mp h',
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
  intros x1 x2,
  dsimp,
  intro h1,
  rw ←(mul_right_inj' h),
  exact h1,
end



variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) :=
begin
  intros x1 x2,
  dsimp,
  intro h1,
  apply injf,
  apply injg,
  exact h1,  
end

end
