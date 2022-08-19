import analysis.special_functions.log.basic

variables a b c d e : ℝ
open real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variables (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
  { apply h₀ },
  apply h₁
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans h₀,
  apply h₁
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
by exact le_trans h₀ h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
le_trans h₀ h₁

example (x : ℝ) : x ≤ x :=
by apply le_refl

example (x : ℝ) : x ≤ x :=
by exact le_refl x

example (x : ℝ) : x ≤ x :=
le_refl x

#check (le_refl  : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

/- Try this. -/
theorem k2 (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
begin
  have h1 : a < c := lt_of_le_of_lt (h₀) (h₁),
  have h2 : a < d := lt_of_lt_of_le h1 h₂,
  exact lt_trans h2 h₃,  
end



example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
by linarith



section
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) :
  d + a ≤ 5 * b :=
by linarith
end

example (h : 1 ≤ a) (h' : b ≤ c) :
  2 + a + exp b ≤ 3 * a + exp c :=
by linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)

#check @add_le_add_left
example (h : a ≤ b) : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h
end

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt h₀,
    apply exp_lt_exp.mpr h₁ },
  apply le_refl
end

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add,
  refl,
  apply exp_le_exp.mpr,
  apply add_le_add,
  refl,
  exact h₀,
end


example : (0 : ℝ) < 1 :=
by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { 
    linarith [exp_pos a],
  },
  have h₁ : 0 < 1 + exp b,
  { 
      linarith [exp_pos b],
  },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add,
  refl,
  rw exp_le_exp,
  exact h,  
end

    example : 0 ≤ a^2 :=
    begin
      -- library_search,
      exact pow_two_nonneg a
    end

example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  apply sub_le_sub,
  refl,
  rw exp_le_exp,
  exact h,
end

example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2     : by ring
    ... ≥ 0                           : by apply pow_two_nonneg,
  calc
    2*a*b
        = 2*a*b + 0                   : by ring
    ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
    ... = a^2 + b^2                   : by ring
end

theorem aux : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0                       : by apply pow_two_nonneg,
  linarith
end

theorem aux_2  {p : ℝ} : p^2 = (abs p)^2 := 
begin
  apply or.elim (em (p ≥ 0)),
  intro ppos,
  have h1 := abs_eq_self.mpr ppos,
  rw h1,
  intro pneg,
  push_neg at pneg,
  have h1 := abs_of_neg pneg,
  rw h1,
  have h2 := neg_sq p,
  rw h2,
end  

example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  have h1 := aux (abs a) (abs b),
  have h2 : |a|^2 = a^2 := by rw ←aux_2,
  have h3 : |b|^2 = b^2 := by rw ←aux_2,
  have h4 : |a|*|b|= |a * b| := (abs_mul a b).symm,
  rw mul_assoc at h1, 
  rw [h2,h3,h4] at h1,
  have h0 : (2:real) >(0:real) := by norm_num,
  exact (le_div_iff' h0).mpr h1,  
end




  
  




