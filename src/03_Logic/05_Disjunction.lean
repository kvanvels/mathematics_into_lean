import data.real.basic

section
variables {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x :=
begin
  cases (le_or_gt 0 x) with h h,
  have h1 := abs_of_nonneg h,
  rw h1,
  have h1 := abs_of_neg h,
  linarith,  
end


theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x :=
begin
  cases (le_or_gt 0 x) with h h,
  have h1 := abs_of_nonneg h,
  linarith,
  have h1 := abs_of_neg h,
  linarith,
end


theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
begin
  cases (le_or_gt 0 (x + y)) with h h,
  have h1 := abs_of_nonneg h,
  rw h1,
  apply add_le_add,
  exact le_abs_self x,  
  exact le_abs_self y,  
  have h1 := abs_of_neg h,
  rw h1,
  ring_nf,
  rw sub_eq_add_neg (-x) y,
  apply add_le_add,
  exact neg_le_abs_self x,
  exact neg_le_abs_self y,
  
end



theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
cases (le_or_gt 0 y) with h h,
have h1 := abs_of_nonneg h,
rw h1,
apply iff.intro,
intro h2,
exact or.inl h2,
intro h2,
apply or.elim h2,
intro h3,
exact h3,
intro h3,
apply lt_of_lt_of_le,
exact h3,
linarith,
have h1 := abs_of_neg h,
rw h1,
apply iff.intro,
intro h2,
exact or.inr h2,
intro h2,
apply or.elim h2,
intro h3,
linarith,
intro h3,
exact h3,
  
end


theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  cases (le_or_gt 0 x) with h h,
  have h1 := abs_of_nonneg h,
  rw h1,  
  apply iff.intro,
  intro h2,
  apply and.intro,
  linarith,
  exact h2,
  intro h2,
  exact h2.right,
  have h1 := abs_of_neg h,
  rw h1,
  apply iff.intro,
  intro h2,
  apply and.intro,
  linarith,
  linarith,
  rintro ⟨h3,h4⟩,
  linarith,

end


end my_abs
end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end

example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
begin
  
  rcases h with ⟨x,y,h1⟩,  
  have hx := pow_two_nonneg x,
  have hy := pow_two_nonneg y,
  rcases h1 with (h1|h2),
  linarith,
  linarith,  
end



example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  rw ←sub_eq_zero at h,
  have h2 : (x^2-1) = (x+1) * (x - 1) := by ring_nf,
  rw h2 at h,
  have h3 := zero_eq_mul.mp h.symm,
  apply or.elim h3,
  intro h4,
  apply or.inr,
  exact add_eq_zero_iff_eq_neg.mp h4,
  intro h5,
  apply or.inl,
  exact sub_eq_zero.mp h5,

end


example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  rw ←sub_eq_zero at h,
  have h1 :(x^2-y^2) = (x+y)*(x-y) := by ring_nf,
  rw h1 at h,
  have h3 := zero_eq_mul.mp h.symm,
  apply or.elim h3,
  intro h4,
  apply or.inr,
  exact  add_eq_zero_iff_eq_neg.mp h4,
  intro h4,
  apply or.inl,
  exact sub_eq_zero.mp h4,
end



section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  rw ←sub_eq_zero at h,
  have h2 : (x^2-1) = (x+1) * (x - 1) := by ring_nf,
  rw h2 at h,
  have h3 := zero_eq_mul.mp h.symm,
  apply or.elim h3,
  intro h4,
  apply or.inr,
  exact add_eq_zero_iff_eq_neg.mp h4,
  intro h5,
  apply or.inl,
  exact sub_eq_zero.mp h5,
end

example (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  rw ←sub_eq_zero at h,
  have h1 :(x^2-y^2) = (x+y)*(x-y) := by ring_nf,
  rw h1 at h,
  have h3 := zero_eq_mul.mp h.symm,
  apply or.elim h3,
  intro h4,
  apply or.inr,
  exact  add_eq_zero_iff_eq_neg.mp h4,
  intro h4,
  apply or.inl,
  exact sub_eq_zero.mp h4,
end


end
--example (a b : ℝ)  (h1 : a + b = 0) : (a = -b)  := by library_search,

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

section
open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
  apply iff.intro,
  intro h1,
  apply or.elim (em P),
  intro h2,
  exact or.inr (h1 h2),
  intro h2,
  exact or.inl h2,
  intro h1,
  intro h2,
  apply or.elim h1,
  intro h3,
  apply false.elim,
  exact h3 h2,
  intro h3,
  exact h3,  
end

end
