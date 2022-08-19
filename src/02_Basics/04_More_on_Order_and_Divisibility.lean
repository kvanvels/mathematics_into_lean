import data.real.basic

section
variables a b c d : ℝ

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end

example : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end

example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end

example : max a b = max b a :=
begin
  apply le_antisymm,
  repeat{
    apply max_le,
    apply le_max_right,
    apply le_max_left,  },
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,  
  have h1 := min_le_left (min a b) c,
  apply le_min,
  
  have h2 := min_le_left a b,
  exact le_trans h1 h2,
  apply le_min,  
  have h2 := min_le_right a b,
  exact le_trans h1 h2,
  exact min_le_right (min a b) c,
  have h1 := min_le_right a (min b c),
  apply le_min,
  apply le_min,
  exact min_le_left a (min b c),  
  have h2 := min_le_left b c,
  exact le_trans h1 h2,
  have h2 := min_le_right b c,
  exact le_trans h1 h2,
  end

lemma aux : min a b + c ≤ min (a + c) (b + c) :=
begin
  apply le_min,
  apply add_le_add,
  apply min_le_left,
  refl,
  apply add_le_add,
  apply min_le_right,
  refl,
end
example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  apply aux,
  rw ←sub_add_cancel (min (a + c) (b + c)) c,
  apply add_le_add_right,
  have h1 := aux (a+c) (b+c) (-c),
  rw [add_neg_cancel_right, add_neg_cancel_right] at h1,
  rw (  tactic.ring.add_neg_eq_sub _ c )at h1,
  exact h1,
end




#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

--example (a b : ℝ) : (a + -b) =( a- b) := by library_search,

example : abs a - abs b ≤ abs (a - b) :=
begin
  have h1 : abs a ≤ abs (a -b) + abs b := 
  calc 
    abs a = abs ((a -b) + b)      :  by simp
      ... ≤ abs (a - b) + abs (b) : by exact (abs_add (a-b) b),  
  linarith,

end

section
variables w x y z : ℕ

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

example : x ∣ x^2 :=
by apply dvd_mul_right

example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
  apply dvd_add,
  apply dvd_mul_of_dvd_right,
  apply dvd_mul_of_dvd_left,
  exact dvd_rfl,
  rw pow_two x,
  apply dvd_mul_of_dvd_left,
  exact dvd_rfl,
  rw pow_two w,
  apply dvd_mul_of_dvd_left,
  exact h,
end

end

section
variables m n : ℕ
open nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)



example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  apply dvd_gcd,
  apply gcd_dvd_right,
  apply gcd_dvd_left,
  apply dvd_gcd,
  apply gcd_dvd_right,
  apply gcd_dvd_left,
end

end
end
