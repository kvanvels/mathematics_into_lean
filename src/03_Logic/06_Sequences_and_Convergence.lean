import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by { ext, ring }

example (a b : ℝ) : abs a = abs (a - b + b) :=
by  { congr, ring }

example {a : ℝ} (h : 1 < a) : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
  { rw [one_mul] },
  exact lt_trans zero_lt_one h
end

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  rw [sub_self, abs_zero],
  apply εpos
end

theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, dsimp,
  have ε2pos : 0 < ε / 2,
  { linarith },
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  use max Ns Nt,
  intros n n_big,
  have h3 := le_max_left Ns Nt,
  have h4 := le_max_right Ns Nt,
  specialize hs n (by linarith),
  specialize ht n (by linarith),
  calc 
    | s n + t n - (a + b) | = | (s n - a) + (t n- b) | : by ring_nf
                      ...   ≤ | s n - a | + |t n - b | : abs_add (s n - a) (t n -b)
                      ...   <  ε/2         + |t n - b | : by linarith
                      ...   <  ε/2 + ε/2                : by linarith
                      ...   = ε                         : by linarith  
end



theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
  have acnz : abs c ≠ 0 := 
  begin
    intro h1,
    rw h1 at acpos,
    linarith,
  end,

  intros ε ε_pos,
  have h3 := cs (ε/|c|) (div_pos ε_pos acpos),
  cases h3 with N h3N,
  apply exists.intro N,
  intros n n_big,
  specialize h3N n n_big,
  calc 
    |c * s n - c * a | 
        = |c * (s n - a)|  : by rw ←mul_sub
    ... = |c|* |s n - a|   : by rw abs_mul
    ... < |c| * (ε / |c| ) : by exact (mul_lt_mul_left acpos).mpr h3N
    ... = ε                : by exact mul_div_cancel' ε acnz,

end

--example (a b : ℝ) (h1 : a > 0) (h2 : b > 0) : a/b > 0:= by library_search,

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n n_big,
  specialize h n n_big,
  
   calc 
     | s n | 
         = |(s n - a) + a| : by ring_nf
     ... ≤ |s n -a | + |a| : abs_add ( s n -a) a
     ... < 1 + |a|         : add_lt_add_right h (abs a)
     ... = |a| + 1         : by rw add_comm,  
end

lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
  have Bpos : 0 < B,
    from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
  have pos₀ : ε / B > 0,
    from div_pos εpos Bpos,
  cases ct _ pos₀ with N₁ h₁,
  apply exists.intro (max N₀ N₁),
  intros n n_big,
  have h3 :=  le_max_left N₀ N₁,
  have h4 :=  le_max_right N₀ N₁,
  specialize h₀ n (by linarith),
  specialize h₁ n (by linarith),

  rw sub_zero,
  rw sub_zero at h₁,
  calc 
  |s n * t n|
      = |s n| * |t n| : abs_mul (s n) (t n)
  ... < B *(ε/B)      : mul_lt_mul'' h₀ h₁ (abs_nonneg _) (abs_nonneg _)
  ... = ε             : mul_div_cancel' _ (ne_of_lt Bpos).symm,
  
end

theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (converges_to_mul_const b cs)),
  { ext, ring },
  ring
end

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0,
  { sorry },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε,
  {
    exact hNa N (le_max_left Na Nb), 
  },
  have absb : abs (s N - b) < ε,
  { exact hNb N (le_max_right Na Nb),    
  },
  have : abs (a - b) < abs (a - b),
  { 
    calc |a -b | = |(a - s N) +(s N - b)| : by ring_nf
             ... ≤ |a - s N| + |s N - b|  : abs_add (a - s N) (s N -b)
             ... = |s N -a | + |s N - b|  : by rw (abs_sub_comm (s N) a)
             ... < ε + ε                  : add_lt_add (hNa N (le_max_left Na Nb)) 
                                                       (hNb N (le_max_right Na Nb))
             ... = |a-b|/2 + |a-b| /2     : by refl
             ... = |a - b|                : by linarith,
  },
  exact lt_irrefl _ this
end



section
variables {α : Type*} [linear_order α]

def converges_to' (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

end

