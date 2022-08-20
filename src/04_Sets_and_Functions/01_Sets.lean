import data.set.lattice
import data.nat.parity
import tactic

section
variable {α : Type*}
variables (s t u : set α)

open set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨h1,h2⟩ | ⟨h3,h4⟩),
  exact ⟨h1,or.inl h2⟩,
  exact ⟨h3,or.inr h4⟩,  
  
end


example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin
  rintros x ⟨h1,h2⟩,
  apply and.intro,
  apply and.intro,
  exact h1,
  intro h3,
  apply h2,
  exact or.inl h3,
  intro h3,
  apply h2,
  apply or.inr h3,
end


example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

example : s ∩ t = t ∩ s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
subset.antisymm (λ x ⟨xs, xt⟩, ⟨xt,xs⟩) (λ x ⟨xt, xs⟩, ⟨xs,xt⟩)



example : s ∩ (s ∪ t) = s :=
begin
  ext,
  apply iff.intro,
  intro h1,
  exact h1.left,
  intro h1,
  apply and.intro,
  exact h1,
  apply or.inl h1,  
end

example : s ∪ (s ∩ t) = s :=
begin
  apply subset_antisymm,
  rintros x (h1 | ⟨h2,h3⟩),
  exact h1,
  exact h2,
  intros x h1,
  apply or.inl,
  exact h1,
end

example : (s \ t) ∪ t = s ∪ t :=
begin
  apply subset_antisymm,
  rintros x (⟨h1,h2⟩|h3),
  apply or.inl h1,
  apply or.inr h3,
  rintros x (h1|h2),
  apply or.elim (em (x ∈ t)),
  intro h2,
  apply or.inr h2,
  intro h2,
  apply or.inl,
  apply and.intro,
  exact h1,
  exact h2,
  apply or.inr h2,  
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  apply subset_antisymm,
  rintros x (⟨h1,h2⟩ | ⟨h3,h4⟩),
  apply and.intro,
  apply or.inl h1,
  intro h3,
  exact h2 h3.right,
  apply and.intro,
  apply or.inr h3,
  intro h5,
  exact h4 h5.left,
  rintros x ⟨(h1|h2),h3⟩,
  apply or.inl,
  apply and.intro,
  exact h1,
  intro h4,
  exact h3 ⟨h1,h4⟩,
  apply or.inr,
  apply and.intro,
  exact h2,
  intro h5,
  exact h3 ⟨h5, h2⟩,
end


def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin
  intro n,
  dsimp,  
  rintros ⟨h2,h3⟩ h4,
  apply or.elim (nat.prime.eq_two_or_odd h2),
  intro h5,
  linarith,
  intro h6,
  have h7 := (nat.even_iff.mp) h4,
  rw h6 at h7,
  linarith,  
end


#print prime
#print nat.prime

example (n : ℕ) : prime n ↔ nat.prime n := nat.prime_iff.symm

example (n : ℕ) (h : prime n) : nat.prime n :=
by { rw nat.prime_iff, exact h }

example (n : ℕ) (h : prime n) : nat.prime n :=
by rwa nat.prime_iff

end
section
variables (s t : set ℕ)

example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x]
end

section
variable (ssubt : s ⊆ t)

include ssubt

example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  rintros x h1,
  apply and.intro,
  exact h₀ x (ssubt h1),
  exact h₁ x (ssubt h1),
  end


example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
begin
  rcases h with ⟨x,Hx,h1⟩,
  have h2 := ssubt Hx,
  apply exists.intro x,
  apply exists.intro h2,
  exact h1.right,  
end

end

end

section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end        

open_locale classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  apply subset_antisymm,  
  intros x,
  rw mem_Inter,
  intro h1,
  intro ι,
  apply or.elim h1,
  intro h2,
  exact or.inr h2,
  intro h2,
  rw mem_Inter at h2,
  specialize h2 ι,
  exact or.inl h2,
  intros x h1,
  rw mem_Inter at h1,
  apply or.elim (em (x∈ s)),
  intro h2,
  apply or.inl h2,
  intro h2,
  apply or.inr,
  rw mem_Inter,
  intro ι,
  specialize h1 ι,
  apply or.elim h1,
  intro h3,
  exact h3,
  intro h3,
  apply false.elim,
  exact h2 h3,  
end

  
def primes : set ℕ := {x | nat.prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_Union₂, refl }

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x = 1} :=
begin
  intro x,
  contrapose!,
  simp,
  apply nat.exists_prime_and_dvd
end

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin
apply eq_univ_of_forall,
intro x,
simp,
rcases nat.exists_infinite_primes x with ⟨p, primep, pge⟩,
apply exists.intro p,
apply and.intro,
exact pge,
exact primep,  

end

end

section
open set

variables {α : Type*} (s : set (set α))

example : ⋃₀ s = ⋃ t ∈ s, t :=
begin
  ext x,
  rw mem_Union₂,
  refl
end

example : ⋂₀ s = ⋂ t ∈ s, t :=
begin
  ext x,
  rw mem_Inter₂,
  refl
end

end

