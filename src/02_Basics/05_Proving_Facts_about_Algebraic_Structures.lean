import topology.metric_space.basic

section
variables {α : Type*} [partial_order α]
variables x y z : α

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
lt_iff_le_and_ne

end

section
variables {α : Type*} [lattice α]
variables x y z : α

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := 
begin
  apply le_antisymm,
  apply le_inf,
  apply inf_le_right,
  apply inf_le_left,
  apply le_inf,
  apply inf_le_right,
  apply inf_le_left,
end

theorem k1 : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,  
  apply le_inf,
  apply le_trans,
  apply inf_le_left,
  apply inf_le_left,
  apply le_inf,
  apply le_trans,
  apply inf_le_left,
  apply inf_le_right,
  apply inf_le_right,
  apply le_inf,
  apply le_inf,
  apply inf_le_left,
  apply le_trans,
  apply inf_le_right,
  apply inf_le_left,
  apply le_trans,
  apply inf_le_right,
  apply inf_le_right,
end



example : x ⊔ y = y ⊔ x := 
begin
  apply le_antisymm,
  apply sup_le,
  apply le_sup_right,
  apply le_sup_left,
  apply sup_le,
  apply le_sup_right,
  apply le_sup_left,        
end
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := 
begin
  apply le_antisymm,
  apply sup_le,
  apply sup_le,
  apply le_sup_left,
  apply le_trans,
  apply @le_sup_left _ _ y z,
  apply le_sup_right,
  apply le_trans,
  apply @le_sup_right _ _ y z,
  apply le_sup_right,
  apply sup_le,
  apply le_trans,
  apply @le_sup_left _ _ x y,
  apply le_sup_left,
  apply sup_le,
  apply le_trans,
  apply @le_sup_right _ _ x y,
  apply le_sup_left,
  apply le_sup_right,
end

theorem absorb1 : x ⊓ (x ⊔ y) = x := 
begin
  apply le_antisymm,
  apply inf_le_left,
  apply le_inf,
  refl,
  apply le_sup_left,
end
theorem absorb2 : x ⊔ (x ⊓ y) = x := 
begin
  apply le_antisymm,
  apply sup_le,
  refl,
  apply inf_le_left,
  apply le_sup_left,
  
end  
end

section
variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

end

section
variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
begin
 rw h,
 rw @inf_comm _ _ (a ⊔ b), 
 rw absorb1, 
 rw @inf_comm _ _ (a ⊔ b), 
 rw h,
 rw ←sup_assoc, 
 rw @inf_comm _ _ c a, 
 rw absorb2, 
 rw inf_comm,  
end

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
begin
rw h, 
rw @sup_comm _ _ (a ⊓ b), 
rw absorb2, 
rw @sup_comm _ _ (a ⊓ b), 
rw h,
rw    ←inf_assoc, 
rw@sup_comm _ _ c a, 
rw absorb1, 
rw sup_comm,
  
  
  
  
end

end

section
variables {R : Type*} [ordered_ring R]
variables a b c : R

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem aux1 : a ≤ b → 0 ≤ b - a := 
begin
  intro h,
  rw [←sub_self a],
  rw sub_eq_add_neg,
  rw sub_eq_add_neg,
  rw add_comm,
  rw add_comm b,
  apply add_le_add_left,
  exact h,
  
end

theorem aux2 : 0 ≤ b - a → a ≤ b := 
begin
  intro h,
  rw [←add_zero a, ←sub_add_cancel b a, add_comm (b-a)],
  apply add_le_add_left,
  exact h,
end

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := 
begin
  have h1 : 0 ≤ (b -a) * c,
  { exact mul_nonneg (aux1 _ _ h) h'},
  rw sub_mul at h1,
  exact aux2 _ _ h1,
end  
end

section
variables {X : Type*} [metric_space X]
variables x y z : X

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)


example (x y : X) : 0 ≤ dist x y :=
begin
  have : 0 ≤ dist x y + dist y x,
  { rw [←dist_self x],
    apply dist_triangle },
  linarith [dist_comm x y]
end


end

