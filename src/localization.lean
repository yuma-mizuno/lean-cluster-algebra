import ring_theory.localization
/-!
This file proves some properties on localizations that are needed to define mutations.

## Main statements

* `is_localization_of_lift_of_sup`: let `A`, `B`, and `C` are commutative rings, and `M` and `N`
  are submonoids of `A`. Suppose that `B` is a localization of `A` at `M` and `C` is a localization
  of `A` at `M ⊔ N`. Then `C` is a localization of `B` at the image of `N` by the localization map
  from `A` to `B`.

-/

namespace is_localization

section

variables
{A : Type*}  [comm_ring A]
(M N : submonoid A)
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization (M ⊔ N) C]

include M N

noncomputable def lift_of_sup : B →+* C :=
lift $ λ h, by simpa only [set_like.coe_mk] using map_units C (⟨h.1, set_like.le_def.mp le_sup_left h.2⟩ : M ⊔ N)

noncomputable def algebra_of_lift_of_sup : algebra B C := ring_hom.to_algebra (lift_of_sup M N B C)

local attribute[instance] algebra_of_lift_of_sup

lemma eq_comp_map_of_lift_of_sup (a : A) : algebra_map A C a = (algebra_map B C (algebra_map A B a)):=
begin
  have : algebra_map B C = lift_of_sup M N B C := by refl,
  rw [this, lift_of_sup, lift_eq],
end

lemma eq_comp_of_lift_of_sup : (algebra_map A C) = (algebra_map B C).comp (algebra_map A B) :=
by ext; by rw [ring_hom.coe_comp]; by exact eq_comp_map_of_lift_of_sup M N B C _

lemma is_localization_of_lift_of_sup
{A : Type*}  [comm_ring A]
(M : submonoid A) (N : submonoid A)
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization (M ⊔ N) C] :
is_localization (N.map (algebra_map A B) : submonoid B) C :=
{ map_units := 
  begin
    intros n',
    rcases submonoid.mem_map.mp n'.property with ⟨n, ⟨hn, H⟩⟩,
    have : n ∈ M ⊔ N := set_like.le_def.mp le_sup_right hn,
    simp only [ring_hom.coe_monoid_hom, subtype.val_eq_coe] at H,
    rw [<- H, <- eq_comp_map_of_lift_of_sup],
    exact is_localization.map_units C ⟨n, this⟩,
  end,
  surj := 
  begin
    intros c,
    rcases surj (M ⊔ N) c with ⟨⟨a, ⟨mn, h_mn⟩⟩ , H⟩,
    rcases submonoid.mem_sup.mp h_mn with ⟨m, hm, n, hn, H'⟩,
    repeat {rw eq_comp_map_of_lift_of_sup M N B C at H},
    rw [set_like.coe_mk] at H,
    dsimp at H,
    have : algebra_map A B n ∈ (N.map (algebra_map A B) : submonoid B),
    apply submonoid.mem_map.mpr,
    use n,
    use hn,
    rw [ring_hom.coe_monoid_hom],
    fsplit,
    fsplit,
    exact ↑((is_unit.unit (map_units B ⟨m, hm⟩))⁻¹) * (algebra_map A B a),
    exact ⟨algebra_map A B n, this⟩,
    simp only [set_like.coe_mk, ring_hom.map_mul],
    rw [<- H, <- H'],
    simp only [ring_hom.map_mul],
    ring_nf,
    apply congr_arg ( * c),
    nth_rewrite  0 <- one_mul ((algebra_map B C) ((algebra_map A B) n)),
    apply congr_arg ( * ((algebra_map B C) ((algebra_map A B) n))),
    rw <- ring_hom.map_mul,
    rw <- ring_hom.map_one (algebra_map B C),
    apply congr_arg,
    rw units.mul_inv_of_eq,
    rw is_unit.unit_spec,
  end,
  eq_iff_exists := 
  begin
    intros b₁ b₂,
    split,
    { intros h,
      rcases surj M b₁ with ⟨⟨a₁, ⟨m₁, hm₁⟩⟩, H₁⟩,
      rcases surj M b₂ with ⟨⟨a₂, ⟨m₂, hm₂⟩⟩, H₂⟩,
      have : algebra_map A C (a₁ * m₂) = algebra_map A C (a₂ * m₁),
      rw eq_comp_map_of_lift_of_sup M N B C,
      rw eq_comp_map_of_lift_of_sup M N B C,
      dsimp at *,
      simp only [ring_hom.map_mul],
      rw [<- H₁, <- H₂],
      simp only [ring_hom.map_mul],
      rw h,
      ring,
      rcases (eq_iff_exists (M ⊔ N) C).mp this with ⟨⟨mn, mn_in⟩, hmn⟩,
      rcases submonoid.mem_sup.mp mn_in with ⟨m, hm, n, hn, H'⟩,
      dsimp at *,
      have : algebra_map A B n ∈ submonoid.map ↑(algebra_map A B) N,
      apply submonoid.mem_map.mpr,
      use n,
      use hn,
      rw [ring_hom.coe_monoid_hom],
      use ⟨algebra_map A B n, this⟩,
      dsimp,
      refine (is_unit.mul_left_inj _).mp _, 
      exact algebra_map A B m,
      exact map_units B ⟨m, hm⟩,
      repeat {rw [mul_assoc, <- ring_hom.map_mul]},
      rw mul_comm at H',
      rw H',
      have hb₁ : b₁ = mk' B a₁ ⟨m₁, hm₁⟩ := eq_mk'_iff_mul_eq.mpr H₁,
      have hb₂ : b₂ = mk' B a₂ ⟨m₂, hm₂⟩ := eq_mk'_iff_mul_eq.mpr H₂,
      rw [hb₁, hb₂],
      nth_rewrite_lhs 0 mul_comm,
      nth_rewrite_rhs 0 mul_comm,
      rw [mul_mk'_eq_mk'_of_mul, mul_mk'_eq_mk'_of_mul],
      refine mk'_eq_of_eq _,
      dsimp,
      exact calc mn * a₂ * m₁ = a₂ * m₁ * mn : by ring
      ...                     = a₁ * m₂ * mn : by rw <-hmn
      ...                     = mn * a₁ * m₂ : by ring },
    { intros h,
      rcases h with ⟨⟨n', hn'⟩, H⟩,
      rcases submonoid.mem_map.mp hn' with ⟨n, ⟨hn, H'⟩⟩,
      have n_in : n ∈ M ⊔ N := submonoid.mem_sup_right hn,
      rcases surj M b₁ with ⟨⟨a₁, ⟨m₁, hm₁⟩⟩, H₁⟩,
      rcases surj M b₂ with ⟨⟨a₂, ⟨m₂, hm₂⟩⟩, H₂⟩,
      dsimp at *,
      have : ∃ m : M, a₁ * m₂ * n * m = a₂ * m₁ * n * m,
      refine (eq_iff_exists M B).mp _,
      simp only [ring_hom.map_mul],
      rw H',
      rw [<- H₁, <- H₂],
      exact calc b₁ * (algebra_map A B) m₁ * (algebra_map A B) m₂ * n'
               = b₁ * n' * (algebra_map A B) m₁ * (algebra_map A B) m₂  : by ring
      ...      = b₂ * n' * (algebra_map A B) m₁ * (algebra_map A B) m₂  : by rw H
      ...      = b₂ * (algebra_map A B) m₂ * (algebra_map A B) m₁ * n'  : by ring,
      rcases this with ⟨⟨m, hm⟩, H''⟩,
      dsimp at H'',
      have p : algebra_map A C (a₁ * m₂) = algebra_map A C (a₂ * m₁),
      refine (eq_iff_exists (M ⊔ N) C).mpr _,
      use ⟨n * m, mul_comm m n ▸ submonoid.mul_mem _ (submonoid.mem_sup_left hm) (submonoid.mem_sup_right hn)⟩,
      dsimp,
      repeat {rw <- mul_assoc},
      exact H'',
      repeat {rw eq_comp_map_of_lift_of_sup M N B C at p},
      simp only [ring_hom.map_mul] at p,
      rw [<- H₁, <- H₂] at p,
      refine (is_unit.mul_left_inj _).mp _,
      exact algebra_map A C (m₁ * m₂),
      have : m₁ * m₂ ∈ M ⊔ N,
      refine submonoid.mul_mem _ (submonoid.mem_sup_left hm₁) (submonoid.mem_sup_left hm₂),
      exact map_units C ⟨m₁ * m₂, this⟩,
      repeat {rw eq_comp_map_of_lift_of_sup M N B C},
      simp only [ring_hom.map_mul] at *,
      repeat {rw mul_assoc at *},
      nth_rewrite 3 mul_comm,
      exact p }
  end, }

end 

section

variables
{A : Type*}  [comm_ring A]
{M : submonoid A} {N : submonoid A}
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization N C]
(h : M ≤ N)

include h

noncomputable def lift_of_le : B →+* C :=
@lift_of_sup A _ M N B _ C _ _ _ _ (by rw sup_eq_right.mpr h; by apply_instance)

noncomputable def algebra_of_lift_of_le : algebra B C := 
ring_hom.to_algebra (lift_of_le B C h)

lemma eq_comp_map_of_lift_of_le (a : A) : 
algebra_map A C a = @algebra_map B C _ _ (algebra_of_lift_of_le B C h) (algebra_map A B a) :=
begin
  have : @algebra_map B C _ _ (algebra_of_lift_of_le B C h) = lift_of_le B C h := by refl,
  rw this,
  dunfold lift_of_le lift_of_sup,
  rw lift_eq,
end

def is_localization_of_lift_of_le (h : M ≤ N) :
@is_localization _ _ (N.map (algebra_map A B) : submonoid B) C _ (algebra_of_lift_of_le B C h) :=
@is_localization_of_lift_of_sup A _ M N B _ C _ _ _ _ (by rw sup_eq_right.mpr h; apply_instance)

end

section

variables 
{A : Type*} [comm_ring A] {M N : submonoid A}
(B : Type*) [comm_ring B] 
[algebra A B] [is_localization M B]

lemma is_localization_of_le_of_exists_mul_mem (h_le : M ≤ N) (h : ∀ n : N, ∃ a : A, ↑n * a ∈ M) :
is_localization N B :=
begin
  split,
  { rintros ⟨n, hn⟩,
    rcases h ⟨n, hn⟩ with ⟨a, hm⟩,
    let p := map_units B ⟨n * a, hm⟩,
    simp only [set_like.coe_mk, is_unit.mul_iff, ring_hom.map_mul] at p,
    exact p.left },
  { intros b,
    rcases surj M b with ⟨⟨a, ⟨m, hm⟩⟩, H⟩,
    use ⟨a, ⟨m, set_like.le_def.mp h_le hm⟩⟩,
    exact H },
  { intros a₁ a₂,
    split,
    intros ha,
    rcases (eq_iff_exists M B).mp ha with ⟨⟨m, hm⟩, H⟩,
    use ⟨m, set_like.le_def.mp h_le hm⟩,
    exact H,
    rintros ⟨⟨n, hn⟩, H⟩,
    rcases h ⟨n, hn⟩ with ⟨a, hm⟩,
    apply (eq_iff_exists M B).mpr _,
    use ⟨n * a, hm⟩,
    rw [set_like.coe_mk, <-mul_assoc, <-mul_assoc],
    congr' 1 }
end

end

section

variables {A : Type*} [integral_domain A] {f : A} (h_ne : f ≠ 0)
(B : Type*) [integral_domain B] (C : Type*) [integral_domain C]
[algebra A B] [algebra A C]
[is_localization.away f B] [is_fraction_ring A C]

--local attribute[instance] algebra_of_lift_of_le
include f h_ne

noncomputable def lift_of_away_frac : B →+* C :=
lift_of_le B C (powers_le_non_zero_divisors_of_no_zero_divisors  h_ne)

noncomputable def algebra_of_away_frac : algebra B C :=
ring_hom.to_algebra (lift_of_away_frac h_ne B C)

--local attribute [instance] algebra_of_away_frac

lemma eq_comp_map_of_lift_of_of_away_frac (a : A) : algebra_map A C a = 
@algebra_map B C _ _ (algebra_of_away_frac h_ne B C) (algebra_map A B a) :=
begin
  have : @algebra_map B C _ _ (algebra_of_away_frac h_ne B C) = lift_of_away_frac h_ne B C := by refl,
  rw this,
  dunfold lift_of_away_frac lift_of_le lift_of_sup,
  rw lift_eq,
end

def is_localization_of_away :
@is_localization B _ ((non_zero_divisors A).map (algebra_map A B) : submonoid B) C _ 
  (algebra_of_lift_of_le B C
  (powers_le_non_zero_divisors_of_no_zero_divisors  h_ne)) :=
is_localization_of_lift_of_le B C _

lemma non_zero_map_le_non_zero :
((non_zero_divisors A).map (algebra_map A B) : submonoid B) ≤ non_zero_divisors B :=
begin
  rintros x ⟨a, ⟨ha, H⟩⟩,
  rw <- H,
  refine ring_hom.map_mem_non_zero_divisors _ _ ha,
  refine is_localization.injective B (powers_le_non_zero_divisors_of_no_zero_divisors  h_ne),
end

lemma exists_mul_mem_of_away_of_ne_zero (g : non_zero_divisors B) :
∃ b : B, ↑g * b ∈ ((non_zero_divisors A).map (algebra_map A B) : submonoid B) :=
begin
  rcases is_localization.surj (submonoid.powers f) (g : B) with ⟨⟨gn, ⟨gd, hg⟩⟩, H⟩,
  dsimp at H,
  use algebra_map A B gd,
  rw H,
  simp only [submonoid.mem_map],
  refine ⟨gn, _, rfl⟩,
  rw mem_non_zero_divisors_iff_ne_zero,
  intros h,
  let p := (is_localization.to_map_eq_zero_iff B (powers_le_non_zero_divisors_of_no_zero_divisors  h_ne)).mpr h,
  rw <- H at p,
  have hgd : (algebra_map A B) gd ∈ non_zero_divisors B,
  rw mem_non_zero_divisors_iff_ne_zero,
  refine is_localization.to_map_ne_zero_of_mem_non_zero_divisors B (powers_le_non_zero_divisors_of_no_zero_divisors  h_ne) _,
  refine set_like.le_def.mp (powers_le_non_zero_divisors_of_no_zero_divisors  h_ne) hg,
  let q := (non_zero_divisors B).mul_mem' g.2 hgd,
  simp at q,
  rw mem_non_zero_divisors_iff_ne_zero at q,
  refine q p,
end

set_option pp.implicit false

def is_fraction_of_algebra_of_away_frac :
@is_fraction_ring B _ C _ (algebra_of_away_frac h_ne B C):=
begin
  letI : algebra B C := (algebra_of_away_frac h_ne B C),
  haveI := is_localization_of_away h_ne B C,
  exact is_localization_of_le_of_exists_mul_mem C (non_zero_map_le_non_zero h_ne B) 
    (λ n, exists_mul_mem_of_away_of_ne_zero h_ne B n),
end

end

end is_localization