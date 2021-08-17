import ring_theory.localization
import tactic.rewrite_search.frontend

noncomputable theory

section

variables {A : Type*}  [comm_ring A]
(M : submonoid A) (N : submonoid A)
{B : Type*} [comm_ring B] (C : Type*) [comm_ring C]
(N' : submonoid B) [algebra A B] [algebra B C]
[is_localization M B] [is_localization N' C]

def algebra.trans
{A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C] : 
algebra A C := (ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B)))

local attribute[instance] algebra.trans

lemma algebra_map_comp : 
algebra_map A C = (algebra_map B C).comp (algebra_map A B) := by refl

lemma mem_union_is_unit
[algebra A B] [algebra B C] [is_localization M B] [is_localization N' C]
(a : (M : set A) ∪ (N'.comap (algebra_map A B) : submonoid A)) : 
is_unit (algebra_map A C a) :=
begin
  cases a with av ap,
  cases ap,
  rw algebra_map_comp,
  simp only [function.comp_app, ring_hom.coe_comp],
  apply is_unit.map',
  refine is_localization.map_units B ⟨av, ap⟩,
  refine is_localization.map_units C ⟨algebra_map A B av, ap⟩
end

lemma mem_sup_is_unit
[algebra A B] [algebra B C] [is_localization M B] [is_localization N' C]
(a : M ⊔ N'.comap (algebra_map A B)) : 
is_unit (algebra_map A C a) :=
begin
  cases a with a_v a_in,
  rw set_like.coe_mk,
  rw [<- submonoid.closure_eq M, 
      <- submonoid.closure_eq (N'.comap (algebra_map A B) : submonoid A)] 
        at a_in,
  rw <- submonoid.closure_union at a_in,
  refine submonoid.closure_induction a_in _ _ _,
  { exact λ a ha, by refine mem_union_is_unit M C N' ⟨a, ha⟩ },
  { refine is_unit.map' _ is_unit_one },
  { intros _ _,
    rw ring_hom.map_mul,
    refine is_unit.mul }
end

lemma sup_surj 
[algebra A B] [algebra B C] [is_localization M B] [is_localization N' C] 
(z : C) (h_map : N' = N.map (algebra_map A B)) : 
∃ (x : A × ↥(M ⊔ N)), z * (algebra_map A C) ↑(x.snd) = (algebra_map A C) x.fst :=
begin
  rw h_map at *,
  tactic.unfreeze_local_instances,
  let y := is_localization.sec ((N.map (algebra_map A B)) : submonoid B) z,
  let x := is_localization.sec M y.1,
  rcases submonoid.mem_map.mp y.2.property with ⟨n, ⟨nh ,H⟩⟩,
  use ⟨x.1, ⟨x.2 * n, submonoid.mul_mem _ (submonoid.mem_sup_left x.2.property) (submonoid.mem_sup_right nh)⟩⟩,
  simp only [set_like.coe_mk, function.comp_app, ring_hom.coe_comp, ring_hom.map_mul, algebra_map_comp],
  rw <- is_localization.sec_spec M (is_localization.sec _ z).1,
  simp at H,
  rw [H, ring_hom.map_mul, <- is_localization.sec_spec _ z],
  ring,
end

lemma sup_eq_iff_exist
[algebra A B] [algebra B C] [is_localization M B] [is_localization N' C] 
(x y : A) (h_map : N' = N.map (algebra_map A B)) : 
(algebra_map A C) x = (algebra_map A C) y ↔ ∃ (c : ↥(M ⊔ N)), x * ↑c = y * ↑c :=
begin
  rw algebra_map_comp,
  simp only [function.comp_app, ring_hom.coe_comp],
  split,
  { let p := @is_localization.eq_iff_exists _ _ N' C _ _ _ (algebra_map A B x) (algebra_map A B y),
    rw h_map at *,
    intros h,
    cases p.mp h with c hc,
    rcases submonoid.mem_map.mp c.property with ⟨c0, ⟨ch ,H⟩⟩,
    simp at H,
    rw <- H at hc,
    simp only [ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe] at hc,
    rw [<- ring_hom.map_mul, <- ring_hom.map_mul] at hc,
    let q := @is_localization.eq_iff_exists _ _ M B _ _ _ (x * c0) (y * c0),
    cases q.mp hc with d hd,
    use ⟨c0 * d, submonoid.mul_mem _ (submonoid.mem_sup_right ch) (submonoid.mem_sup_left d.property)⟩,
    dsimp,
    rw [mul_assoc, mul_assoc] at hd,
    exact hd },
  { rintros ⟨⟨cv, cp⟩, hc⟩,
    rw submonoid.mem_sup at cp,
    cases cp with c1 c2,
    repeat {rw submonoid.closure_eq at c2},
    rcases c2 with ⟨cm, ⟨a, ⟨an, ha⟩⟩⟩,
    let p := @is_localization.eq_iff_exists _ _ N' C _ _ _ (algebra_map A B (x * c1)) (algebra_map A B (y * c1)),
    let a' := algebra_map A B a,
    have a'_in : a' ∈ N',
    { rw h_map,
      use a,
      use an,
      simp only [ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe] },
    have : (algebra_map B C) ((algebra_map A B) (x * c1)) = (algebra_map B C) ((algebra_map A B) (y * c1)),
    { apply p.mpr,
      use ⟨a', a'_in⟩,
      simp,
      repeat {rw <- ring_hom.map_mul},
      repeat {assoc_rw ha},
      simp at hc,
      rw hc },
    simp only [ring_hom.map_mul] at this,
    rw <- is_unit.mul_left_inj (is_unit.map' (algebra_map B C) (is_localization.map_units B ⟨c1, cm⟩)),
    assumption },
end

lemma sup.is_localization
(h_map : N' = N.map (algebra_map A B)) :
is_localization (M ⊔ N) C :=
begin
  split,
  { rintros ⟨y, yp⟩,
    simp only [set_like.coe_mk],
    have hy : y ∈ M ⊔ N'.comap (algebra_map A B),
    { rw h_map,
      refine set_like.le_def.mp _ yp,
      refine sup_le_sup_left _ _,
      exact submonoid.le_comap_map N },
    exact mem_sup_is_unit M C N' ⟨y, hy⟩ },
  { refine λ c, sup_surj M N C N' c h_map },
  { refine λ a₁ a₂, sup_eq_iff_exist M N C N' a₁ a₂ h_map }
end

lemma is_localization.le
(h_map : N' = N.map (algebra_map A B))
(h_le : M ≤ N) :
is_localization N C :=
begin
  have : M ⊔ N = N,
    simp only [sup_eq_right],
    assumption,
  rw <- this,
  exact sup.is_localization M N C N' h_map,
end

lemma id_comap : N = N.comap (ring_hom.id A) :=
begin
  apply le_antisymm,
  intros n hn,
  simp at *,
  exact hn,
  intros n hn,
  simp at *,
  exact hn,
end

lemma le_comap (h_le : M ≤ N) : M ≤ N.comap (ring_hom.id A) :=
begin
  rw <- id_comap N,
  exact h_le,
end

end

section

variables
{A : Type*}  [comm_ring A]
(M : submonoid A) (N : submonoid A)
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization (M ⊔ N) C]

include M N

def lift_sup : B →+* C :=
begin
  refine @is_localization.lift A _ M B _ _ C _ _ (algebra_map A C) _,
  rintros ⟨m, hm⟩,
  dsimp,
  refine is_localization.map_units C (⟨m, set_like.le_def.mp le_sup_left hm⟩ : M ⊔ N),
end

def algebra_of_lift_sup : algebra B C := ring_hom.to_algebra (lift_sup M N B C)

local attribute[instance] algebra_of_lift_sup

lemma comp_eq_app (a : A) : algebra_map A C a = (algebra_map B C (algebra_map A B a)):=
begin
  have : algebra_map B C = lift_sup M N B C := by refl,
  rw this,
  unfold lift_sup,
  simp only [is_localization.lift_eq],
end

lemma comp_eq : (algebra_map A C) = (algebra_map B C).comp (algebra_map A B) :=
begin
  ext,
  simp only [function.comp_app, ring_hom.coe_comp],
  refine comp_eq_app _ _ _ _ _,
end

def lift_sup.is_localization
{A : Type*}  [comm_ring A]
(M : submonoid A) (N : submonoid A)
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization (M ⊔ N) C] :
is_localization (N.map (algebra_map A B) : submonoid B) C :=
begin
  split,
  { intros n',
    rcases submonoid.mem_map.mp n'.property with ⟨n, ⟨hn, H⟩⟩,
    simp only [ring_hom.coe_monoid_hom, subtype.val_eq_coe] at H,
    have : n ∈ M ⊔ N := set_like.le_def.mp le_sup_right hn,
    rw [<- H, <- comp_eq_app],
    refine is_localization.map_units C ⟨n, this⟩ },
  { intros c,
    let c0 := is_localization.sec ((M ⊔ N) : submonoid A) c,
    rcases is_localization.surj (M ⊔ N) c with ⟨⟨a, ⟨mn, h_mn⟩⟩ , H⟩,
    rcases submonoid.mem_sup.mp h_mn with ⟨m, hm, n, hn, H'⟩,
    repeat {rw comp_eq_app M N B C at H},
    rw [set_like.coe_mk] at H,
    dsimp at H,
    have : algebra_map A B n ∈ (N.map (algebra_map A B) : submonoid B),
    apply submonoid.mem_map.mpr,
    use n,
    use hn,
    rw [ring_hom.coe_monoid_hom],
    fsplit,
    fsplit,
    exact ↑((is_unit.unit (is_localization.map_units B ⟨m, hm⟩))⁻¹) * (algebra_map A B a),
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
    rw is_unit.unit_spec },
  { intros b₁ b₂,
    split,
    { intros h,
      rcases is_localization.surj M b₁ with ⟨⟨a₁, ⟨m₁, hm₁⟩⟩, H₁⟩,
      rcases is_localization.surj M b₂ with ⟨⟨a₂, ⟨m₂, hm₂⟩⟩, H₂⟩,
      have : algebra_map A C (a₁ * m₂) = algebra_map A C (a₂ * m₁),
      rw comp_eq_app M N B C,
      rw comp_eq_app M N B C,
      dsimp at *,
      simp only [ring_hom.map_mul],
      rw [<- H₁, <- H₂],
      simp only [ring_hom.map_mul],
      rw h,
      ring,
      rcases (is_localization.eq_iff_exists (M ⊔ N) C).mp this with ⟨⟨mn, mn_in⟩, hmn⟩,
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
      exact is_localization.map_units B ⟨m, hm⟩,
      repeat {rw [mul_assoc, <- ring_hom.map_mul]},
      rw mul_comm at H',
      rw H',
      have hb₁ : b₁ = is_localization.mk' B a₁ ⟨m₁, hm₁⟩ := is_localization.eq_mk'_iff_mul_eq.mpr H₁,
      have hb₂ : b₂ = is_localization.mk' B a₂ ⟨m₂, hm₂⟩ := is_localization.eq_mk'_iff_mul_eq.mpr H₂,
      rw [hb₁, hb₂],
      nth_rewrite_lhs 0 mul_comm,
      nth_rewrite_rhs 0 mul_comm,
      rw [is_localization.mul_mk'_eq_mk'_of_mul, is_localization.mul_mk'_eq_mk'_of_mul],
      refine is_localization.mk'_eq_of_eq _,
      dsimp,
      exact calc mn * a₂ * m₁ = a₂ * m₁ * mn : by ring
      ...                      = a₁ * m₂ * mn : by rw <-hmn
      ...                      = mn * a₁ * m₂ : by ring },
    { intros h,
      rcases h with ⟨⟨n', hn'⟩, H⟩,
      rcases submonoid.mem_map.mp hn' with ⟨n, ⟨hn, H'⟩⟩,
      have n_in : n ∈ M ⊔ N := submonoid.mem_sup_right hn,
      rcases is_localization.surj M b₁ with ⟨⟨a₁, ⟨m₁, hm₁⟩⟩, H₁⟩,
      rcases is_localization.surj M b₂ with ⟨⟨a₂, ⟨m₂, hm₂⟩⟩, H₂⟩,
      dsimp at *,
      have : ∃ m : M, a₁ * m₂ * n * m = a₂ * m₁ * n * m,
      refine (is_localization.eq_iff_exists M B).mp _,
      simp only [ring_hom.map_mul],
      rw H',
      rw [<- H₁, <- H₂],
      exact calc b₁ * (algebra_map A B) m₁ * (algebra_map A B) m₂ * n'
               = b₁ * n' * (algebra_map A B) m₁ * (algebra_map A B) m₂  : by ring
      ...      = b₂ * n' * (algebra_map A B) m₁ * (algebra_map A B) m₂  : by rw H
      ...      = b₂ * (algebra_map A B) m₂ * (algebra_map A B) m₁ * n'  : by ring,
      rcases this with ⟨⟨m, hm⟩, H''⟩,
      have : n * m ∈ M ⊔ N,
      rw mul_comm,
      refine submonoid.mul_mem _ (submonoid.mem_sup_left hm) (submonoid.mem_sup_right hn),
      dsimp at H'',
      have p : algebra_map A C (a₁ * m₂) = algebra_map A C (a₂ * m₁),
      refine (is_localization.eq_iff_exists (M ⊔ N) C).mpr _,
      use ⟨n * m, this⟩,
      dsimp,
      repeat {rw <- mul_assoc},
      exact H'',
      repeat {rw comp_eq_app M N B C at p},
      simp only [ring_hom.map_mul] at p,
      rw [<- H₁, <- H₂] at p,
      refine (is_unit.mul_left_inj _).mp _,
      exact algebra_map A C (m₁ * m₂),
      have : m₁ * m₂ ∈ M ⊔ N,
      refine submonoid.mul_mem _ (submonoid.mem_sup_left hm₁) (submonoid.mem_sup_left hm₂),
      exact is_localization.map_units C ⟨m₁ * m₂, this⟩,
      repeat {rw comp_eq_app M N B C},
      simp only [ring_hom.map_mul] at *,
      repeat {rw mul_assoc at *},
      nth_rewrite 3 mul_comm,
      exact p } },
end

end

section

variables
{A : Type*}  [comm_ring A]
(M : submonoid A) (N : submonoid A)
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization N C]

def algebra_of_lift_le (h : M ≤ N) : algebra B C := 
begin
  have : M ⊔ N = N := sup_eq_right.mpr h,
  rw <- this at *,
  resetI,
  refine algebra_of_lift_sup M N B C,
end

local attribute[instance] algebra_of_lift_le

def lift_le.is_localization (h : M ≤ N) :
@is_localization _ _ (N.map (algebra_map A B) : submonoid B) C _ (algebra_of_lift_le M N B C h) :=
begin
  have : M ⊔ N = N := sup_eq_right.mpr h,
  haveI : is_localization (M ⊔ N) C := by rw this; apply_instance,
  exact lift_sup.is_localization M N B C,
end

end

section

variables {A : Type*} [integral_domain A]
(B : Type*) [integral_domain B] (C : Type*) [integral_domain C]
[algebra A B] [algebra A C]

local attribute[instance] algebra_of_lift_le

#check @is_localization

lemma is_fraction.le
(f : A) (h_ne : f ≠ 0)
[is_localization.away f B] [is_fraction_ring A C] :
@is_localization B _ ((non_zero_divisors A).map (algebra_map A B) : submonoid B) C _ 
  (algebra_of_lift_le (submonoid.powers f) (non_zero_divisors A) B C
  (powers_le_non_zero_divisors_of_domain h_ne)) :=
lift_le.is_localization (submonoid.powers f) (non_zero_divisors A) B C _


end



#check @is_localization

section

/-
variables {A : Type*}  [comm_ring A]
(M : submonoid A) (N : submonoid A)
(B : Type*) [comm_ring B] (C : Type*) [comm_ring C]
[algebra A B] [algebra A C]
[is_localization M B] [is_localization N C]

noncomputable
def lift_id (h_le : M ≤ N) : B →+* C := is_localization.map C (ring_hom.id A) (le_comap M N h_le)

example (h_le : M ≤ N) (h : ∀ n : N, ∃ a : A, ∃ m : M, (n : A) = a * m) : 
function.bijective (lift_id M N B C h_le) :=
begin
  let M' := (M.map (algebra_map A B) : submonoid B),
  haveI : algebra B C := ring_hom.to_algebra (lift_id M N B C h_le),
  have : is_localization M' C,
  { },
  fsplit,
  intros b₁ b₂ hb,
  let z:= is_localization.sec N (lift_id M N B C h_le b₁),
  -- with a n,
  rcases h z.2 with ⟨a', ⟨m, hm⟩⟩,
end

-/

end