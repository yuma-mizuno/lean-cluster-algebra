import linear_algebra.dual
import algebra.monoid_algebra
import ring_theory.localization
import ring_theory.nilpotent
import linear_algebra.bilinear_form
import tactic.basic
import localization

universes u

noncomputable theory
open_locale classical

section skew_sym_bilin_form
namespace skew_sym_bilin_form

open skew_sym_bilin_form bilin_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_monoid M] [module R M] {B : bilin_form R M}

def is_skew_sym (B : bilin_form R M) : Prop := 
∀ (x y : M), B x y = - B y x

variable (H : is_skew_sym B)
include H

lemma skew_sym (x y : M) : B x y = - B y x := H x y

lemma is_refl : refl_bilin_form.is_refl B := 
λ x y H1, by rw H y x; exact neg_eq_zero.mpr H1

lemma ortho_sym {x y : M} :
  is_ortho B x y ↔ is_ortho B y x := refl_bilin_form.ortho_sym (is_refl H)

lemma is_alt [no_zero_divisors R] [char_zero R] : alt_bilin_form.is_alt B := 
begin
  intros n,
  let h :=  H n n,
  rw eq_neg_iff_add_eq_zero at h,
  simp only [add_self_eq_zero] at h,
  exact h,
end

@[simp]
lemma self_eq_zero  [no_zero_divisors R] [char_zero R] (x : M) : B x x = 0 :=  is_alt H x

@[simp]
lemma self_eq_zero_to_lin [no_zero_divisors R] [char_zero R] (x : M)  : to_lin' B x x = 0 := self_eq_zero H x

end skew_sym_bilin_form
end skew_sym_bilin_form

namespace cluster

class inductive eq_or_eq_neg {N : Type*} [add_comm_group N] (v w : N) : Prop
| eq : w = v → eq_or_eq_neg
| eq_neg : w = -v  → eq_or_eq_neg

class inductive is_sign (ε : ℤ) : Prop
| pos : ε = 1 → is_sign
| neg : ε = -1 → is_sign

instance one.is_sign : is_sign 1 := is_sign.pos rfl

instance neg_one.is_sign : is_sign (-1) := is_sign.neg rfl

instance neg.is_sign (ε : ℤ) [is_sign ε] : is_sign (-ε) :=
begin
  let h : is_sign ε := by apply_instance,
  refine is_sign.rec_on h (λ H, _) (λ H, _),
  rw H,
  apply_instance,
  rw H,
  rw neg_neg,
  apply_instance,
end

open skew_sym_bilin_form

class skew_symmetric_form (N : Type*) [add_comm_group N] :=
(form : bilin_form ℤ N)
(skew : is_skew_sym form)

variables {N : Type*} [add_comm_group N] [no_zero_smul_divisors ℤ N]
[skew_symmetric_form N] 

section seed_mutation

variables (s s' : multiset N) (v : N) (ε : ℤ)

open skew_symmetric_form

abbreviation B := @bilin_form.to_lin ℤ N _ _ _ form

def pl_mutation (v : N) (ε : ℤ) : N → N :=
λ n, n + (max 0 (ε * (B n v))) • v

def pl_mutation.equiv : N ≃ N :=
{ to_fun := pl_mutation v ε,
  inv_fun := pl_mutation (-v) (-ε),
  left_inv := 
  begin
    intros n,
    unfold pl_mutation,
    simp only [neg_mul_eq_neg_mul_symm,
      algebra.id.smul_eq_mul, bilin_form.to_lin_apply, linear_map.smul_apply, 
      bilin_form.neg_right, mul_neg_eq_neg_mul_symm, smul_neg, linear_map.map_smul, 
      linear_map.add_apply, linear_map.map_add],
    rw self_eq_zero skew,
    simp only [add_zero, add_neg_cancel_right,
      mul_neg_eq_neg_mul_symm, neg_neg, mul_zero, neg_zero],
  end,
  right_inv := 
  begin
    intros n,
    unfold pl_mutation,
    simp only [neg_mul_eq_neg_mul_symm, linear_map.map_neg, algebra.id.smul_eq_mul, 
      bilin_form.to_lin_apply, linear_map.smul_apply, bilin_form.neg_right, mul_neg_eq_neg_mul_symm, 
      linear_map.neg_apply, smul_neg, neg_neg, linear_map.map_smul, linear_map.add_apply, linear_map.map_add],
    rw self_eq_zero skew,
    simp only [add_zero, neg_add_cancel_right, eq_self_iff_true, mul_zero, neg_zero],
  end }

lemma pl_mutation.bijective :
function.bijective (pl_mutation v ε) :=
(pl_mutation.equiv v ε).bijective

@[simp] lemma pl_mutation_neg_left_id :
pl_mutation (-v) (-ε) ∘ pl_mutation v ε = id :=
by ext x; apply (pl_mutation.equiv v ε).left_inv x

@[simp] lemma pl_mutation_neg_righ_id :
pl_mutation v ε ∘ pl_mutation (-v) (-ε) = id :=
by ext x; apply (pl_mutation.equiv v ε).right_inv x

structure seed_mutation (s s' : multiset N) :=
(sign : ℤ)
(is_sign : is_sign sign)
(src_vect : N)
(tar_vect : N)
(src_in : src_vect ∈ s)
(tar_in : tar_vect ∈ s')
(seed_tar_src : s'.erase tar_vect = multiset.map (pl_mutation src_vect sign)  (s.erase src_vect))
(vect_tar_src : tar_vect = - src_vect)

end seed_mutation

section direction
variables {s s' : multiset N} (μ : seed_mutation s s') (v : N)

class is_mutation_direction  : Prop :=
(is_direction : ∃ k : ℤ, v = k • μ.src_vect)

class is_primitive_mutation_direction  : Prop :=
(is_primitive_direction : eq_or_eq_neg μ.src_vect v)

lemma seed_mutation.is_direction [is_mutation_direction μ v] :
∃ k : ℤ, v = k • μ.src_vect := is_mutation_direction.is_direction

lemma seed_mutation.is_primitive_direction [is_primitive_mutation_direction μ v] :
v = μ.src_vect ∨ v = μ.tar_vect := 
begin
   cases @is_primitive_mutation_direction.is_primitive_direction N _ _ _ _ _ μ v _ with h₁ h₂,
   rw h₁,
   simp only [true_or, eq_self_iff_true],
   rw h₂,
   rw μ.vect_tar_src,
   simp only [eq_self_iff_true, neg_inj, or_true],
end

instance src_vect_is_mutation_direction :
is_mutation_direction μ μ.src_vect := by use 1; simp

instance tar_vect_is_mutation_direction :
is_mutation_direction μ μ.tar_vect := by use -1; simp; exact μ.vect_tar_src

instance direction_of_primitive_direction [is_primitive_mutation_direction μ v] : 
is_mutation_direction μ v :=
begin
  cases μ.is_primitive_direction v with h,
  rw h,
  apply_instance,
  rw h,
  apply_instance,
end

lemma seed_mutation.tar_vect_eq_neg_src_vect {s s' : multiset N} (μ : seed_mutation s s') : μ.tar_vect = - μ.src_vect :=
μ.vect_tar_src

lemma seed_mutation.src_vect_eq_neg_tar_vect {s s' : multiset N} (μ : seed_mutation s s') :  μ.src_vect = - μ.tar_vect :=
by calc
  μ.src_vect = - - μ.src_vect : by rw neg_neg
          ... =   - μ.tar_vect : by rw μ.vect_tar_src

instance sign_tar_vect_is_mutation_direction :
is_mutation_direction μ (μ.sign • μ.tar_vect) :=
begin
  let p := μ.is_sign,
  cases μ.is_sign with pos neg,
  rw pos,
  simp,
  apply_instance,
  rw neg,
  rw μ.tar_vect_eq_neg_src_vect,
  simp,
  apply_instance,
end

instance sign_src_vect_is_mutation_direction :
is_mutation_direction μ (μ.sign • μ.src_vect) :=
begin
  cases μ.is_sign with pos neg,
  rw pos,
  simp,
  apply_instance,
  rw neg,
  rw μ.src_vect_eq_neg_tar_vect,
  simp,
  apply_instance,
end

end direction

section seed_mutation

open skew_symmetric_form

namespace seed_mutation



/-
@[simp] lemma form_tar_src_eq_zero {s s' : multiset N} (μ : seed_mutation s s') : 
B μ.tar_vect μ.src_vect = 0 :=
begin
  rw μ.vect_tar_src,
  simp,
  rw self_eq_zero skew,
end

@[simp] lemma form_src_tar_eq_zero {s s' : multiset N} (μ : seed_mutation s s') : 
B μ.src_vect μ.tar_vect = 0 :=
begin
  rw μ.vect_tar_src,
  simp,
  rw self_eq_zero skew,
end

-/

@[simp] lemma form_mutation_direction_eq_zero {s s' : multiset N} (μ : seed_mutation s s')
(v w : N) [is_mutation_direction μ v] [is_mutation_direction μ w] : 
B v w = 0 :=
begin
  cases μ.is_direction v with k hk,
  cases μ.is_direction w with l hl,
  rw [hk, hl],
  simp only [algebra.id.smul_eq_mul,
    bilin_form.to_lin_apply,
    linear_map.smul_apply,
    bilin_form.smul_right,
    linear_map.map_smul],
  rw self_eq_zero skew,
  simp,
end

end seed_mutation

lemma pl_mutation_eq (v : N) {w : N} (ε : ℤ) (c : ℤ) (h : w = c • v) : pl_mutation v ε w = w :=
begin
  unfold pl_mutation,
  rw h,
  simp,
  rw self_eq_zero skew,
  simp,
end

@[simp] lemma pl_mutation_eq' (v : N) (ε : ℤ) : pl_mutation v ε v = v :=
begin
  have p : v = (1 : ℤ) • v := by simp,
  exact pl_mutation_eq v ε 1 p,
end

def seed_mutation.symm {s s' : multiset N} (μ : seed_mutation s s') : seed_mutation s' s :=
{ sign := - μ.sign,
  is_sign := 
  begin
    cases μ.is_sign with pos neg,
    rw pos,
    exact is_sign.neg rfl,
    rw neg,
    rw neg_neg,
    exact is_sign.pos rfl,
  end,
  src_vect := μ.tar_vect,
  tar_vect := μ.src_vect,
  src_in := μ.tar_in,
  tar_in := μ.src_in,
  seed_tar_src :=
  begin
    let h := μ.seed_tar_src,
    rw [multiset.map_erase] at h,
    rw [h, multiset.map_erase],
    simp only [function.comp_app, multiset.map_congr, multiset.map_map],
    rw [pl_mutation_eq μ.src_vect μ.sign 1, pl_mutation_eq μ.tar_vect (-μ.sign) (-1),
      μ.tar_vect_eq_neg_src_vect],
    simp only [id.def, multiset.map_id', eq_self_iff_true, multiset.map_congr, cluster.pl_mutation_neg_left_id],
    congr,
    apply eq.symm,
    apply multiset.map_id',
    repeat {simp},
    apply μ.src_vect_eq_neg_tar_vect,
    exact function.bijective.injective (pl_mutation.bijective μ.tar_vect (-μ.sign)),
    exact function.bijective.injective (pl_mutation.bijective μ.src_vect μ.sign),
  end,
  vect_tar_src := μ.src_vect_eq_neg_tar_vect, }




end seed_mutation


section


def ring_of_function (N : Type*) [add_comm_group N]  :=
add_monoid_algebra ℤ (module.dual ℤ N)

local attribute [reducible, inline] add_monoid_algebra ring_of_function

instance : comm_ring (ring_of_function N) := add_monoid_algebra.comm_ring
instance : comm_ring (module.dual ℤ N →₀ ℤ) := add_monoid_algebra.comm_ring

open skew_symmetric_form

variable [h : is_integral_domain (ring_of_function(N))]

instance ring_of_function.integral_domain : integral_domain (ring_of_function N) := 
is_integral_domain.to_integral_domain _ h

instance finsupp.integral_domain [h : is_integral_domain (ring_of_function(N))] : 
integral_domain (module.dual ℤ N →₀ ℤ) :=  
begin
  apply' ring_of_function.integral_domain,
  assumption,
end

local attribute [instance, priority 50] ring_of_function.integral_domain finsupp.integral_domain

def function_of_vector (v : N) : (ring_of_function N) :=
finsupp.single 0 1 + finsupp.single (B v) 1

lemma function_of_vector_ne_zero  (v : N) : function_of_vector v ≠ 0 :=
begin
  unfold function_of_vector,
  let H := eq_or_ne (B v) 0,
  rw [ne.def] at H,
  cases H,
  rw [H, finsupp.nonzero_iff_exists],
  use 0,
  simp,
  rw finsupp.nonzero_iff_exists,
  use 0,
  simp only [finsupp.single_eq_same, pi.add_apply, finsupp.coe_add],
  have : ( 0 : module.dual ℤ N) ∉ (finsupp.single (B v) 1 : ring_of_function N).support,
  { rw [finsupp.support_single_ne_zero, finset.mem_singleton, <- ne.def, ne_comm],
      exact H,
      simp },
  rw finsupp.not_mem_support_iff at this,
  rw this,
  simp,
end

lemma function_of_vector_is_palindromic  (v : N) :
(finsupp.single (B v) 1 : (ring_of_function N)) * (function_of_vector (-v)) = function_of_vector v :=
begin
  unfold function_of_vector,
  erw mul_add,
  repeat {rw add_monoid_algebra.single_mul_single},
  simp only [add_zero, mul_one, linear_map.map_neg, add_right_neg],
  apply add_comm,
end

def function_of_vector_is_palindromic' (v : N) : 
(finsupp.single (B (- v)) 1 : ring_of_function N) * (function_of_vector v) = function_of_vector (-v) :=
begin
  let h := function_of_vector_is_palindromic (-v),
  rw neg_neg at h,
  assumption',
end

def pow_neg_vect_in_pow_vect {v : N} {f : ring_of_function N} (h : f ∈ submonoid.powers (function_of_vector (-v))) : 
∃ k : ℕ, ((finsupp.single (B (k • v)) 1) : ring_of_function N) * f ∈ submonoid.powers (function_of_vector v) :=
begin
  cases h with k h,
  use k,
  rw <- h,
  unfold function_of_vector,
  simp only [linear_map.map_neg, linear_map.map_smul_of_tower, linear_map.to_fun_eq_coe],
  rw [<- one_pow k, <- add_monoid_algebra.single_pow, one_pow k, <- mul_pow, mul_add],
  repeat {rw add_monoid_algebra.single_mul_single},
  simp only [add_zero, mul_one, add_right_neg],
  rw add_comm,
  exact ⟨k, rfl⟩,
end

def pow_vect_in_pow_neg_vect {v : N} {f : ring_of_function N} (h : f ∈ submonoid.powers (function_of_vector v)) : 
∃ k : ℕ, ((finsupp.single (B (k • (-v))) 1) : ring_of_function N) * f ∈ submonoid.powers (function_of_vector (-v)) :=
begin
  cases h with k h,
  use k,
  rw <- h,
  unfold function_of_vector,
  simp only [linear_map.map_neg, linear_map.map_smul_of_tower, linear_map.to_fun_eq_coe],
  rw [<- one_pow k, <- add_monoid_algebra.single_pow, one_pow k, <- mul_pow, mul_add],
  repeat {rw add_monoid_algebra.single_mul_single},
  simp only [add_zero, mul_one, add_left_neg],
  rw add_comm,
  exact ⟨k, rfl⟩,
end




variables (v w : N) (S : Type*) [integral_domain S]
variables [algebra (ring_of_function N) S] 
[is_localization.away (function_of_vector v) S]
[is_localization.away (function_of_vector w) S]

abbreviation is_localization_at_vect : Prop := is_localization.away (function_of_vector v) S

/-
lemma is_localization_at_congr (vect_eq : v = w) :
(is_localization_at_vect v S) ↔ (is_localization_at_vect w S) :=
begin
  tactic.unfreeze_local_instances,
  subst vect_eq,
end
 
/-
instance is_localization_at_vect_neg_neg : is_localization_at_vect (-ε • -v) S :=
(is_localization_at_congr S (ε • v) (-ε • -v) $ by simp).mp $ by assumption
-/

lemma ring_of_function.map_powers : submonoid.map (ring_equiv.to_monoid_hom 
  (ring_equiv.refl _)) (submonoid.powers (function_of_vector v)) = 
  submonoid.powers (function_of_vector v) :=
begin
  simp only [eq_self_iff_true, submonoid.map_id, ring_equiv.to_monoid_hom_refl],
end

def function_of_vector.unit : units S :=
{ val := algebra_map (ring_of_function N) S (function_of_vector v),
  inv := is_localization.mk' S 1 ⟨function_of_vector v, submonoid.mem_powers _⟩,
  val_inv := 
  begin
    rw [is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self],
  end,
  inv_val := 
  begin
    rw [mul_comm, is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self],
  end, }

-/

/- lemma is_unit_of_vector : 
is_unit (is_localization.mk' S (function_of_vector v) (1 : submonoid.powers (function_of_vector v))) :=
begin
  use function_of_vector.unit v S,
  rw is_localization.mk'_one,
  refl,
end -/


def monomial.unit (m : module.dual ℤ N) : units S :=
{ val := algebra_map (ring_of_function N) S (finsupp.single m 1),
  inv := algebra_map (ring_of_function N) S (finsupp.single (-m) 1),
  val_inv := 
  begin
    rw <- ring_hom.map_mul,
    have : finsupp.single m 1 * finsupp.single (-m) 1 = (1 : ring_of_function N),
    rw add_monoid_algebra.single_mul_single,
    simp,
    exact add_monoid_algebra.one_def,
    rw this,
    apply ring_hom.map_one,
  end,
  inv_val :=
  begin
    rw <- ring_hom.map_mul,
    have : finsupp.single (-m) 1 * finsupp.single m 1 = (1 : ring_of_function N),
    rw add_monoid_algebra.single_mul_single,
    simp,
    exact add_monoid_algebra.one_def,
    rw this,
    apply ring_hom.map_one,
  end, }




/- lemma is_unit_of_neg_vector (h : w = -v) : 
is_unit (is_localization.mk' S (function_of_vector w) (1 : submonoid.powers (function_of_vector v))) :=
begin
  rw <- units.is_unit_mul_units _ (monomial.unit S (B v)),
  use function_of_vector.unit v S,
  rw is_localization.mk'_one,
  unfold function_of_vector.unit,
  unfold function_of_vector,
  unfold monomial.unit,
  simp only [linear_map.map_neg, ring_hom.map_add, units.coe_mk],
  rw [<- ring_hom.map_add, <- ring_hom.map_add, <- ring_hom.map_mul],
  congr,
  rw [add_mul, add_monoid_algebra.single_mul_single, add_monoid_algebra.single_mul_single, add_comm, h],
  simp,
end
 -/
end

section mutation

local attribute [class] is_integral_domain

variables {s s' : multiset N} (μ : seed_mutation s s') (S S' : Type*) [integral_domain S] [integral_domain S']
[algebra (ring_of_function N) S] [algebra (ring_of_function N) S']
[is_localization.away (function_of_vector (μ.sign • μ.src_vect)) S]
[is_localization.away (function_of_vector (μ.sign • μ.tar_vect)) S']
instance algebra_S : algebra (module.dual ℤ N →₀ ℤ) S:= by assumption
instance algebra_S' : algebra (module.dual ℤ N →₀ ℤ) S':= by assumption



open skew_symmetric_form

lemma is_localizaiton_eq_vect (v w : N) (h : w = v) (S : Type*) [integral_domain S] [algebra (ring_of_function N) S] :
is_localization.away (function_of_vector v) S → is_localization.away (function_of_vector w) S := by subst h; simp

/- lemma is_localizaiton_neg_vect (v w : N) (h : w = -v) (S : Type*) [integral_domain S] [algebra (ring_of_function N) S] :
is_localization.away (function_of_vector v) S → is_localization.away (function_of_vector w) S :=
begin
  intros H,
  subst h,
  resetI,
  split,
  { intros y,
    cases y with y yp,
    cases pow_neg_vect_in_pow_vect yp with k h_in,
    cases (is_localization.map_units S ⟨(finsupp.single (B (k • v)) 1 : ring_of_function N) * y, h_in⟩) with x hx,
    use monomial.unit S (k • (- B v)) * x,
    unfold monomial.unit,
    simp only [set_like.coe_mk, units.coe_mk, neg_nsmul, neg_neg, units.coe_mul],
    rw hx,
    erw <- ring_hom.map_mul,
    congr,
    dsimp,
    rw <- mul_assoc,
    rw add_monoid_algebra.single_mul_single,
    simp only [mul_one, linear_map.map_smul_of_tower, add_left_neg],
    rw <- add_monoid_algebra.one_def,
    rw one_mul },
  { intros z,
    rcases is_localization.surj (submonoid.powers (function_of_vector v)) z with ⟨⟨a, y⟩, hx⟩,
    cases y with y yp,
    cases pow_vect_in_pow_neg_vect yp with k h_in,
    use ⟨a * (finsupp.single (B (k • -v)) 1), ⟨(finsupp.single (B (k • -v)) 1 : ring_of_function N) * y, h_in⟩⟩,
    simp only [set_like.coe_mk, linear_map.map_neg, linear_map.map_smul_of_tower, neg_nsmul, ring_hom.map_mul],
    simp at hx,
    rw <- hx,
    rw mul_assoc,
    apply congr_arg (λ x, z * x),
    rw [<- ring_hom.map_mul, <- ring_hom.map_mul],
    apply congr_arg (algebra_map (ring_of_function N) S),
    rw mul_comm },
  { 
    intros x y,
    sorry
  },
end -/


/-
instance is_localization.tar_S : is_localization.away (function_of_vector (μ.tar_vect)) S :=
begin
  apply is_localizaiton_neg_vect μ.src_vect μ.tar_vect μ.tar_vect_eq_neg_src_vect,
  assumption,
end


instance is_localization.sign_src_S : is_localization.away (function_of_vector (μ.sign • μ.src_vect)) S :=
begin
  cases μ.is_sign,
  rw h,
  rw one_smul,
  assumption,
  rw h,
  rw μ.src_vect_eq_neg_tar_vect,
  simp,
  apply is_localizaiton_neg_vect μ.src_vect μ.tar_vect μ.tar_vect_eq_neg_src_vect,
  assumption,
end


instance is_localization.sign_tar_S' : is_localization.away (function_of_vector (μ.sign • μ.tar_vect)) S' :=
begin
  cases μ.is_sign,
  rw [h, one_smul],
  assumption,
  rw [h, μ.tar_vect_eq_neg_src_vect],
  simp,
  apply is_localizaiton_neg_vect μ.tar_vect μ.src_vect μ.src_vect_eq_neg_tar_vect,
  assumption,
end
-/

open skew_symmetric_form

/- def function_of_vector.unit : units S :=
{ val := algebra_map (ring_of_function N) S (function_of_vector v),
  inv := is_localization.mk' S 1 ⟨function_of_vector v, submonoid.mem_powers _⟩,
  val_inv := 
  begin
    rw [is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self],
  end,
  inv_val := 
  begin
    rw [mul_comm, is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self],
  end, } -/


def seed_mutation.unit : units S :=
{ val := algebra_map (ring_of_function N) S (function_of_vector (μ.sign • μ.src_vect)),
  inv := is_localization.mk' S 1 ⟨function_of_vector (μ.sign • μ.src_vect), submonoid.mem_powers _⟩,
  val_inv := by rw [is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self],
  inv_val := by rw [mul_comm, is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self] }

variables (ε : ℤ) [is_sign ε]

def mutation_monomial_aux : multiplicative (module.dual ℤ N) →* S :=
{ to_fun := λ m, 
  is_localization.mk' S
    (finsupp.single (multiplicative.to_add m) 1) (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect)))
      * units.val ((μ.unit S)^(ε • (-(multiplicative.to_add m) μ.src_vect))),
  map_one' :=
  begin
    have h : is_sign ε := by apply_instance,
    cases h with pos neg,
    rw pos,
    dsimp,
    rw [neg_zero, mul_zero, gpow_zero],
    unfold units.val,
    rw [mul_one, <- add_monoid_algebra.one_def, is_localization.mk'_one, ring_hom.map_one],
    rw neg,
    dsimp,
    rw [neg_zero, neg_mul_eq_neg_mul_symm, mul_zero, neg_zero, gpow_zero ],
    unfold units.val,
    rw [mul_one, <- add_monoid_algebra.one_def, is_localization.mk'_one, ring_hom.map_one],
  end,
  map_mul' := 
  begin
    intros x y,
    have h : is_sign ε := by apply_instance,
    cases h with pos neg,
    rw pos,
    dsimp,
    rw [one_mul, one_mul, one_mul, <- to_add_mul, gpow_neg, gpow_neg, gpow_neg, to_add_mul],
    rw [gpow_add, <- one_mul (1 : ℤ), <- add_monoid_algebra.single_mul_single],
    rw <- one_mul (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))),
    rw is_localization.mk'_mul,
    simp only [mul_inv_rev, mul_one],
    unfold units.val,
    ring_exp,
    rw neg,
    dsimp,
    rw [neg_mul_neg, neg_mul_neg, neg_mul_neg, one_mul, one_mul, one_mul],
    rw [gpow_add, <- one_mul (1 : ℤ), <- add_monoid_algebra.single_mul_single],
    rw <- one_mul (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))),
    rw is_localization.mk'_mul,
    simp only [mul_inv_rev, mul_one],
    unfold units.val,
    ring_exp,
  end}

def mutation_monomial : multiplicative (module.dual ℤ N) →* S :=
{ to_fun := λ m, 
  is_localization.mk' S
    (finsupp.single (multiplicative.to_add m) 1) (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect)))
      * units.val ((μ.unit S)^(-(multiplicative.to_add m) μ.src_vect)),
  map_one' :=
  begin
    dsimp,
    rw [neg_zero, gpow_zero],
    unfold units.val,
    rw [mul_one, <- add_monoid_algebra.one_def, is_localization.mk'_one, ring_hom.map_one],
  end,
  map_mul' := 
  begin
    intros x y,
    dsimp,
    rw [<- to_add_mul, gpow_neg, gpow_neg, gpow_neg, to_add_mul],
    rw [gpow_add, <- one_mul (1 : ℤ), <- add_monoid_algebra.single_mul_single],
    rw <- one_mul (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))),
    rw is_localization.mk'_mul,
    simp only [mul_inv_rev, mul_one],
    unfold units.val,
    ring_exp,
  end}

def mutation_to_localization_aux : ring_of_function N →+* S :=
add_monoid_algebra.lift_nc_ring_hom (int.cast_ring_hom S)
(mutation_monomial_aux μ S ε) (λ _ _, (commute.all _ _))

@[simp]
lemma mutation_of_function_of_mutation_direction_aux
(v : N) [is_mutation_direction μ v] :
(mutation_to_localization_aux μ S ε) (function_of_vector v) = 
  is_localization.mk' S (function_of_vector v) 
      (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) :=
begin
  unfold mutation_to_localization_aux,
  unfold function_of_vector,
  unfold mutation_monomial_aux,
  unfold add_monoid_algebra.lift_nc_ring_hom,
  cases μ.is_direction v with k hk,
simp only [mul_one,
 ring_hom.eq_int_cast,
 one_mul,
 ring_hom.coe_mk,
 ring_hom.map_add,
 to_add_of_add,
 int.cast_one,
 ring_hom.coe_add_monoid_hom,
 monoid_hom.coe_mk,
 add_monoid_algebra.lift_nc_single,
 of_add_zero,
 monoid_hom.map_one],
 rw μ.form_mutation_direction_eq_zero,
 simp only [algebra.id.smul_eq_mul, gpow_zero, mul_zero, neg_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end

def mutation_to_localization : ring_of_function N →+* S :=
add_monoid_algebra.lift_nc_ring_hom (int.cast_ring_hom S)
(mutation_monomial μ S) (λ _ _, (commute.all _ _))

@[simp]
lemma mutation_of_function_of_mutation_direction
(v : N) [is_mutation_direction μ v] :
(mutation_to_localization μ S) (function_of_vector v) = 
  is_localization.mk' S (function_of_vector v) 
      (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) :=
begin
  unfold mutation_to_localization,
  unfold function_of_vector,
  unfold mutation_monomial,
  unfold add_monoid_algebra.lift_nc_ring_hom,
  cases μ.is_direction v with k hk,
  simp only [mul_one,
  ring_hom.eq_int_cast,
  one_mul,
  ring_hom.coe_mk,
  ring_hom.map_add,
  to_add_of_add,
  int.cast_one,
  ring_hom.coe_add_monoid_hom,
  monoid_hom.coe_mk,
  add_monoid_algebra.lift_nc_single,
  of_add_zero,
  monoid_hom.map_one],
 rw μ.form_mutation_direction_eq_zero,
  rw [neg_zero, gpow_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end


/-
lemma mutation_of_function_of_src_vect :
(mutation_to_localization μ S) (function_of_vector μ.src_vect) = 
  is_localization.mk' S (function_of_vector μ.src_vect) 
      (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
begin
  unfold mutation_to_localization,
  unfold function_of_vector,
  unfold mutation_monomial,
  unfold add_monoid_algebra.lift_nc_ring_hom,
  simp only [mul_one,
    ring_hom.eq_int_cast,
    one_mul,
    ring_hom.coe_mk,
    ring_hom.map_add,
    to_add_of_add,
    int.cast_one,
    ring_hom.coe_add_monoid_hom,
    monoid_hom.coe_mk,
    add_monoid_algebra.lift_nc_single,
    of_add_zero,
    monoid_hom.map_one, linear_map.to_fun_eq_coe],
  rw bilin_form.to_lin_apply,
  rw [self_eq_zero skew, neg_zero, gpow_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end

lemma mutation_of_function_of_tar_vect :
(mutation_to_localization μ S) (function_of_vector μ.tar_vect) = 
  is_localization.mk' S (function_of_vector μ.tar_vect) 
    (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
begin
  unfold mutation_to_localization,
  unfold function_of_vector,
  unfold mutation_monomial,
  unfold add_monoid_algebra.lift_nc_ring_hom,
  simp only [mul_one,
    ring_hom.eq_int_cast,
    one_mul,
    ring_hom.coe_mk,
    ring_hom.map_add,
    to_add_of_add,
    int.cast_one,
    ring_hom.coe_add_monoid_hom,
    monoid_hom.coe_mk,
    add_monoid_algebra.lift_nc_single,
    of_add_zero,
    monoid_hom.map_one, linear_map.to_fun_eq_coe],
  rw [seed_mutation.form_tar_src_eq_zero, neg_zero, gpow_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end

lemma mutation_of_function_of_sign_tar_vect :
(mutation_to_localization μ S) (function_of_vector (μ.sign • μ.tar_vect)) = 
  is_localization.mk' S (function_of_vector (μ.sign • μ.tar_vect)) 
    (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
begin
  cases μ.is_sign,
  rw h,
  rw one_smul,
  rw mutation_of_function_of_tar_vect μ S,
  rw h,
  rw μ.tar_vect_eq_neg_src_vect,
  simp,
  apply mutation_of_function_of_src_vect,
end

lemma mutation_of_function_of_sign_src_vect :
(mutation_to_localization μ S) (function_of_vector (μ.sign • μ.src_vect)) =
  is_localization.mk' S (function_of_vector (μ.sign • μ.src_vect)) 
    (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
begin
  cases μ.is_sign,
  rw h,
  rw one_smul,
  rw mutation_of_function_of_src_vect μ S,
  rw h,
  nth_rewrite 0 src_vect_eq_neg_tar_vect,
  simp,
  apply mutation_of_function_of_src_vect,
end



lemma seed_mutation.is_unit_of_vector
{s s' : multiset N}
(μ : seed_mutation s s')
(v : N) [is_mutation_direction μ v] :
is_unit (is_localization.mk' S (function_of_vector (μ.sign • μ.src_vect)) 
  (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect)))) :=
begin
  use function_of_vector.unit v S,
  rw is_localization.mk'_one,
  refl,
end

lemma mutation_is_unit
(v : N) [is_mutation_direction μ v] :
is_unit (mutation_to_localization μ S (function_of_vector v)) :=
begin
  rw mutation_of_function_of_mutation_direction,
  apply is_unit_of_vector μ.src_vect S,
end

-/

/- lemma is_unit_of_sign_tar_vect  : 
is_unit (is_localization.mk' S (function_of_vector (μ.sign • μ.tar_vect))
  (1 : submonoid.powers (function_of_vector (μ.sign • μ.tar_vect)))) :=
  sorry -/

lemma is_unit_mutation : is_unit ((mutation_to_localization μ S) (function_of_vector (μ.sign • μ.src_vect))) :=
begin
  rw mutation_of_function_of_mutation_direction ,
  rw is_localization.mk'_one,
  refine @is_localization.map_units (ring_of_function N) _ _ S _ _ _ 
    ⟨function_of_vector (μ.sign • μ.src_vect), submonoid.mem_powers _⟩
end

lemma is_unit_mutation_aux : is_unit ((mutation_to_localization_aux μ S ε) (function_of_vector (μ.sign • μ.src_vect))) :=
begin
  rw mutation_of_function_of_mutation_direction_aux ,
  rw is_localization.mk'_one,
  refine @is_localization.map_units (ring_of_function N) _ _ S _ _ _ 
    ⟨function_of_vector (μ.sign • μ.src_vect), submonoid.mem_powers _⟩
end

def mutation_between_localization_aux : S →+* S :=
is_localization.away.lift (function_of_vector (μ.sign • μ.src_vect)) (is_unit_mutation_aux μ S ε)

def mutation_between_localization : S →+* S :=
is_localization.away.lift (function_of_vector (μ.sign • μ.src_vect)) (is_unit_mutation μ S)

@[simp] lemma mutation_alg_const' : ((mutation_between_localization_aux μ S ε).comp (algebra_map (ring_of_function N) S)).comp add_monoid_algebra.single_zero_ring_hom =
(algebra_map (ring_of_function N) S ).comp add_monoid_algebra.single_zero_ring_hom := dec_trivial

@[simp] lemma mutation_alg_const (b : ℤ) : mutation_between_localization_aux μ S ε ((algebra_map (ring_of_function N) S) (finsupp.single 0 b)) =
algebra_map (ring_of_function N) S (finsupp.single 0 b) :=
begin
  have h : finsupp.single (0 : module.dual ℤ N) b = add_monoid_algebra.single_zero_ring_hom b := by refl,
  rw h,
  repeat {rw <- ring_hom.comp_apply},
  repeat {rw <- ring_hom.coe_comp},
  rw mutation_alg_const',
end

@[simp] lemma mutation_alg_monomial (a : multiplicative(module.dual ℤ N)) : 
(mutation_between_localization_aux μ S ε) ((algebra_map (ring_of_function N) S) (finsupp.single a 1)) =
algebra_map (ring_of_function N) S (finsupp.single a 1) 
  * (((μ.unit S) ^ (ε • (- a μ.src_vect))).val) :=
begin
  unfold mutation_between_localization_aux is_localization.away.lift,
  rw is_localization.lift_eq,
  unfold mutation_to_localization_aux add_monoid_algebra.lift_nc_ring_hom,
  dsimp,
  rw add_monoid_algebra.lift_nc_single,
  unfold mutation_monomial_aux,
  dsimp,
  rw [int.cast_one, one_mul, <- units.val_coe],
  simp only [gpow_neg, units.ne_zero, or_false, mul_neg_eq_neg_mul_symm, mul_eq_mul_right_iff],
  rw is_localization.mk'_one,
  congr,
end

@[simp]
lemma mutation_between_of_function_of_mutation_direction (k : ℤ) : 
mutation_between_localization_aux μ S ε  (units.val ((μ.unit S) ^ k )) = 
(units.val ((μ.unit S) ^ k)) := 
begin
  unfold mutation_between_localization_aux,
  unfold is_localization.away.lift,
  unfold seed_mutation.unit,
  induction k,
  { dsimp,
    rw [gpow_coe_nat, <- units.val_coe,  units.coe_pow, ring_hom.map_pow], 
    dsimp,
    rw [is_localization.lift_eq],
    apply congr_arg (λ x : S, x ^ k),
    rw mutation_of_function_of_mutation_direction_aux,
    rw is_localization.mk'_one },
  { rw [gpow_neg_succ_of_nat, <- units.val_coe, <- inv_pow,units.coe_pow, units.coe_inv],
    simp only [units.coe_mk], 
    rw [ring_hom.map_pow],
    apply congr_arg (λ x : S, x ^ k.succ),
    rw is_localization.lift_mk'_spec,
    simp only [set_like.coe_mk, cluster.mutation_of_function_of_mutation_direction_aux, ring_hom.map_one],
    erw <- is_localization.mk'_mul,
    rw [one_mul, mul_one, is_localization.mk'_self] },
end


/-
instance is_localization.symm_tar_S : is_localization.away (function_of_vector μ.symm.tar_vect) S :=
begin
  have : μ.symm.tar_vect = μ.src_vect := by refl,
  rw this,
  assumption,
end

instance is_localization.symm_tar_S' : is_localization.away (function_of_vector μ.symm.src_vect) S' :=
begin
  have : μ.symm.src_vect = μ.tar_vect := by refl,
  rw this,
  assumption,
end


lemma mutation_function_of_vector (k : ℤ) : 
mutation_between_localization μ S S' 
  (units.val ((function_of_vector.unit (μ.symm.sign • μ.symm.src_vect) S') ^ k )) = 
(units.val ((function_of_vector.unit (μ.sign • μ.src_vect) S) ^ k)) := 
begin
  unfold mutation_between_localization,
  unfold is_localization.away.lift,
  unfold function_of_vector.unit,
  induction k,
  { dsimp,
    rw [gpow_coe_nat, <- units.val_coe, <- units.val_coe, units.coe_pow, ring_hom.map_pow,  gpow_coe_nat], 
    dsimp,
    rw [is_localization.lift_eq, units.coe_pow],
    dsimp,
    apply congr_arg (λ x : S, x ^ k),
    have : μ.symm.sign = - μ.sign := by refl,
    rw this,
      have : μ.symm.src_vect =  μ.tar_vect := by refl,
    rw this,
    rw seed_mutation.tar_vect_eq_neg_src_vect,
    simp only [smul_neg, neg_neg, neg_smul],
    erw is_localization.lift_mk'_spec,
    rw [mutation_of_function_of_vector, localization.mk_eq_mk', submonoid.coe_one, ring_hom.map_one, one_mul] },
  { rw [gpow_neg_succ_of_nat, <- units.val_coe, <- inv_pow,units.coe_pow, units.coe_inv],
    simp only [units.coe_mk], 
    rw [ring_hom.map_pow],
    apply congr_arg (λ x : localization_at_vector (ε • v), x ^ k.succ),
    rw [localization.away.inv_self, localization.mk_eq_mk'],
    erw is_localization.lift_mk'_spec,
    rw [ring_hom.map_one,set_like.coe_mk, mutation_of_function_of_vector, localization.mk_eq_mk'],
    erw <- is_localization.mk'_mul,
    rw [one_mul, mul_one, is_localization.mk'_self] },
end




lemma id_as_lift (R : Type*) (S : Type*) [comm_ring R] [comm_ring S] [algebra R S] : ring_hom.id (localization_at_vector (ε • v)) = is_localization.lift 
  (@map_units _ _ (submonoid.powers (function_of_vector (ε • v))) (localization_at_vector (ε • v)) _ _ _) := 
begin
  ext z,
  rw ring_hom.id_apply,
  rw lift_id,
end
-/

def seed_mutation.isom_away : S ≃+* S :=
ring_equiv.of_hom_inv (mutation_between_localization_aux μ S ε)
(mutation_between_localization_aux μ S (-ε))
begin
  ext x,
  have : ring_hom.id S = is_localization.lift 
  (@is_localization.map_units _ _ (submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) S _ _ _),
  { ext z,
    rw ring_hom.id_apply,
    rw is_localization.lift_id },
  rw this,
  rw is_localization.lift_unique,
  rw <- function.funext_iff,
  rw [<- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) S],
  apply add_monoid_algebra.ring_hom_ext,
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_alg_const, mutation_alg_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_alg_monomial, ring_hom.map_mul, mutation_alg_monomial, mul_assoc],
    simp only [gpow_neg],
    rw mutation_between_of_function_of_mutation_direction,
    simp only [algebra.id.smul_eq_mul, gpow_neg, mul_neg_eq_neg_mul_symm],
    simp only [neg_mul_eq_neg_mul_symm, gpow_neg, inv_inv],
    erw units.val_inv,
    apply mul_one },
end
begin
  ext x,
  have : ring_hom.id S = is_localization.lift 
  (@is_localization.map_units _ _ (submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) S _ _ _),
  { ext z,
    rw ring_hom.id_apply,
    rw is_localization.lift_id },
  rw this,
  rw is_localization.lift_unique,
  rw <- function.funext_iff,
  rw [<- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) S],
  apply add_monoid_algebra.ring_hom_ext,
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_alg_const, mutation_alg_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_alg_monomial, ring_hom.map_mul, mutation_alg_monomial, mul_assoc],
    simp only [gpow_neg],
    rw mutation_between_of_function_of_mutation_direction,
    simp only [algebra.id.smul_eq_mul, gpow_neg, mul_neg_eq_neg_mul_symm],
    simp only [neg_mul_eq_neg_mul_symm, gpow_neg, inv_inv],
    erw units.val_inv,
    apply mul_one },
end


section
variables 
[is_integral_domain (ring_of_function N)]
(K : Type*) [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K] 

open localization

def algebra_away_frac : algebra S K :=
(algebra_of_lift_le S K (powers_le_non_zero_divisors_of_domain (function_of_vector_ne_zero (μ.sign • μ.src_vect))))

local attribute[instance] algebra_away_frac

/- def away_frac_localization : 
is_localization ((non_zero_divisors (ring_of_function N)).map (algebra_map (ring_of_function N) S) : submonoid S) K :=
away_is_fraction S K (function_of_vector (μ.sign • μ.src_vect)) (function_of_vector_ne_zero (μ.sign • μ.src_vect))

local attribute[instance] away_frac_localization

lemma mutation_map_non_zero_non_zero : submonoid.map (seed_mutation.isom_away μ S ε).to_monoid_hom 
  ((non_zero_divisors (ring_of_function N)).map (algebra_map (ring_of_function N) S)) = 
  ((non_zero_divisors (ring_of_function N)).map (algebra_map (ring_of_function N) S)) :=
begin
  sorry,
end

lemma seed_mutation.non_zero_le_comap_non_zero : 
let N' := (((non_zero_divisors (ring_of_function N)).map (algebra_map (ring_of_function N) S)) : submonoid S) in
N' ≤ N'.comap (μ.isom_away S ε) :=
begin
  dsimp,
  intros f hf,
  rcases hf with ⟨g, hg, H⟩,
  dsimp at *,
  rw submonoid.mem_comap,
  have : μ.isom_away S ε f ≠ 0,
  sorry,
end -/


def seed_mutation.algebra_of_away_frac : algebra S K := 
algebra_of_away_frac S K _ (function_of_vector_ne_zero (μ.sign • μ.src_vect))


def seed_mutation.is_fraction_of_algebra_of_away_frac : @is_fraction_ring S _ K _ (μ.algebra_of_away_frac S K) :=
is_fraction_of_algebra_of_away_frac S K _ _



local attribute[instance] seed_mutation.algebra_of_away_frac seed_mutation.is_fraction_of_algebra_of_away_frac

def seed_mutation.field_equiv : K ≃+* K := 
is_fraction_ring.field_equiv_of_ring_equiv (μ.isom_away S ε)

end


end mutation

end cluster
