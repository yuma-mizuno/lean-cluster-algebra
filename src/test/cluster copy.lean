import linear_algebra.dual
import algebra.monoid_algebra
import ring_theory.localization
import ring_theory.nilpotent
import linear_algebra.bilinear_form
import tactic.basic
import tactic.equiv_rw

universes u

noncomputable theory
open_locale classical

namespace skew_sym_bilin_form

open skew_sym_bilin_form bilin_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_monoid M] [module R M] {B : bilin_form R M}

def is_skew_sym (B : bilin_form R M) : Prop := 
∀ (x y : M), B x y = - B y x

variable (H : is_skew_sym B)
include H

lemma skew_sym (x y : M) : B x y = - B y x := H x y

lemma is_refl : refl_bilin_form.is_refl B := 
λ x y H1, 
begin
  rw H y x,
  exact neg_eq_zero.mpr H1,
end


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
lemma self_eq_zero [no_zero_divisors R] [char_zero R] (x : M) : B x x = 0 :=  is_alt H x

end skew_sym_bilin_form

namespace cluster

class skew_symmetric_form (N : Type*) [add_comm_group N] :=
(form : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)
(skew : ∀ n n' : N, form n n' = - form n' n)

namespace skew_symmetric_form

variables {N : Type*} [add_comm_group N] [skew_symmetric_form N]

@[simp]lemma square_zero  : ∀ n : N, form n n = 0 :=
begin
  intros n,
  have h : form n n = - form n n,
    exact skew n n,
  rw eq_neg_iff_add_eq_zero at h,
  simp only [add_self_eq_zero] at h,
  exact h,
end

end skew_symmetric_form

section seed_mutation

open cluster.skew_symmetric_form 

variables {N : Type*} [add_comm_group N] [no_zero_smul_divisors ℤ N]
{B : bilin_form ℤ N}
[skew_symmetric_form N] (s s' : multiset N) (v : N) (ε : ℤ)


def pl_mutation : N → N :=
λ n, n + (max 0 (ε * (form n v))) • v

def pl_mutation.equiv : N ≃ N :=
{ to_fun := pl_mutation v ε,
  inv_fun := pl_mutation (-v) (-ε),
  left_inv := 
  begin
    intros n,
    unfold pl_mutation,
    simp only [neg_mul_eq_neg_mul_symm, linear_map.map_neg, linear_map.add_apply, linear_map.map_add],
    rw [gsmul_neg, add_assoc, <- sub_eq_add_neg, <- sub_gsmul],
    simp only [add_right_eq_self, algebra.id.smul_eq_mul, linear_map.map_smul_of_tower, linear_map.smul_apply],
    rw <- sub_eq_add_neg,
    simp only [square_zero,zero_gsmul, eq_self_iff_true, sub_zero, mul_neg_eq_neg_mul_symm, neg_neg, mul_zero, sub_self],
  end,
  right_inv := 
  begin
    intros n,
    unfold pl_mutation,
    simp only [neg_mul_eq_neg_mul_symm,linear_map.map_neg,algebra.id.smul_eq_mul,
      linear_map.map_smul_of_tower,linear_map.smul_apply,
      mul_neg_eq_neg_mul_symm,linear_map.neg_apply,
      smul_neg,neg_neg,linear_map.add_apply,linear_map.map_add,square_zero,add_zero, mul_zero, neg_zero],
    rw [add_assoc, add_comm],
    simp only [eq_self_iff_true, add_left_neg, zero_add],
  end }

lemma pl_mutation.bijective :
function.bijective (pl_mutation v ε) :=
(pl_mutation.equiv v ε).bijective

structure seed_mutation (s s' : multiset N) :=
(sign : ℤ)
(is_sign : sign = 1 ∨ sign = -1)
(src_vect : N)
(tar_vect : N)
(src_in : src_vect ∈ s)
(tar_in : tar_vect ∈ s')
(seed_tar_src : s'.erase tar_vect = multiset.map (pl_mutation src_vect sign)  (s.erase src_vect))
(vect_tar_src : tar_vect = - src_vect)

namespace seed_mutation

lemma tar_vect_eq_neg_src_vect {s s' : multiset N} (μ : seed_mutation s s') : μ.tar_vect = - μ.src_vect :=
μ.vect_tar_src

lemma src_vect_eq_neg_tar_vect {s s' : multiset N} (μ : seed_mutation s s') :  μ.src_vect = - μ.tar_vect :=
by calc
  μ.src_vect = - - μ.src_vect : by rw neg_neg
          ... = - μ.tar_vect : by rw μ.vect_tar_src



@[simp] lemma form_tar_src_eq_zero {s s' : multiset N} (μ : seed_mutation s s') : 
form (μ.tar_vect) μ.src_vect = 0 :=
begin
  rw μ.vect_tar_src,
  simp only [linear_map.map_neg,
    cluster.skew_symmetric_form.square_zero,
    linear_map.neg_apply,
    neg_zero],
end

@[simp] lemma form_src_tar_eq_zero {s s' : multiset N} (μ : seed_mutation s s') : 
form (μ.src_vect) μ.tar_vect = 0 :=
begin
  rw μ.vect_tar_src,
  simp only [linear_map.map_neg,
    cluster.skew_symmetric_form.square_zero,
    linear_map.neg_apply,
    neg_zero],
end

end seed_mutation

lemma pl_mutation_eq (v : N) {w : N} (ε : ℤ) (c : ℤ) (h : w = c • v) : pl_mutation v ε w = w :=
begin
  unfold pl_mutation,
  rw h,
  simp only [add_zero,
    algebra.id.smul_eq_mul,
    max_eq_right,
    linear_map.smul_apply,
    cluster.skew_symmetric_form.square_zero,
    zero_smul,
    mul_zero,
    linear_map.map_smul],
end

@[simp] lemma pl_mutation_eq' : pl_mutation v ε v = v :=
begin
  have p : v = (1 : ℤ) • v := by simp,
  exact pl_mutation_eq v ε 1 p,
end

def seed_mutation.symm {s s' : multiset N} (μ : seed_mutation s s') : seed_mutation s' s :=
{ sign := - μ.sign,
  is_sign := 
  begin
    cases μ.is_sign with h,
    exact or.inr (congr_arg has_neg.neg h),
    exact or.inl ((congr_arg has_neg.neg h).trans rfl),
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
    congr,
    have : pl_mutation (-μ.src_vect) (-μ.sign) ∘ pl_mutation μ.src_vect μ.sign = id,
      ext x,
      apply (pl_mutation.equiv μ.src_vect μ.sign).left_inv x,
    rw this,
    apply eq.symm,
    apply multiset.map_id',
    repeat {simp},
    apply μ.src_vect_eq_neg_tar_vect,
    exact function.bijective.injective (pl_mutation.bijective μ.tar_vect (-μ.sign)),
    exact function.bijective.injective (pl_mutation.bijective μ.src_vect μ.sign),
  end,
  vect_tar_src := μ.src_vect_eq_neg_tar_vect, }

end seed_mutation




open cluster.skew_symmetric_form


variables {N : Type*} [add_comm_group N] [no_zero_smul_divisors ℤ N]
[skew_symmetric_form N]

/-
structure ambient_ring :=
(carrier : Type u)
(integral_domain : integral_domain carrier)
(ambient_lattice : Type u)
(add_comm_group : add_comm_group ambient_lattice)
(no_zero_smul_divisors : no_zero_smul_divisors ℤ ambient_lattice)
(skew_symmetric_form : skew_symmetric_form ambient_lattice)
(to_monoid_alg : carrier ≃+* add_monoid_algebra ℤ (module.dual ℤ ambient_lattice))

def is_ring_of_function {R} [comm_ring R] (s : multiset N)  : Prop :=
∃ h : add_monoid_algebra ℤ (module.dual ℤ N) ≃+* R, true


@[simp] lemma function_of_vector.neg_neg : function_of_vector (-ε • -v) = 
  function_of_vector (ε • v) :=
begin
  simp,
end
-/


section

abbreviation ring_of_function (N : Type*) [add_comm_group N]  :=
add_monoid_algebra ℤ (module.dual ℤ N)

instance : comm_ring (ring_of_function N) :=
add_monoid_algebra.comm_ring

instance : comm_ring (module.dual ℤ N →₀ ℤ) := add_monoid_algebra.comm_ring

def function_of_vector (v : N) : ring_of_function N :=
finsupp.single 0 1 + finsupp.single  (form v) 1

lemma function_of_vector_neq_zero  (v : N) : function_of_vector v ≠ 0 :=
begin
  unfold function_of_vector,
  let h := eq_or_ne (form v) 0,
  simp at h,
  cases h,
  rw [h, finsupp.nonzero_iff_exists],
  use 0,
  simp,
  rw finsupp.nonzero_iff_exists,
  use 0,
  simp only [finsupp.single_eq_same, pi.add_apply, finsupp.coe_add],
  have : ( 0 : module.dual ℤ N) ∉ (finsupp.single (form v) 1 : ring_of_function N).support,
  { rw [finsupp.support_single_ne_zero, finset.mem_singleton],
    tidy },
  rw finsupp.not_mem_support_iff at this,
  rw this,
  simp,
end


def function_of_vector.is_palindromic (v : N) : 
(finsupp.single (form v) 1 : ring_of_function N) * (function_of_vector (-v)) = function_of_vector v :=
begin
  unfold function_of_vector,
  rw mul_add,
  repeat {rw add_monoid_algebra.single_mul_single},
  simp only [add_zero, mul_one, linear_map.map_neg, add_right_neg],
  apply add_comm,
end

def function_of_vector.is_palindromic' (v : N) : 
(finsupp.single (form (- v)) 1 : ring_of_function N) * (function_of_vector v) = function_of_vector (-v) :=
begin
  let h := function_of_vector.is_palindromic (-v),
  rw neg_neg at h,
  assumption,
end

def pow_neg_vect_in_pow_vect {v : N} {f : ring_of_function N} (h : f ∈ submonoid.powers (function_of_vector (-v))) : 
∃ k : ℕ, ((finsupp.single (form (k • v)) 1) : ring_of_function N) * f ∈ submonoid.powers (function_of_vector v) :=
begin
  cases h with k h,
  use k,
  rw <- h,
  unfold function_of_vector,
  simp only [linear_map.map_neg, linear_map.map_smul_of_tower],
  rw [<- one_pow k, <- add_monoid_algebra.single_pow, one_pow k, <- mul_pow, mul_add],
  repeat {rw add_monoid_algebra.single_mul_single},
  simp only [add_zero, mul_one, add_right_neg],
  rw add_comm,
  exact ⟨k, rfl⟩,
end

def pow_vect_in_pow_neg_vect {v : N} {f : ring_of_function N} (h : f ∈ submonoid.powers (function_of_vector v)) : 
∃ k : ℕ, ((finsupp.single (form (k • (-v))) 1) : ring_of_function N) * f ∈ submonoid.powers (function_of_vector (-v)) :=
begin
  cases h with k h,
  use k,
  rw <- h,
  unfold function_of_vector,
  simp only [linear_map.map_neg, linear_map.map_smul_of_tower],
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

lemma is_localization_at_congr (h : v = w) :
(is_localization_at_vect v S) ↔ (is_localization_at_vect w S) :=
begin
  tactic.unfreeze_local_instances,
  subst h,
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

lemma is_unit_of_vector : 
is_unit (is_localization.mk' S (function_of_vector v) (1 : submonoid.powers (function_of_vector v))) :=
begin
  use function_of_vector.unit v S,
  rw is_localization.mk'_one,
  refl,
end


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

lemma is_unit_of_neg_vector (h : w = -v) : 
is_unit (is_localization.mk' S (function_of_vector w) (1 : submonoid.powers (function_of_vector v))) :=
begin
  rw <- units.is_unit_mul_units _ (monomial.unit S (form v)),
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

end

section mutation

variables {s s' : multiset N} (μ : seed_mutation s s')   (S S' : Type*) [integral_domain S] [integral_domain S']
[algebra (ring_of_function N) S] [algebra (ring_of_function N) S']
[is_localization.away (function_of_vector μ.src_vect) S]
[is_localization.away (function_of_vector μ.tar_vect) S']
instance algebra_S : algebra (module.dual ℤ N →₀ ℤ) S:= by assumption
instance algebra_S' : algebra (module.dual ℤ N →₀ ℤ) S':= by assumption


/-
instance : is_localization.away (function_of_vector μ.src_vect) S :=
{ map_units := λ y, ,
  surj := _,
  eq_iff_exists := _ }
-/

lemma is_localizaiton_neg_vect (v w : N) (h : w = -v) (S : Type*) [integral_domain S] [algebra (ring_of_function N) S] :
is_localization.away (function_of_vector v) S → is_localization.away (function_of_vector w) S :=
begin
  intros H,
  subst h,
  resetI,
  split,
  { intros y,
    cases y with y yp,
    cases pow_neg_vect_in_pow_vect yp with k h_in,
    cases (is_localization.map_units S ⟨(finsupp.single (form (k • v)) 1 : ring_of_function N) * y, h_in⟩) with x hx,
    use monomial.unit S (k • (- form v)) * x,
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
    use ⟨a * (finsupp.single (form (k • -v)) 1), ⟨(finsupp.single (form (k • -v)) 1 : ring_of_function N) * y, h_in⟩⟩,
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
end

instance is_localization.tar_S : is_localization.away (function_of_vector (μ.tar_vect)) S :=
begin
  apply is_localizaiton_neg_vect μ.src_vect μ.tar_vect μ.tar_vect_eq_neg_src_vect,
  assumption,
end

/-
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

#check is_localization.away (function_of_vector μ.tar_vect) S

open skew_symmetric_form



#print instances comm_ring
set_option pp.implicit false



/-
instance : comm_ring (@module.dual ℤ N int.comm_semiring (@add_comm_group.to_add_comm_monoid N _inst_1)
         (@add_comm_group.int_module N _inst_1) →₀ ℤ) :=
begin
  apply add_monoid_algebra.comm_ring,
end


instance : comm_ring (module.dual ℤ N  →₀ ℤ) :=
begin
  apply add_monoid_algebra.comm_ring,
end

instance :  algebra (module.dual ℤ N →₀ ℤ) S':=
begin
  assumption,
end

-/

#check λ m : module.dual ℤ N, (is_localization.mk' S' ((finsupp.single (multiplicative.to_add m) 1) : ring_of_function N) 1)

def mutation_monomial : multiplicative (module.dual ℤ N) →* S :=
{ to_fun := λ m, 
  (is_localization.mk' S
    (finsupp.single (multiplicative.to_add m) 1) (1 : submonoid.powers (function_of_vector μ.src_vect)))
  * (units.val ((function_of_vector.unit μ.src_vect S)^(-(multiplicative.to_add m) μ.src_vect))),
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
    rw <- one_mul (1 : submonoid.powers (function_of_vector μ.src_vect)),
    rw is_localization.mk'_mul,
    simp only [mul_inv_rev, mul_one],
    unfold units.val,
    ring_exp,
  end}

def mutation_to_localization : ring_of_function N →+* S :=
add_monoid_algebra.lift_nc_ring_hom (int.cast_ring_hom S)
(mutation_monomial μ S) (λ _ _, (commute.all _ _))

lemma mutation_of_function_of_src_vect :
  (mutation_to_localization μ S) (function_of_vector μ.src_vect) = 
    is_localization.mk' S (function_of_vector μ.src_vect) (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
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
    monoid_hom.map_one],
 rw [cluster.skew_symmetric_form.square_zero, neg_zero, gpow_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end

lemma mutation_of_function_of_tar_vect :
  (mutation_to_localization μ S) (function_of_vector μ.tar_vect) = 
    is_localization.mk' S (function_of_vector μ.tar_vect) (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
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
    monoid_hom.map_one],
  rw [seed_mutation.form_tar_src_eq_zero, neg_zero, gpow_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end

lemma mutation_of_function_of_sign_tar_vect :
  (mutation_to_localization μ S) (function_of_vector (μ.sign • μ.tar_vect)) = 
    is_localization.mk' S (function_of_vector (μ.sign • μ.tar_vect)) (1 : submonoid.powers (function_of_vector μ.src_vect)) :=
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

lemma mutation_is_unit' : is_unit ((mutation_to_localization μ S) (function_of_vector (μ.sign • μ.tar_vect))) :=
begin
  cases μ.is_sign with h,
  rw h,
  rw one_smul,
  rw μ.src_vect_eq_neg_tar_vect at *,
  rw mutation_of_function_of_tar_vect,
  apply is_unit_of_neg_vector μ.src_vect μ.tar_vect S μ.tar_vect_eq_neg_src_vect,
  rw h,
  rw μ.tar_vect_eq_neg_src_vect at *,
  simp,
  rw mutation_of_function_of_src_vect,
  apply is_unit_of_vector μ.src_vect S,
end


lemma mutation_is_unit : is_unit ((mutation_to_localization μ S) (function_of_vector μ.tar_vect)) :=
begin
  rw μ.src_vect_eq_neg_tar_vect at *,
  rw mutation_of_function_of_tar_vect,
  apply is_unit_of_neg_vector μ.src_vect μ.tar_vect S μ.tar_vect_eq_neg_src_vect,
end

def mutation_between_localization : S' →+* S :=
is_localization.away.lift (function_of_vector (μ.tar_vect)) (mutation_is_unit _ _)

@[simp] lemma mutation_alg_const' : ((mutation_between_localization μ S S').comp (algebra_map (ring_of_function N) S')).comp add_monoid_algebra.single_zero_ring_hom =
(algebra_map (ring_of_function N) S ).comp add_monoid_algebra.single_zero_ring_hom := dec_trivial

@[simp] lemma mutation_alg_const (b : ℤ) : mutation_between_localization μ S S' ((algebra_map (ring_of_function N) S') (finsupp.single 0 b)) =
algebra_map (ring_of_function N) S (finsupp.single 0 b) :=
begin
  have h : finsupp.single (0 : module.dual ℤ N) b = add_monoid_algebra.single_zero_ring_hom b := by refl,
  rw h,
  repeat {rw <- ring_hom.comp_apply},
  repeat {rw <- ring_hom.coe_comp},
  rw mutation_alg_const',
end

@[simp] lemma mutation_alg_monomial (a : multiplicative(module.dual ℤ N)) : (mutation_between_localization μ S S') ((algebra_map (ring_of_function N) S') (finsupp.single a 1)) =
algebra_map (ring_of_function N) S ((finsupp.single a 1) * ((function_of_vector.unit (μ.sign • μ.src_vect) S) ^ (- a μ.src_vect)).val) :=
begin
  unfold mutation_between_localization is_localization.away.lift,
  rw is_localization.lift_eq,
  unfold mutation_to_localization add_monoid_algebra.lift_nc_ring_hom,
  dsimp,
  rw add_monoid_algebra.lift_nc_single,
  unfold mutation_monomial,
  dsimp,
  rw [int.cast_one,one_mul,gpow_neg,localization.mk_eq_mk'],
  apply congr_arg (* (function_of_vector.unit (ε • v) ^ a v).inv),
  have h : algebra_map (ring_of_function N) (localization_at_vector (ε • v)) 1 = 1 := by refl,
  rw <- mul_one (@is_localization.mk' (ring_of_function N) _ _ (localization (submonoid.powers (function_of_vector (ε • v)))) _ _ _ (finsupp.single a 1) 1),
  rw <- h,
  apply is_localization.mk'_spec,
end

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


lemma id_as_lift (R : Type*) (S : Type*) [comm_ring R] [comm_ring S] [algebra R S] : ring_hom.id (localization_at_vector (ε • v)) = is_localization.lift 
  (@map_units _ _ (submonoid.powers (function_of_vector (ε • v))) (localization_at_vector (ε • v)) _ _ _) := 
begin
  ext z,
  rw ring_hom.id_apply,
  rw lift_id,
end

def mutation_isom_localization : S' ≃+* S :=
ring_equiv.of_hom_inv (mutation_between_localization μ S S')
(mutation_between_localization μ.symm S' S)
begin
  ext,
  have : ring_hom.id S' = is_localization.lift 
  (@is_localization.map_units _ _ (submonoid.powers (function_of_vector μ.tar_vect)) S' _ _ _),
  { ext z,
    rw ring_hom.id_apply,
    rw is_localization.lift_id },
  rw this,
  rw is_localization.lift_unique,
  rw <- function.funext_iff,
rw [<- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) S'],
    apply add_monoid_algebra.ring_hom_ext,
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    sorry,},
--    rw [mutation_alg_const, cast_alg_map, mutation_alg_const, cast_alg_map] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    sorry
    /-
    dsimp,
    rw [mutation_alg_monomial, ring_hom.map_mul, cast_alg_map, ring_hom.map_mul, mutation_alg_monomial,
      ring_hom.map_mul,ring_hom.map_mul, cast_alg_map, mul_assoc],
    rw cast_apply_function_at_vector (ε • v) (-ε • -v),
    rw cast_apply_function_at_vector (-ε • -v) (ε • v),
    rw mutation_between_localization.function_at_vector,
    rw cast_apply_function_at_vector (-ε • -v) (ε • v),
    simp only [linear_map.map_neg, gpow_neg, neg_neg],
    erw units.val_inv,
    apply mul_one -/},
end
begin
  sorry
end

set_option pp.implicit false



def mutation_isom_field  (μ : seed_mutation s s') 
[is_localization.away (function_of_vector μ.src_vect) S]
[is_localization.away (function_of_vector μ.tar_vect) S'] 
{K K' : Type*}
[field K] [algebra S K] [is_fraction_ring S K]
[field K'] [algebra S' K'] [is_fraction_ring S' K'] : 
K' ≃+* K := is_fraction_ring.field_equiv_of_ring_equiv  (mutation_isom_localization μ S S')

set_option pp.implicit false

example (v : N) [integral_domain (ring_of_function N)] : 
(submonoid.powers (function_of_vector v)) ≤ (non_zero_divisors (ring_of_function N)) :=
begin
  intros x h,
  intros f hf,
  cases h with k h,
  have h : ¬ is_nilpotent (function_of_vector v),
  intros p,
  have : no_zero_divisors (ring_of_function N),
  { refine @domain.to_no_zero_divisors (ring_of_function N) _,},
  let H := is_nilpotent.eq_zero p,
  rw is_fraction_ring.exists_reduced_fraction,
end

example (v : N) [is_localization.away (function_of_vector v) S] {K : Type*} [field K] [algebra (ring_of_function N) K] [algebra S K] : 
is_fraction_ring S K → is_fraction_ring (ring_of_function N) K :=
begin
  intros h,
  split,
  intros y,
  rw @is_localization.map_units _ _ (submonoid.powers (function_of_vector v)) S _ _ _ y,
end

def mutation_isom_field'  (μ : seed_mutation s s')
{K K' : Type*}
[field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K]
[field K'] [algebra (ring_of_function N) K'] [is_fraction_ring (ring_of_function N) K'] : 
K' ≃+* K := 
begin
  is_fraction_ring.field_equiv_of_ring_equiv  (mutation_isom_localization μ S S')
end
/-
Cluster algebra 
subring of the ambient field fraction_ring R.
-/

end mutation

end cluster
