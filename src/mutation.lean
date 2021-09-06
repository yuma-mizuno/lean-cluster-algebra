import linear_algebra.dual
import algebra.monoid_algebra
import ring_theory.localization
import linear_algebra.bilinear_form
import tactic.basic
import localization
/-!
# Mutations

This file defines mutations as isomorphisms between ambient fields.

A seed mutation is a combinatorial operation on a ℤ-module `N` given by a piecewise-linear
transformation on `N`. A mutation is a field isomorphism associated with a seed mutation.
It is an isomorphism on the `K` that is a field of fractions of the group algebra 
of the dual module of `N`. We define mutations by the following three steps.

Step 1. We define a map `seed_mutation.monomial_to_away` that is a monoid hom 
from `module.dual ℤ N` to `S`, where `S` is a localization of the group algebra of 
`module.dual ℤ N` away from a non-zero element in the group algebra of `module.dual ℤ N`.
Step 2. We show that the map defined in Step 1 induces a isomorphism on `S`.
Step 3. We show that the map defined in Step 2 induces a isomorphism on `K` by using the following
general fact on localizations: a composition of localizations are equivalent to a single localization 
when submonoids under these localizations satisfies appropriate inclusion conditions. 

## Main definitions

* `seed_mutation (s s' : multiset N)` is a structure expressing that `μ : seed_mutatoin s s'`
  is a seed mutation with a source seed `s` and a target seed `s'`.
* `seed_mutation.field_equiv μ K` is a field isomorphism `K ≃+* K` associated with 
  a seed mutation `μ`.

## Main statements

* `mutation_field_equiv_map_monomial` gives a fomula for a mutation on the monomials.
-/

open_locale classical

namespace skew_sym_bilin_form

section skew_sym_bilin_form

open bilin_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_monoid M] [module R M] {B : bilin_form R M}

def is_skew_sym (B : bilin_form R M) : Prop := 
∀ (x y : M), B x y = - B y x

variable (H : is_skew_sym B)
include H

lemma skew_sym (x y : M) : B x y = - B y x := H x y

lemma is_refl : refl_bilin_form.is_refl B := λ x y H1, (H y x).symm ▸ neg_eq_zero.mpr H1

lemma ortho_sym {x y : M} : is_ortho B x y ↔ is_ortho B y x := 
refl_bilin_form.ortho_sym (is_refl H)

lemma is_alt [no_zero_divisors R] [char_zero R] : alt_bilin_form.is_alt B := 
λ n, add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (H n n))

@[simp]
lemma self_eq_zero  [no_zero_divisors R] [char_zero R] (x : M) : B x x = 0 := is_alt H x

@[simp]
lemma self_eq_zero_to_lin [no_zero_divisors R] [char_zero R] (x : M) : to_lin' B x x = 0 := 
self_eq_zero H x

end skew_sym_bilin_form

end skew_sym_bilin_form

class inductive is_sign (ε : ℤ) : Prop
| pos : ε = 1 → is_sign
| neg : ε = -1 → is_sign

instance one.is_sign : is_sign 1 := is_sign.pos rfl

instance neg_one.is_sign : is_sign (-1) := is_sign.neg rfl

instance neg.is_sign (ε : ℤ) [is_sign ε] : is_sign (-ε) :=
begin
  let h : is_sign ε := by apply_instance,
  refine is_sign.rec_on h (λ H, _) (λ H, _),
  repeat {any_goals { rw H <|> apply_instance <|> rw neg_neg }},
end

open skew_sym_bilin_form

class skew_symmetric_form (N : Type*) [add_comm_group N] :=
(form : bilin_form ℤ N)
(skew : is_skew_sym form)

variables {N : Type*} [add_comm_group N] [skew_symmetric_form N] 

section seed_mutation

variables (s s' : multiset N) (v : N) (ε : ℤ)

open skew_symmetric_form

abbreviation B := @bilin_form.to_lin ℤ N _ _ _ form

def pl_mutation (v : N) (ε : ℤ) : N → N :=
λ n, n + (max 0 (ε * (B n v))) • v

def pl_mutation.equiv : N ≃ N :=
{ to_fun := pl_mutation v ε,
  inv_fun := pl_mutation (-v) (-ε),
  left_inv := λ n, by unfold pl_mutation; by simp only 
    [ neg_mul_eq_neg_mul_symm, algebra.id.smul_eq_mul, bilin_form.to_lin_apply, linear_map.smul_apply, 
      bilin_form.neg_right, mul_neg_eq_neg_mul_symm, smul_neg, linear_map.map_smul, 
      linear_map.add_apply, linear_map.map_add, self_eq_zero skew,
      add_zero, add_neg_cancel_right, neg_neg, mul_zero, neg_zero],
  right_inv := λ n, by unfold pl_mutation; by simp only
    [ neg_mul_eq_neg_mul_symm, linear_map.map_neg, algebra.id.smul_eq_mul, 
      bilin_form.to_lin_apply, linear_map.smul_apply, bilin_form.neg_right, mul_neg_eq_neg_mul_symm, 
      linear_map.neg_apply, smul_neg, neg_neg, linear_map.map_smul, linear_map.add_apply, linear_map.map_add,
      self_eq_zero skew, add_zero, neg_add_cancel_right, eq_self_iff_true, mul_zero, neg_zero] }

lemma pl_mutation.bijective : function.bijective (pl_mutation v ε) :=
(pl_mutation.equiv v ε).bijective

@[simp] lemma pl_mutation_neg_left_id : pl_mutation (-v) (-ε) ∘ pl_mutation v ε = id :=
by ext x; apply (pl_mutation.equiv v ε).left_inv x

@[simp] lemma pl_mutation_neg_righ_id : pl_mutation v ε ∘ pl_mutation (-v) (-ε) = id :=
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

lemma seed_mutation.is_direction [is_mutation_direction μ v] :
∃ k : ℤ, v = k • μ.src_vect := is_mutation_direction.is_direction

instance src_vect_is_mutation_direction :
is_mutation_direction μ μ.src_vect := by {use 1, simp}

instance tar_vect_is_mutation_direction :
is_mutation_direction μ μ.tar_vect := by {use -1, simp, exact μ.vect_tar_src}

lemma seed_mutation.tar_vect_eq_neg_src_vect {s s' : multiset N} (μ : seed_mutation s s') : 
μ.tar_vect = - μ.src_vect := μ.vect_tar_src

lemma seed_mutation.src_vect_eq_neg_tar_vect {s s' : multiset N} (μ : seed_mutation s s') :  
μ.src_vect = - μ.tar_vect := 
by calc μ.src_vect = - - μ.src_vect : by rw neg_neg
        ...         =   - μ.tar_vect : by rw μ.vect_tar_src

instance sign_tar_vect_is_mutation_direction : is_mutation_direction μ (μ.sign • μ.tar_vect) :=
begin
  cases μ.is_sign with h h, 
  repeat { any_goals {rw h <|> simp <|> apply_instance <|> rw μ.tar_vect_eq_neg_src_vect }},
end

instance sign_src_vect_is_mutation_direction : is_mutation_direction μ (μ.sign • μ.src_vect) :=
begin
  cases μ.is_sign with h h, 
  repeat { any_goals {rw h <|> simp <|> apply_instance <|> rw μ.src_vect_eq_neg_tar_vect }},
end

end direction

section seed_mutation

open skew_symmetric_form

namespace seed_mutation

@[simp] lemma form_mutation_direction_eq_zero {s s' : multiset N} (μ : seed_mutation s s')
(v w : N) [is_mutation_direction μ v] [is_mutation_direction μ w] : form v w = 0 :=
begin
  cases μ.is_direction v with k hk,
  cases μ.is_direction w with l hl,
  rw [hk, hl],
  simp only [bilin_form.smul_right, bilin_form.smul_left, mul_eq_zero, self_eq_zero skew, or_true, eq_self_iff_true],
end

@[simp] lemma form_mutation_direction_eq_zero' {s s' : multiset N} (μ : seed_mutation s s')
(v w : N) [is_mutation_direction μ v] [is_mutation_direction μ w] : B v w = 0 := 
begin
  simp only [bilin_form.to_lin_apply],
  exact form_mutation_direction_eq_zero μ v w,
end

end seed_mutation

lemma pl_mutation_eq (v : N) {w : N} (ε : ℤ) (c : ℤ) (h : w = c • v) : pl_mutation v ε w = w :=
begin
  unfold pl_mutation, rw h, 
  simp only [add_right_eq_self, algebra.id.smul_eq_mul, bilin_form.to_lin_apply, linear_map.smul_apply, 
    linear_map.map_smul, self_eq_zero skew, max_eq_right, eq_self_iff_true, zero_smul, mul_zero],
end

@[simp] lemma pl_mutation_eq' (v : N) (ε : ℤ) : pl_mutation v ε v = v :=
pl_mutation_eq v ε 1 (one_gsmul _).symm

def seed_mutation.symm {s s' : multiset N} (μ : seed_mutation s s') : seed_mutation s' s :=
{ sign := - μ.sign,
  is_sign := @is_sign.rec_on _ (is_sign (- μ.sign)) μ.is_sign 
    (λ h, h.symm ▸ neg_one.is_sign) (λ h, h.symm ▸ one.is_sign),
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
    simp only [id.def, multiset.map_id', eq_self_iff_true, multiset.map_congr, pl_mutation_neg_left_id],
    congr,
    apply eq.symm,
    apply multiset.map_id',
    any_goals {simp only [one_gsmul, neg_smul]},
    apply μ.src_vect_eq_neg_tar_vect,
    exact function.bijective.injective (pl_mutation.bijective μ.tar_vect (-μ.sign)),
    exact function.bijective.injective (pl_mutation.bijective μ.src_vect μ.sign),
  end,
  vect_tar_src := μ.src_vect_eq_neg_tar_vect }

end seed_mutation

section function_of_vector

def ring_of_function (N : Type*) [add_comm_group N]  :=
add_monoid_algebra ℤ (module.dual ℤ N)

local attribute [reducible, inline] add_monoid_algebra ring_of_function

noncomputable instance : comm_ring (ring_of_function N) := add_monoid_algebra.comm_ring
noncomputable instance : comm_ring (module.dual ℤ N →₀ ℤ) := add_monoid_algebra.comm_ring

open skew_symmetric_form

noncomputable theory def function_of_vector (v : N) : (ring_of_function N) :=
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

end function_of_vector

section mutation_away

local attribute [class] is_integral_domain

variables {s s' : multiset N} (μ : seed_mutation s s') (S : Type*) [integral_domain S]
[algebra (ring_of_function N) S]
[is_localization.away (function_of_vector (μ.sign • μ.src_vect)) S]

instance algebra_away : algebra (module.dual ℤ N →₀ ℤ) S := by assumption

open skew_symmetric_form

variables (ε : ℤ) [is_sign ε]

namespace seed_mutation

def away_unit : units S :=
{ val := algebra_map (ring_of_function N) S (function_of_vector (μ.sign • μ.src_vect)),
  inv := is_localization.mk' S 1 ⟨function_of_vector (μ.sign • μ.src_vect), submonoid.mem_powers _⟩,
  val_inv := by rw [is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self],
  inv_val := by rw [mul_comm, is_localization.mul_mk'_eq_mk'_of_mul, mul_one, is_localization.mk'_self] }

def monomial_to_away : multiplicative (module.dual ℤ N) →* S :=
{ to_fun := λ m, 
  is_localization.mk' S
    (finsupp.single (multiplicative.to_add m) 1) (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect)))
      * ↑((μ.away_unit S)^(ε • (-(multiplicative.to_add m) μ.src_vect))),
  map_one' :=
  begin
    simp only [mul_one, algebra.id.smul_eq_mul, gpow_zero, units.coe_one,
      to_add_one, mul_zero, linear_map.zero_apply, neg_zero],
    rw [<- add_monoid_algebra.one_def, is_localization.mk'_one, ring_hom.map_one],
  end,
  map_mul' := λ x y,
  begin
    simp only [algebra.id.smul_eq_mul, gpow_neg, mul_neg_eq_neg_mul_symm,
      neg_add_rev, linear_map.add_apply, to_add_mul],
    rw [<- one_mul (1 : ℤ), <- add_monoid_algebra.single_mul_single],
    rw [<- one_mul (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))),
      is_localization.mk'_mul, mul_add, gpow_add],
    simp only [mul_one, gpow_neg, mul_neg_eq_neg_mul_symm, units.coe_mul],
    ring_exp,
  end }

def to_away : ring_of_function N →+* S :=
add_monoid_algebra.lift_nc_ring_hom (int.cast_ring_hom S)
(μ.monomial_to_away S ε) (λ _ _, (commute.all _ _))

end seed_mutation

@[simp]
lemma to_away_of_function_of_mutation_direction (v : N) [is_mutation_direction μ v] :
(μ.to_away S ε) (function_of_vector v) = 
  is_localization.mk' S (function_of_vector v) 
      (1 : submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) :=
begin
  unfold seed_mutation.to_away function_of_vector 
    seed_mutation.monomial_to_away add_monoid_algebra.lift_nc_ring_hom,
  cases μ.is_direction v with k hk,
  simp only [mul_one,
    ring_hom.eq_int_cast,
    one_mul,
    bilin_form.to_lin_apply,
    ring_hom.coe_mk,
    ring_hom.map_add,
    to_add_of_add,
    int.cast_one,
    ring_hom.coe_add_monoid_hom,
    monoid_hom.coe_mk,
    add_monoid_algebra.lift_nc_single,
    of_add_zero,
    monoid_hom.map_one, μ.form_mutation_direction_eq_zero,
    algebra.id.smul_eq_mul, gpow_zero, mul_zero, neg_zero, units.coe_one, mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
  refl,
end

lemma is_unit_to_away : 
is_unit (μ.to_away S ε (function_of_vector (μ.sign • μ.src_vect))) :=
begin
  rw to_away_of_function_of_mutation_direction,
  rw is_localization.mk'_one,
  refine @is_localization.map_units (ring_of_function N) _ _ S _ _ _ 
    ⟨function_of_vector (μ.sign • μ.src_vect), submonoid.mem_powers _⟩,
end

def seed_mutation.ring_hom_away : S →+* S :=
is_localization.away.lift (function_of_vector (μ.sign • μ.src_vect)) (is_unit_to_away μ S ε)

@[simp] lemma mutation_away_map_const' : 
((μ.ring_hom_away S ε).comp (algebra_map (ring_of_function N) S)).comp 
  add_monoid_algebra.single_zero_ring_hom =
  (algebra_map (ring_of_function N) S ).comp add_monoid_algebra.single_zero_ring_hom := 
dec_trivial

@[simp] lemma mutation_away_map_const (b : ℤ) : 
μ.ring_hom_away S ε ((algebra_map (ring_of_function N) S) (finsupp.single 0 b)) =
algebra_map (ring_of_function N) S (finsupp.single 0 b) :=
begin
  have h : finsupp.single (0 : module.dual ℤ N) b = add_monoid_algebra.single_zero_ring_hom b := by refl,
  rw h,
  repeat {rw <- ring_hom.comp_apply},
  repeat {rw <- ring_hom.coe_comp},
  rw mutation_away_map_const',
end

@[simp] lemma mutation_away_map_monomial (a : multiplicative(module.dual ℤ N)) : 
(μ.ring_hom_away S ε) ((algebra_map (ring_of_function N) S) (finsupp.single a 1)) =
algebra_map (ring_of_function N) S (finsupp.single a 1) 
  * ↑((μ.away_unit S) ^ (ε • (- a μ.src_vect))) :=
begin
  unfold seed_mutation.ring_hom_away is_localization.away.lift,
  rw is_localization.lift_eq,
  unfold seed_mutation.to_away add_monoid_algebra.lift_nc_ring_hom,
  dsimp,
  rw add_monoid_algebra.lift_nc_single,
  unfold seed_mutation.monomial_to_away,
  dsimp,
  rw [int.cast_one, one_mul],
  simp only [gpow_neg, units.ne_zero, or_false, mul_neg_eq_neg_mul_symm, mul_eq_mul_right_iff],
  rw is_localization.mk'_one,
  congr,
end

@[simp]
lemma mutation_away_eq_self_of_gpow_of_unit (k : ℤ) : 
μ.ring_hom_away S ε ↑((μ.away_unit S) ^ k ) = ↑((μ.away_unit S) ^ k) := 
begin
  unfold seed_mutation.ring_hom_away is_localization.away.lift seed_mutation.away_unit,
  induction k,
  { dsimp,
    rw [gpow_coe_nat,  units.coe_pow, ring_hom.map_pow], 
    dsimp,
    rw [is_localization.lift_eq],
    apply congr_arg (λ x : S, x ^ k),
    rw to_away_of_function_of_mutation_direction,
    rw is_localization.mk'_one },
  { rw [gpow_neg_succ_of_nat, <- inv_pow,units.coe_pow],
    rw [ring_hom.map_pow],
    apply congr_arg (λ x : S, x ^ k.succ),
    simp only [units.coe_mk, units.inv_mk],
    rw is_localization.lift_mk'_spec,
    simp only [set_like.coe_mk, to_away_of_function_of_mutation_direction, ring_hom.map_one],
    rw <- is_localization.mk'_mul,
    rw [one_mul, mul_one, is_localization.mk'_self] },
end

def seed_mutation.ring_equiv_away : S ≃+* S :=
ring_equiv.of_hom_inv (μ.ring_hom_away S ε)
(μ.ring_hom_away S (-ε))
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
    rw [mutation_away_map_const, mutation_away_map_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_away_map_monomial, ring_hom.map_mul, mutation_away_map_monomial, mul_assoc],
    simp only [gpow_neg],
    rw mutation_away_eq_self_of_gpow_of_unit,
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
    rw [mutation_away_map_const, mutation_away_map_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_away_map_monomial, ring_hom.map_mul, mutation_away_map_monomial, mul_assoc],
    simp only [gpow_neg],
    rw mutation_away_eq_self_of_gpow_of_unit,
    simp only [algebra.id.smul_eq_mul, gpow_neg, mul_neg_eq_neg_mul_symm],
    simp only [neg_mul_eq_neg_mul_symm, gpow_neg, inv_inv],
    erw units.val_inv,
    apply mul_one },
end

end mutation_away

section mutation_frac

variables 
[is_integral_domain (ring_of_function N)]
{s s' : multiset N} (μ : seed_mutation s s')
(K : Type*) [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K] 
(ε : ℤ) [is_sign ε]

local attribute [class] is_integral_domain

def ring_of_function.integral_domain : integral_domain (ring_of_function N) := 
is_integral_domain.to_integral_domain _ (by assumption)

local attribute [instance] ring_of_function.integral_domain 

abbreviation seed_mutation.away := localization.away (function_of_vector (μ.sign • μ.src_vect))

def away.integral_domain : integral_domain μ.away :=
is_localization.integral_domain_of_le_non_zero_divisors μ.away
  (powers_le_non_zero_divisors_of_no_zero_divisors (function_of_vector_ne_zero (μ.sign • μ.src_vect)))

local attribute [instance]  away.integral_domain

def seed_mutation.algebra_of_away_frac : algebra μ.away K :=
is_localization.algebra_of_away_frac (function_of_vector_ne_zero (μ.sign • μ.src_vect)) μ.away K

local attribute[instance] seed_mutation.algebra_of_away_frac

def seed_mutation.is_fraction_of_algebra_of_away_frac : 
@is_fraction_ring μ.away _ K _ (μ.algebra_of_away_frac K) :=
is_localization.is_fraction_of_algebra_of_away_frac _ μ.away K

local attribute[instance] seed_mutation.is_fraction_of_algebra_of_away_frac

private def z 
{K : Type*} [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K] 
(m : module.dual ℤ N) := algebra_map (ring_of_function N) K (finsupp.single m 1)

def seed_mutation.field_equiv : K ≃+* K := 
is_fraction_ring.field_equiv_of_ring_equiv (μ.ring_equiv_away μ.away 1)

lemma mutation_field_equiv_map_monomial (m : module.dual ℤ N) : 
μ.field_equiv K (z m)  = 
z m * (1 + z (B (μ.sign • μ.src_vect))) ^ - m μ.src_vect :=
begin
  unfold z seed_mutation.field_equiv is_fraction_ring.field_equiv_of_ring_equiv seed_mutation.ring_equiv_away,
  let h_ne := function_of_vector_ne_zero (μ.sign • μ.src_vect),
  repeat {rw is_localization.eq_comp_map_of_lift_of_of_away_frac h_ne μ.away K},
  simp only [fpow_neg, linear_map.map_smul, is_localization.ring_equiv_of_ring_equiv_eq, 
    mutation_away_map_monomial, algebra.id.smul_eq_mul, one_mul, gpow_neg, mul_eq_mul_left_iff, inv_inj', 
    mul_neg_eq_neg_mul_symm, ring_hom.map_units_inv, ring_equiv.of_hom_inv_apply, ring_hom.map_mul],
  apply or.inl,
  unfold seed_mutation.away_unit function_of_vector,
  induction m μ.src_vect;
  simp only [ring_hom.map_add, units.coe_mk, gpow_neg_succ_of_nat, inv_inj', ring_hom.map_pow,
      ring_hom.map_units_inv, linear_map.map_smul, units.coe_pow, int.of_nat_eq_coe, gpow_coe_nat];
  rw <- add_monoid_algebra.one_def;
  simp only [ring_hom.map_one],
end

end mutation_frac
