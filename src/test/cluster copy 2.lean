import linear_algebra.dual
import algebra.monoid_algebra
import ring_theory.localization
import ring_theory.nilpotent
import linear_algebra.bilinear_form
import tactic.basic

universes u

noncomputable theory
open_locale classical

section
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


@[simp]
lemma self_eq_zero_to_lin [no_zero_divisors R] [char_zero R] (x : M)  : to_lin' B x x = 0 := self_eq_zero H x

end skew_sym_bilin_form
end

namespace cluster

open skew_sym_bilin_form

class skew_symmetric_form (N : Type*) [add_comm_group N] :=
(form : bilin_form ℤ N)
(skew : is_skew_sym form)

section seed_mutation


variables {N : Type*} [add_comm_group N] [no_zero_smul_divisors ℤ N]
[skew_symmetric_form N] (s s' : multiset N) (v : N) (ε : ℤ)

open skew_symmetric_form


@[reducible]
def B := @bilin_form.to_lin ℤ N _ _ _ form

def pl_mutation (v : N) (ε : ℤ) : N → N :=
λ n, n + (max 0 (ε * (B n v))) • v

def pl_mutation.equiv : N ≃ N :=
{ to_fun := pl_mutation v ε,
  inv_fun := pl_mutation (-v) (-ε),
  left_inv := 
  begin
    intros n,
    unfold pl_mutation,
    simp,
    rw self_eq_zero skew,
    simp,
  end,
  right_inv := 
  begin
    intros n,
    unfold pl_mutation,
    simp,
    rw self_eq_zero skew,
    simp,
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

end seed_mutation

lemma pl_mutation_eq (v : N) {w : N} (ε : ℤ) (c : ℤ) (h : w = c • v) : pl_mutation v ε w = w :=
begin
  unfold pl_mutation,
  rw h,
  simp,
  rw self_eq_zero skew,
  simp,
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

--def  h : is_integral_domain (add_monoid_algebra ℤ (module.dual ℤ N)) := sorry

section



abbreviation ring_of_function (N : Type*) [add_comm_group N]  :=
add_monoid_algebra ℤ (module.dual ℤ N)


open skew_symmetric_form


variable {h : is_integral_domain (add_monoid_algebra ℤ (module.dual ℤ N))}
include h
/-
#check default (nat → nat × bool)
#reduce default (nat → nat × bool)

@[priority 10]
instance : integral_domain (ring_of_function N) :=  h
@[priority 10]
instance : integral_domain (add_monoid_algebra ℤ (module.dual ℤ N)) :=  h
@[priority 10]
instance : integral_domain (module.dual ℤ N →₀ ℤ) :=  add_monoid_algebra.integral_domain
local attribute [instance, priority 1100] finsupp.has_add
local attribute [instance, priority 1100] add_monoid_algebra.has_mul

-/
@[priority 10]
instance : integral_domain (ring_of_function N) := is_integral_domain.to_integral_domain _ h
--@[priority 10]
--instance : integral_domain (add_monoid_algebra ℤ (module.dual ℤ N)) := is_integral_domain.to_integral_domain _ h
@[priority 10]
instance : integral_domain (module.dual ℤ N →₀ ℤ) :=  
begin
  apply' ring_of_function.integral_domain,
  assumption,
end
omit h

instance : comm_ring (ring_of_function N) := add_monoid_algebra.comm_ring
instance : comm_ring (module.dual ℤ N →₀ ℤ) := add_monoid_algebra.comm_ring


def function_of_vector (v : N) : (ring_of_function N) :=
finsupp.single 0 1 + finsupp.single (B v) 1

lemma function_of_vector_neq_zero  (v : N) : function_of_vector v ≠ 0 :=
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




#print classes
#print instances integral_domain

#reduce (by apply_instance : inhabited ℕ)
#reduce (infer_instance : inhabited ℕ)


include h

#check distrib.to_has_mul 
#check  @has_add.add
       (@finsupp
          (@module.dual int N int.comm_semiring (@add_comm_group.to_add_comm_monoid N _)
             (@add_comm_group.int_module N _))
          int
          int.has_zero)
       (@distrib.to_has_add
          (@finsupp
             (@module.dual int N int.comm_semiring (@add_comm_group.to_add_comm_monoid N _)
                (@add_comm_group.int_module N _))
             int
             int.has_zero)
          (@ring.to_distrib
             (@finsupp
                (@module.dual int N int.comm_semiring (@add_comm_group.to_add_comm_monoid N _)
                   (@add_comm_group.int_module N _))
                int
                int.has_zero)
             (@domain.to_ring
                (@finsupp
                   (@module.dual int N int.comm_semiring (@add_comm_group.to_add_comm_monoid N _)
                      (@add_comm_group.int_module N _))
                   int
                   int.has_zero)
                (@integral_domain.to_domain
                   (@finsupp
                      (@module.dual int N int.comm_semiring (@add_comm_group.to_add_comm_monoid N _)
                         (@add_comm_group.int_module N _))
                      int
                      int.has_zero)
                   (@finsupp.integral_domain N _ _ _ h)))))


#check (@finsupp.integral_domain N _ _ _ _)

#check nat.mul

lemma function_of_vector.is_palindromic  (v : N) :
(finsupp.single (B v) 1 : (ring_of_function N)) * (function_of_vector (-v)) = function_of_vector v :=
begin
  unfold function_of_vector,
  erw mul_add,
  repeat {rw add_monoid_algebra.single_mul_single},
  simp only [add_zero, mul_one, linear_map.map_neg, add_right_neg],
  apply add_comm,
end

def function_of_vector.is_palindromic' (v : N) : 
(finsupp.single (B (- v)) 1 : ring_of_function N) * (function_of_vector v) = function_of_vector (-v) :=
begin
  let h := function_of_vector.is_palindromic (-v),
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

omit h
abbreviation is_localization_at_vect : Prop := is_localization.away (function_of_vector v) S

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

end

section mutation

variables {s s' : multiset N} (μ : seed_mutation s s')   (S S' : Type*) [integral_domain S] [integral_domain S']
[algebra (ring_of_function N) S] [algebra (ring_of_function N) S']
[is_localization.away (function_of_vector μ.src_vect) S]
[is_localization.away (function_of_vector μ.tar_vect) S']
instance algebra_S : algebra (module.dual ℤ N →₀ ℤ) S:= by assumption
instance algebra_S' : algebra (module.dual ℤ N →₀ ℤ) S':= by assumption

open skew_symmetric_form
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


def mutation_isom_field
[is_localization.away (function_of_vector μ.src_vect) S]
[is_localization.away (function_of_vector μ.tar_vect) S'] 
(K K' : Type*)
[field K] [algebra S K] [is_fraction_ring S K]
[field K'] [algebra S' K'] [is_fraction_ring S' K'] : 
K' ≃+* K := 
is_fraction_ring.field_equiv_of_ring_equiv  (mutation_isom_localization μ S S')


def mutation_isom_field'
(K K' : Type*)
[field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K]
[field K'] [algebra (ring_of_function N) K'] [is_fraction_ring (ring_of_function N) K'] : 
K' ≃+* K := 
begin

end

#print mutation_isom_field


set_option pp.all false
#check semiring.to_non_assoc_semiring

lemma powers_le_non_zero_divisors (R : Type*) [integral_domain R] (f : R) (ne_zero : f ≠ 0) : 
submonoid.powers f ≤ non_zero_divisors R :=
begin
  intros x H,
  intros g hf,
  cases H with k H,
  cases integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero g x hf with _ hx,
  assumption',
  rw hx at H,
  let h : ¬ is_nilpotent f := λ p, ne_zero p.eq_zero,
  unfold is_nilpotent at h,
  rw not_exists at h,
  apply false.elim,
  exact h k H,
end

lemma powers_le_non_zero_divisors' (v : N) {h : is_integral_domain (add_monoid_algebra ℤ (module.dual ℤ N))} : 
(submonoid.powers (function_of_vector v)) ≤ (non_zero_divisors (ring_of_function N)) :=
begin
  letI inst_h := is_integral_domain.to_integral_domain _ h,
  apply powers_le_non_zero_divisors,
  refine function_of_vector_neq_zero v,
end

example (v : N) {h : is_integral_domain (add_monoid_algebra ℤ (module.dual ℤ N))}
[is_localization.away (function_of_vector v) S] {K : Type*} [field K] [algebra (ring_of_function N) K] [algebra S K] : 
is_fraction_ring S K → is_fraction_ring (ring_of_function N) K :=
begin
  intros h,
  split,
  intros y,
  let P:= (powers_le_non_zero_divisors v),
  unfold_projs at P,
  cases y,
  let P' := @P y_property,
  rw is_localization.map_units S (powers_le_non_zero_divisors y),
end

example
{R S K : Type*} [comm_ring R] [comm_ring S] [comm_ring K] [algebra R S] [algebra R K] [algebra S K]
(M : submonoid R) (N : submonoid R) (N' : submonoid S)
[is_localization M S] [is_localization N K] [is_localization N' K]
(h_map : N' = N.map (algebra_map R S).to_monoid_hom) (h_le : M ≤ N ):
is_localization N K :=
begin
  split,
end


lemma is_localization.closure_union
{A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C]
(M : submonoid A) (N : submonoid A) (N' : submonoid B)
[is_localization M B] [is_localization N' C]
(h_map : N' = N.map (algebra_map A B).to_monoid_hom) :
@is_localization _ _ (M ⊔ N) C _
(ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B))) :=
begin
  letI : algebra A C := ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B)),
  have h_comp : algebra_map A C = (algebra_map B C).comp (algebra_map A B) := by refl,
  split,
  { intros y,
    cases y with y_v y_in,
    rw set_like.coe_mk,
    rw [<- submonoid.closure_eq M, <- submonoid.closure_eq N] at y_in,
    rw <- submonoid.closure_union at y_in,
    refine submonoid.closure_induction y_in _ _ _,
    { intros x hx,
      cases hx,
      rw h_comp,
      simp only [function.comp_app, ring_hom.coe_comp],
      apply is_unit.map',
      refine is_localization.map_units B ⟨x, hx⟩,
      have : algebra_map A B x ∈ N',
      { rw h_map,
        simp only [ring_hom.to_monoid_hom_eq_coe, submonoid.mem_map],
        use x,
        use hx,
        simp only [ring_hom.coe_monoid_hom] },
      refine is_localization.map_units C ⟨algebra_map A B x, this⟩ },
    { apply is_unit.map',
      refine is_unit_one },
    { intros x y,
      rw ring_hom.map_mul,
      refine is_unit.mul } },
  { intros z,
    let y := is_localization.sec N' z,
    let x := is_localization.sec M y.1,
    have : ∃ (x : A) (H : x ∈ N), (algebra_map A B).to_monoid_hom x = y.2,
    { rw <- submonoid.mem_map,
      tactic.unfreeze_local_instances,
      subst h_map,
      refine y.2.property },
    cases this with x0 H,
    cases H with H p,
    have : x.2.val * x0 ∈ M ⊔ N,
    { refine submonoid.mul_mem _ _ _,
      apply submonoid.mem_sup_left,
      exact x.2.property ,
      apply submonoid.mem_sup_right,
      exact H },
    use ⟨x.1, ⟨x.2 * x0, this⟩⟩,
    rw h_comp,
    simp only [set_like.coe_mk, function.comp_app, ring_hom.coe_comp, ring_hom.map_mul],
    rw <- is_localization.sec_spec M y.1,
    simp at p,
    rw [p, ring_hom.map_mul, <- is_localization.sec_spec N' z],
    ring },
  { intros x y,
    rw [h_comp], 
    simp only [function.comp_app, ring_hom.coe_comp],
    split,
    { let p:= @is_localization.eq_iff_exists _ _ N' C _ _ _ (algebra_map A B x) (algebra_map A B y),
      intros h,
      cases p.mp h with c hc,
      have : ∃ (x : A) (H : x ∈ N), (algebra_map A B).to_monoid_hom x = c,
      { rw <- submonoid.mem_map,
        tactic.unfreeze_local_instances,
        subst h_map,
        refine c.property },
      cases this with c0 H,
      cases H with H app_c0,
      rw <- app_c0 at hc,
      simp only [ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe] at hc,
      rw [<- ring_hom.map_mul, <- ring_hom.map_mul] at hc,
      let q := @is_localization.eq_iff_exists _ _ M B _ _ _ (x * c0) (y * c0),
      cases q.mp hc with d hd,
      have : c0 * d ∈ M ⊔ N,
      { refine submonoid.mul_mem _ _ _,
        apply submonoid.mem_sup_right,
        exact H ,
        apply submonoid.mem_sup_left,
        exact d.property },
      use ⟨c0 * d, this⟩,
      dsimp,
      rw [mul_assoc, mul_assoc] at hd,
      exact hd},
    { intros h,
      cases h with c hc,
      cases c with cv cp,
      rw submonoid.mem_sup at cp,
      cases cp with c1 c2,
      repeat {rw submonoid.closure_eq at c2},
      rcases c2 with ⟨cm, ⟨ a,⟨an,ha ⟩⟩⟩,
      let p:= @is_localization.eq_iff_exists _ _ N' C _ _ _ (algebra_map A B (x * c1)) (algebra_map A B (y * c1)),
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
      have h_unit : is_unit ((algebra_map B C) ((algebra_map A B) c1)),
      { apply is_unit.map',
        refine is_localization.map_units B ⟨c1, cm⟩ },
      rw <- is_unit.mul_left_inj h_unit,
      assumption } },
end

lemma is_localization.le
{A B : Type*} (C : Type*) [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C]
(M : submonoid A) (N : submonoid A) (N' : submonoid B)
[is_localization M B] [is_localization N' C]
(h_map : N' = N.map (algebra_map A B).to_monoid_hom)
(h_le : M ≤ N) :
@is_localization _ _ N C _
(ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B))) :=
begin
  have : (submonoid.closure ((M : set A) ∪ N)) = N,
    rw submonoid.closure_union,
    simp only [submonoid.closure_eq, sup_eq_right],
    assumption,
  rw <- this,
  refine is_localization.closure_union M N N' h_map,
end

#print instances algebra

@[priority 500]
instance trans {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] (M : submonoid A)
[algebra A B]
[is_localization M B] (f : B ≃+* C) : 
@is_localization _ _ M C _ 
(ring_hom.to_algebra (f.to_ring_hom.comp (algebra_map A B))) :=
begin
  letI : algebra A C := ring_hom.to_algebra (f.to_ring_hom.comp (algebra_map A B)),
  have h_comp : algebra_map A C = f.to_ring_hom.comp (algebra_map A B) := by refl,
  split,
  { intros y,
    let g := f.symm,
    have : algebra_map A C y = f.to_ring_hom (g.to_ring_hom (algebra_map A C y)),
    simp,
    rw this,
    apply is_unit.map' f.to_ring_hom,
    rw h_comp,
    repeat {rw <- ring_hom.comp_apply},
    rw <- ring_hom.comp_assoc,
    simp only [ring_hom.coe_comp, ring_equiv.to_ring_hom_eq_coe, ring_equiv.coe_to_ring_hom, 
      ring_equiv.symm_apply_apply, function.comp_app],
    refine @is_localization.map_units A _ M B _ _ _ y },
  { intros c,
    let b := f.symm.to_ring_hom c,
    cases is_localization.surj M b with bv bp,
    use bv,
    rw h_comp,
    simp only [function.comp_app, ring_hom.coe_comp],
    rw <- bp,
    have : c = f.to_ring_hom b,
    simp,
    rw this,
    rw <-  ring_hom.map_mul },
  { intros a a',
    split,
    { intros h,
      rw h_comp at h,
      let p:= congr_arg f.symm.to_ring_hom  h,
      simp at p,
      cases (is_localization.eq_iff_exists M B).mp p with c hc,
      exact ⟨c, hc⟩ },
  { rintros ⟨c, hc⟩,
    rw h_comp,
    simp only [function.comp_app, ring_hom.coe_comp],
    apply congr_arg f.to_ring_hom,
    let p:= congr_arg (algebra_map A B)  hc,
    simp at p,
    refine (is_unit.mul_left_inj _).mp p,
    exact is_localization.map_units B c } }
end

example
{A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C]
(M : submonoid A) (N : submonoid A) (N' : submonoid B)
[is_localization M B]
[@is_localization _ _ N C _ (ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B)))] 
(h_map : N' = N.map (algebra_map A B).to_monoid_hom)
(h_le : M ≤ N) :
is_localization N' C  :=
begin
  let C' := localization N',
  letI : algebra A C := ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B)),
  letI : algebra A C' := ring_hom.to_algebra ((algebra_map B C').comp (algebra_map A B)),
  letI : is_localization N C' := is_localization.le C' M N N' h_map h_le,
  have : submonoid.map (ring_equiv.refl A).to_monoid_hom N = N := by simp,
  let h_equiv : C ≃+* C' := is_localization.ring_equiv_of_ring_equiv C C' (ring_equiv.refl A) this,
end


lemma aaa 
{A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C]
(M : submonoid A) (N : submonoid A) (N' : submonoid B)
[is_localization M B] 
[@is_localization _ _ (submonoid.closure ((M : set A) ∪ N)) C _ (ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B)))] 
(h_map : N' = N.map (algebra_map A B).to_monoid_hom) :
is_localization N' C :=
begin
  letI : algebra A C := ring_hom.to_algebra ((algebra_map B C).comp (algebra_map A B)),
  have h_comp : algebra_map A C = (algebra_map B C).comp (algebra_map A B) := by refl,
  rw h_map,
  split,
  { intros b,
    rcases b with ⟨bv, ⟨av, ⟨a_in, a_map⟩⟩⟩,
    have a_in_MN : av ∈ submonoid.closure ((M : set A) ∪ N),
    rw [submonoid.closure_union, submonoid.closure_eq, submonoid.closure_eq],
    apply submonoid.mem_sup_right a_in,
    simp only [subtype.coe_mk],
    rw <- a_map,
    exact is_localization.map_units C ⟨av, a_in_MN⟩,},
  { intros c,
    let a := is_localization.sec (submonoid.closure ((M : set A) ∪ N)) c,
--    erw [submonoid.closure_union, submonoid.closure_eq, submonoid.closure_eq] at a,
    cases a.2 with mv mp,
    rw [submonoid.closure_union, submonoid.closure_eq, submonoid.closure_eq] at mp,
    rw submonoid.mem_sup at mp,
    rcases mp with ⟨m0,m0_in,n0,n0_in,h_mn⟩,
    have : algebra_map A B n0 ∈ submonoid.map (algebra_map A B).to_monoid_hom N,
    { simp only [ring_hom.to_monoid_hom_eq_coe, submonoid.mem_map],
      use n0,
      use n0_in,
      simp only [ring_hom.coe_monoid_hom] },
      let q := (is_localization.map_units B ⟨m0, m0_in⟩),
    use ⟨(algebra_map A B a.1) * (is_localization.map_units B ⟨m0, m0_in⟩).unit.inv, ⟨algebra_map A B n0, this ⟩⟩,
    simp only [set_like.coe_mk, ring_hom.map_mul],
    have  : algebra_map A C a.1 = (algebra_map B C) ((algebra_map A B) a.1) := by refl,
    rw [<- this],
    rw <- is_localization.sec_spec (submonoid.closure ((M : set A) ∪ N)) c,
    rw <- is_unit.mul_left_inj (is_unit.map (algebra_map B C).to_monoid_hom (is_localization.map_units B ⟨m0, m0_in⟩)),
    simp only [set_like.coe_mk, ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe],
    repeat {rw mul_assoc},
    apply congr_arg (λ x, c * x),
  repeat {rw <- ring_hom.map_mul},
    rw  [mul_comm n0 m0, h_mn],
    rw <- units.coe_inv,
    rw units.inv_mul,
    rw is_unit.unit_spec,
    rw is_unit.unit,
    simp?,
  }
end


instance {h : is_integral_domain (add_monoid_algebra ℤ (module.dual ℤ N))}
{S K : Type*} [comm_ring S] [comm_ring K] [algebra (ring_of_function N) K] [algebra S K]
[is_fraction_ring (ring_of_function N) K] :
is_fraction_ring S K :=
begin
  split,
  refine is_localization.map_units S (submonoid.powers.)
end


lemma is_localization_unique
{A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra A C]
(M : submonoid A) 
[is_localization M B] [is_localization M C] :
B ≃+* C := 
let f := (@is_localization.lift A _ M B _ _ C _ _ (algebra_map A C) (is_localization.map_units C)) in
let g := (@is_localization.lift A _ M C _ _ B _ _ (algebra_map A B) (is_localization.map_units B)) in
ring_equiv.of_hom_inv f g
begin
  have : g.comp f = (@is_localization.lift A _ M B _ _ B _ _ (algebra_map A B) (is_localization.map_units B)),
  refine is_localization.epic_of_localization_map M _ _ (by simp),
  rw this,
  refine is_localization.lift_unique _ (by simp),
end
begin
  have : f.comp g = (@is_localization.lift A _ M C _ _ C _ _ (algebra_map A C) (is_localization.map_units C)),
  refine is_localization.epic_of_localization_map M _ _ (by simp),
  rw this,
  refine is_localization.lift_unique _ (by simp),
end

@[priority 1500]
instance away_at_vect.integral_domain (v : N) {h : is_integral_domain (ring_of_function N)} : 
integral_domain (localization.away (function_of_vector v)) :=
begin
  refine @is_localization.integral_domain_localization _ 
    (@ring_of_function.integral_domain _ _ _ _ h) _ _,
  refine powers_le_non_zero_divisors' v,
  assumption,
end

end mutation

section
variables {s s' : multiset N}

set_option trace.class_instances true

def mutation_isom_field' {h : is_integral_domain (ring_of_function N)} (μ : seed_mutation s s')
{K K' : Type*} 
[comm_ring K]  [algebra (ring_of_function N) K]  [is_fraction_ring (ring_of_function N) K]
[comm_ring K'] [algebra (ring_of_function N) K'] [is_fraction_ring (ring_of_function N) K'] : 
K' ≃+* K := 
let S  := localization.away (function_of_vector μ.src_vect) in
let S' := localization.away (function_of_vector μ.tar_vect) in
let L  := fraction_ring S  in
let L' := fraction_ring S' in
begin
  have : algebra S L,
  apply_instance,
  haveI : algebra S' L := @localization.algebra S' _ (non_zero_divisors S'),
  haveI : integral_domain S := away_at_vect.integral_domain μ.src_vect h,
  haveI : integral_domain S' := away_at_vect.integral_domain μ.tar_vect h,
  let f := mutation_isom_field μ S S' L L',
end
/-
Cluster algebra 
subring of the ambient field fraction_ring R.
-/

end


end cluster
