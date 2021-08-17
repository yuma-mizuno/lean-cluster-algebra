import linear_algebra.dual
import algebra.monoid_algebra
import ring_theory.localization
import tactic.basic
import tactic.equiv_rw

universes u

noncomputable theory
open_locale classical

namespace cluster

class skew_symmetric_form (N : Type u) [add_comm_group N] :=
(form : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)
(H_skew : ∀ n n' : N, form n n' = - form n' n)

namespace skew_symmetric_form

@[simp]
lemma square_zero {N : Type*} [add_comm_group N] [skew_symmetric_form N] : ∀ n : N, form n n = 0 :=
begin
  intros n,
  have h : form n n = - form n n,
    exact H_skew n n,
  rw eq_neg_iff_add_eq_zero at h,
  simp only [add_self_eq_zero] at h,
  exact h,
end

end skew_symmetric_form

section seed_mutation

variables {N : Type u} [add_comm_group N] [no_zero_smul_divisors ℤ N]
[skew_symmetric_form N] (s : multiset N) (v : N) (ε : ℤ)

open skew_symmetric_form

def pl_seed_mutation : N → N :=
λ n, n + (max 0 (ε * (form n v))) • v

def seed_mutation (H : v ∈ s) : multiset N :=
multiset.cons (-v) (multiset.erase (multiset.map (pl_seed_mutation v ε) s) v)


def is_seed_mutation (s s' : multiset N) (H : v ∈ s) : Prop :=
s' = multiset.cons (-v) (multiset.erase (multiset.map (pl_seed_mutation v ε) s) v)

lemma seed_mutation.neg_in (H : v ∈ s) : -v ∈ (seed_mutation s v ε H) :=
multiset.mem_cons_self _ _

lemma pl_seed_mutation.bijective :
function.bijective (pl_seed_mutation v ε) :=
begin    
  refine function.bijective_iff_has_inverse.mpr _,
  use pl_seed_mutation (-v) (-ε),
  split,
  unfold function.left_inverse,
  intros n,
  unfold pl_seed_mutation,
  simp only [neg_mul_eq_neg_mul_symm, linear_map.map_neg, linear_map.add_apply, linear_map.map_add],
  rw [gsmul_neg, add_assoc, <- sub_eq_add_neg, <- sub_gsmul],
  simp only [add_right_eq_self, algebra.id.smul_eq_mul, linear_map.map_smul_of_tower, linear_map.smul_apply],
  rw <- sub_eq_add_neg,
  simp only [square_zero,zero_gsmul, eq_self_iff_true, sub_zero, mul_neg_eq_neg_mul_symm, neg_neg, mul_zero, sub_self],
  unfold function.right_inverse,
  intros n,
  unfold pl_seed_mutation,
  simp only [neg_mul_eq_neg_mul_symm,linear_map.map_neg,algebra.id.smul_eq_mul,
    linear_map.map_smul_of_tower,linear_map.smul_apply,
    mul_neg_eq_neg_mul_symm,linear_map.neg_apply,
    smul_neg,neg_neg,linear_map.add_apply,linear_map.map_add,square_zero,add_zero, mul_zero, neg_zero],
  rw [add_assoc, add_comm],
  simp only [eq_self_iff_true, add_left_neg, zero_add],
end

lemma seed_mutation.involution (H : v ∈ s) :
seed_mutation (seed_mutation s v ε H) (-v) (-ε) (seed_mutation.neg_in s v ε H)  = s :=
begin
  unfold seed_mutation,
  simp only [multiset.map_cons, neg_neg],
  unfold pl_seed_mutation,
  simp only [neg_mul_eq_neg_mul_symm,add_zero, linear_map.map_neg,
    max_eq_right, multiset.erase_cons_head, cluster.skew_symmetric_form.square_zero,
    mul_neg_eq_neg_mul_symm, multiset.map_congr, linear_map.neg_apply, smul_neg,
    zero_smul,neg_neg, mul_zero,neg_zero],
  rw [multiset.map_erase, multiset.map_map], 
  unfold function.comp,
  simp only [add_zero, algebra.id.smul_eq_mul, max_eq_right, multiset.map_id',
    linear_map.smul_apply, add_neg_cancel_right, cluster.skew_symmetric_form.square_zero,
    multiset.map_congr, zero_smul, mul_zero, linear_map.map_smul,
    linear_map.add_apply, linear_map.map_add, neg_zero],
  apply multiset.cons_erase H,
  apply function.bijective.injective,
  have h : (λ (n : N), n + -(max 0 (ε * (form n) v) • v)) = 
    (λ (n : N), n + (max 0 (-ε * (form n) (-v)) • -v)),
    apply funext,
    intros n,
    simp only [neg_mul_eq_neg_mul_symm, linear_map.map_neg, add_left_inj,
      mul_neg_eq_neg_mul_symm, smul_neg, neg_neg],
  rw h,
  apply pl_seed_mutation.bijective,
end

end seed_mutation

section mutation

variables {N : Type u} [add_comm_group N] [no_zero_smul_divisors ℤ N]
[skew_symmetric_form N] (s : multiset N) (v : N) (ε : ℤ)


open skew_symmetric_form

def ring_of_function (N : Type u) [add_comm_group N] [no_zero_smul_divisors ℤ N] : Type u :=
add_monoid_algebra ℤ (module.dual ℤ N)

instance : comm_ring (ring_of_function N) :=
add_monoid_algebra.comm_ring

def function_of_vector : ring_of_function N :=
finsupp.single 0 1 + finsupp.single  (form v) 1

/-
@[simp] lemma function_of_vector.neg_neg : function_of_vector (-ε • -v) = 
  function_of_vector (ε • v) :=
begin
  simp,
end
-/


def localization_at_vector : Type u :=
localization.away (function_of_vector v)

instance : comm_ring (localization_at_vector v) :=
localization.comm_ring

instance : algebra (ring_of_function N) (localization_at_vector v) :=
localization.algebra

instance : is_localization (submonoid.powers (function_of_vector v)) (localization_at_vector v) :=
localization.is_localization

instance : is_localization.away (function_of_vector v) (localization_at_vector v) :=
localization.is_localization

lemma ring_of_function.map_powers : submonoid.map (ring_equiv.to_monoid_hom 
  (ring_equiv.refl _)) (submonoid.powers (function_of_vector v)) = 
  submonoid.powers (function_of_vector v) :=
begin
  simp only [eq_self_iff_true, submonoid.map_id, ring_equiv.to_monoid_hom_refl],
end

lemma localization_at_vector.ring_hom : (localization_at_vector v) →+*
  localization_at_vector v :=
is_localization.ring_equiv_of_ring_equiv (localization_at_vector v)
  (localization_at_vector v)
  (ring_equiv.refl _) (ring_of_function.map_powers v)

def function_of_vector.unit : units (localization_at_vector v) :=
{ val := localization.mk (function_of_vector v) 1,
  inv := localization.away.inv_self (function_of_vector v),
  val_inv := 
  begin
    unfold localization.away.inv_self,
    simp only [localization.mk_eq_mk'],
    rw <- is_localization.mk'_mul (localization (submonoid.powers (function_of_vector v))),
    simp only [mul_one, one_mul, eq_self_iff_true, is_localization.mk'_self],
  end,
  inv_val := 
  begin
    rw mul_comm,
    unfold localization.away.inv_self,
    simp only [localization.mk_eq_mk'],
    rw <- is_localization.mk'_mul (localization (submonoid.powers (function_of_vector v))),
    simp only [mul_one, one_mul, eq_self_iff_true, is_localization.mk'_self],
  end, }

lemma is_unit_of_vector : 
is_unit ((localization.mk (function_of_vector v) 1) : (localization_at_vector v)) :=
begin
  use function_of_vector.unit v,
  refl,
end

def mutation_monomial : multiplicative (module.dual ℤ N) →* localization_at_vector (ε • v) :=
{ to_fun := λ m,
  (localization.mk (finsupp.single (multiplicative.to_add m) (1 : ℤ)) 1) * 
    (units.val ((function_of_vector.unit (ε • v))^(-(multiplicative.to_add m) v))),
  map_one' :=
  begin
    simp only [gpow_zero, to_add_one, localization.mk_eq_mk', linear_map.zero_apply, neg_zero],
    unfold units.val,
    simp only [mul_one],
    rw <- add_monoid_algebra.one_def,
    apply submonoid.localization_map.mk'_one _,
  end,
  map_mul' := 
  begin
    intros x y,
    dsimp,
    rw <- to_add_mul,
    simp only [gpow_neg, neg_add_rev, to_add_mul],
    unfold units.val,
    rw [gpow_add, <- one_mul (1 : ℤ), <- add_monoid_algebra.single_mul_single],
    unfold units.val,
    simp only [one_mul],
    rw [gpow_neg, gpow_neg],
    unfold units.val,
    rw <- one_mul (1 : (submonoid.powers (function_of_vector (ε • v)))),
    simp only [localization.mk_eq_mk'],
    rw is_localization.mk'_mul (localization (submonoid.powers (function_of_vector (ε • v)))),
    simp only [one_mul],
    ring_exp,
  end}

def mutation_to_localization : ring_of_function N →+* localization_at_vector (ε • v) :=
add_monoid_algebra.lift_nc_ring_hom (int.cast_ring_hom (localization_at_vector (ε • v)))
(mutation_monomial v ε) (λ _ _, (commute.all _ _))

lemma mutation_of_function_of_vector :
  (mutation_to_localization v ε) (function_of_vector (ε • v)) = localization.mk (function_of_vector (ε • v)) 1 :=
begin
  unfold mutation_to_localization,
  unfold function_of_vector,
  unfold mutation_monomial,
  unfold add_monoid_algebra.lift_nc_ring_hom,
  simp only [one_inv, mul_one, algebra.id.smul_eq_mul, ring_hom.eq_int_cast, one_mul, ring_hom.coe_mk, 
    ring_hom.map_add, to_add_of_add, gpow_zero, linear_map.smul_apply, int.cast_one, ring_hom.coe_add_monoid_hom, 
    cluster.skew_symmetric_form.square_zero, monoid_hom.coe_mk, add_monoid_algebra.lift_nc_single, localization.mk_eq_mk', 
    mul_zero, linear_map.map_smul, of_add_zero, monoid_hom.map_one],
  rw [neg_zero,gpow_zero],
  unfold units.val,
  simp only [mul_one],
  rw [is_localization.mk'_one, is_localization.mk'_one, <- add_monoid_algebra.one_def],
  simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one],
end

lemma mutation_is_unit : is_unit ((mutation_to_localization v ε) (function_of_vector (ε • v))) :=
begin
  rw mutation_of_function_of_vector,
  apply is_unit_of_vector,
end

def mutation_between_localization : localization_at_vector (ε • v) →+* localization_at_vector (ε • v) :=
is_localization.away.lift (function_of_vector (ε • v)) (mutation_is_unit v ε)


lemma mutation_between_localization.function_at_vector (k : ℤ) : mutation_between_localization v ε (function_of_vector.unit (ε • v) ^ k).val = 
(function_of_vector.unit (ε • v) ^ k).val := 
begin
  unfold mutation_between_localization,
  unfold is_localization.away.lift,
  unfold function_of_vector.unit,
  induction k,
  { rw [int.of_nat_eq_coe, gpow_coe_nat, <- units.val_coe, units.coe_pow, ring_hom.map_pow],
    apply congr_arg (λ x : localization_at_vector (ε • v), x ^ k),
    rw [units.coe_mk, localization.mk_eq_mk'],
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



def localization_at_vector.cast_ring_equiv (v w : N) (h_eq : v = w) : localization_at_vector v ≃+* localization_at_vector w :=
begin
  induction h_eq, refl,
end


@[simp] lemma mutation_alg_const' : ((mutation_between_localization v ε).comp (algebra_map (ring_of_function N) (localization_at_vector (ε • v)))).comp add_monoid_algebra.single_zero_ring_hom =
(algebra_map (ring_of_function N) (localization_at_vector (ε • v))).comp add_monoid_algebra.single_zero_ring_hom := dec_trivial

@[simp] lemma mutation_alg_const (b : ℤ) : mutation_between_localization v ε (algebra_map (ring_of_function N) (localization_at_vector (ε • v)) (finsupp.single 0 b)) =
algebra_map (ring_of_function N) (localization_at_vector (ε • v)) (finsupp.single 0 b) :=
begin
  have h : finsupp.single (0 : module.dual ℤ N) b = add_monoid_algebra.single_zero_ring_hom b := by refl,
  rw h,
  repeat {rw <- ring_hom.comp_apply},
  repeat {rw <- ring_hom.coe_comp},
  rw mutation_alg_const',
end

@[simp] lemma mutation_alg_monomial (a : multiplicative(module.dual ℤ N)) : (mutation_between_localization v ε) ((algebra_map (ring_of_function N) (localization_at_vector (ε • v))) (finsupp.single a 1)) =
(algebra_map (ring_of_function N) (localization_at_vector (ε • v))) (finsupp.single a 1) * ((function_of_vector.unit (ε • v))^(- a v)).val :=
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

lemma sign_vector_neg_neg :  (-ε • -v) = (ε • v) := by simp

@[simp] lemma cast_alg_map (v w : N) (h_eq : v = w) (f : ring_of_function N) : 
ring_equiv.to_ring_hom (localization_at_vector.cast_ring_equiv v w h_eq) (algebra_map (ring_of_function N) (localization_at_vector v) f)
= algebra_map (ring_of_function N) (localization_at_vector w) f :=
begin
  induction h_eq,
  refl,
end

@[simp] lemma cast_ring_equiv_id : (localization_at_vector.cast_ring_equiv v v rfl) = ring_equiv.refl _ := by refl

open is_localization

lemma id_as_lift : ring_hom.id (localization_at_vector (ε • v)) = is_localization.lift 
  (@map_units _ _ (submonoid.powers (function_of_vector (ε • v))) (localization_at_vector (ε • v)) _ _ _) := 
begin
  ext z,
  rw ring_hom.id_apply,
  rw lift_id,
end

@[simp] lemma cast_apply_function_at_vector (v w : N) (h_eq : v = w) (k : ℤ) : 
ring_equiv.to_ring_hom (localization_at_vector.cast_ring_equiv v w h_eq) (function_of_vector.unit v ^ k).val =
(function_of_vector.unit w ^ k).val :=
begin
  subst h_eq,
  refl,
end

def mutation_isom_localization : localization_at_vector (ε • v) ≃+* localization_at_vector (ε • v) :=
ring_equiv.of_hom_inv (mutation_between_localization v ε) 
  (((localization_at_vector.cast_ring_equiv (-ε • -v) (ε • v) $ by simp).to_ring_hom.comp 
  (mutation_between_localization (-v) (-ε)) ).comp 
  (localization_at_vector.cast_ring_equiv (ε • v) (-ε • -v) $ by simp).to_ring_hom)
begin
  rw id_as_lift,
  apply eq.symm,
  apply lift_unique,
  rw [<- function.funext_iff, <- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) (localization_at_vector (ε • v))],
  apply add_monoid_algebra.ring_hom_ext,
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_alg_const, cast_alg_map, mutation_alg_const, cast_alg_map] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_alg_monomial, ring_hom.map_mul, cast_alg_map, ring_hom.map_mul, mutation_alg_monomial,
      ring_hom.map_mul,ring_hom.map_mul, cast_alg_map, mul_assoc],
    rw cast_apply_function_at_vector (ε • v) (-ε • -v),
    rw cast_apply_function_at_vector (-ε • -v) (ε • v),
    rw mutation_between_localization.function_at_vector,
    rw cast_apply_function_at_vector (-ε • -v) (ε • v),
    simp only [linear_map.map_neg, gpow_neg, neg_neg],
    erw units.val_inv,
    apply mul_one },
end
begin
  rw id_as_lift,
  apply eq.symm,
  apply lift_unique,
  rw [<- function.funext_iff, <- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) (localization_at_vector (ε • v))],
  apply add_monoid_algebra.ring_hom_ext,
  { intros b,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [cast_alg_map, mutation_alg_const, cast_alg_map, mutation_alg_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [cast_alg_map, mutation_alg_monomial],
    rw ring_hom.map_mul,
    rw [cast_alg_map,ring_hom.map_mul, mutation_alg_monomial],
    rw cast_apply_function_at_vector (-ε • -v) (ε • v),
    rw mutation_between_localization.function_at_vector,
    simp only [linear_map.map_neg, gpow_neg, neg_neg],
    rw mul_assoc,
    erw units.val_inv,
    apply mul_one },
end

@[simp] lemma mutation_isom_localization.coe_ring_hom : 
(mutation_isom_localization v ε).to_ring_hom = mutation_between_localization v ε :=
by refl


set_option pp.implicit false


variables (R : Type*) [integral_domain R] (h : R ≃+* ring_of_function N)

#check algebra (localization_at_vector v)

instance  ambient_ring.algebra (h : R ≃+* ring_of_function N) : algebra R (localization_at_vector v) :=
begin
  refine ring_hom.to_algebra _,
  refine ring_hom.comp _ h.to_ring_hom,
  refine algebra.to_ring_hom,
end

instance ambient_ring.is_localization (h : R ≃+* ring_of_function N) : 
@is_localization _ _ ((submonoid.powers (function_of_vector (ε • v))).comap h.to_monoid_hom)
  (localization_at_vector v) _ (ambient_ring.algebra v R h) :=
sorry


#check (localization_at_vector.is_localization v).map_units 
/-

lemma a (h : R ≃+* ring_of_function N)  :  ((non_zero_divisors R).map 
  (algebra_map R (localization_at_vector (ε • v))).to_monoid_hom).map 
  (mutation_isom_localization v ε).to_monoid_hom 
= ((non_zero_divisors (ring_of_function N)).map 
  (algebra_map (ring_of_function N) (localization_at_vector (ε • v))).to_monoid_hom) := 
begin
  sorry
end
-/

lemma a (h : is_integral_domain (ring_of_function N))  :  ((non_zero_divisors (ring_of_function N)).map 
  (algebra_map (ring_of_function N) (localization_at_vector (ε • v))).to_monoid_hom).map 
  (mutation_isom_localization v ε).to_monoid_hom 
= ((non_zero_divisors (ring_of_function N)).map 
  (algebra_map (ring_of_function N) (localization_at_vector (ε • v))).to_monoid_hom) := 
begin
  have : integral_domain (ring_of_function N),
    apply is_integral_domain.to_integral_domain (ring_of_function N) h,
  resetI,
  ext,
  split,
  intros hx,
  rcases hx with ⟨a, ⟨ha1, ha2⟩⟩,
  rcases ha1 with ⟨a0, ⟨g1, g2⟩⟩,
  use a0,
  split,
  assumption,
  sorry,
  sorry,
end



#check (mutation_isom_localization v ε)
#check (non_zero_divisors (ring_of_function N)).map (algebra_map (ring_of_function N) (localization_at_vector (ε • v))).to_monoid_hom
#check algebra_map (ring_of_function N) (localization_at_vector v)

instance ring_of_function.integral_domain (H : is_integral_domain (ring_of_function N)) : integral_domain (ring_of_function N) :=
is_integral_domain.to_integral_domain (ring_of_function N) h

def mutation_isom_field {H : is_integral_domain (ring_of_function N)} : 
@fraction_ring (ring_of_function N) (ring_of_function.integral_domain H) ≃+* 
@fraction_ring (ring_of_function N) (ring_of_function.integral_domain H) :=
begin

end


/-
\
is_localization.field_equiv_of_ring_equiv 



Cluster algebra 
subring of the ambient field fraction_ring R.
-/

end mutation
end cluster