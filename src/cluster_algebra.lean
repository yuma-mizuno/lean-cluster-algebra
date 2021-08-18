import category_theory.category.Quiv
import category_theory.over
import algebra.category.CommRing
import mutation

noncomputable theory

open cluster category_theory opposite

local attribute [class] is_integral_domain

section

variables 
(N : Type*) [add_comm_group N] [skew_symmetric_form N] [is_integral_domain (ring_of_function N)]
(K : Type*) [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K]

instance : algebra (ring_of_function N) ↥(CommRing.of K) := by {dsimp, apply_instance}
instance : is_fraction_ring (ring_of_function N) ↥(CommRing.of K) := by {dsimp, apply_instance}
instance : field ↥(CommRing.of K) := by {dsimp, apply_instance}

def laurent_subring 
(N : Type*) [add_comm_group N] [skew_symmetric_form N] 
(K : Type*) [field K] [algebra (ring_of_function N) K] : 
subring K := (algebra_map (ring_of_function N) K).range

private def z 
{N : Type*} [add_comm_group N] [skew_symmetric_form N]
{K : Type*} [field K] [algebra (ring_of_function N) K] 
[is_fraction_ring (ring_of_function N) K] (m : module.dual ℤ N) := 
algebra_map (ring_of_function N) K (finsupp.single m 1)

def seeds : quiver (multiset N) :=
{ hom := seed_mutation }

local attribute [instance] seeds

def mutation_paths : category (paths (multiset N)) := 
(paths.category_paths (multiset N))

local attribute [instance] mutation_paths

def mutation_prefunctor : prefunctor (multiset N) CommRingᵒᵖ :=
{ obj := λ s,  op (CommRing.of K),
  map := λ s s' μ, quiver.hom.op (ring_equiv.to_ring_hom (μ.field_equiv K))}

@[simp] lemma mutation_prefunctor.obj_eq_ring (s : multiset N) : 
(mutation_prefunctor N K).obj s = op (CommRing.of K) := by refl

def mutation_functor : paths (multiset N) ⥤ CommRingᵒᵖ :=
{ obj := λ s, (mutation_prefunctor N K).obj s,
  map := λ s s' γ, compose_path ((mutation_prefunctor N K).map_path γ),
  map_id' := λ γ, by refl,
  map_comp' := by {rintros, simp} }

@[simp] lemma mutation_functor.obj_eq_ring (γ : paths (multiset N)) : 
(mutation_functor N K).obj γ = op (CommRing.of K) := by refl

end

section
variables 
{N : Type*} [add_comm_group N] [skew_symmetric_form N] [is_integral_domain (ring_of_function N)]
{K : Type*} [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K]

local attribute [instance] seeds
local attribute [instance] mutation_paths

variables (s : multiset N)
include s

def field_hom_of_under_mutation_path (γ : @under _ (mutation_paths N) s) : K →+* K :=
let g := quiver.hom.unop ((under.post (mutation_functor N K)).obj γ).hom in by simpa using g

def upper_cluster_algebra :=
infi (λ γ, (laurent_subring N K).map (field_hom_of_under_mutation_path s γ))

def vector.is_monomial_at : set (module.dual ℤ N) := λ m, ∀ v ∈ s, m v ≥ 0

def is_monomial_at : set K := 
λ f, ∃ m : module.dual ℤ N, f = z m ∧ vector.is_monomial_at s m

def cluster_monomials : set K := 
⋃ γ, field_hom_of_under_mutation_path s γ '' is_monomial_at s

def cluster_algebra : subring K := subring.closure (cluster_monomials s)

theorem laurent_phenomenon : (cluster_algebra s : subring K) ≤ upper_cluster_algebra s :=
by sorry

end
