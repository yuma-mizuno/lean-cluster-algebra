import ring_theory.localization
import category_theory.yoneda
import algebra.category.CommRing.basic

open category_theory

section

universe u
variables {A : Type u} [comm_ring A] (M : submonoid A)

def is_unit_of_ring_hom_functor : CommRing.{u} ⥤ Type u :=
{ obj := λ B , { f : A →+* B // ∀ a : M, is_unit (f a) },
  map := λ B C f g, 
  { val := f.comp g,
    property := λ a, is_unit.map (f.to_monoid_hom) (g.property a) },
  map_id' := λ B, by ext1; cases x; simp at *; ext1; refl,
  map_comp' := λ B C D f g, by refl }

lemma representable_of_is_localization (B : Type u) [comm_ring B] [algebra A B] [is_localization M B] :
∃ f : (coyoneda.obj (opposite.op (CommRing.of B)) ⟶ (is_unit_of_ring_hom_functor M)), is_iso f :=
begin
  fsplit,
  fsplit,
  intros C,
  simp only [category_theory.coyoneda_obj_obj, opposite.unop_op],
  intros f,
  fsplit,
  haveI : algebra A ↥(CommRing.of B) := by dsimp; apply_instance,
  exact f.comp (algebra_map A B),
  dsimp,
  intros a,
  refine @is_unit.map B ↥C _ _ f.to_monoid_hom _ _,
  refine is_localization.map_units B a,
  exact λ X Y f, by refl,
  fsplit,
  fsplit,
  fsplit,
  intros C g,
  dsimp,
  refine @is_localization.lift A _ M B _ _ C _ _ g.val g.property,
  intros B C f,
  dsimp at *,
  ext1 g,
  simp only [category_theory.types_comp_apply, category_theory.coyoneda_obj_map],
  refine is_localization.lift_unique _ _,
  exact λ _, by simp; refl,
  exact ⟨by ext; simp, by ext; simp⟩,
end

instance : functor.corepresentable (is_unit_of_ring_hom_functor M) :=
{ has_corepresentation := 
  ⟨ opposite.op (CommRing.of (localization M)),
    (representable_of_is_localization M (localization M)).some,
    (representable_of_is_localization M (localization M)).some_spec ⟩ }

@[priority 500]
instance algebra_of_representation
(B : Type u) [comm_ring B]
(α : coyoneda.obj (opposite.op (CommRing.of B)) ⟶ (is_unit_of_ring_hom_functor M))
[is_iso α] :
algebra A B := ring_hom.to_algebra (α.app (CommRing.of B) (𝟙 (CommRing.of B))).val

@[priority 500]
instance is_localization_of_representation (B : Type u) [comm_ring B] 
(α : coyoneda.obj (opposite.op (CommRing.of B)) ⟶ (is_unit_of_ring_hom_functor M))
[is_iso α] :
is_localization M B :=
begin
  let β := inv α,
  let f := α.app (CommRing.of B) (𝟙 (CommRing.of B)),
  let fv := f.val,
  let fp := f.property,
  dsimp at *,
  split,
  refine f.property,
  have g := β.app (CommRing.of (localization M)) _,
  tactic.swap,
  fsplit,
  dsimp,
  exact (algebra_map A (localization M)),
  intros a,
  dsimp,
  exact is_localization.map_units (localization M) a,
  intros b,
  simp only [category_theory.coyoneda_obj_obj, opposite.unop_op] at g,

  let p := g b,
  simp only [CommRing.coe_of] at p,
  cases is_localization.surj M p with q h,
  use q,
  sorry,
  intros a a',
  sorry,
end

noncomputable instance :
algebra A (is_unit_of_ring_hom_functor M).corepr_X :=
ring_hom.to_algebra (is_unit_of_ring_hom_functor M).corepr_x.val


instance  :
is_localization M (is_unit_of_ring_hom_functor M).corepr_X :=
begin
  sorry,
end

lemma is_localization.trans {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] (M : submonoid A)
[algebra A B]
[is_localization M B] (f : B ≃+* C) : 
@is_localization _ _ M C _ 
(ring_hom.to_algebra (f.to_ring_hom.comp (algebra_map A B))) :=
begin
  sorry,
end


end