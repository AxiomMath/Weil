module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Morphisms.Etale
public import Weil.Defs.AlgebraicGeometry.Sites.AffineSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The value of the affine restriction `F₀` at an étale algebra

Let `X = Spec A` with `A` noetherian, let `F` be a presheaf on the étale category `Et(X)` of
noetherian separated étale `X`-schemes, and let `F₀` be its restriction to the étale category
`Et(A)` of étale `A`-algebras: `F₀(B)` is the object of compatible families `(s_{V,φ})` indexed by
the pairs of an object `V` of `Et(X)` and a morphism `φ : V ⟶ Spec B` over `X`.

For `B` in `Et(A)` the scheme `Spec B` is noetherian (as `B` is of finite type over `A`),
separated (as it is affine) and étale over `X`, so it is an object of `Et(X)`. The pair
`(Spec B, 𝟙)` is an initial pair, since every pair `(V, φ)` receives the unique morphism `φ`;
hence the component `F₀(B) → F(Spec B)`, `(s_{V,φ}) ↦ s_{Spec B, 𝟙}`, is an isomorphism, and it is
natural in `B`.

## Main definitions

* `AlgebraicGeometry.EtaleCategory.toNoetherianSeparatedEtale B hS`: the functor
  `Et(A) ⥤ Et(Spec A)ᵒᵖ`, `B ↦ Spec B`.
* `AlgebraicGeometry.affineRestriction.specIndex X`: the pair `(Spec B, 𝟙)`.
* `AlgebraicGeometry.affineRestriction.valueIso F`: the natural isomorphism
  `F₀ ≅ (B ↦ F(Spec B))`.

## Main results

* `AlgebraicGeometry.affineRestriction.isInitial_specIndex`: the pair `(Spec B, 𝟙)` is initial.
* `AlgebraicGeometry.affineRestriction.valueIso_hom_app`: the components of `valueIso F` are the
  maps `(s_{V,φ}) ↦ s_{Spec B, 𝟙}`.
* `AlgebraicGeometry.affineRestriction.bijective_π_specIndex`: for a presheaf of sets, the map
  `F₀(B) → F(Spec B)`, `(s_{V,φ}) ↦ s_{Spec B, 𝟙}`, is bijective.

## Implementation notes

The scheme `Spec B` belongs to the big étale site because a quasi-compact morphism locally of
finite type does not increase the size of a scheme (Stacks 000R (5)). The noetherian hypothesis
on `A` is the source's standing assumption, and is needed for `Spec B` to be an object of `Et(X)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {A : CommRingCat.{u}} (B : BigEtaleSite.{u}) (hS : B.Contains (Spec A))

namespace EtaleCategory

/-- The étale structure morphism `Spec B ⟶ Spec A` of an object `B` of `Et(A)`. -/
abbrev specHom (X : EtaleCategory A) : Spec X.unop.left.unop ⟶ Spec A := X.unop.hom

instance etale_specHom (X : EtaleCategory A) : Etale (specHom X) := X.unop.prop

include hS in
/-- The scheme `Spec B` of an étale `A`-algebra `B` lies in every big étale site containing
`Spec A`. -/
lemma contains_spec_unop_left (X : EtaleCategory A) : B.Contains (Spec X.unop.left.unop) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (specHom X) hS

lemma spec_map_comp_specHom {X Y : EtaleCategory A} (g : X ⟶ Y) :
    Spec.map g.unop.left.unop ≫ specHom X = specHom Y := by
  simpa using g.unop.w

variable [IsNoetherianRing A]

/-- The spectrum of an étale algebra over a noetherian ring is noetherian. -/
instance isNoetherian_spec_unop_left (X : EtaleCategory A) :
    IsNoetherian (Spec X.unop.left.unop) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (specHom X)
  exact ⟨⟩

/-- The object `Spec B` of `Et(Spec A)` attached to an étale `A`-algebra `B`. -/
def toNoetherianSeparatedEtaleObj (X : EtaleCategory A) :
    SmallNoetherianSeparatedEtale B (Spec A) hS :=
  SmallNoetherianSeparatedEtale.mk (Spec X.unop.left.unop) (contains_spec_unop_left B hS X)
    (specHom X)

@[simp]
lemma toScheme_obj_toNoetherianSeparatedEtaleObj (X : EtaleCategory A) :
    (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj
      (toNoetherianSeparatedEtaleObj B hS X) = Spec X.unop.left.unop :=
  rfl

@[simp]
lemma structureMorphism_toNoetherianSeparatedEtaleObj (X : EtaleCategory A) :
    SmallNoetherianSeparatedEtale.structureMorphism (toNoetherianSeparatedEtaleObj B hS X) =
      specHom X :=
  rfl

/-- **`Spec B` is an object of `Et(Spec A)`**, functorially in the étale `A`-algebra `B`: the
functor `Et(A) ⥤ Et(Spec A)ᵒᵖ`, `B ↦ Spec B`, sending `B ⟶ C` to `Spec C ⟶ Spec B`. -/
@[weil "lem_fk102_affine_restriction_value"]
def toNoetherianSeparatedEtale :
    EtaleCategory A ⥤ (SmallNoetherianSeparatedEtale B (Spec A) hS)ᵒᵖ where
  obj X := op (toNoetherianSeparatedEtaleObj B hS X)
  map {X Y} g := op ((SmallNoetherianSeparatedEtale.homEquiv _ _).symm
    ⟨Spec.map g.unop.left.unop, spec_map_comp_specHom g⟩)
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply SmallNoetherianSeparatedEtale.hom_ext
    change Spec.map (𝟙 X).unop.left.unop = 𝟙 _
    exact Spec.map_id _
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    apply SmallNoetherianSeparatedEtale.hom_ext
    change Spec.map (f ≫ g).unop.left.unop = Spec.map g.unop.left.unop ≫ Spec.map f.unop.left.unop
    rw [← Spec.map_comp]
    rfl

@[simp]
lemma toNoetherianSeparatedEtale_obj (X : EtaleCategory A) :
    (toNoetherianSeparatedEtale B hS).obj X = op (toNoetherianSeparatedEtaleObj B hS X) :=
  rfl

@[simp]
lemma toScheme_map_toNoetherianSeparatedEtale_map {X Y : EtaleCategory A} (g : X ⟶ Y) :
    (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).map
      ((toNoetherianSeparatedEtale B hS).map g).unop = Spec.map g.unop.left.unop :=
  rfl

end EtaleCategory

namespace affineRestriction

variable {B hS} [IsNoetherianRing A]

/-- The pair `(Spec B, 𝟙)` over `Spec B`. -/
def specIndex (X : EtaleCategory A) : affineRestrictionIndex B hS X :=
  affineRestrictionIndex.mk X (EtaleCategory.toNoetherianSeparatedEtaleObj B hS X) (𝟙 _)
    (Category.id_comp _)

lemma specIndex_eq_mk_id (X : EtaleCategory A) :
    specIndex (B := B) (hS := hS) X =
      StructuredArrow.mk (Y := op (EtaleCategory.toNoetherianSeparatedEtaleObj B hS X))
        (T := (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).op) (𝟙 _) := by
  simp only [specIndex, affineRestrictionIndex.mk]
  congr 1

/-- **The pair `(Spec B, 𝟙)` is initial**: every pair `(V, φ)` receives exactly one morphism from
it, namely `φ`. -/
def isInitial_specIndex (X : EtaleCategory A) : IsInitial (specIndex (B := B) (hS := hS) X) :=
  (specIndex_eq_mk_id X) ▸ StructuredArrow.mkIdInitial

variable {C : Type v} [Category.{w} C] [HasLimitsOfSize.{u, u} C]
  (F : EtalePresheaf B (Spec A) hS C)

instance isIso_π_specIndex (X : EtaleCategory A) : IsIso (π F X (specIndex X)) :=
  isIso_π_of_isInitial (isInitial_specIndex X) _

/-- The pair `(Spec B, 𝟙)` is sent by `Spec C ⟶ Spec B` to the pair `(Spec C, Spec C ⟶ Spec B)`,
which receives the morphism `Spec C ⟶ Spec B` from `(Spec B, 𝟙)`. -/
lemma π_specIndex_map {X Y : EtaleCategory A} (g : X ⟶ Y) :
    (affineRestriction B hS F).map g ≫ π F Y (specIndex Y) =
      π F X (specIndex X) ≫ F.map ((EtaleCategory.toNoetherianSeparatedEtale B hS).map g) := by
  refine (map_π_mk F g _ _ _).trans ?_
  refine Eq.trans ?_ (π_mk_map F ((EtaleCategory.toNoetherianSeparatedEtale B hS).map g).unop
    (𝟙 _) (Category.id_comp _)).symm
  congr 2

/-- **The value of `F₀` at `B` is `F(Spec B)`, naturally in `B`**: the natural isomorphism
`F₀ ≅ (B ↦ F(Spec B))` whose components are `(s_{V,φ}) ↦ s_{Spec B, 𝟙}`. -/
@[weil "lem_fk102_affine_restriction_value"]
def valueIso :
    affineRestriction B hS F ≅ EtaleCategory.toNoetherianSeparatedEtale B hS ⋙ F :=
  NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (π F X (specIndex X)) (isIso_π_specIndex F X))
    (fun g ↦ π_specIndex_map F g)

/-- The components of `valueIso F` are the maps `(s_{V,φ}) ↦ s_{Spec B, 𝟙}`. -/
@[weil "lem_fk102_affine_restriction_value", simp]
lemma valueIso_hom_app (X : EtaleCategory A) :
    (valueIso F).hom.app X = π F X (specIndex X) :=
  rfl

section Types

variable [HasLimitsOfSize.{u, u} (Type v)] (F : EtalePresheaf B (Spec A) hS (Type v))

/-- **`F₀(B) → F(Spec B)`, `(s_{V,φ}) ↦ s_{Spec B, 𝟙}`, is bijective** for a presheaf of
sets. -/
@[weil "lem_fk102_affine_restriction_value"]
theorem bijective_π_specIndex (X : EtaleCategory A) :
    Function.Bijective (π F X (specIndex X)) :=
  (isIso_iff_bijective _).mp inferInstance

end Types

end affineRestriction

end AlgebraicGeometry

end
