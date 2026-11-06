module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec

/-!
# The scheme of generic points

For a scheme `X`, the *scheme of generic points* is the disjoint union
`η_X = ∐_η Spec κ(η)` over the generic points `η` of the irreducible components of `X`,
together with the morphism `j_X : η_X ⟶ X` whose restriction to `Spec κ(η)` is the canonical
morphism `Spec κ(η) ⟶ X` with image `η`. For a noetherian scheme there are finitely many
generic points. For an integral scheme with function field `K` the scheme of generic points is
`Spec K` and `j_X` is the inclusion of the generic point.

## Main definitions

- `AlgebraicGeometry.Scheme.genericPointsScheme`: the scheme `η_X = ∐_η Spec κ(η)`.
- `AlgebraicGeometry.Scheme.genericPointsMorphism`: the morphism `j_X : η_X ⟶ X`.

## Main results

- `AlgebraicGeometry.Scheme.ι_genericPointsMorphism`: the restriction of `j_X` to the summand
  `Spec κ(η)` is `X.fromSpecResidueField η`.
- `AlgebraicGeometry.Scheme.range_genericPointsMorphism`: the image of `j_X` is the set of
  generic points of `X`.
- `AlgebraicGeometry.Scheme.finite_genericPoints`: a scheme with noetherian underlying space
  has finitely many generic points.
- `AlgebraicGeometry.Scheme.genericPointsSchemeIsoSpecFunctionField` and
  `AlgebraicGeometry.Scheme.genericPointsSchemeIsoSpecFunctionField_hom_genericPointsMorphism`:
  for `X` integral, `η_X ≅ Spec K` with `K = X.functionField`, identifying `j_X` with the
  inclusion of the generic point `Stacks.EtaleCohomology.genericPointInclusion X`.

## Implementation notes

The definition is made for an arbitrary scheme: the coproduct of schemes over any index type
in the universe of `X` exists, so neither the noetherian hypothesis nor the finiteness of the
set of generic points is needed to form `η_X`; finiteness is recorded separately. The summands
are spectra of residue fields `κ(η)`, not of the local rings at the generic points (which are
artinian, and fields exactly when `X` is reduced at `η`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The *scheme of generic points* `η_X = ∐_η Spec κ(η)` of a scheme `X`: the disjoint union of
the spectra of the residue fields at the generic points of the irreducible components of `X`. -/
@[weil "def_fk105_generic_points_scheme"]
noncomputable def genericPointsScheme : Scheme.{u} :=
  ∐ fun η : _root_.genericPoints X => Spec (X.residueField η)

/-- The canonical morphism `j_X : η_X ⟶ X` from the scheme of generic points, whose restriction
to the summand `Spec κ(η)` is `X.fromSpecResidueField η`. -/
@[weil "def_fk105_generic_points_scheme"]
noncomputable def genericPointsMorphism : X.genericPointsScheme ⟶ X :=
  Sigma.desc fun η : _root_.genericPoints X => X.fromSpecResidueField η

/-- The coprojection of the summand `Spec κ(η)` into the scheme of generic points. -/
noncomputable def genericPointsSchemeι (η : _root_.genericPoints X) :
    Spec (X.residueField η) ⟶ X.genericPointsScheme :=
  Sigma.ι (fun η : _root_.genericPoints X => Spec (X.residueField η)) η

@[reassoc (attr := simp)]
theorem ι_genericPointsMorphism (η : _root_.genericPoints X) :
    X.genericPointsSchemeι η ≫ X.genericPointsMorphism = X.fromSpecResidueField η :=
  Sigma.ι_desc _ _

/-- Two morphisms out of the scheme of generic points agree when they agree on every summand. -/
theorem genericPointsScheme_hom_ext {Y : Scheme.{u}} {f g : X.genericPointsScheme ⟶ Y}
    (h : ∀ η, X.genericPointsSchemeι η ≫ f = X.genericPointsSchemeι η ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- Every point of the scheme of generic points lies in one of the summands `Spec κ(η)`. -/
theorem exists_genericPointsSchemeι_eq (z : X.genericPointsScheme) :
    ∃ (η : _root_.genericPoints X) (y : Spec (X.residueField η)),
      X.genericPointsSchemeι η y = z := by
  obtain ⟨⟨η, y⟩, rfl⟩ := (sigmaMk fun η : _root_.genericPoints X =>
    Spec (X.residueField η)).surjective z
  exact ⟨η, y, (sigmaMk_mk (fun η : _root_.genericPoints X => Spec (X.residueField η)) η y).symm⟩

/-- The image of `j_X : η_X ⟶ X` is the set of generic points of `X`. -/
theorem range_genericPointsMorphism :
    Set.range X.genericPointsMorphism = _root_.genericPoints X := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨η, y, rfl⟩ := X.exists_genericPointsSchemeι_eq z
    have : X.fromSpecResidueField η y ∈ ({(η : X)} : Set X) := by
      rw [← range_fromSpecResidueField]; exact ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, ι_genericPointsMorphism, Set.mem_singleton_iff.mp this]
    exact η.2
  · intro hx
    obtain ⟨y, hy⟩ : (x : X) ∈ Set.range (X.fromSpecResidueField x) := by
      rw [range_fromSpecResidueField]; rfl
    refine ⟨X.genericPointsSchemeι ⟨x, hx⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ι_genericPointsMorphism]
    exact hy

/-- A scheme whose underlying space is noetherian (for instance a noetherian scheme) has
finitely many generic points, so its scheme of generic points is a finite disjoint union. -/
theorem finite_genericPoints [TopologicalSpace.NoetherianSpace X] :
    Finite (_root_.genericPoints X) :=
  have := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  Finite.of_equiv _ genericPoints.equiv.symm

section Integral

variable [IsIntegral X]

noncomputable instance : Unique (_root_.genericPoints X) where
  default := ⟨genericPoint X, by rw [genericPoints_eq_singleton]; rfl⟩
  uniq := by
    rintro ⟨x, hx⟩
    rw [genericPoints_eq_singleton] at hx
    exact Subtype.ext hx

attribute [local instance] AlgebraicGeometry.isIso_residue_genericPoint

/-- For an integral scheme `X` with function field `K`, the scheme of generic points is
`Spec K`. -/
noncomputable def genericPointsSchemeIsoSpecFunctionField :
    Spec X.functionField ≅ X.genericPointsScheme :=
  (asIso (Spec.map (X.residue (genericPoint X)))).symm ≪≫
    (coproductUniqueIso fun η : _root_.genericPoints X => Spec (X.residueField η)).symm

/-- For an integral scheme `X` with function field `K`, the morphism `j_X` is the inclusion
`Spec K ⟶ X` of the generic point, under the identification `η_X ≅ Spec K`. -/
@[weil "def_fk105_generic_points_scheme"]
theorem genericPointsSchemeIsoSpecFunctionField_hom_genericPointsMorphism :
    X.genericPointsSchemeIsoSpecFunctionField.hom ≫ X.genericPointsMorphism =
      Stacks.EtaleCohomology.genericPointInclusion X := by
  change inv (Spec.map (X.residue (genericPoint X))) ≫ (X.genericPointsSchemeι default ≫
    X.genericPointsMorphism) = _
  rw [ι_genericPointsMorphism, fromSpecResidueField]
  exact IsIso.inv_hom_id_assoc _ _

end Integral

end AlgebraicGeometry.Scheme
