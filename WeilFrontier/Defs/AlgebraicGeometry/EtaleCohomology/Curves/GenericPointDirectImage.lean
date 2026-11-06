module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# The sheaf of invertible rational functions on the small étale site

Let `X` be an irreducible scheme with function field `K = X.functionField` and generic point
`j : Spec K ⟶ X`. For an étale `X`-scheme `U`, the rational functions on `U` are the functions
on its generic fibre `U ×_X Spec K`, and `𝓡_X^*` is the sheaf of their unit groups,
`U ↦ Γ(U ×_X Spec K, 𝒪)ˣ`; it is the direct image `j_* 𝐆_{m,K}`. Pulling an invertible function
back along the projection `U ×_X Spec K ⟶ U` defines the canonical map `𝒪_X^* ⟶ 𝓡_X^*`.

This file states both on the small étale site `SmallEtale B X hX` of a big étale site `B`
containing `X`, by restricting the corresponding objects of Mathlib's small étale site of `X`
along `AlgebraicGeometry.SmallEtale.toEtaleSite`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.multiplicativeSheaf`: `𝐆_{m,X} = 𝒪_X^*` on `SmallEtale B X hX`.
* `AlgebraicGeometry.SmallEtale.rationalFunctionUnitsSheaf`: `𝓡_X^* = j_* 𝐆_{m,K}`.
* `AlgebraicGeometry.SmallEtale.toRationalFunctionUnits`: the canonical map
  `𝒪_X^* ⟶ 𝓡_X^*`.

## Main results

* `AlgebraicGeometry.SmallEtale.rationalFunctionUnitsSheaf_obj`: the sections of `𝓡_X^*` over
  `U` are the invertible functions on the generic fibre `U ×_X Spec K`.
* `AlgebraicGeometry.SmallEtale.toRationalFunctionUnits_app_ofUnit`: on sections the canonical
  map restricts an invertible function along the projection `U ×_X Spec K ⟶ U`.

## Implementation notes

The objects are the images, under the inverse of the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv` of sheaf categories, of Mathlib-site objects:
`Stacks.Kummer.multiplicativeSheaf X`, the direct image
`Stacks.EtaleCohomology.genericPointDirectImage X` of `𝐆_{m,K}`, and the comparison morphism
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison` along the generic point. That
inverse is restriction along `toEtaleSite`, so every sections formula is a definitional identity.
The coefficients are `AddCommGrpCat.{max (u + 1) v}`, those of the reused objects. The ring
sheaf `𝓡_X` itself is not needed and not defined: only its units enter.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **`𝐆_{m,X} = 𝒪_X^*` on the small étale site `SmallEtale B X hX`**: the sections over `U` are
the invertible global functions on `U`. It is the restriction of
`Stacks.Kummer.multiplicativeSheaf X` from Mathlib's small étale site. -/
abbrev multiplicativeSheaf : Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v} :=
  (sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
    (Stacks.Kummer.multiplicativeSheaf.{u, v} X)

/-- The sections of `𝐆_{m,X}` over `U` are the units of `Γ(U, 𝒪_U)`. -/
theorem multiplicativeSheaf_obj (U : SmallEtale B X hX) :
    ToType ((multiplicativeSheaf.{u, v} B X hX).obj.obj (op U)) =
      ULift.{max (u + 1) v} (Additive (Γ(((toEtaleSite B X hX).obj U).left, ⊤))ˣ) :=
  rfl

variable [IrreducibleSpace X]

/-- **The sheaf `𝓡_X^*` of invertible rational functions** on the small étale site of an
irreducible scheme `X`: its sections over `U` are the invertible functions on the generic fibre
`U ×_X Spec K`, `K = X.functionField`. It is the direct image `j_* 𝐆_{m,K}` along the generic
point `j : Spec K ⟶ X`. -/
@[weil "not_fk105_rational_function_units"]
abbrev rationalFunctionUnitsSheaf : Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v} :=
  (sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
    ((Stacks.EtaleCohomology.genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)))

/-- The sections of `𝓡_X^*` over `U` are the units of the ring of functions on the generic fibre
`U ×_X Spec K`. -/
theorem rationalFunctionUnitsSheaf_obj (U : SmallEtale B X hX) :
    ToType ((rationalFunctionUnitsSheaf.{u, v} B X hX).obj.obj (op U)) =
      ULift.{max (u + 1) v} (Additive (Γ(pullback ((toEtaleSite B X hX).obj U).hom
        (Stacks.EtaleCohomology.genericPointInclusion X), ⊤))ˣ) :=
  rfl

/-- **The canonical map `𝒪_X^* ⟶ 𝓡_X^*`**: an invertible function on an étale `X`-scheme `U` is
pulled back along the projection `U ×_X Spec K ⟶ U` to an invertible rational function on `U`.
It is the restriction of `Stacks.EtaleCohomology.multiplicativeDirectImageComparison` along the
generic point. -/
@[weil "not_fk105_rational_function_units"]
def toRationalFunctionUnits :
    multiplicativeSheaf.{u, v} B X hX ⟶ rationalFunctionUnitsSheaf.{u, v} B X hX :=
  (sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.map
    (Stacks.EtaleCohomology.multiplicativeDirectImageComparison.{u, v}
      (Stacks.EtaleCohomology.genericPointInclusion X))

/-- **On sections the canonical map is pull-back along `U ×_X Spec K ⟶ U`.** -/
@[simp]
theorem toRationalFunctionUnits_app_ofUnit (U : SmallEtale B X hX)
    (x : (Γ(((toEtaleSite B X hX).obj U).left, ⊤))ˣ) :
    (toRationalFunctionUnits.{u, v} B X hX).hom.app (op U) (Stacks.Kummer.ofUnit x) =
      Stacks.Kummer.ofUnit
        (U := (Stacks.EtaleCohomology.smallEtaleBaseChange
          (Stacks.EtaleCohomology.genericPointInclusion X)).obj ((toEtaleSite B X hX).obj U))
        (Units.map (pullback.fst ((toEtaleSite B X hX).obj U).hom
          (Stacks.EtaleCohomology.genericPointInclusion X)).appTop.hom.toMonoidHom x) :=
  rfl

end AlgebraicGeometry.SmallEtale

end
