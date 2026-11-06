module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# Invertible rational functions as a direct image

Let `X` be a scheme with scheme of generic points `j_X : η_X ⟶ X`
(`AlgebraicGeometry.Scheme.genericPointsMorphism`), and let `𝓡_X` be its sheaf of rational
functions on the small étale site, `𝓡_X(U) = Γ(U ×_X η_X, 𝒪)`. The presheaf `𝓡_X^*` of
invertible rational functions, `U ↦ Γ(U ×_X η_X, 𝒪)ˣ`, is the direct image
`j_{X*} 𝐆_{m,η_X}` of the étale unit sheaf of `η_X`: both have sections `Γ(U ×_X η_X, 𝒪)ˣ`
over `U`, and in both the restriction maps are pull-back of functions along the base changes
of morphisms of étale `X`-schemes. In particular `𝓡_X^*` is an étale sheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.rationalFunctionsUnitsPresheaf`: the presheaf of abelian
  groups `𝓡_X^*`, `U ↦ Γ(U ×_X η_X, 𝒪)ˣ` (written additively), on `SmallEtale B X hX`.
* `AlgebraicGeometry.SmallEtale.rationalFunctionsUnitsSheaf`: `𝓡_X^*` as an étale sheaf.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.rationalFunctionsUnitsPresheaf`: the
  restriction of `𝓡_X^*` to the étale category `Et(X)`.

## Main results

* `AlgebraicGeometry.SmallEtale.rationalFunctionsUnitsPresheaf_eq_directImage`:
  `𝓡_X^* = j_{X*} 𝐆_{m,η_X}` as presheaves on `SmallEtale B X hX`.
* `AlgebraicGeometry.SmallEtale.isSheaf_rationalFunctionsUnitsPresheaf`: `𝓡_X^*` is a sheaf.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.rationalFunctionsUnitsPresheaf_eq_directImage`
  and `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isSheaf_rationalFunctionsUnitsPresheaf`:
  the same on `Et(X)`.

## Implementation notes

The scheme `η_X` need not lie in the big étale site `B`, so `𝐆_{m,η_X}` is
`Stacks.Kummer.multiplicativeSheaf` on Mathlib's small étale site of `η_X`, its direct image is
`Stacks.EtaleCohomology.etaleAbelianDirectImage` along `j_X` (precomposition with base change),
and the result is restricted to `SmallEtale B X hX` by the inverse of
`AlgebraicGeometry.SmallEtale.sheafEquiv`. The coefficients are those of these objects,
`AddCommGrpCat.{max (u + 1) v}`, so the unit groups are raised along `ULift`. With these
choices the identification is definitional. No noetherian hypothesis on `X` is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

namespace SmallEtale

/-- **The presheaf `𝓡_X^*` of invertible rational functions** on the small étale site of `X`:
the units of the sheaf of rational functions `𝓡_X`, `U ↦ Γ(U ×_X η_X, 𝒪)ˣ`, written
additively and raised to the coefficient universe `max (u + 1) v`. -/
abbrev rationalFunctionsUnitsPresheaf :
    (SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  (sheafRationalFunctions B X hX).obj ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) v, u}

/-- The sections of `𝓡_X^*` over `U` are the invertible functions on `U ×_X η_X`. -/
lemma rationalFunctionsUnitsPresheaf_obj (U : SmallEtale B X hX) :
    ToType ((rationalFunctionsUnitsPresheaf.{u, v} B X hX).obj (op U)) =
      ULift.{max (u + 1) v}
        (Additive (Γ(pullback ((toOver B X hX).obj U).hom X.genericPointsMorphism, ⊤))ˣ) :=
  rfl

/-- **`𝓡_X^* = j_{X*} 𝐆_{m,η_X}` as presheaves on the small étale site of `X`**: the units of
the sheaf of rational functions are the direct image, along the scheme of generic points
`j_X : η_X ⟶ X`, of the étale unit sheaf of `η_X`. -/
@[weil "lem_fk105_rational_functions_units_direct_image"]
theorem rationalFunctionsUnitsPresheaf_eq_directImage :
    rationalFunctionsUnitsPresheaf.{u, v} B X hX =
      ((sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
        ((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, v} X.genericPointsMorphism).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} X.genericPointsScheme))).obj :=
  rfl

/-- **`𝓡_X^*` is an étale sheaf**, being the direct image of the étale sheaf `𝐆_{m,η_X}`. -/
@[weil "lem_fk105_rational_functions_units_direct_image"]
theorem isSheaf_rationalFunctionsUnitsPresheaf :
    Presheaf.IsSheaf (topology B X hX) (rationalFunctionsUnitsPresheaf.{u, v} B X hX) := by
  rw [rationalFunctionsUnitsPresheaf_eq_directImage]
  exact ObjectProperty.FullSubcategory.property _

/-- The étale sheaf `𝓡_X^*` of invertible rational functions on the small étale site of `X`. -/
abbrev rationalFunctionsUnitsSheaf : Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v} :=
  ⟨rationalFunctionsUnitsPresheaf.{u, v} B X hX, isSheaf_rationalFunctionsUnitsPresheaf B X hX⟩

/-- The sheaf `𝓡_X^*` is the restriction to `SmallEtale B X hX` of `j_{X*} 𝐆_{m,η_X}`. -/
lemma rationalFunctionsUnitsSheaf_eq_directImage :
    rationalFunctionsUnitsSheaf.{u, v} B X hX =
      (sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
        ((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, v} X.genericPointsMorphism).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} X.genericPointsScheme)) :=
  rfl

end SmallEtale

namespace SmallNoetherianSeparatedEtale

/-- **The presheaf `𝓡_X^*` of invertible rational functions on `Et(X)`**:
`U ↦ Γ(U ×_X η_X, 𝒪)ˣ` on the étale category of noetherian separated étale `X`-schemes. -/
abbrev rationalFunctionsUnitsPresheaf : EtalePresheaf B X hX AddCommGrpCat.{max (u + 1) v} :=
  (inclusion B X hX).op ⋙ SmallEtale.rationalFunctionsUnitsPresheaf.{u, v} B X hX

/-- **`𝓡_X^* = j_{X*} 𝐆_{m,η_X}` as presheaves on `Et(X)`.** -/
@[weil "lem_fk105_rational_functions_units_direct_image"]
theorem rationalFunctionsUnitsPresheaf_eq_directImage :
    rationalFunctionsUnitsPresheaf.{u, v} B X hX =
      (inclusion B X hX).op ⋙
        ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
          ((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, v} X.genericPointsMorphism).obj
            (Stacks.Kummer.multiplicativeSheaf.{u, v} X.genericPointsScheme))).obj :=
  rfl

/-- **`𝓡_X^*` is an étale sheaf on `Et(X)`.** -/
@[weil "lem_fk105_rational_functions_units_direct_image"]
theorem isSheaf_rationalFunctionsUnitsPresheaf :
    Presheaf.IsSheaf (topology B X hX) (rationalFunctionsUnitsPresheaf.{u, v} B X hX) :=
  (inclusion B X hX).op_comp_isSheaf (topology B X hX) (SmallEtale.topology B X hX)
    (SmallEtale.rationalFunctionsUnitsSheaf.{u, v} B X hX)

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
