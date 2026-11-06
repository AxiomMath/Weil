module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageSmoothCurveVanishing

/-!
# Cohomology of the direct image of `𝐆_m` along the generic point of a curve

Let `X` be a smooth curve over an algebraically closed field `k`, let `η = Spec k(X)` be its
generic point and `j : η ⟶ X` the inclusion. Then

`H^i(X, j_* 𝐆_{m,η}) ≅ H^i(η, 𝐆_m)` for every `i ≥ 0`.

The proof is the collapse of the Leray spectral sequence when all higher direct images vanish,
obtained without a spectral sequence: if `R^q f_* F = 0` for `q > 0`, then `f_*` applied to an
injective resolution of `F` is an injective resolution of `f_* F`, and global sections on the
target composed with `f_*` are global sections on the source. For `j` and `𝐆_m` the vanishing
`R^q j_* 𝐆_{m,η} = 0` (`q > 0`) is [Stacks, Tag 03RJ].

## Main results

* `AlgebraicGeometry.sheafHEtaleAbelianDirectImageAddEquivOfIsZero`: for a morphism
  `f : Y ⟶ X` and an abelian étale sheaf `F` on `Y` with `R^q f_* F = 0` for every `q > 0`,
  `H^i(X, f_* F) ≃+ H^i(Y, F)` for every `i`.
* `AlgebraicGeometry.sheafHGenericPointDirectImageMultiplicativeSheafAddEquiv`:
  `H^i(X, j_* 𝐆_{m,η}) ≃+ H^i(η, 𝐆_m)` for a smooth curve `X` over an algebraically closed
  field and every `i`.

## Implementation notes

A curve (`AlgebraicGeometry.IsCurve`) is integral, so the scheme of generic points `η_X` is
`Spec k(X)` and `j_X` is the inclusion of the generic point
(`AlgebraicGeometry.Scheme.genericPointsSchemeIsoSpecFunctionField_hom_genericPointsMorphism`);
the statement is made with `Spec k(X)` and `Stacks.EtaleCohomology.genericPointInclusion`.
Sheaves are on the small étale site `X.smallEtaleTopology` with coefficients in
`AddCommGrpCat.{u + 1}`, and `𝐆_m` is `Stacks.Kummer.multiplicativeSheaf`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ)
* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

attribute [local instance] Stacks.Cohomology.GlobalSections.additive_Γ

/-- The direct image along `f : Y ⟶ X` on abelian sheaves of the small étale sites, with
coefficients in `AddCommGrpCat.{u + 1}`, preserves injective objects. -/
local instance preservesInjectiveObjects_etaleAbelianDirectImage_aux {X Y : Scheme.{u}}
    (f : Y ⟶ X) : (etaleAbelianDirectImage.{u, u + 1} f).PreservesInjectiveObjects :=
  smallEtalePushforwardAb_preservesInjectiveObjects f

/-- **Cohomology of a direct image with vanishing higher direct images.** Let `f : Y ⟶ X` be a
morphism of schemes and `F` an abelian sheaf on `Y_étale` with `R^q f_* F = 0` for every
`q > 0`. Then `H^i(X, f_* F) ≃+ H^i(Y, F)` for every `i`. -/
def sheafHEtaleAbelianDirectImageAddEquivOfIsZero {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hR : ∀ q : ℕ, 0 < q →
      IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F))
    (n : ℕ) :
    Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj F) n ≃+
      Sheaf.H.{u + 1, u + 1} F n :=
  Iso.addCommGroupIsoToAddEquiv
    (((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1}
          X.smallEtaleTopology n).app _).symm ≪≫
      (Stacks.RightDerivedComp.objIso (etaleAbelianDirectImage.{u, u + 1} f)
          (InjectiveResolution.of F) hR
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).symm ≪≫
      (ModuleSheafCohomology.rightDerivedIso
          (etaleAbelianDirectImageCompGlobalSectionsIso f) n).app F ≪≫
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1}
          Y.smallEtaleTopology n).app F)

/-- **The cohomology of `j_* 𝐆_m` along the generic point of a smooth curve.** Let `X` be a
smooth curve over an algebraically closed field `k`, `η = Spec k(X)` its generic point and
`j : η ⟶ X` the inclusion. Then `H^i(X, j_* 𝐆_{m,η}) ≅ H^i(η, 𝐆_m)` for every `i ≥ 0`. -/
@[weil "lem_fk105_generic_point_cohomology_direct_image_gm"]
def sheafHGenericPointDirectImageMultiplicativeSheafAddEquiv {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (i : ℕ) :
    Sheaf.H.{u + 1, u + 1} ((genericPointDirectImage.{u, u + 1} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) i ≃+
      Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)) i :=
  sheafHEtaleAbelianDirectImageAddEquivOfIsZero (genericPointInclusion X) _
    (fun q hq => isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_smoothCurve g q hq)
    i

end AlgebraicGeometry

end
