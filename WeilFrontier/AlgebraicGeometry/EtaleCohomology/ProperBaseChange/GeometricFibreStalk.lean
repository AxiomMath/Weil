module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SmoothProperSpecializationUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChangeFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit

/-!
# The stalk of a higher direct image at a geometric point is the cohomology of the fibre

Let `f : X ⟶ S` be a proper morphism of schemes, `s̄ : Spec Ω ⟶ S` a geometric point (`Ω`
separably closed) with geometric fibre `X_s̄ = X ×_S Spec Ω` and projection `g' : X_s̄ ⟶ X`, and
let `F` be a torsion abelian sheaf on `X_étale`. Then for every `n` the canonical map
`Hⁿ((Rf_* F)_s̄) ⟶ Hⁿ(X_s̄, g'⁻¹ F)` is an isomorphism, naturally in `F`.

The canonical map is the composite of the following natural maps, defined for every morphism `f`
and every object of the unbounded derived category: the stalk at `s̄` commutes with cohomology
sheaves and is the stalk of the inverse image along `s̄` at the canonical point of `Spec Ω`; the
derived base change map `s̄⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` of the cartesian square of the fibre; and the
identification of the stalk at the canonical point of `Spec Ω` of `Rf'_*` with `RΓ(X_s̄, -)`.
Only the base change map is not invertible in general; for `f` proper it is invertible on torsion
sheaves by the proper base change theorem (Stacks 095T).

The derived category, the derived direct image `Rf_*` and the derived stalk are those of the
specialization theorem for smooth proper morphisms (Stacks 0GKD,
`AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper_unconditional`), so the result
can be read directly on the stalks it compares.

## Main definitions

* `AlgebraicGeometry.derivedStalkHomologyToFibreHypercohomology`: the natural map
  `Hⁿ((Rf_* E)_s̄) ⟶ Hⁿ(RΓ(X_s̄, g'⁻¹ E))` on the unbounded derived category of `X_étale`.
* `AlgebraicGeometry.stalkHigherDirectImageToFibreCohomology`: the natural map
  `Hⁿ((Rf_*(F[0]))_s̄) ⟶ Hⁿ(X_s̄, g'⁻¹ F)` on abelian sheaves, in the spelling of the derived
  stalk of Stacks 0GKD.
* `AlgebraicGeometry.stalkRightDerivedPushforwardToFibreCohomology`: the base change
  homomorphism `(Rⁿf_* F)_s̄ ⟶ Hⁿ(X_s̄, g'⁻¹ F)` on the stalk of the classical higher direct
  image.
* `AlgebraicGeometry.stalkHigherDirectImageIsoFibreCohomology`,
  `AlgebraicGeometry.stalkHigherDirectImageNatIsoFibreCohomology`,
  `AlgebraicGeometry.stalkRightDerivedPushforwardNatIsoFibreCohomology`: the resulting
  isomorphisms for `f` proper, objectwise and as natural isomorphisms on torsion sheaves.

## Main results

* `AlgebraicGeometry.isIso_stalkBaseChangeHomomorphism_app`: the proper base change theorem at a
  geometric point, for `f` proper and `F` torsion, for the source's base change homomorphism
  `AlgebraicGeometry.stalkBaseChangeHomomorphism`: global sections over `Spec Ω` of the base
  change homomorphism `AlgebraicGeometry.geometricPointHigherBaseChange` of the fibre square.
* `AlgebraicGeometry.isIso_stalkHigherDirectImageToFibreCohomology_app` and
  `AlgebraicGeometry.isIso_stalkRightDerivedPushforwardToFibreCohomology_app`: the same for the
  natural maps built directly on derived stalks, which give the natural isomorphisms above.

## Implementation notes

The inverse image to the fibre is `Stacks.EtaleCohomology.etaleAbelianInverseImage`, the one in
which the derived base change map is stated;
`AlgebraicGeometry.fibreCohomologyInverseImageIsoPullback` compares the result with the inverse
image `Stacks.EtaleCohomology.smallEtalePullbackAb`. The source's `ℤ/n`-sheaf with `n`
invertible and projective `f` are special cases of a torsion abelian sheaf and a proper `f`.

## References

* [Freitag–Kiehl, *Étale cohomology and the Weil conjecture*, I.6.3]
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The natural map `Hⁿ((Rf_* E)_s̄) ⟶ Hⁿ(RΓ(X_s̄, g'⁻¹ E))` from the cohomology of the derived
stalk at a geometric point `s̄` of a derived direct image to the hypercohomology of the geometric
fibre `X_s̄ = X ×_S Spec Ω`, for an object `E` of the unbounded derived category of `X_étale`.
Every step but the derived base change map of the fibre square is an isomorphism. -/
def derivedStalkHomologyToFibreHypercohomology (n : ℤ) :
    letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (pullback f s)
    smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} n ⟶
      etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f s) ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (Sheaf.Γ (pullback f s).smallEtaleTopology Ab.{u + 1}) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} n :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (pullback f s)
  let can := ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber (A := Ab.{u + 1})
  let D := smallEtaleDerivedPushforwardAb f
  let Hn := fun (Z : Scheme.{u}) ↦
    DerivedCategory.homologyFunctor (Sheaf Z.smallEtaleTopology Ab.{u + 1}) n
  Functor.whiskerLeft D ((smallEtaleStalkAb s).mapDerivedCategoryHomologyIso n).hom ≫
    Functor.whiskerLeft (D ⋙ Hn S)
      ((GrothendieckTopology.Point.sheafFiberUliftNatIso (pointSmallEtale s) Ab.{u + 1}).inv ≫
        (etaleAbelianSheafFiberIsoInverseImageSheafFiber.{u, 0} s).hom) ≫
    Functor.whiskerLeft D (Functor.whiskerRight
      ((etaleAbelianInverseImage.{u, 0} s).mapDerivedCategoryHomologyIso n).inv can) ≫
    Functor.whiskerRight (Functor.whiskerRight
      (etaleAbelianDerivedBaseChange.{u, 0} f s (pullback.fst f s) (pullback.snd f s)
        pullback.condition) (Hn (Spec (.of Ω)))) can ≫
    Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f s) ⋙
        etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f s))
      (can.mapDerivedCategoryHomologyIso n).inv ≫
    Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f s))
      (Functor.whiskerRight
        (etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso.{u, 0}
          (pullback.snd f s)).hom (DerivedCategory.homologyFunctor Ab.{u + 1} n))

/-- The natural map `Hⁿ(RΓ(X_s̄, (g'⁻¹ F)[0])) ≅ Hⁿ(X_s̄, g'⁻¹ F)` comparing the hypercohomology
of the fibre on a sheaf placed in degree `0` with its étale cohomology. -/
def fibreHypercohomologySingleIsoCohomology (n : ℕ) :
    letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (pullback f s)
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0 ⋙
        etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f s) ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (Sheaf.Γ (pullback f s).smallEtaleTopology Ab.{u + 1}) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ) ≅
      etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (pullback f s)
  letI := hasExt_sheaf_smallEtale_succ (pullback f s)
  let Γ' := Sheaf.Γ (pullback f s).smallEtaleTopology Ab.{u + 1}
  Functor.isoWhiskerRight
      ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s)).mapDerivedCategorySingleFunctor 0)
      (Stacks.DerivedFunctor.totalRightDerived Γ' ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (etaleAbelianInverseImage.{u, 0} (pullback.fst f s))
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived Γ'
        (Stacks.DerivedFunctor.totalRightDerived Γ')
        ((Stacks.DerivedFunctor.homotopyMap Γ').totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective n ≪≫
      Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{0}
        (pullback f s).smallEtaleTopology n)

/-- **The base change homomorphism at a geometric point**, `Hⁿ((Rf_* F)_s̄) ⟶ Hⁿ(X_s̄, g'⁻¹ F)`,
natural in the abelian sheaf `F` on `X_étale`: the map
`AlgebraicGeometry.derivedStalkHomologyToFibreHypercohomology` on `F` placed in degree `0`,
followed by the identification of hypercohomology of a sheaf with its étale cohomology. -/
def stalkHigherDirectImageToFibreCohomology (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0 ⋙
        smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ) ⟶
      etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  letI := hasExt_sheaf_smallEtale_succ (pullback f s)
  Functor.whiskerLeft (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
      (derivedStalkHomologyToFibreHypercohomology f s n) ≫
    (fibreHypercohomologySingleIsoCohomology f s n).hom

/-- **Proper base change at a geometric point** (Freitag–Kiehl I.6.3, Stacks 0DDF (1)). For `f`
proper and `F` a torsion abelian sheaf on `X_étale`, the base change homomorphism
`Hⁿ((Rf_* F)_s̄) ⟶ Hⁿ(X_s̄, g'⁻¹ F)` is an isomorphism. -/
theorem isIso_stalkHigherDirectImageToFibreCohomology_app [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    IsIso ((stalkHigherDirectImageToFibreCohomology f s n).app F) := by
  have : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f s (pullback.fst f s) (pullback.snd f s)
      pullback.condition).app ((DerivedCategory.singleFunctor _ 0).obj F)) :=
    cohomologyCommutesWithBaseChange_of_isProper f s (pullback.fst f s) (pullback.snd f s)
      (IsPullback.of_hasPullback f s) F hF
  simp only [stalkHigherDirectImageToFibreCohomology, derivedStalkHomologyToFibreHypercohomology,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have := Functor.map_isIso
    (DerivedCategory.homologyFunctor (Sheaf (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1}) (n : ℤ))
    ((etaleAbelianDerivedBaseChange.{u, 0} f s (pullback.fst f s) (pullback.snd f s)
      pullback.condition).app ((DerivedCategory.singleFunctor _ 0).obj F))
  have := Functor.map_isIso
    (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber (A := Ab.{u + 1}))
    ((DerivedCategory.homologyFunctor (Sheaf (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1})
      (n : ℤ)).map ((etaleAbelianDerivedBaseChange.{u, 0} f s (pullback.fst f s)
        (pullback.snd f s) pullback.condition).app ((DerivedCategory.singleFunctor _ 0).obj F)))
  repeat' first | assumption | infer_instance | apply IsIso.comp_isIso'

/-- **Proper base change at a geometric point**, as an isomorphism
`Hⁿ((Rf_* F)_s̄) ≅ Hⁿ(X_s̄, g'⁻¹ F)` for `f` proper and `F` a torsion abelian sheaf on
`X_étale`; it is the component at `F` of the natural map
`AlgebraicGeometry.stalkHigherDirectImageToFibreCohomology`, so it is natural in `F`
(`AlgebraicGeometry.stalkHigherDirectImageIsoFibreCohomology_hom_naturality`). -/
def stalkHigherDirectImageIsoFibreCohomology [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    (DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ)).obj
        ((smallEtaleDerivedStalkAb s).obj ((smallEtaleDerivedPushforwardAb f).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) ≅
      AddCommGrpCat.of
        (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s)).obj F) n) :=
  @asIso _ _ _ _ ((stalkHigherDirectImageToFibreCohomology f s n).app F)
    (isIso_stalkHigherDirectImageToFibreCohomology_app f s F hF n)

/-- The isomorphism `AlgebraicGeometry.stalkHigherDirectImageIsoFibreCohomology` is the
component of the natural map `AlgebraicGeometry.stalkHigherDirectImageToFibreCohomology`. -/
theorem stalkHigherDirectImageIsoFibreCohomology_hom [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    (stalkHigherDirectImageIsoFibreCohomology f s F hF n).hom =
      (stalkHigherDirectImageToFibreCohomology f s n).app F :=
  rfl

/-- The isomorphism `AlgebraicGeometry.stalkHigherDirectImageIsoFibreCohomology` is natural in
the torsion sheaf. -/
@[reassoc]
theorem stalkHigherDirectImageIsoFibreCohomology_hom_naturality [IsProper f]
    {F G : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (φ : F ⟶ G) (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    (DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ)).map
        ((smallEtaleDerivedStalkAb s).map ((smallEtaleDerivedPushforwardAb f).map
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).map φ))) ≫
        (stalkHigherDirectImageIsoFibreCohomology f s G hG n).hom =
      (stalkHigherDirectImageIsoFibreCohomology f s F hF n).hom ≫
        (Sheaf.functorH (pullback f s).smallEtaleTopology n).map
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s)).map φ) :=
  (stalkHigherDirectImageToFibreCohomology f s n).naturality φ

/-- **Proper base change at a geometric point**, as a natural isomorphism of functors on the
torsion abelian sheaves on `X_étale`: `Hⁿ((Rf_* F)_s̄) ≅ Hⁿ(X_s̄, g'⁻¹ F)`. -/
def stalkHigherDirectImageNatIsoFibreCohomology [IsProper f] (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι ⋙
        DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0 ⋙
        smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ) ≅
      (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι ⋙
        etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  letI := hasExt_sheaf_smallEtale_succ (pullback f s)
  letI : IsIso (Functor.whiskerLeft (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι
      (stalkHigherDirectImageToFibreCohomology f s n)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F ↦
      isIso_stalkHigherDirectImageToFibreCohomology_app f s F.obj F.property n
  asIso (Functor.whiskerLeft (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι
    (stalkHigherDirectImageToFibreCohomology f s n))

/-- The stalk at `s̄` of the classical higher direct image `Rⁿf_* F` is the `n`-th cohomology of
the derived stalk at `s̄` of `Rf_*(F[0])`, naturally in `F`: the stalk is exact, so it commutes
with cohomology, and `Hⁿ(Rf_*(F[0])) = Rⁿf_* F`. -/
def stalkRightDerivedPushforwardIsoDerivedStalkHomology (n : ℕ) :
    (smallEtalePushforwardAb f).rightDerived n ⋙ smallEtaleStalkAb s ≅
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0 ⋙
        smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ) :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (smallEtalePushforwardAb f) (smallEtaleDerivedPushforwardAb f)
        (smallEtaleDerivedPushforwardAbUnit f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective n).symm (smallEtaleStalkAb s) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0 ⋙
        smallEtaleDerivedPushforwardAb f)
      ((smallEtaleStalkAb s).mapDerivedCategoryHomologyIso n).symm

/-- **The base change homomorphism `(Rⁿf_* F)_s̄ ⟶ Hⁿ(X_s̄, g'⁻¹ F)` at a geometric point**, on the
stalk of the classical higher direct image, natural in the abelian sheaf `F` on `X_étale`: the
identification `AlgebraicGeometry.stalkRightDerivedPushforwardIsoDerivedStalkHomology` followed
by `AlgebraicGeometry.stalkHigherDirectImageToFibreCohomology`. -/
def stalkRightDerivedPushforwardToFibreCohomology (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    (smallEtalePushforwardAb f).rightDerived n ⋙ smallEtaleStalkAb s ⟶
      etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  (stalkRightDerivedPushforwardIsoDerivedStalkHomology f s n).hom ≫
    stalkHigherDirectImageToFibreCohomology f s n

/-- **Proper base change at a geometric point** (Freitag–Kiehl I.6.3, Stacks 0DDF (1)). Let
`f : X ⟶ S` be proper, `s̄ : Spec Ω ⟶ S` a geometric point with geometric fibre
`X_s̄ = X ×_S Spec Ω` and projection `g' : X_s̄ ⟶ X`, and `F` a torsion abelian sheaf on
`X_étale`. Then for every `n` the base change homomorphism `(Rⁿf_* F)_s̄ ⟶ Hⁿ(X_s̄, g'⁻¹ F)` is an
isomorphism. -/
theorem isIso_stalkRightDerivedPushforwardToFibreCohomology_app [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    IsIso ((stalkRightDerivedPushforwardToFibreCohomology f s n).app F) := by
  have := isIso_stalkHigherDirectImageToFibreCohomology_app f s F hF n
  dsimp only [stalkRightDerivedPushforwardToFibreCohomology]
  rw [NatTrans.comp_app]
  infer_instance

/-- **Proper base change at a geometric point**, as a natural isomorphism of functors on the
torsion abelian sheaves on `X_étale`: `(Rⁿf_* F)_s̄ ≅ Hⁿ(X_s̄, g'⁻¹ F)`. -/
def stalkRightDerivedPushforwardNatIsoFibreCohomology [IsProper f] (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι ⋙
        (smallEtalePushforwardAb f).rightDerived n ⋙ smallEtaleStalkAb s ≅
      (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι ⋙
        etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  letI := hasExt_sheaf_smallEtale_succ (pullback f s)
  letI : IsIso (Functor.whiskerLeft (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι
      (stalkRightDerivedPushforwardToFibreCohomology f s n)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F ↦
      isIso_stalkRightDerivedPushforwardToFibreCohomology_app f s F.obj F.property n
  asIso (Functor.whiskerLeft (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).ι
    (stalkRightDerivedPushforwardToFibreCohomology f s n))

/-- The cohomology of the fibre, with the inverse image of `F` along `g' : X_s̄ ⟶ X` taken as the
left adjoint `Stacks.EtaleCohomology.smallEtalePullbackAb` of direct image rather than as
`Stacks.EtaleCohomology.etaleAbelianInverseImage`: the two inverse images are isomorphic. -/
def fibreCohomologyInverseImageIsoPullback (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n ≅
      smallEtalePullbackAb (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  letI := hasExt_sheaf_smallEtale_succ (pullback f s)
  Functor.isoWhiskerRight (smallEtalePullbackAbIsoEtaleAbelianInverseImage (pullback.fst f s)).symm
    (Sheaf.functorH (pullback f s).smallEtaleTopology n)

/-! ### The base change homomorphism of the source, at a geometric point -/

/-- The base change homomorphism `s̄⁻¹(Rⁿf_* F) ⟶ Rⁿf'_*(g'⁻¹ F)` of the cartesian square of the
geometric fibre, `f' : X_s̄ ⟶ Spec Ω`: the canonical degree-`n` base change map
`Stacks.EtaleCohomology.etaleAbelianHigherBaseChange` read on classical higher direct images. By
`Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChange_eq` it is the base change
homomorphism computed from resolutions. -/
def geometricPointHigherBaseChange (n : ℕ) :
    (smallEtalePushforwardAb f).rightDerived n ⋙ etaleAbelianInverseImage.{u, 0} s ⟶
      etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        (smallEtalePushforwardAb (pullback.snd f s)).rightDerived n :=
  (etaleAbelianHigherBaseChangeSourceIso.{u, 0} f s n).inv ≫
    etaleAbelianHigherBaseChange.{u, 0} f s (pullback.fst f s) (pullback.snd f s)
      pullback.condition n ≫
    (etaleAbelianHigherBaseChangeTargetIso.{u, 0} (pullback.fst f s) (pullback.snd f s) n).hom

omit [IsSepClosed Ω] in
/-- For `f` proper and `F` torsion, the base change homomorphism of the geometric fibre square is
an isomorphism of sheaves on `Spec Ω` (proper base change, Stacks 095T). -/
theorem isIso_geometricPointHigherBaseChange_app [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    IsIso ((geometricPointHigherBaseChange f s n).app F) := by
  have : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f s (pullback.fst f s) (pullback.snd f s)
      pullback.condition).app ((DerivedCategory.singleFunctor _ 0).obj F)) :=
    cohomologyCommutesWithBaseChange_of_isProper f s (pullback.fst f s) (pullback.snd f s)
      (IsPullback.of_hasPullback f s) F hF
  have := Functor.map_isIso
    (DerivedCategory.homologyFunctor (Sheaf (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1}) (n : ℤ))
    ((etaleAbelianDerivedBaseChange.{u, 0} f s (pullback.fst f s) (pullback.snd f s)
      pullback.condition).app ((DerivedCategory.singleFunctor _ 0).obj F))
  exact IsIso.comp_isIso'
    (Iso.isIso_hom ((etaleAbelianHigherBaseChangeSourceIso.{u, 0} f s n).app F).symm)
    (IsIso.comp_isIso' this (Iso.isIso_hom
      ((etaleAbelianHigherBaseChangeTargetIso.{u, 0} (pullback.fst f s) (pullback.snd f s) n).app
        F)))

/-- The stalk at a geometric point `s̄` is global sections over `Spec Ω` of the inverse image
along `s̄`. -/
def smallEtaleStalkAbIsoInverseImageGamma :
    smallEtaleStalkAb s ≅
      etaleAbelianInverseImage.{u, 0} s ⋙ Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1} :=
  (GrothendieckTopology.Point.sheafFiberUliftNatIso (pointSmallEtale s) Ab.{u + 1}).symm ≪≫
    etaleAbelianSheafFiberIsoInverseImageGamma.{u, 0} s

/-- For a morphism `f' : X' ⟶ Spec Ω` to the spectrum of a separably closed field, global
sections of `Rⁿf'_* G` are the étale cohomology `Hⁿ(X', G)`, naturally in `G`. -/
def directImageRightDerivedGammaIsoCohomology {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of Ω))
    (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ X'
    (smallEtalePushforwardAb f').rightDerived n ⋙
        Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1} ≅
      Sheaf.functorH X'.smallEtaleTopology n :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X'
  letI := hasExt_sheaf_smallEtale_succ X'
  let can := ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber (A := Ab.{u + 1})
  let Γ' := Sheaf.Γ X'.smallEtaleTopology Ab.{u + 1}
  Functor.isoWhiskerLeft _ (sheafFiberUliftIdIsoGamma.{u, 0} Ω).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (smallEtalePushforwardAb f') (smallEtaleDerivedPushforwardAb f')
        (smallEtaleDerivedPushforwardAbUnit f')
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective n).symm can ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology Ab.{u + 1}) 0 ⋙
        smallEtaleDerivedPushforwardAb f')
      (can.mapDerivedCategoryHomologyIso n).symm ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology Ab.{u + 1}) 0)
      (Functor.isoWhiskerRight
        (etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso.{u, 0} f')
        (DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ))) ≪≫
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived Γ'
        (Stacks.DerivedFunctor.totalRightDerived Γ')
        ((Stacks.DerivedFunctor.homotopyMap Γ').totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective n ≪≫
    Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{0} X'.smallEtaleTopology n

/-- **The base change homomorphism `(Rⁿf_* F)_s̄ ⟶ Hⁿ(X_s̄, F_s̄)` at a geometric point**, as the
source defines it: the map on global sections over `Spec Ω` of the base change homomorphism
`AlgebraicGeometry.geometricPointHigherBaseChange` of the geometric fibre square, read through
the identification of the stalk at `s̄` with global sections of the inverse image along `s̄`
(`AlgebraicGeometry.smallEtaleStalkAbIsoInverseImageGamma`) and of global sections of
`Rⁿf'_*` with cohomology of the fibre
(`AlgebraicGeometry.directImageRightDerivedGammaIsoCohomology`). -/
def stalkBaseChangeHomomorphism (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f s)
    (smallEtalePushforwardAb f).rightDerived n ⋙ smallEtaleStalkAb s ⟶
      etaleAbelianInverseImage.{u, 0} (pullback.fst f s) ⋙
        Sheaf.functorH (pullback f s).smallEtaleTopology n :=
  letI := hasExt_sheaf_smallEtale_succ (pullback f s)
  Functor.whiskerLeft ((smallEtalePushforwardAb f).rightDerived n)
      (smallEtaleStalkAbIsoInverseImageGamma s).hom ≫
    Functor.whiskerRight (geometricPointHigherBaseChange f s n)
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1}) ≫
    Functor.whiskerLeft (etaleAbelianInverseImage.{u, 0} (pullback.fst f s))
      (directImageRightDerivedGammaIsoCohomology (pullback.snd f s) n).hom

/-- **Proper base change at a geometric point** (Freitag–Kiehl I.6.3). Let `f : X ⟶ S` be
proper, `s̄ : Spec Ω ⟶ S` a geometric point with geometric fibre `X_s̄ = X ×_S Spec Ω` and
projection `g' : X_s̄ ⟶ X`, and `F` a torsion abelian sheaf on `X_étale`. Then for every `n` the
base change homomorphism `(Rⁿf_* F)_s̄ ⟶ Hⁿ(X_s̄, g'⁻¹ F)` is an isomorphism. -/
@[weil "thm_fk106_proper_base_change_geometric_fiber"]
theorem isIso_stalkBaseChangeHomomorphism_app [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    IsIso ((stalkBaseChangeHomomorphism f s n).app F) := by
  have := isIso_geometricPointHigherBaseChange_app f s F hF n
  have := Functor.map_isIso (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology Ab.{u + 1})
    ((geometricPointHigherBaseChange f s n).app F)
  simp only [stalkBaseChangeHomomorphism, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

end AlgebraicGeometry
