module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ZModForgetConstructible
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The free sheaf of `ℤ/nℤ`-modules on a constructible sheaf of sets is constructible

Let `n ≥ 1`, `Λ = ℤ/nℤ`, `Y` a scheme and `M` a constructible sheaf of sets on the small étale
site of `Y`. The free sheaf of `Λ`-modules `M^Λ`, the sheafification of the presheaf
`U ↦ Λ^(M(U))`, is then a constructible sheaf of abelian groups on `Y`.

On every affine open of `Y` the stratification on whose strata the inverse image of `M` is finite
locally constant also serves for `M^Λ`: the free module sheaf commutes with inverse image to a
stratum, and on a stratum it carries a finite locally constant sheaf of sets to a locally constant
sheaf of `Λ`-modules whose constant values `Λ^(E)` are free on a finite set, hence finite. The
underlying abelian sheaf of a constructible sheaf of `ℤ/nℤ`-modules is constructible.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_freeZModModuleSheaf`: the underlying sheaf of
  abelian groups of `M^Λ`, `Λ = ℤ/nℤ`, is constructible.
* `AlgebraicGeometry.isConstructibleModuleSheaf_freeZModModuleSheaf`: `M^Λ` is a constructible
  sheaf of `Λ`-modules.

## Implementation notes

Sheaves on the small étale site of a scheme in universe `u` take values in `Type (u + 1)`, while
`ZMod n : Type`. The free module `Λ^(E)` on a type `E : Type (u + 1)` is therefore the copower
`ModuleCat.copower (ModuleCat.of (ZMod n) (ULift (ZMod n)))`, i.e. `E →₀ ULift (ZMod n)`, which
is the free `ℤ/nℤ`-module functor with the universe of the ring released (`ModuleCat.free`
requires the ring to live in the universe of the modules). The sheaf `M^Λ` is
`CategoryTheory.Sheaf.composeAndSheafify` of that functor.

The proof does not go through the generic-point criterion used in [FK]: the definition of
constructibility used here (Stacks, Tag 03RW) is by finite stratifications of affine opens, and
the free module sheaf preserves each ingredient of that definition directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The direct image of sheaves of modules over a ring `Λ : Type` with values in
`ModuleCat.{u + 1} Λ` along small étale base change is a right adjoint:
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCat` at the module universe `u + 1`,
where instance search cannot solve `max (u + 1) ?r = u + 1`. -/
@[local instance]
theorem SmallEtale.isRightAdjointPushforward_moduleCatSucc (B : BigEtaleSite.{u}) (Λ : Type)
    [CommRing Λ] {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1, 0} B Λ f

/-- Sheaves of modules over a ring `Λ : Type` with values in `ModuleCat.{u + 1} Λ` on the
localizations of a small étale site admit sheafification:
`AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCat` at the module universe `u + 1`. -/
@[local instance]
theorem SmallEtale.hasWeakSheafifyOver_moduleCatSucc (B : BigEtaleSite.{u}) (Λ : Type)
    [CommRing Λ] (T : B.Scheme) (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ) :=
  SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, 0} B Λ T V

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (n : ℕ) [NeZero n]

/-- The free sheaf of `ℤ/nℤ`-modules `M^Λ` on a sheaf of sets `M` on the small étale site of
`X`, with `Λ = ℤ/nℤ`: the sheafification of `U ↦ Λ^(M(U))`. -/
abbrev freeZModModuleSheaf :
    Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n)) :=
  Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
    (ModuleCat.copower (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))

/-- **The free sheaf of `ℤ/nℤ`-modules on a constructible sheaf of sets is a constructible sheaf
of `ℤ/nℤ`-modules.** -/
theorem isConstructibleModuleSheaf_freeZModModuleSheaf
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hM : IsConstructibleSetSheaf B X M) :
    IsConstructibleModuleSheaf B X (ZMod n) ((freeZModModuleSheaf B X n).obj M) :=
  isConstructibleModuleSheaf_composeAndSheafify_copower.{u, 0} B X (ZMod n)
    (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) M hM

/-- **The free sheaf of `ℤ/nℤ`-modules on a constructible sheaf of sets is constructible.** For
`n ≥ 1`, `Λ = ℤ/nℤ` and a constructible sheaf of sets `M` on the small étale site of a scheme
`X`, the sheaf `M^Λ` is a constructible sheaf of abelian groups on `X`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_constructible"]
theorem isConstructibleAbelianSheaf_freeZModModuleSheaf
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hM : IsConstructibleSetSheaf B X M) :
    IsConstructibleAbelianSheaf B X
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj
        ((freeZModModuleSheaf B X n).obj M)) :=
  isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_zmod.{u, 0} B n X _
    (isConstructibleModuleSheaf_freeZModModuleSheaf B X n M hM)

end AlgebraicGeometry

end

/-! ### Representable étale sheaves are constructible -/

/-!
# Representable étale sheaves are constructible

Let `X` be a scheme and `U ⟶ X` an étale morphism. The sheaf of sets `h_U : V ↦ Hom_X(V, U)` on
the small étale site of `X` is constructible as soon as `X` and `U` are quasi-compact and
quasi-separated; in particular this holds for every object `U` of the category `Et(X)` of
noetherian separated étale `X`-schemes over a noetherian scheme `X`.

## Main results

* `AlgebraicGeometry.SmallEtale.isConstructibleSetSheaf_representableSheaf`: for `X` and `U`
  quasi-compact and quasi-separated, the sheaf `h_U` is constructible.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isConstructibleSetSheaf_representableSheaf`:
  for `X` noetherian and `U` in `Et(X)`, the sheaf `h_U` is constructible.

## Implementation notes

Constructible sheaves of sets on the small étale site are sheaves with values in `Type (u + 1)`,
the universe of the objects of the site, while `h_U` takes values in `Type u`, the universe of
its morphisms. The statement is therefore about `h_U` composed with `uliftFunctor`, which is the
Yoneda sheaf `uliftYoneda` of the subcanonical small étale site, i.e. the sheafified
representable sheaf of Stacks 03S8.

The proof of [FK] verifies the generic-point criterion of constructibility using a generic
splitting of étale schemes and topological invariance of the étale site; here the result is
deduced from Stacks 03S8 (1), whose proof goes through the finite étale stratification of
Stacks 03S0 instead.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The sheaf `h_U` composed with `uliftFunctor` is the sheafified representable sheaf of `U`. -/
noncomputable def sheafifiedYonedaIsoRepresentableSheafUlift
    (U : SmallEtale B X.obj X.property) :
    (Sheaf.sheafifiedYoneda (topology B X.obj X.property)).obj U ≅
      (sheafCompose (topology B X.obj X.property) uliftFunctor.{u + 1, u}).obj
        ((representableSheaf B X.obj X.property).obj U) :=
  (Sheaf.sheafifiedYonedaIsoUliftYoneda' (topology B X.obj X.property)).app U ≪≫
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerRight
        ((sheafToPresheaf _ _).mapIso ((representableSheafIsoYoneda B X.obj X.property).app U))
        uliftFunctor.{u + 1, u}).symm

/-- **Representable étale sheaves are constructible.** For an étale morphism `U ⟶ X` of
quasi-compact quasi-separated schemes, the sheaf of sets `h_U : V ↦ Hom_X(V, U)` on the small
étale site of `X` is constructible. -/
@[weil "lem_fk104_representable_sheaf_constructible"]
theorem isConstructibleSetSheaf_representableSheaf
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleSetSheaf B X
      ((sheafCompose (topology B X.obj X.property) uliftFunctor.{u + 1, u}).obj
        ((representableSheaf B X.obj X.property).obj U)) :=
  isConstructibleSetSheaf_congr B X (sheafifiedYonedaIsoRepresentableSheafUlift B X U)
    (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X U)

end SmallEtale

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Representable étale sheaves are constructible.** Let `X` be a noetherian scheme and
`U ⟶ X` an object of `Et(X)`. The sheaf of sets `h_U : V ↦ Hom_X(V, U)` on the small étale site
of `X` is constructible. -/
@[weil "lem_fk104_representable_sheaf_constructible"]
theorem isConstructibleSetSheaf_representableSheaf [IsNoetherian X.obj]
    (U : SmallNoetherianSeparatedEtale B X.obj X.property) :
    IsConstructibleSetSheaf B X
      ((sheafCompose (SmallEtale.topology B X.obj X.property) uliftFunctor.{u + 1, u}).obj
        ((SmallEtale.representableSheaf B X.obj X.property).obj
          ((inclusion B X.obj X.property).obj U))) := by
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  have : CompactSpace ((inclusion B X.obj X.property).obj U).obj.left.obj :=
    (inferInstance : CompactSpace ((toScheme B X.obj X.property).obj U))
  have : QuasiSeparatedSpace ((inclusion B X.obj X.property).obj U).obj.left.obj :=
    (IsLocallyNoetherian.quasiSeparatedSpace :
      QuasiSeparatedSpace ((toScheme B X.obj X.property).obj U))
  exact SmallEtale.isConstructibleSetSheaf_representableSheaf B X _

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry
