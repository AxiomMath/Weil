module

public import Weil.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Unconditional
public import Weil.Attr

/-!
# The condition that base change holds for a pair of morphisms

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, `X_T = X ×_S T`, and
`f' : X_T ⟶ T`, `g' : X_T ⟶ X` the projections. *Base change holds for `(f, g)`*, written
`BC(f, g)`, if for every abelian sheaf `F` on the small étale site of `X` which is torsion prime
to the residue characteristics of `S` and every `i ≥ 0`, the base change homomorphism
$$ g^{-1} R^i f_* F ⟶ R^i f'_* (g'^{-1} F) $$
is an isomorphism. The smooth base change theorem says that `BC(f, g)` holds when `g` is smooth
and `f` is quasi-compact and quasi-separated.

## Main definitions

* `AlgebraicGeometry.SmallEtale.SatisfiesBaseChange`: the condition `BC(f, g)`.

## Main results

* `AlgebraicGeometry.SmallEtale.satisfiesBaseChange_iff_higherBaseChangeMapAb`: the condition
  in terms of the base change map `Stacks.EtaleCohomology.higherBaseChangeMapAb` on Mathlib's
  small étale sites and the torsion condition
  `Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn`.
* `AlgebraicGeometry.SmallEtale.satisfiesBaseChange_of_smooth`: `BC(f, g)` holds for `g` smooth
  and `f` quasi-compact and quasi-separated.

## Implementation notes

The fibre product is not fixed: the condition is asked of every cartesian square
`IsPullback f' g' g f`. Since any two fibre products are uniquely isomorphic, this is the same as
asking it of one of them. The base change homomorphism is
`AlgebraicGeometry.SmallEtale.higherBaseChangeMap`, and torsion prime to the residue
characteristics of `S` is `AlgebraicGeometry.SmallEtale.IsTorsionPrimeToResidueCharacteristics`.
Freitag and Kiehl assume `X`, `S`, `T` and `X_T` noetherian; the definition makes sense, and is
stated, for arbitrary schemes, and agrees with theirs under those hypotheses.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7][FreitagKiehl]
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X S T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)

/-- **Base change holds for `(f, g)`.** For morphisms `f : X ⟶ S` and `g : T ⟶ S`, the condition
`BC(f, g)`: for every cartesian square
```
X_T --g'--> X
 |f'        |f
 v          v
 T  --g---> S
```
every abelian sheaf `F` on the small étale site of `X` which is torsion prime to the residue
characteristics of `S` and every `i ≥ 0`, the base change homomorphism
`g⁻¹ R^i f_* F ⟶ R^i f'_* (g')⁻¹ F` is an isomorphism. -/
@[weil "def_fk107_sbc_holds"]
def SatisfiesBaseChange (f : X ⟶ S) (g : T ⟶ S) : Prop :=
  ∀ ⦃XT : Scheme.{u}⦄ (f' : XT ⟶ T) (g' : XT ⟶ X) (sq : IsPullback f' g' g f)
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1}),
    IsTorsionPrimeToResidueCharacteristics B X hX S F →
      ∀ i : ℕ, IsIso (higherBaseChangeMap B hX hT f g f' g' sq.w i F)

variable {B hX hT}

/-- Unfolding `BC(f, g)`: the base change homomorphism of a cartesian square is an isomorphism
at every sheaf which is torsion prime to the residue characteristics of `S`. -/
theorem SatisfiesBaseChange.isIso {f : X ⟶ S} {g : T ⟶ S}
    (h : SatisfiesBaseChange B hX hT f g) {XT : Scheme.{u}} {f' : XT ⟶ T} {g' : XT ⟶ X}
    (sq : IsPullback f' g' g f) {F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1}}
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) (i : ℕ) :
    IsIso (higherBaseChangeMap B hX hT f g f' g' sq.w i F) :=
  h f' g' sq F hF i

/-- A sheaf torsion prime to the residue characteristics of `S` on the small étale site
corresponds on Mathlib's small étale site to one with torsion of orders invertible on `S`. -/
theorem IsTorsionPrimeToResidueCharacteristics.hasTorsionOrdersInvertibleOn_sheafEquiv_functor_obj
    {F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1}}
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) :
    HasTorsionOrdersInvertibleOn S ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F) :=
  (isTorsionPrimeToResidueCharacteristics_toEtaleSite_iff _).mp
    (hF.of_iso ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).unitIso.app F))

/-- The base change homomorphism on the small étale sites is an isomorphism when the base change
map on Mathlib's small étale sites is one at the corresponding sheaf. -/
theorem isIso_higherBaseChangeMap_of_isIso_app {f : X ⟶ S} {g : T ⟶ S} {XT : Scheme.{u}}
    {f' : XT ⟶ T} {g' : XT ⟶ X} (sq : IsPullback f' g' g f)
    {F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1}} (i : ℕ)
    (h : IsIso ((higherBaseChangeMapAb g f f' g' sq.w i).app
      ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F))) :
    IsIso (higherBaseChangeMap B hX hT f g f' g' sq.w i F) :=
  Functor.map_isIso (sheafEquiv B T hT AddCommGrpCat.{u + 1}).inverse _

/-- Conversely, `BC(f, g)` gives invertibility of the base change map on Mathlib's small étale
sites at every sheaf with torsion of orders invertible on `S`. -/
theorem isIso_higherBaseChangeMapAb_app_of_satisfiesBaseChange {f : X ⟶ S} {g : T ⟶ S}
    (h : SatisfiesBaseChange B hX hT f g) {XT : Scheme.{u}} {f' : XT ⟶ T} {g' : XT ⟶ X}
    (sq : IsPullback f' g' g f) {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : HasTorsionOrdersInvertibleOn S G) (i : ℕ) :
    IsIso ((higherBaseChangeMapAb g f f' g' sq.w i).app G) := by
  let EX := sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have hF : IsTorsionPrimeToResidueCharacteristics B X hX S (EX.inverse.obj G) :=
    (isTorsionPrimeToResidueCharacteristics_toEtaleSite_iff G).mpr hG
  have h1 : IsIso ((sheafEquiv B T hT AddCommGrpCat.{u + 1}).inverse.map
      ((higherBaseChangeMapAb g f f' g' sq.w i).app (EX.functor.obj (EX.inverse.obj G)))) :=
    h f' g' sq _ hF i
  have h2 : IsIso
      ((higherBaseChangeMapAb g f f' g' sq.w i).app (EX.functor.obj (EX.inverse.obj G))) :=
    isIso_of_reflects_iso _ (sheafEquiv B T hT AddCommGrpCat.{u + 1}).inverse
  exact (NatTrans.isIso_app_iff_of_iso _ (EX.counitIso.app G)).mp h2

/-- **`BC(f, g)` on Mathlib's small étale sites.** Base change holds for `(f, g)` if and only if,
for every cartesian square, the base change map `Stacks.EtaleCohomology.higherBaseChangeMapAb`
is an isomorphism at every abelian sheaf on Mathlib's small étale site of `X` with torsion of
orders invertible on `S`. -/
theorem satisfiesBaseChange_iff_higherBaseChangeMapAb (f : X ⟶ S) (g : T ⟶ S) :
    SatisfiesBaseChange B hX hT f g ↔
      ∀ ⦃XT : Scheme.{u}⦄ (f' : XT ⟶ T) (g' : XT ⟶ X) (sq : IsPullback f' g' g f)
        (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        HasTorsionOrdersInvertibleOn S G →
          ∀ i : ℕ, IsIso ((higherBaseChangeMapAb g f f' g' sq.w i).app G) := by
  constructor
  · intro h XT f' g' sq G hG i
    exact isIso_higherBaseChangeMapAb_app_of_satisfiesBaseChange h sq hG i
  · intro h XT f' g' sq F hF i
    exact isIso_higherBaseChangeMap_of_isIso_app sq i
      (h f' g' sq _ hF.hasTorsionOrdersInvertibleOn_sheafEquiv_functor_obj i)

/-- **Smooth base change gives `BC(f, g)`.** If `g` is smooth and `f` is quasi-compact and
quasi-separated, base change holds for `(f, g)`. -/
theorem satisfiesBaseChange_of_smooth (f : X ⟶ S) (g : T ⟶ S) [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] : SatisfiesBaseChange B hX hT f g :=
  fun _ f' g' sq F hF i ↦ isIso_higherBaseChangeMap_of_smooth hT f g f' g' sq F hF i

end AlgebraicGeometry.SmallEtale

end
