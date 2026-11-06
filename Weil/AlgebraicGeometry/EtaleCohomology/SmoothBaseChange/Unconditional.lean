module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Unconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import Weil.AlgebraicGeometry.Morphisms.Smooth
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Attr
public import StacksFrontier.RingTheory.Excellent.Basic

/-!
# The smooth base change theorem on the small étale site

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, `X_T = X ×_S T`, with projections
`f' : X_T ⟶ T` and `g' : X_T ⟶ X`. If `g` is smooth and `f` is quasi-compact and
quasi-separated (for instance if `X` is noetherian), then for every abelian sheaf `F` on the
small étale site of `X` which is torsion prime to the residue characteristics of `S` and every
`i ≥ 0`, the base change homomorphism `g⁻¹ R^i f_* F ⟶ R^i f'_* (g')⁻¹ F` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.SmallEtale.higherBaseChangeMap`: the base change homomorphism
  `g⁻¹ R^i f_* F ⟶ R^i f'_* (g')⁻¹ F` for an abelian sheaf `F` on the small étale site
  `AlgebraicGeometry.SmallEtale` of `X`, as a morphism of sheaves on the small étale site of `T`.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_higherBaseChangeMap_of_smooth`: the smooth base change
  theorem, for `f` quasi-compact and quasi-separated.
* `AlgebraicGeometry.SmallEtale.isIso_higherBaseChangeMap_of_smooth_of_isNoetherian`: the same
  for morphisms of noetherian schemes, in the form of Freitag and Kiehl.

## Implementation notes

Inverse and direct images and their derived functors are those of Mathlib's small étale sites
`Scheme.smallEtaleTopology`. The base change homomorphism on the small étale site
`AlgebraicGeometry.SmallEtale` is the one on Mathlib's sites,
`Stacks.EtaleCohomology.higherBaseChangeMapAb`, carried along the equivalences of sheaf
categories `AlgebraicGeometry.SmallEtale.sheafEquiv`. The theorem is
[Stacks, Theorem 0EYU],
`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth`, where the
roles of the two morphisms are exchanged. Its torsion hypothesis, on the stalks at
geometric points, follows from the local one
`AlgebraicGeometry.SmallEtale.IsTorsionPrimeToResidueCharacteristics`. Freitag and Kiehl assume
all schemes noetherian; only the quasi-compactness and quasi-separatedness of `f` are used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7][FreitagKiehl]
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X S T XT : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)

/-- **The base change homomorphism** `g⁻¹ R^i f_* F ⟶ R^i f'_* (g')⁻¹ F` of a commutative square
`f' ≫ g = g' ≫ f`, for an abelian sheaf `F` on the small étale site of `X`: the base change map
`Stacks.EtaleCohomology.higherBaseChangeMapAb` on Mathlib's small étale sites, carried to the
small étale sites `AlgebraicGeometry.SmallEtale` of `X` and `T` by
`AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
def higherBaseChangeMap (f : X ⟶ S) (g : T ⟶ S) (f' : XT ⟶ T) (g' : XT ⟶ X)
    (w : f' ≫ g = g' ≫ f) (i : ℕ) (F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1}) :
    (sheafEquiv B T hT AddCommGrpCat.{u + 1}).inverse.obj
        (((smallEtalePushforwardAb f).rightDerived i ⋙ smallEtalePullbackAb g).obj
          ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F)) ⟶
      (sheafEquiv B T hT AddCommGrpCat.{u + 1}).inverse.obj
        ((smallEtalePullbackAb g' ⋙ (smallEtalePushforwardAb f').rightDerived i).obj
          ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F)) :=
  (sheafEquiv B T hT AddCommGrpCat.{u + 1}).inverse.map
    ((higherBaseChangeMapAb g f f' g' w i).app
      ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F))

variable {B hX}

/-- A sheaf on the small étale site of `X` which is torsion prime to the residue characteristics
of `S` corresponds, on Mathlib's small étale site, to one whose stalks at all geometric points
are torsion of orders invertible on `S`. -/
theorem IsTorsionPrimeToResidueCharacteristics.exists_nsmul_eq_zero_smallEtaleStalkAb
    {F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1}}
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) (t : GeometricPoint X)
    (a : ↑((smallEtaleStalkAb t.hom).obj
      ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F))) :
    ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0 := by
  let E := sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have h : IsTorsionPrimeToResidueCharacteristics B X hX S (E.inverse.obj (E.functor.obj F)) :=
    hF.of_iso (E.unitIso.app F)
  exact ((isTorsionPrimeToResidueCharacteristics_toEtaleSite_iff (E.functor.obj F)).mp h)
    |>.exists_nsmul_eq_zero_smallEtaleStalkAb t a

/-- **The smooth base change theorem** ([Stacks, Theorem 0EYU]). Let `f : X ⟶ S` be
quasi-compact and quasi-separated, `g : T ⟶ S` smooth, and `X_T` a fibre product of `f` and `g`
with projections `f' : X_T ⟶ T` and `g' : X_T ⟶ X`. For every abelian sheaf `F` on the small
étale site of `X` which is torsion prime to the residue characteristics of `S` and every `i`, the
base change homomorphism `g⁻¹ R^i f_* F ⟶ R^i f'_* (g')⁻¹ F` is an isomorphism. -/
theorem isIso_higherBaseChangeMap_of_smooth (f : X ⟶ S) (g : T ⟶ S) (f' : XT ⟶ T)
    (g' : XT ⟶ X) (sq : IsPullback f' g' g f) [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1})
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) (i : ℕ) :
    IsIso (higherBaseChangeMap B hX hT f g f' g' sq.w i F) := by
  have := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth g f' g' f sq
    ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj F)
    (hF.exists_nsmul_eq_zero_smallEtaleStalkAb) i
  unfold higherBaseChangeMap
  infer_instance

/-- **The smooth base change theorem for noetherian schemes.** Let `f : X ⟶ S` and `g : T ⟶ S`
be morphisms of noetherian schemes with `X_T = X ×_S T` noetherian, and `f' : X_T ⟶ T`,
`g' : X_T ⟶ X` the projections. If `g` is smooth and `F` is an abelian sheaf on the small étale
site of `X` which is torsion prime to the residue characteristics of `S`, then for every `i ≥ 0`
the base change homomorphism `g⁻¹ R^i f_* F ⟶ R^i f'_* (g')⁻¹ F` is an isomorphism. -/
@[weil "thm_fk107_smooth_base_change"]
theorem isIso_higherBaseChangeMap_of_smooth_of_isNoetherian [IsNoetherian X] [IsNoetherian S]
    [IsNoetherian T] [IsNoetherian XT] (f : X ⟶ S) (g : T ⟶ S) (f' : XT ⟶ T) (g' : XT ⟶ X)
    (sq : IsPullback f' g' g f) [Smooth g]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u + 1})
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) (i : ℕ) :
    IsIso (higherBaseChangeMap B hX hT f g f' g' sq.w i F) := by
  have hS : QuasiSeparatedSpace S :=
    @IsLocallyNoetherian.quasiSeparatedSpace S ‹IsNoetherian S›.toIsLocallyNoetherian
  have hXs : QuasiSeparatedSpace X :=
    @IsLocallyNoetherian.quasiSeparatedSpace X ‹IsNoetherian X›.toIsLocallyNoetherian
  have hXc : CompactSpace X := ‹IsNoetherian X›.toCompactSpace
  have hqc : QuasiCompact f := @quasiCompact_of_compactSpace _ _ f hXc hS
  have hqs : QuasiSeparated f := @QuasiSeparated.of_quasiSeparatedSpace _ _ f hXs
  exact @isIso_higherBaseChangeMap_of_smooth B X S T XT hX hT f g f' g' sq ‹_› hqc hqs F hF i

end AlgebraicGeometry.SmallEtale

end

/-! ### Smooth base change for étale morphisms over bases of bounded dimension -/

/-!
# Smooth base change for étale morphisms over bases of bounded dimension

Freitag and Kiehl prove the smooth base change theorem by induction on the dimension of the
base. For an integer `r ≥ -1` let `SBC_r` be the assertion: for every noetherian scheme `S` of
dimension `≤ r` all of whose local rings are excellent, every étale morphism `f : X ⟶ S` (of
finite type), every smooth morphism `g : T ⟶ S` all of whose fibres have dimension `≤ 1`, every
abelian sheaf `F` on `X_ét` which is torsion prime to the residue characteristics of `S` and
every `i ≥ 0`, the base change map
$$ g^* R^i f_* F ⟶ R^i f'_* (g'^* F) $$
is an isomorphism, where `f' : X_T ⟶ T` and `g' : X_T ⟶ X` are the projections of
`X_T = X ×_S T`. The statement here is that `SBC_r` holds for every `r ≥ -1`.

It is a special case of the smooth base change theorem [Stacks, Tag 0EYU], which needs neither
the dimension, the excellence nor the fibre-dimension condition, and only asks `f` to be
quasi-compact and quasi-separated.

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_quasiCompact_of_smooth`: the base
  change map `g^* R^i f_* F ⟶ R^i f'_* (g'^* F)` is an isomorphism for `f` quasi-compact and
  quasi-separated, `g` smooth, and `F` with torsion of orders invertible on `S`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_etale_of_dim_le`: the assertion
  `SBC_r` for every `r ≥ -1`.

## Implementation notes

Sheaves are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology` with
coefficients `Ab.{u + 1}`, the setting of the base change map
`Stacks.EtaleCohomology.higherBaseChangeMapAb`. In the source the smooth morphism is the second
argument of the base change situation; `higherBaseChangeMapAb` takes the morphism along which one
pulls back (here `g`) first.

The condition "torsion prime to the residue characteristics of `S`" is
`Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn S F`: every local section is, on an étale
covering, killed by a positive integer which is a unit in `Γ(S, 𝒪_S)`. On the small étale site
`AlgebraicGeometry.SmallEtale` this is
`AlgebraicGeometry.SmallEtale.IsTorsionPrimeToResidueCharacteristics`, by
`AlgebraicGeometry.SmallEtale.isTorsionPrimeToResidueCharacteristics_toEtaleSite_iff`.

An integer `r ≥ -1` and the condition `dim S ≤ r` are encoded as `topologicalKrullDim S <
(r + 1).toNat`: for `r = -1` this says `topologicalKrullDim S = ⊥`, that is `S = ∅`, and for
`r ≥ 0` it says `topologicalKrullDim S ≤ r`. Étale morphisms of finite type in the sense of the
source are `AlgebraicGeometry.Etale` together with `AlgebraicGeometry.QuasiCompact`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7, pp. 74–76][FreitagKiehl]
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Smooth base change along a quasi-compact quasi-separated morphism.** Let
```
X_T --g'--> X
 |f'        |f
 v          v
 T  --g---> S
```
be a cartesian square of schemes with `f` quasi-compact and quasi-separated and `g` smooth. For
every abelian sheaf `F` on `X_ét` with torsion of orders invertible on `S` and every `i`, the
base change map `g^* R^i f_* F ⟶ R^i f'_* (g'^* F)` is an isomorphism. -/
theorem isIso_higherBaseChangeMapAb_app_of_quasiCompact_of_smooth
    {X T S XT : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (f' : XT ⟶ T) (g' : XT ⟶ X)
    (sq : IsPullback f' g' g f) [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (hF : HasTorsionOrdersInvertibleOn S F)
    (i : ℕ) : IsIso ((higherBaseChangeMapAb g f f' g' sq.w i).app F) :=
  SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth g f' g' f sq F
    (fun t a ↦ hF.exists_nsmul_eq_zero_smallEtaleStalkAb t a) i

/-- **`SBC_r` holds for every `r ≥ -1`.** Let `r ≥ -1` be an integer and `S` a noetherian scheme
of dimension `≤ r` all of whose local rings are excellent. Let `f : X ⟶ S` be étale of finite
type, `g : T ⟶ S` smooth with all fibres of dimension `≤ 1`, and
```
X_T --g'--> X
 |f'        |f
 v          v
 T  --g---> S
```
a cartesian square. Then for every abelian sheaf `F` on `X_ét` which is torsion prime to the
residue characteristics of `S` and every `i ≥ 0`, the base change map
`g^* R^i f_* F ⟶ R^i f'_* (g'^* F)` is an isomorphism.

The condition `dim S ≤ r` is written `topologicalKrullDim S < (r + 1).toNat`, which for `r = -1`
says that `S` is empty. -/
@[weil "lem_fk107_sbc_restricted_all_dimensions"]
theorem isIso_higherBaseChangeMapAb_app_of_etale_of_dim_le (r : ℤ) (_hr : -1 ≤ r)
    {X T S XT : Scheme.{u}} [hS : IsNoetherian S]
    (_hdim : topologicalKrullDim S < ((r + 1).toNat : WithBot ℕ∞))
    (_hexc : ∀ s : S, IsExcellent (S.presheaf.stalk s))
    (f : X ⟶ S) (g : T ⟶ S) (f' : XT ⟶ T) (g' : XT ⟶ X) (sq : IsPullback f' g' g f)
    [Etale f] [QuasiCompact f] [Smooth g]
    (_hfib : ∀ s : S, topologicalKrullDim (g.fiber s) ≤ 1)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (hF : HasTorsionOrdersInvertibleOn S F)
    (i : ℕ) : IsIso ((higherBaseChangeMapAb g f f' g' sq.w i).app F) := by
  have := hS.toIsLocallyNoetherian
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : QuasiSeparated f := (quasiSeparated_iff_quasiSeparatedSpace f).mpr inferInstance
  exact isIso_higherBaseChangeMapAb_app_of_quasiCompact_of_smooth f g f' g' sq F hF i

end Stacks.EtaleCohomology

end
