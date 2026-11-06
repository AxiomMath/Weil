module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.VanishingAboveDegreeTwo
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Attr

/-!
# Finiteness and vanishing properties of sheaf cohomology

For an abelian sheaf `F` on a site (for instance the small étale site of a scheme `X`), the
*cohomology bound properties* are the symbols `fin` and `van m` for integers `m ≥ 2`:

* `fin(X, F)`: the cohomology group `H^q(X, F)` is finite for every `q ≥ 0`;
* `van_m(X, F)`: `H^q(X, F) = 0` for every `q ≥ m`.

They are the bookkeeping device by which finiteness and vanishing of the étale cohomology of
constructible sheaves on curves are proved simultaneously, by reductions that preserve
either property.

## Main definitions

* `CategoryTheory.Sheaf.CohomologyBoundProperty`: the symbols `fin` and `van m` (`2 ≤ m`).
* `CategoryTheory.Sheaf.CohomologyBoundProperty.Holds`: the assertion `P(X, F)` for an abelian
  sheaf `F` on a site.

## Main results

* `CategoryTheory.Sheaf.CohomologyBoundProperty.holds_fin_iff`,
  `CategoryTheory.Sheaf.CohomologyBoundProperty.holds_van_iff`: the two assertions unfolded.
* `CategoryTheory.Sheaf.CohomologyBoundProperty.holds_congr`: the assertion depends only on
  the cohomology groups up to isomorphism; `holds_iff_of_iso` for isomorphic sheaves.
* `CategoryTheory.Sheaf.CohomologyBoundProperty.holds_van_three_iff_isVanishingAboveDegreeTwo`:
  `van_3` is `Stacks.EtaleCohomology.IsVanishingAboveDegreeTwo` (Stacks, Tag 0A53).
* `AlgebraicGeometry.SmallEtale.cohomologyBoundProperty_holds_sheafEquiv_functor_obj_iff`: the
  assertion is the same on the bounded small étale site and on `X.smallEtaleTopology`.

## Implementation notes

The definition is made for an arbitrary site; the source's case is the small étale site
`AlgebraicGeometry.SmallEtale` of a scheme. Vanishing of `H^q` is spelled `Subsingleton`, as in
`Stacks.EtaleCohomology.IsVanishingAboveDegreeTwo`, since `CategoryTheory.Sheaf.H` is an
`Ext`-group. The `Ext`-universe instance is a parameter, `CategoryTheory.HasExt` not being an
instance.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.5.
-/

@[expose] public section

open CategoryTheory

universe w₀' w₀ v' u' w' w v u

namespace CategoryTheory.Sheaf

/-- **The cohomology bound properties.** The symbols `fin` (finiteness of all cohomology
groups) and `van m` for an integer `m ≥ 2` (vanishing of cohomology in degrees `≥ m`). -/
@[weil "def_fk105_cohomology_bound_property"]
inductive CohomologyBoundProperty : Type
  /-- `fin`: every cohomology group is finite. -/
  | fin
  /-- `van m`, for `m ≥ 2`: cohomology vanishes in every degree `q ≥ m`. -/
  | van (m : ℕ) (hm : 2 ≤ m)
  deriving DecidableEq

namespace CohomologyBoundProperty

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- **The assertion `P(X, F)`.** For an abelian sheaf `F`: `fin(F)` says `H^q(F)` is finite for
every `q`, and `van_m(F)` says `H^q(F) = 0` for every `q ≥ m`. -/
@[weil "def_fk105_cohomology_bound_property"]
def Holds : CohomologyBoundProperty → Sheaf J AddCommGrpCat.{w} → Prop
  | fin, F => ∀ q : ℕ, Finite (F.H q)
  | van m _, F => ∀ q : ℕ, m ≤ q → Subsingleton (F.H q)

theorem holds_fin_iff (F : Sheaf J AddCommGrpCat.{w}) :
    fin.Holds F ↔ ∀ q : ℕ, Finite (F.H q) :=
  Iff.rfl

theorem holds_van_iff {m : ℕ} (hm : 2 ≤ m) (F : Sheaf J AddCommGrpCat.{w}) :
    (van m hm).Holds F ↔ ∀ q : ℕ, m ≤ q → Subsingleton (F.H q) :=
  Iff.rfl

/-- Vanishing in degrees `≥ m` implies vanishing in degrees `≥ m'` for `m ≤ m'`. -/
theorem Holds.van_mono {m m' : ℕ} {hm : 2 ≤ m} (hm' : 2 ≤ m') (hmm' : m ≤ m')
    {F : Sheaf J AddCommGrpCat.{w}} (h : (van m hm).Holds F) : (van m' hm').Holds F :=
  fun q hq => h q (hmm'.trans hq)

/-- **The assertion depends only on the cohomology groups.** If two abelian sheaves, possibly on
different sites, have isomorphic cohomology groups in every degree, then each cohomology bound
property holds for one exactly when it holds for the other. -/
theorem holds_congr {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
    [HasSheafify J' AddCommGrpCat.{w₀}] [HasExt.{w₀'} (Sheaf J' AddCommGrpCat.{w₀})]
    (P : CohomologyBoundProperty) {F : Sheaf J AddCommGrpCat.{w}}
    {G : Sheaf J' AddCommGrpCat.{w₀}} (e : ∀ q : ℕ, F.H q ≃+ G.H q) :
    P.Holds F ↔ P.Holds G := by
  cases P with
  | fin =>
    exact forall_congr' fun q => (e q).toEquiv.finite_iff
  | van m hm =>
    exact forall_congr' fun q => imp_congr_right fun _ =>
      ⟨fun _ => (e q).symm.injective.subsingleton, fun _ => (e q).injective.subsingleton⟩

/-- Each cohomology bound property is invariant under isomorphism of sheaves. -/
theorem holds_iff_of_iso (P : CohomologyBoundProperty) {F G : Sheaf J AddCommGrpCat.{w}}
    (e : F ≅ G) : P.Holds F ↔ P.Holds G :=
  P.holds_congr fun q => ((Sheaf.functorH J q).mapIso e).addCommGroupIsoToAddEquiv

/-- **`van_3` is vanishing above degree two** (Stacks, Tag 0A53). -/
theorem holds_van_three_iff_isVanishingAboveDegreeTwo {X : AlgebraicGeometry.Scheme.{u}}
    [HasExt.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (van 3 (by norm_num)).Holds F ↔ Stacks.EtaleCohomology.IsVanishingAboveDegreeTwo.{u, v, w'} F :=
  forall_congr' fun q => imp_congr_left (by omega)

end CohomologyBoundProperty

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})]
  [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]

/-- A cohomology bound property holds for an abelian sheaf on the bounded small étale site
exactly when it holds for the corresponding sheaf on `S.smallEtaleTopology`. -/
theorem cohomologyBoundProperty_holds_sheafEquiv_functor_obj_iff
    (P : Sheaf.CohomologyBoundProperty) (F : Sheaf (topology B S hS) AddCommGrpCat.{u}) :
    P.Holds ((sheafEquiv B S hS AddCommGrpCat.{u}).functor.obj F) ↔ P.Holds F :=
  (P.holds_congr fun q => cohomologyAddEquivOfSmallEtale B S hS F q).symm

/-- A cohomology bound property holds for an abelian sheaf on `S.smallEtaleTopology` exactly
when it holds for its restriction to the bounded small étale site. -/
theorem cohomologyBoundProperty_holds_sheafEquiv_inverse_obj_iff
    (P : Sheaf.CohomologyBoundProperty) (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    P.Holds ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj F) ↔ P.Holds F :=
  (P.holds_congr fun q => cohomologyAddEquiv B S hS F q).symm

end AlgebraicGeometry.SmallEtale
