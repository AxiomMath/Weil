/-
Copyright (c) 2026 Weil project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Weil.AlgebraicGeometry.EtaleCohomology.PurelyInseparableFieldExtensionCohomologyIso
public import Weil.Attr

/-!
# Étale cohomology is invariant under algebraic extension of a separably closed base field

Let `k` be a separably closed field, `K / k` an algebraic field extension, `Y` a scheme over `k`
and `e : Y ⊗_k K ⟶ Y` the projection. For every abelian sheaf `G` on the small étale site of `Y`
and every `ν ≥ 0`, the restriction map `H^ν(Y, G) → H^ν(Y ⊗_k K, e^* G)` is bijective.

An algebraic extension of a separably closed field is purely inseparable, so this is the
invariance of étale cohomology under purely inseparable extension of the base field.

## Main results

* `SmallEtale.bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec_of_isSepClosed`:
  the restriction map along `Y ⊗_k K ⟶ Y` is bijective for `k` separably closed and `K / k`
  algebraic.

## Implementation notes

The source states the result for `Y` of finite type over `k` and `K / k` finite; neither
hypothesis is used, and the result is stated for any scheme over `k` and any algebraic `K / k`.
As in `SmallEtale.bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec`, the scheme
`Y ⊗_k K` is an object of the big étale site given with a pullback square over
`Spec K ⟶ Spec k`, and the restriction map is
`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`, the inverse image on `Ext`-groups out of
the constant sheaf `ℤ` precomposed with the constant-sheaf comparison.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Abelian

universe w u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K] {Y YK : B.Scheme} (s : B.inclusion.obj Y ⟶ Spec (.of k))
  (e : YK ⟶ Y) (p : B.inclusion.obj YK ⟶ Spec (.of K))
  [HasExt.{w} (Sheaf (topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (topology B YK.obj YK.property) AddCommGrpCat.{u + 1})]

/-- **Étale cohomology is invariant under algebraic extension of a separably closed base
field.** Let `k` be a separably closed field, `K / k` an algebraic field extension, `Y` a scheme
over `k` (structure morphism `s`) and `e : Y ⊗_k K ⟶ Y` the projection, where `Y ⊗_k K` is given
with a pullback square over `Spec K ⟶ Spec k`. For every abelian sheaf `G` on the small étale
site of `Y` and every `ν`, the restriction map `H^ν(Y, G) →+ H^ν(Y ⊗_k K, e^* G)` is
bijective. -/
@[weil "lem_fk106_base_change_purely_inseparable_field"]
theorem bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec_of_isSepClosed
    (sq : IsPullback (B.inclusion.map e) p s (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (G : Sheaf (topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap B e G ν) :=
  bijective_smallEtaleCohomologyRestrictionMap_of_isPullback_spec k K s e p sq G ν

end AlgebraicGeometry.SmallEtale

end
