module

public import Weil.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.ConstantIffPurelyInseparablePullbackConstant
public import Weil.CategoryTheory.Sites.Pullback
public import Weil.Attr

/-!
# The unit of the inverse image along a purely inseparable morphism

Let `f : T ⟶ S` be a (finite) purely inseparable morphism of schemes and `G` a sheaf of sets on
the small étale site of `S`. Then the unit `G ⟶ f_* f^* G` of the adjunction `f^* ⊣ f_*` is an
isomorphism. The same holds for sheaves with values in any category with enough limits and
colimits.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable` — for `f`
  purely inseparable, the unit `G ⟶ f_* f^* G` is an isomorphism for every sheaf `G`.
* `AlgebraicGeometry.isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable_type` — the case
  of sheaves of sets.
* `AlgebraicGeometry.isIso_smallEtaleInverseImageUnit_of_universalHomeomorphism` — more
  generally, the unit is a natural isomorphism for every universal homeomorphism `f`.

## Implementation notes

The source proves the statement stalkwise: at a geometric point `y` of `S` with unique lift `x`
to `T`, the stalk of the unit is the composite of the bijections `G_y ≅ (f^* G)_x` and
`(f_* f^* G)_y ≅ (f^* G)_x`. Here it follows from topological invariance of the étale topos: a
purely inseparable morphism is a universal homeomorphism, so `f^*` is an equivalence of sheaf
categories (`AlgebraicGeometry.isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism`),
and the unit of an adjunction whose left adjoint is fully faithful is an isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

section General

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasLimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- For a universal homeomorphism `f`, the unit `𝟭 ⟶ f_* ∘ f^*` of the inverse image is a
natural isomorphism. -/
theorem isIso_smallEtaleInverseImageUnit_of_universalHomeomorphism
    [UniversalHomeomorphism (B.inclusion.map f)] :
    IsIso (smallEtaleInverseImageUnit B f A) := by
  have := isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism B f A
  exact (smallEtaleInverseImageAdjunction B f A).unit_isIso_of_L_fully_faithful

/-- **The unit is an isomorphism along a purely inseparable morphism.** If `f : T ⟶ S` is
purely inseparable, then for every sheaf `G` on the small étale site of `S` the unit
`G ⟶ f_* f^* G` is an isomorphism. -/
@[weil "lem_fk103_purely_inseparable_unit_iso"]
theorem isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    IsIso ((smallEtaleInverseImageUnit B f A).app G) := by
  have := hf.universalHomeomorphism
  have := isIso_smallEtaleInverseImageUnit_of_universalHomeomorphism B f A
  infer_instance

end General

/-- **The unit is an isomorphism along a purely inseparable morphism, for sheaves of sets.** If
`f : T ⟶ S` is purely inseparable and `G` is an étale sheaf of sets on `S`, the unit
`G ⟶ f_* f^* G` is an isomorphism. -/
@[weil "lem_fk103_purely_inseparable_unit_iso"]
theorem isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable_type
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    IsIso ((smallEtaleInverseImageUnit B f (Type (u + 1))).app G) :=
  isIso_smallEtaleInverseImageUnit_app_of_isPurelyInseparable B f _ hf G

end AlgebraicGeometry

end
