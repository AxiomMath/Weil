module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.PurelyInseparableUnitIso
public import Weil.Attr

/-!
# The counit of the inverse image along a purely inseparable morphism

Let `f : T ⟶ S` be a (finite) purely inseparable morphism of schemes and `F` a sheaf of sets on
the small étale site of `T`. Then the counit `f^* f_* F ⟶ F` of the adjunction `f^* ⊣ f_*` is an
isomorphism. The same holds for sheaves with values in any category with enough limits and
colimits.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleInverseImageAdjunction_counit_of_universalHomeomorphism` —
  for a universal homeomorphism `f`, the counit `f^* ∘ f_* ⟶ 𝟭` is a natural isomorphism.
* `AlgebraicGeometry.isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable` —
  for `f` purely inseparable, the counit `f^* f_* F ⟶ F` is an isomorphism for every sheaf `F`.
* `AlgebraicGeometry.isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable_type`
  — the case of sheaves of sets.

## Implementation notes

The source proves the statement stalkwise: at a geometric point `x` of `T` over `y = f ∘ x`, the
stalk of the counit, preceded by the bijection `(f_* F)_y ≅ (f^* f_* F)_x`, is the bijection
`(f_* F)_y ≅ F_x`. Here it follows from topological invariance of the étale topos: a purely
inseparable morphism is a universal homeomorphism, so `f^*` is an equivalence of sheaf categories
(`AlgebraicGeometry.isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism`); the right
adjoint of an equivalence is an equivalence, hence fully faithful, and the counit of an
adjunction whose right adjoint is fully faithful is an isomorphism.

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

/-- For a universal homeomorphism `f`, the counit `f^* ∘ f_* ⟶ 𝟭` of the inverse image is a
natural isomorphism. -/
theorem isIso_smallEtaleInverseImageAdjunction_counit_of_universalHomeomorphism
    [UniversalHomeomorphism (B.inclusion.map f)] :
    IsIso (smallEtaleInverseImageAdjunction B f A).counit := by
  have := isEquivalence_smallEtaleInverseImage_of_universalHomeomorphism B f A
  have := (smallEtaleInverseImageAdjunction B f A).isEquivalence_right_of_isEquivalence_left
  exact (smallEtaleInverseImageAdjunction B f A).counit_isIso_of_R_fully_faithful

/-- **The counit is an isomorphism along a purely inseparable morphism.** If `f : T ⟶ S` is
purely inseparable, then for every sheaf `F` on the small étale site of `T` the counit
`f^* f_* F ⟶ F` is an isomorphism. -/
@[weil "lem_fk103_purely_inseparable_counit_iso"]
theorem isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) A) :
    IsIso ((smallEtaleInverseImageAdjunction B f A).counit.app F) := by
  have := hf.universalHomeomorphism
  have := isIso_smallEtaleInverseImageAdjunction_counit_of_universalHomeomorphism B f A
  infer_instance

end General

/-- **The counit is an isomorphism along a purely inseparable morphism, for sheaves of sets.** If
`f : T ⟶ S` is purely inseparable and `F` is an étale sheaf of sets on `T`, the counit
`f^* f_* F ⟶ F` is an isomorphism. -/
@[weil "lem_fk103_purely_inseparable_counit_iso"]
theorem isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable_type
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) (Type (u + 1))) :
    IsIso ((smallEtaleInverseImageAdjunction B f (Type (u + 1))).counit.app F) :=
  isIso_smallEtaleInverseImageAdjunction_counit_app_of_isPurelyInseparable B f _ hf F

end AlgebraicGeometry

end
