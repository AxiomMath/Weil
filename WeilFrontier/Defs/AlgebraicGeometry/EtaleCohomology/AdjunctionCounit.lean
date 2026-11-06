module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# Counits of the inverse image – direct image adjunction on small étale sites

Let `f : T ⟶ S` be a morphism of a big étale site `B` and let `F` be a sheaf on the small étale
site of `T` with values in a category `A`. Write `η` for the unit of the adjunction
`f^* ⊣ f_*` (`AlgebraicGeometry.smallEtaleInverseImageAdjunction`). A morphism of sheaves
`θ : f^* f_* F ⟶ F` is a *counit for `F`* if `f_* θ ∘ η_{f_* F} = id_{f_* F}`.

The counit of the adjunction at `F` is a counit for `F` (a triangle identity), and it is the only
one: the map `θ ↦ f_* θ ∘ η_{f_* F}` is the hom-set bijection of the adjunction, hence
injective.

## Main definitions

* `AlgebraicGeometry.IsSmallEtaleCounit`: the property of `θ : f^* f_* F ⟶ F` of being a counit
  for `F`.

## Main results

* `AlgebraicGeometry.isSmallEtaleCounit_iff`: `θ` is a counit for `F` if and only if it is the
  counit of the adjunction `f^* ⊣ f_*` at `F`.
* `AlgebraicGeometry.isSmallEtaleCounit_counit_app`: the counit of the adjunction is a counit.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
variable {A : Type w} [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **Counit for a sheaf.** A morphism `θ : f^* f_* F ⟶ F` of sheaves on the small étale site of
`T` is a counit for `F` if `f_* θ ∘ η_{f_* F} = id_{f_* F}`, where `η` is the unit of the
adjunction `f^* ⊣ f_*`. -/
@[weil "def_fk103_adjunction_counit"]
def IsSmallEtaleCounit (F : Sheaf (SmallEtale.topology B T.obj T.property) A)
    (θ : (smallEtaleInverseImage B f A).obj
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj F) ⟶
        F) : Prop :=
  (smallEtaleInverseImageAdjunction B f A).unit.app
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj F) ≫
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).map θ =
      𝟙 _

variable {B f}

/-- `θ` is a counit for `F` if and only if it is the counit of the adjunction `f^* ⊣ f_*` at
`F`. -/
theorem isSmallEtaleCounit_iff (F : Sheaf (SmallEtale.topology B T.obj T.property) A)
    (θ : (smallEtaleInverseImage B f A).obj
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj F) ⟶
        F) :
    IsSmallEtaleCounit B f F θ ↔ θ = (smallEtaleInverseImageAdjunction B f A).counit.app F := by
  constructor
  · intro h
    apply ((smallEtaleInverseImageAdjunction B f A).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Adjunction.right_triangle_components]
    exact h
  · rintro rfl
    exact (smallEtaleInverseImageAdjunction B f A).right_triangle_components F

/-- The counit of the adjunction `f^* ⊣ f_*` at `F` is a counit for `F`. -/
theorem isSmallEtaleCounit_counit_app (F : Sheaf (SmallEtale.topology B T.obj T.property) A) :
    IsSmallEtaleCounit B f F ((smallEtaleInverseImageAdjunction B f A).counit.app F) :=
  (isSmallEtaleCounit_iff F _).2 rfl

end AlgebraicGeometry

end
