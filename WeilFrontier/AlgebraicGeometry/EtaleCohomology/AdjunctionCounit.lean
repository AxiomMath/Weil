module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.AdjunctionCounit
public import Weil.Attr

/-!
# Existence and uniqueness of counits on small étale sites

Let `f : T ⟶ S` be a morphism of a big étale site `B` and let `F` be a sheaf on the small étale
site of `T`. There is exactly one morphism `θ : f^* f_* F ⟶ F` with
`f_* θ ∘ η_{f_* F} = id_{f_* F}`, where `η` is the unit of the adjunction `f^* ⊣ f_*`: namely the
counit of that adjunction at `F`. Indeed `θ ↦ f_* θ ∘ η_{f_* F}` is the hom-set bijection of the
adjunction, and exactly one `θ` is sent to the identity.

## Main results

* `AlgebraicGeometry.existsUnique_isSmallEtaleCounit`: there is exactly one counit for `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} {f : T ⟶ S}
variable {A : Type w} [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- For a sheaf `F` on the small étale site of `T` there is exactly one counit
`θ : f^* f_* F ⟶ F`, i.e. exactly one `θ` with `f_* θ ∘ η_{f_* F} = id_{f_* F}`. -/
@[weil "lem_fk103_adjunction_counit_exists_unique"]
theorem existsUnique_isSmallEtaleCounit (F : Sheaf (SmallEtale.topology B T.obj T.property) A) :
    ∃! θ, IsSmallEtaleCounit B f F θ :=
  ⟨_, isSmallEtaleCounit_counit_app F, fun θ h => (isSmallEtaleCounit_iff F θ).1 h⟩

end AlgebraicGeometry

end
