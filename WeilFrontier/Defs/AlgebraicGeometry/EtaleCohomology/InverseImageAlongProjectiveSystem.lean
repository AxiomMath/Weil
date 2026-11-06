module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# Inverse images and base changes along a projective system of schemes

Let `X = lim Xᵢ` be a projective system of schemes with limit, given by a diagram
`D : I ⥤ B.Scheme` in the category of schemes of a big étale site `B` and a cone `c` over it
with apex `X = c.pt` and projections `pᵢ = c.π.app i`, and let `i₀` be an index. A morphism
`f : j ⟶ i₀` of `I` is a relation `j ≥ i₀`, with transition morphism `p_{j i₀} = D.map f`.

For an étale sheaf `F_{i₀}` on `X_{i₀}` (of sets, of abelian groups, or with values in any
category `A` with the relevant colimits and sheafification) one writes

* `F_j = p_{j i₀}^* F_{i₀}` for its inverse image on `X_j`, and
* `F = p_{i₀}^* F_{i₀}` for its inverse image on `X`,

and likewise `u_j`, `u` for the inverse images of a morphism `u : F_{i₀} ⟶ G_{i₀}` of sheaves:
these are the object and morphism parts of the inverse image functors below. For an
`X_{i₀}`-scheme `U_{i₀}` and an `X_{i₀}`-morphism `f_{i₀}` one writes `U_j`, `U`, `f_j`, `f`
for their base changes to `X_j` and to `X`; for étale `X_{i₀}`-schemes these are the base change
functors between the small étale categories.

## Main definitions

* `AlgebraicGeometry.smallEtaleStageInverseImage` — `F_{i₀} ↦ F_j = p_{j i₀}^* F_{i₀}`.
* `AlgebraicGeometry.smallEtaleLimitInverseImage` — `F_{i₀} ↦ F = p_{i₀}^* F_{i₀}`.
* `AlgebraicGeometry.smallEtaleStageBaseChange`, `AlgebraicGeometry.smallEtaleLimitBaseChange` —
  `U_{i₀} ↦ U_j`, `U_{i₀} ↦ U` for étale `X_{i₀}`-schemes.
* `AlgebraicGeometry.overStageBaseChange`, `AlgebraicGeometry.overLimitBaseChange` — the same for
  arbitrary `X_{i₀}`-schemes.

## Implementation notes

The index category is an arbitrary category, as in `AlgebraicGeometry.IsProjectiveSystemWithLimit`;
the stages `j ≥ i₀` are the morphisms `f : j ⟶ i₀`. The notation needs none of the conditions
of a projective system with limit; in the situation of the source these are
`AlgebraicGeometry.IsProjectiveSystemWithLimit (D ⋙ ι) (ι.mapCone c)`, `ι` the inclusion of
`B.Scheme` into schemes. The inverse images are `AlgebraicGeometry.smallEtaleInverseImage` on
the small étale sites `AlgebraicGeometry.SmallEtale`, and the base changes are
`AlgebraicGeometry.smallEtaleBaseChange` and `CategoryTheory.Over.pullback`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4, p. 49][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u u'

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {I : Type u'} [Category I]

section InverseImage

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]

/-- **The sheaves `F_j`.** For a stage `f : j ⟶ i₀` of the diagram `D`, the inverse image
`F_j = p_{j i₀}^* F_{i₀}` along the transition morphism `p_{j i₀} = D.map f`, sending a sheaf
`F_{i₀}` on the small étale site of `X_{i₀}` to a sheaf on that of `X_j`, and a morphism `u` of
sheaves to `u_j`. -/
@[weil "not_fk104_inverse_image_along_projective_system"]
abbrev smallEtaleStageInverseImage (D : I ⥤ B.Scheme) {j i₀ : I} (f : j ⟶ i₀)
    [HasWeakSheafify (SmallEtale.topology B (D.obj j).obj (D.obj j).property) A] :
    Sheaf (SmallEtale.topology B (D.obj i₀).obj (D.obj i₀).property) A ⥤
      Sheaf (SmallEtale.topology B (D.obj j).obj (D.obj j).property) A :=
  smallEtaleInverseImage B (D.map f) A

/-- **The sheaf `F`.** The inverse image `F = p_{i₀}^* F_{i₀}` along the projection
`p_{i₀} = c.π.app i₀` from the limit `X = c.pt`, sending a sheaf `F_{i₀}` on the small étale site
of `X_{i₀}` to a sheaf on that of `X`, and a morphism `u` of sheaves to `u`. -/
@[weil "not_fk104_inverse_image_along_projective_system"]
abbrev smallEtaleLimitInverseImage {D : I ⥤ B.Scheme} (c : Cone D) (i₀ : I)
    [HasWeakSheafify (SmallEtale.topology B c.pt.obj c.pt.property) A] :
    Sheaf (SmallEtale.topology B (D.obj i₀).obj (D.obj i₀).property) A ⥤
      Sheaf (SmallEtale.topology B c.pt.obj c.pt.property) A :=
  smallEtaleInverseImage (S := D.obj i₀) (T := c.pt) B (c.π.app i₀) A

end InverseImage

section BaseChange

/-- **The étale schemes `U_j`.** For a stage `f : j ⟶ i₀`, the base change
`U_j = U_{i₀} ×_{X_{i₀}} X_j` of an étale `X_{i₀}`-scheme, and of an `X_{i₀}`-morphism of étale
`X_{i₀}`-schemes. -/
@[weil "not_fk104_inverse_image_along_projective_system"]
abbrev smallEtaleStageBaseChange (D : I ⥤ B.Scheme) {j i₀ : I} (f : j ⟶ i₀) :
    SmallEtale B (D.obj i₀).obj (D.obj i₀).property ⥤
      SmallEtale B (D.obj j).obj (D.obj j).property :=
  smallEtaleBaseChange B (D.map f)

/-- **The étale scheme `U`.** The base change `U = U_{i₀} ×_{X_{i₀}} X` of an étale
`X_{i₀}`-scheme to the limit, and of an `X_{i₀}`-morphism of étale `X_{i₀}`-schemes. -/
@[weil "not_fk104_inverse_image_along_projective_system"]
abbrev smallEtaleLimitBaseChange {D : I ⥤ B.Scheme} (c : Cone D) (i₀ : I) :
    SmallEtale B (D.obj i₀).obj (D.obj i₀).property ⥤ SmallEtale B c.pt.obj c.pt.property :=
  smallEtaleBaseChange (S := D.obj i₀) (T := c.pt) B (c.π.app i₀)

/-- **The schemes `U_j`.** For a stage `f : j ⟶ i₀`, the base change
`U_j = U_{i₀} ×_{X_{i₀}} X_j` of an arbitrary `X_{i₀}`-scheme, and of an `X_{i₀}`-morphism. -/
@[weil "not_fk104_inverse_image_along_projective_system"]
abbrev overStageBaseChange (D : I ⥤ B.Scheme) {j i₀ : I} (f : j ⟶ i₀) :
    Over (D.obj i₀) ⥤ Over (D.obj j) :=
  Over.pullback (D.map f)

/-- **The scheme `U`.** The base change `U = U_{i₀} ×_{X_{i₀}} X` of an arbitrary
`X_{i₀}`-scheme to the limit, and of an `X_{i₀}`-morphism. -/
@[weil "not_fk104_inverse_image_along_projective_system"]
abbrev overLimitBaseChange {D : I ⥤ B.Scheme} (c : Cone D) (i₀ : I) :
    Over (D.obj i₀) ⥤ Over c.pt :=
  Over.pullback (X := c.pt) (Y := D.obj i₀) (c.π.app i₀)

/-- The étale base change to a stage is the base change of the underlying `X_{i₀}`-scheme. -/
lemma smallEtaleStageBaseChange_obj_obj (D : I ⥤ B.Scheme) {j i₀ : I} (f : j ⟶ i₀)
    (U : SmallEtale B (D.obj i₀).obj (D.obj i₀).property) :
    ((smallEtaleStageBaseChange B D f).obj U).obj = (overStageBaseChange B D f).obj U.obj :=
  rfl

/-- The étale base change to the limit is the base change of the underlying `X_{i₀}`-scheme. -/
lemma smallEtaleLimitBaseChange_obj_obj {D : I ⥤ B.Scheme} (c : Cone D) (i₀ : I)
    (U : SmallEtale B (D.obj i₀).obj (D.obj i₀).property) :
    ((smallEtaleLimitBaseChange B c i₀).obj U).obj = (overLimitBaseChange B c i₀).obj U.obj :=
  rfl

end BaseChange

end AlgebraicGeometry

end
