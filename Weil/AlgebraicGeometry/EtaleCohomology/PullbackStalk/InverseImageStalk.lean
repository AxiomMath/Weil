module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# Stalks of the inverse image of an étale sheaf

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B`, let `x` be a geometric point of
`T` and let `y = f ∘ x` be the image geometric point of `S`. For every sheaf `G` on the small
étale site of `S`, with values in a category `A` such as sets or abelian groups, the stalk of `G`
at `y` is canonically isomorphic to the stalk of the inverse image `f^* G` at `x`, naturally
in `G`.

On germs the isomorphism is the classical one: the germ of a section `s ∈ G(U)` at a pointed
étale neighborhood `(U, u)` of `y` corresponds to the germ at the pointed neighborhood
`(T ×_S U, (x, u))` of `x` of the section of `f^* G` obtained from `s` through the unit of the
adjunction `f^* ⊣ f_*`.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageSheafFiberIso` — the natural isomorphism
  `G_y ≅ (f^* G)_x`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageSheafFiberIso_germ` — its effect on germs.

## Implementation notes

Stalks at a geometric point `x` are taken as the fibre functor of the point of the site
`AlgebraicGeometry.geometricPointSitePoint`, whose fibre over an étale `T`-scheme `V` is the set
of lifts of `x` to `V`, so that the stalk is the colimit over pointed étale neighborhoods.
The isomorphism is the inverse of the Stacks project's
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso`, which is obtained from the identification of
the inverse image of a point of a site along base change with the image point; the explicit
inverse maps `Φ` and `Ψ` on representatives of the colimits are not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.obj)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A] [HasProducts.{u} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- Stalks on the small étale sites are colimits indexed by categories of size `u`. -/
local instance : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u, u + 1} A

/-- **Stalks of the inverse image.** For a geometric point `x` of `T` with image `y = f ∘ x`,
the stalk at `y` of a sheaf `G` on the small étale site of `S` is isomorphic to the stalk at `x`
of its inverse image `f^* G`, naturally in `G`. -/
@[weil "lem_fk102_inverse_image_stalk"]
def smallEtaleInverseImageSheafFiberIso :
    (geometricPointSitePoint B S.obj S.property (x.map (B.inclusion.map f))).sheafFiber ≅
      smallEtaleInverseImage B f A ⋙ (geometricPointSitePoint B T.obj T.property x).sheafFiber :=
  (smallEtalePullbackSheafFiberIso B f x A).symm

/-- On germs, the isomorphism `G_y ≅ (f^* G)_x` sends the germ of a section `t` of `G` over a
pointed étale neighborhood `V` of `y` to the germ, at a pointed étale neighborhood `U` of `x`
mapping to the base change of `V` compatibly with the points, of the section of `f^* G`
obtained from `t` through the unit of the adjunction `f^* ⊣ f_*`. -/
lemma smallEtaleInverseImageSheafFiberIso_germ
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (U : (geometricPointFiber B T.obj T.property x).Elements)
    (V : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f))).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B T.obj T.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.obj S.property
        (x.map (B.inclusion.map f)))).op ⋙ G.obj) (op V) ≫
        (smallEtaleInverseImageSheafFiberIso B f x A).hom.app G =
      pullbackSectionAlongHom B f A G V.1 U.1 a ≫
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B T.obj T.property x)).op ⋙
          ((smallEtaleInverseImage B f A).obj G).obj) (op U) := by
  rw [← smallEtalePullbackSheafFiberIso_germ B f x A G U V a ha]
  simp only [smallEtaleInverseImageSheafFiberIso, Iso.symm_hom]
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ?_))
  exact (congrArg (_ ≫ ·) ((smallEtalePullbackSheafFiberIso B f x A).hom_inv_id_app G)).trans
    (Category.comp_id _)

end AlgebraicGeometry

end
