module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImages
public import Weil.Attr

/-!
# The inverse image of sheaves on the small étale site

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B`, and let `G` be a sheaf on the
small étale site of `S`, of sets, of abelian groups, or with values in any category `A` with the
relevant colimits and sheafification. The inverse image `f^* G` is the sheaf on the small étale
site of `T` associated with the inverse image presheaf `f⁻¹_pre G`
(`AlgebraicGeometry.smallEtaleInverseImagePresheaf`), whose sections over an étale `T`-scheme
`V` are `colim G(U)` over the pairs `(U, h : V ⟶ U)` compatible with `f`.

The functor `f^*` is left adjoint to the direct image `f_*`, which sends a sheaf `F` on the small
étale site of `T` to `U ↦ F(T ×_S U)`: the presheaf inverse image is left adjoint to restriction
along base change, and sheafification is left adjoint to the inclusion of sheaves.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImage` — the inverse image functor `f^*` on sheaves on the
  small étale sites with values in `A`.
* `AlgebraicGeometry.smallEtaleInverseImageAdjunction` — the adjunction `f^* ⊣ f_*`.
* `AlgebraicGeometry.smallEtaleInverseImageIsoSheafify` — `f^*` is, up to a canonical
  isomorphism, sheafification of the inverse image presheaf.
* `AlgebraicGeometry.smallEtaleInverseImageObjIso` — `f^* G` is the sheaf associated with
  `f⁻¹_pre G`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageObjIso_hom_naturality` — the identification of `f^* G`
  with the sheafification of `f⁻¹_pre G` is natural in `G`.

## Implementation notes

The inverse image is Mathlib's `CategoryTheory.Functor.sheafPullback` along base change
`AlgebraicGeometry.smallEtaleBaseChange B f`, the chosen left adjoint of the direct image, which
is the form in which the Stacks project's étale cohomology library uses it (at coefficients
`Type (u + 1)`, `AddCommGrpCat.{u + 1}`, `ModuleCat.{u + 1} Λ`). The definition as the
sheafification of the presheaf inverse image is recorded as the canonical isomorphism
`AlgebraicGeometry.smallEtaleInverseImageIsoSheafify`, which is Mathlib's
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`: both functors are left
adjoint to the direct image.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03Q0](https://stacks.math.columbia.edu/tag/03Q0)
* [Stacks Project, Tag 04I3](https://stacks.math.columbia.edu/tag/04I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **The inverse image `f^*`.** The functor sending a sheaf `G` on the small étale site of `S`
with values in `A` to the sheaf on the small étale site of `T` associated with the inverse image
presheaf `f⁻¹_pre G` (`smallEtaleInverseImageIsoSheafify`). It is the left adjoint of the direct
image along `f` (`smallEtaleInverseImageAdjunction`). -/
@[weil "def_fk102_inverse_image"]
abbrev smallEtaleInverseImage :
    Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) A :=
  (smallEtaleBaseChange B f).sheafPullback A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- **The adjunction `f^* ⊣ f_*`.** The inverse image is left adjoint to the direct image,
`(f_* F)(U) = F(T ×_S U)`. -/
abbrev smallEtaleInverseImageAdjunction :
    smallEtaleInverseImage B f A ⊣
      (smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) :=
  (smallEtaleBaseChange B f).sheafAdjunctionContinuous A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- **`f^*` is the sheafification of `f⁻¹_pre`.** The inverse image functor is canonically
isomorphic to the composite of the inclusion of sheaves into presheaves, the inverse image
presheaf functor `f⁻¹_pre`, and sheafification. -/
@[weil "def_fk102_inverse_image"]
def smallEtaleInverseImageIsoSheafify :
    smallEtaleInverseImage B f A ≅
      sheafToPresheaf (SmallEtale.topology B S.obj S.property) A ⋙
        smallEtaleInverseImagePresheaf B f A ⋙
          presheafToSheaf (SmallEtale.topology B T.obj T.property) A :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange B f) A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- **The sheaf `f^* G`.** For a sheaf `G` on the small étale site of `S`, the inverse image
`f^* G` is the sheaf associated with the inverse image presheaf `f⁻¹_pre G`. -/
@[weil "def_fk102_inverse_image"]
def smallEtaleInverseImageObjIso (G : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    (smallEtaleInverseImage B f A).obj G ≅
      (presheafToSheaf (SmallEtale.topology B T.obj T.property) A).obj
        ((smallEtaleInverseImagePresheaf B f A).obj G.obj) :=
  (smallEtaleInverseImageIsoSheafify B f A).app G

/-- The identification of `f^* G` with the sheafification of `f⁻¹_pre G` is natural in `G`. -/
@[reassoc]
lemma smallEtaleInverseImageObjIso_hom_naturality
    {G G' : Sheaf (SmallEtale.topology B S.obj S.property) A} (φ : G ⟶ G') :
    (smallEtaleInverseImage B f A).map φ ≫ (smallEtaleInverseImageObjIso B f A G').hom =
      (smallEtaleInverseImageObjIso B f A G).hom ≫
        (presheafToSheaf (SmallEtale.topology B T.obj T.property) A).map
          ((smallEtaleInverseImagePresheaf B f A).map φ.hom) :=
  (smallEtaleInverseImageIsoSheafify B f A).hom.naturality φ

end AlgebraicGeometry

end
