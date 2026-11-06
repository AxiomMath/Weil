module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# The inverse image preserves presentations by representable sheaves

Let `f : T ⟶ S` be a morphism of schemes of a big étale site, and let `H` be a sheaf of sets on
the small étale site of `S` presented as a coequalizer
`∐_α h_{Z_α} ⇉ ∐_β h_{W_β} → H` of a pair of morphisms between coproducts of representable
sheaves. Since the inverse image `f^*` is a left adjoint, it preserves coproducts and
coequalizers; since `f^* h_Z ≅ h_{T ×_S Z}`, the sheaf `f^* H` is then the coequalizer of a pair
`∐_α h_{T ×_S Z_α} ⇉ ∐_β h_{T ×_S W_β}` on the small étale site of `T`.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageSigmaRepresentableSheafIso` — the isomorphism
  `f^* (∐_α h_{Z_α}) ≅ ∐_α h_{T ×_S Z_α}`.
* `AlgebraicGeometry.isColimitSmallEtaleInverseImageCofork` — `f^* p` is a coequalizer of
  `(f^* a, f^* b)` whenever `p` is a coequalizer of `(a, b)`.
* `AlgebraicGeometry.isColimitSmallEtaleInverseImageSigmaRepresentableCofork` — transported along
  the isomorphisms above, `f^* H` is a coequalizer of a pair
  `∐_α h_{T ×_S Z_α} ⇉ ∐_β h_{T ×_S W_β}`.

## Implementation notes

The representable sheaf `h_Z` is `AlgebraicGeometry.SmallEtale.representableSheaf`, lifted to the
universe `Type (max (u + 1) w)` in which the inverse image of sheaves of sets is formed, as in
`AlgebraicGeometry.smallEtaleInverseImageRepresentableSheafIso`. The index sets of the
coproducts live in any universe `Type t` with `UnivLE.{t, max (u + 1) w}`, so that the
coproducts exist.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- Coproducts indexed by a type of universe at most `max (u + 1) w` exist in the category of
sheaves of sets `Type (max (u + 1) w)` on a small étale site. -/
instance hasColimitsOfShape_discrete_sheaf_smallEtale (X : B.Scheme) (ι : Type t)
    [UnivLE.{t, max (u + 1) w}] :
    HasColimitsOfShape (Discrete ι)
      (Sheaf (SmallEtale.topology B X.obj X.property) (Type (max (u + 1) w))) := by
  have : HasColimitsOfShape (Discrete ι) (Type (max (u + 1) w)) := inferInstance
  exact Sheaf.instHasColimitsOfShape

/-- **`f^*` preserves coequalizers.** If `p : Y ⟶ H` is a coequalizer of `a, b : X ⇉ Y` in the
sheaves of sets on the small étale site of `S`, then `f^* p` is a coequalizer of
`(f^* a, f^* b)`. -/
@[weil "lem_fk102_inverse_image_preserves_coequalizer"]
def isColimitSmallEtaleInverseImageCofork
    {X Y H : Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) w))}
    {a b : X ⟶ Y} {p : Y ⟶ H} (w : a ≫ p = b ≫ p) (hp : IsColimit (Cofork.ofπ p w)) :
    IsColimit (Cofork.ofπ (f := (smallEtaleInverseImage B f (Type (max (u + 1) w))).map a)
      (g := (smallEtaleInverseImage B f (Type (max (u + 1) w))).map b)
      ((smallEtaleInverseImage B f (Type (max (u + 1) w))).map p)
      (by simp only [← Functor.map_comp, w])) :=
  have :=
    (smallEtaleInverseImageAdjunction B f (Type (max (u + 1) w))).leftAdjoint_preservesColimits
  isColimitCoforkMapOfIsColimit _ w hp

variable {ι κ : Type t} [UnivLE.{t, max (u + 1) w}]

/-- **`f^* (∐_α h_{Z_α}) ≅ ∐_α h_{T ×_S Z_α}`.** The inverse image of a coproduct of representable
sheaves is the coproduct of the representable sheaves of the base changes. -/
@[weil "lem_fk102_inverse_image_preserves_coequalizer"]
def smallEtaleInverseImageSigmaRepresentableSheafIso (Z : ι → SmallEtale B S.obj S.property) :
    (smallEtaleInverseImage B f (Type (max (u + 1) w))).obj
        (∐ fun α ↦ (sheafCompose (SmallEtale.topology B S.obj S.property)
          uliftFunctor.{max (u + 1) w, u}).obj
            ((SmallEtale.representableSheaf B S.obj S.property).obj (Z α))) ≅
      ∐ fun α ↦ (sheafCompose (SmallEtale.topology B T.obj T.property)
          uliftFunctor.{max (u + 1) w, u}).obj
            ((SmallEtale.representableSheaf B T.obj T.property).obj
              ((smallEtaleBaseChange B f).obj (Z α))) :=
  have :=
    (smallEtaleInverseImageAdjunction B f (Type (max (u + 1) w))).leftAdjoint_preservesColimits
  PreservesCoproduct.iso _ _ ≪≫
    Sigma.mapIso fun α ↦ (smallEtaleInverseImageRepresentableSheafIso.{w} B f).app (Z α)

/-- **`f^*` preserves a presentation by representable sheaves.** Let
`a, b : ∐_α h_{Z_α} ⇉ ∐_β h_{W_β}` and `p : ∐_β h_{W_β} ⟶ H` be morphisms of sheaves of sets on
the small étale site of `S`, with `p` a coequalizer of `(a, b)`. Transporting `f^* a`, `f^* b`
and `f^* p` along `smallEtaleInverseImageSigmaRepresentableSheafIso` exhibits `f^* H` as a
coequalizer of a pair `∐_α h_{T ×_S Z_α} ⇉ ∐_β h_{T ×_S W_β}` on the small étale site of `T`. -/
@[weil "lem_fk102_inverse_image_preserves_coequalizer"]
def isColimitSmallEtaleInverseImageSigmaRepresentableCofork
    (Z : ι → SmallEtale B S.obj S.property) (W : κ → SmallEtale B S.obj S.property)
    {H : Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) w))}
    {a b : (∐ fun α ↦ (sheafCompose (SmallEtale.topology B S.obj S.property)
          uliftFunctor.{max (u + 1) w, u}).obj
            ((SmallEtale.representableSheaf B S.obj S.property).obj (Z α))) ⟶
        ∐ fun β ↦ (sheafCompose (SmallEtale.topology B S.obj S.property)
          uliftFunctor.{max (u + 1) w, u}).obj
            ((SmallEtale.representableSheaf B S.obj S.property).obj (W β))}
    {p : (∐ fun β ↦ (sheafCompose (SmallEtale.topology B S.obj S.property)
          uliftFunctor.{max (u + 1) w, u}).obj
            ((SmallEtale.representableSheaf B S.obj S.property).obj (W β))) ⟶ H}
    (w : a ≫ p = b ≫ p) (hp : IsColimit (Cofork.ofπ p w)) :
    IsColimit (Cofork.ofπ
      (f := (smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f Z).inv ≫
        (smallEtaleInverseImage B f (Type (max (u + 1) w))).map a ≫
          (smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f W).hom)
      (g := (smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f Z).inv ≫
        (smallEtaleInverseImage B f (Type (max (u + 1) w))).map b ≫
          (smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f W).hom)
      ((smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f W).inv ≫
        (smallEtaleInverseImage B f (Type (max (u + 1) w))).map p)
      (by simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, w])) :=
  Cofork.isColimitOfIsos _ (isColimitSmallEtaleInverseImageCofork.{w} B f w hp) _
    (smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f Z)
    (smallEtaleInverseImageSigmaRepresentableSheafIso.{t, w} B f W) (Iso.refl _)
    (by simp) (by simp) (by simp)

end AlgebraicGeometry

end
