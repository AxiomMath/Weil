module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.SiteIsomorphism
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# Direct images of representable sheaves along purely inseparable morphisms

Let `B` be a big étale site and `f : X ⟶ Y` a purely inseparable morphism (finite, universally
injective and surjective) of its underlying category, with `Y` locally noetherian. Base change
`U ↦ U ×_Y X` is then fully faithful on the small étale category of `Y`, and every noetherian
separated étale `X`-scheme `V` is isomorphic to `W ×_Y X` for a noetherian separated étale
`Y`-scheme `W`. Consequently, for every presheaf of sets `F` on the small étale site of `X`
that is represented by a noetherian separated `V`, the direct image
`(f_* F)(U) = F(U ×_Y X) ≅ Hom_X(U ×_Y X, W ×_Y X) ≅ Hom_Y(U, W)` is represented by `W`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.fullyFaithfulSmallEtaleBaseChange`: base change along a
  finite, universally injective, surjective morphism is fully faithful on small étale
  categories.
* `AlgebraicGeometry.BigEtaleSite.presheafDirectImageYonedaIso`: for such `f`, the direct image
  of the Yoneda presheaf of `W ×_Y X` is the Yoneda presheaf of `W`.
* `AlgebraicGeometry.BigEtaleSite.isRepresentableInEt_presheafDirectImage`: the direct image of a
  representable presheaf along a purely inseparable morphism with locally noetherian target is
  representable.
* `AlgebraicGeometry.BigEtaleSite.isRepresentableInEt_smallPushforward`: the same for étale
  sheaves and the sheaf direct image.

## Implementation notes

The proof does not go through the representability criterion by finite stalks and open
difference loci used in the source. It uses instead that base change along a universal
homeomorphism is an equivalence of étale categories (Stacks, Tag 04DZ): full faithfulness on the
whole small étale category is transported from Mathlib's category of étale schemes along the
comparison of the two base-change functors, and the representing object is supplied by the
equivalence `Et(Y) ≌ Et(X)` of noetherian separated étale schemes.

The local noetherianity of `Y` is needed, and holds in the source, where every scheme is
noetherian: for `Y` the spectrum of a non-noetherian local ring whose maximal ideal is nilpotent
and `X` its closed point, `f_*` of the terminal sheaf `X̃` is the terminal sheaf `Ỹ`, which is
represented by no noetherian scheme.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl1988]
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)

section FullyFaithful

variable [IsIntegralHom (B.inclusion.map f)] [UniversallyInjective (B.inclusion.map f)]
  [Surjective (B.inclusion.map f)]

/-- **Base change along a universal homeomorphism is fully faithful on small étale
categories.** For `f : X ⟶ Y` integral, universally injective and surjective, the functor
`U ↦ U ×_Y X` from the small étale category of `Y` to that of `X` is fully faithful. -/
noncomputable def fullyFaithfulSmallEtaleBaseChange :
    (smallEtaleBaseChange B f).FullyFaithful := by
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsEquivalence :=
    Stacks.Etale.etalePullback_isEquivalence (B.inclusion.map f)
  have hfull : (smallEtaleBaseChange B f ⋙ SmallEtale.toEtaleSite B X.obj X.property).Full :=
    Functor.Full.of_iso (SmallEtale.toEtaleSiteBaseChangeIso B f).symm
  have hfaith :
      (smallEtaleBaseChange B f ⋙ SmallEtale.toEtaleSite B X.obj X.property).Faithful :=
    Functor.Faithful.of_iso (SmallEtale.toEtaleSiteBaseChangeIso B f).symm
  have : (smallEtaleBaseChange B f).Full :=
    Functor.Full.of_comp_faithful _ (SmallEtale.toEtaleSite B X.obj X.property)
  have : (smallEtaleBaseChange B f).Faithful :=
    Functor.Faithful.of_comp _ (SmallEtale.toEtaleSite B X.obj X.property)
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **The direct image of the sheaf represented by `W ×_Y X` is the sheaf represented by
`W`.** For `f : X ⟶ Y` integral, universally injective and surjective and `W` étale over `Y`,
`(f_* (W ×_Y X)~)(U) = Hom_X(U ×_Y X, W ×_Y X) ≅ Hom_Y(U, W)`, naturally in `U`. -/
noncomputable def presheafDirectImageYonedaIso (W : SmallEtale B Y.obj Y.property) :
    (presheafDirectImage B f (Type u)).obj (yoneda.obj ((smallEtaleBaseChange B f).obj W)) ≅
      yoneda.obj W :=
  NatIso.ofComponents
    (fun U ↦ ((fullyFaithfulSmallEtaleBaseChange f).homEquiv (X := U.unop) (Y := W)).symm.toIso)
    (fun {U U'} g ↦ by
      ext (a : (smallEtaleBaseChange B f).obj U.unop ⟶ (smallEtaleBaseChange B f).obj W)
      apply (fullyFaithfulSmallEtaleBaseChange f).map_injective
      change (smallEtaleBaseChange B f).map ((fullyFaithfulSmallEtaleBaseChange f).preimage
          ((smallEtaleBaseChange B f).map g.unop ≫ a)) = (smallEtaleBaseChange B f).map
          (g.unop ≫ (fullyFaithfulSmallEtaleBaseChange f).preimage a)
      rw [Functor.FullyFaithful.map_preimage, Functor.map_comp,
        Functor.FullyFaithful.map_preimage])

end FullyFaithful

/-- **The direct image of a representable sheaf along a purely inseparable morphism is
representable.** Let `f : X ⟶ Y` be purely inseparable, with `Y` locally noetherian, and let `F`
be a presheaf of sets on the small étale site of `X` that is representable by a noetherian
separated étale `X`-scheme. Then the direct image `f_* F` is representable on `Y` by a
noetherian separated étale `Y`-scheme. -/
@[weil "lem_fk103_purely_inseparable_direct_image_representable"]
theorem isRepresentableInEt_presheafDirectImage
    (hf : (B.inclusion.map f).IsPurelyInseparable) [IsLocallyNoetherian Y.obj]
    {F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ Type u} (hF : SmallEtale.IsRepresentableInEt F) :
    SmallEtale.IsRepresentableInEt ((presheafDirectImage B f (Type u)).obj F) := by
  have : IsFinite (B.inclusion.map f) := hf.isFinite
  have : UniversallyInjective (B.inclusion.map f) := hf.universallyInjective
  have : Surjective (B.inclusion.map f) := hf.surjective
  obtain ⟨V, hV, ⟨e⟩⟩ := hF
  have := SmallNoetherianSeparatedEtale.essSurj_baseChange f
  let V' : SmallNoetherianSeparatedEtale B X.obj X.property := ⟨V, hV⟩
  let W := (SmallNoetherianSeparatedEtale.baseChange f).objPreimage V'
  let eW : (smallEtaleBaseChange B f).obj W.obj ≅ V :=
    (SmallNoetherianSeparatedEtale.inclusion B X.obj X.property).mapIso
      ((SmallNoetherianSeparatedEtale.baseChange f).objObjPreimageIso V')
  refine ⟨W.obj, W.property, ⟨(presheafDirectImageYonedaIso f W.obj).symm ≪≫
    (presheafDirectImage B f (Type u)).mapIso (yoneda.mapIso eW ≪≫ e)⟩⟩

/-- **The direct image of a representable étale sheaf along a purely inseparable morphism is
representable**, for the sheaf direct image `smallPushforward`. -/
theorem isRepresentableInEt_smallPushforward
    (hf : (B.inclusion.map f).IsPurelyInseparable) [IsLocallyNoetherian Y.obj]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)}
    (hF : SmallEtale.IsRepresentableInEt F.obj) :
    SmallEtale.IsRepresentableInEt ((B.smallPushforward f (Type u)).obj F).obj :=
  isRepresentableInEt_presheafDirectImage f hf hF

end AlgebraicGeometry.BigEtaleSite

end
