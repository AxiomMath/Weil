module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import Weil.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical

/-!
# A sheaf representable off a closed set, with empty stalks on it, is representable

Let `X` be a scheme, `A ⊆ X` a closed subset and `j : X ∖ A ⟶ X` the open immersion of its
complement. Let `G` be an étale sheaf of sets on `X` such that the restriction `G|_{X ∖ A}` is
isomorphic to the sheaf `Ỹ` represented by an étale `X ∖ A`-scheme `Y`, and such that the stalk
`G_x` is empty at every geometric point `x` of `X` lying over a point of `A`. Then `G` is
isomorphic to the sheaf `Ỹ'` represented by `Y' = Y`, regarded as an étale `X`-scheme through
`j`; in particular `G` is representable.

The proof: the section `ξ ∈ G|_{X ∖ A}(Y) = G(Y')` corresponding to `id_Y` defines, by the
Yoneda lemma, a morphism `ψ : Ỹ' ⟶ G` whose restriction to `X ∖ A` is the given isomorphism
(composed with the identification `Ỹ'|_{X ∖ A} ≅ Ỹ`, which holds because `j` is a
monomorphism). It is an isomorphism because it is bijective on all stalks: at a geometric point
over `X ∖ A` the stalks of `Ỹ'` and `G` are those of their restrictions to `X ∖ A`, and at a
geometric point over `A` both stalks are empty, since `Y' ⟶ X` factors through `X ∖ A`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.representedSheafPostcomposeRestrictIso`: for `U ⟶ X`
  a monomorphism, the identification `Ỹ ≅ Ỹ'|_U`.
* `AlgebraicGeometry.SmallEtale.homOfSection`: the morphism `Ỹ ⟶ G` defined by a section of
  `G` over `Y` (the Yoneda lemma).

## Main results

* `AlgebraicGeometry.SmallEtale.nonempty_iso_representedSheaf_postcompose_of_isEmpty_sheafFiber`:
  the statement for an arbitrary open immersion `U ⟶ X` in the small étale site, the stalks
  being empty at the geometric points over the complement of its image.
* `AlgebraicGeometry.SmallEtale.nonempty_iso_representedSheaf_postcompose_of_range_eq_compl`:
  the statement for `X ∖ A`, presented as an open immersion with image `Aᶜ`.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_range_eq_compl`: in particular `G` is
  representable when `Y` is noetherian and separated.

## Implementation notes

The statement is made on the small étale site `AlgebraicGeometry.SmallEtale` of a big étale
site, with geometric points over algebraically closed fields and stalks
`(geometricPointSitePoint B X hX x).sheafFiber`. The open subscheme `X ∖ A` enters as an object
`U` of the small étale site whose structure morphism is an open immersion with image the
complement of `A`; any such `U` is isomorphic to `X ∖ A` over `X`. That `A` is closed is then
automatic, the image of an open immersion being open. The isomorphism `G|_U ≅ Ỹ` is asked for
as an isomorphism of presheaves, which is the same as an isomorphism of sheaves.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

/- FK states it on Et(X); it is stated on StacksFrontier's `SmallEtale` (the étale site used
throughout), with `X ∖ A` an open immersion `U ⟶ X` in the small étale site with image `Aᶜ`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

/-- A geometric point of `X` lying over a point of the image of an open immersion `j : V ⟶ X`
is the image under `j` of a geometric point of `V`. -/
lemma exists_map_eq_of_isOpenImmersion {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (x : GeometricPoint X) (hx : x.hom default ∈ Set.range j) :
    ∃ t : GeometricPoint V, t.map j = x := by
  have h : Set.range x.hom ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y default]
  refine ⟨⟨x.residueField, IsOpenImmersion.lift j x.hom h⟩, ?_⟩
  cases x
  simp only [GeometricPoint.map, IsOpenImmersion.lift_fac]

end GeometricPoint

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} (U : SmallEtale B X hX)

/-- For an object `U` of the small étale site of `X` whose structure morphism is a
monomorphism and an étale `U`-scheme `Y`, the sheaf `Ỹ` represented by `Y` on the small étale
site of `U` is the restriction to `U` of the sheaf `Ỹ'` represented by `Y`, regarded as an étale
`X`-scheme: `Hom_U(V, Y) = Hom_X(V, Y)`. -/
def representedSheafPostcomposeRestrictIso [Mono U.obj.hom]
    (Y : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (representedSheaf Y).obj ≅ (smallEtalePostcompose B X hX U).op ⋙
      (representedSheaf ((smallEtalePostcompose B X hX U).obj Y)).obj :=
  NatIso.ofComponents
    (fun V ↦ ((Functor.FullyFaithful.ofFullyFaithful
      (smallEtalePostcompose B X hX U)).homEquiv (X := V.unop) (Y := Y)).toIso)
    (fun {V W} h ↦ by
      ext a
      exact (smallEtalePostcompose B X hX U).map_comp h.unop a)

/-- **The Yoneda lemma for represented sheaves.** A section `ξ ∈ G(Y)` defines the morphism
`Ỹ ⟶ G`, `a ↦ a^* ξ`. -/
def homOfSection (G : smallEtaleTopos.{u, u} B X hX) (Y : SmallEtale B X hX)
    (ξ : G.obj.obj (op Y)) : representedSheaf Y ⟶ G :=
  ⟨yonedaEquiv.symm ξ⟩

/-- The morphism `Ỹ' ⟶ G` defined by the section `φ_Y(id_Y)` of `G` over `Y'` restricts on
`U` to the isomorphism `φ : Ỹ ≅ G|_U` it comes from. -/
lemma representedSheafPostcomposeRestrictIso_hom_comp_whiskerLeft_homOfSection
    (G : smallEtaleTopos.{u, u} B X hX) [Mono U.obj.hom]
    (Y : SmallEtale B U.obj.left.1 U.obj.left.property)
    (φ : (representedSheaf Y).obj ≅ (smallEtalePostcompose B X hX U).op ⋙ G.obj) :
    (representedSheafPostcomposeRestrictIso U Y).hom ≫
      Functor.whiskerLeft (smallEtalePostcompose B X hX U).op
        (homOfSection G _ (φ.hom.app (op Y) (𝟙 Y))).hom = φ.hom := by
  ext V a
  change G.obj.map ((smallEtalePostcompose B X hX U).map a).op (φ.hom.app (op Y) (𝟙 Y)) =
    φ.hom.app V a
  have := NatTrans.naturality_apply φ.hom a.op (𝟙 Y)
  exact this.symm.trans (congrArg (φ.hom.app V)
    (show _ = a from Category.comp_id (show V.unop ⟶ Y from a)))

/-- The stalk of the sheaf represented by an étale `U`-scheme `Y`, regarded as an étale
`X`-scheme, is empty at every geometric point of `X` lying over a point outside the image of
`U ⟶ X`. -/
lemma isEmpty_sheafFiber_representedSheaf_postcompose
    (Y : SmallEtale B U.obj.left.1 U.obj.left.property)
    (x : GeometricPoint X) (hx : x.hom default ∉ Set.range (B.inclusion.map U.obj.hom)) :
    IsEmpty (((geometricPointSitePoint B X hX x).sheafFiber (A := Type u)).obj
      (representedSheaf ((smallEtalePostcompose B X hX U).obj Y))) := by
  refine ⟨fun z ↦ hx ?_⟩
  obtain ⟨⟨V⟩, a, -⟩ := Types.jointly_surjective' z
  obtain ⟨p, hp⟩ := V.2
  have h1 := SmallEtale.toScheme_map_comp B X hX (show V.1 ⟶ _ from a)
  have h2 : x.hom = (p ≫ (toScheme B X hX).map (show V.1 ⟶ _ from a) ≫
      B.inclusion.map Y.obj.hom) ≫ B.inclusion.map U.obj.hom := by
    rw [← hp, ← h1]
    simp only [Category.assoc]
    rfl
  exact ⟨_, by rw [h2, Scheme.Hom.comp_apply]⟩

/-- **A sheaf representable on an open, with empty stalks off it, is representable.** Let
`U ⟶ X` be an object of the small étale site of `X` which is an open immersion, `G` an étale
sheaf of sets on `X` and `Y` an étale `U`-scheme with an isomorphism `Ỹ ≅ G|_U`. If the stalk
of `G` is empty at every geometric point of `X` lying over a point outside the image of `U`,
then `G` is isomorphic to the sheaf represented by `Y`, regarded as an étale `X`-scheme. -/
theorem nonempty_iso_representedSheaf_postcompose_of_isEmpty_sheafFiber
    [IsOpenImmersion (B.inclusion.map U.obj.hom)] (G : smallEtaleTopos.{u, u} B X hX)
    (Y : SmallEtale B U.obj.left.1 U.obj.left.property)
    (φ : (representedSheaf Y).obj ≅ (smallEtalePostcompose B X hX U).op ⋙ G.obj)
    (hG : ∀ x : GeometricPoint X, x.hom default ∉ Set.range (B.inclusion.map U.obj.hom) →
      IsEmpty (((geometricPointSitePoint B X hX x).sheafFiber (A := Type u)).obj G)) :
    Nonempty (representedSheaf ((smallEtalePostcompose B X hX U).obj Y) ≅ G) := by
  have : Mono U.obj.hom := B.inclusion.mono_of_mono_map inferInstance
  let ψ := homOfSection G _ (φ.hom.app (op Y) (𝟙 Y))
  suffices IsIso ψ from ⟨asIso ψ⟩
  rw [isIso_iff_forall_bijective_geometricPointSitePoint_sheafFiber]
  intro x
  by_cases hx : x.hom default ∈ Set.range (B.inclusion.map U.obj.hom)
  · obtain ⟨t, rfl⟩ := GeometricPoint.exists_map_eq_of_isOpenImmersion _ x hx
    have hw : IsIso (Functor.whiskerLeft (smallEtalePostcompose B X hX U).op ψ.hom) := by
      have e := representedSheafPostcomposeRestrictIso_hom_comp_whiskerLeft_homOfSection U G Y φ
      have : Functor.whiskerLeft (smallEtalePostcompose B X hX U).op ψ.hom =
          (representedSheafPostcomposeRestrictIso U Y).inv ≫ φ.hom := by
        rw [← e, Iso.inv_hom_id_assoc]
      rw [this]
      infer_instance
    have hn := etaleStalkRestrictionMap_naturality B X hX U t ψ.hom
    rw [← isIso_iff_bijective]
    change IsIso ((etaleStalkPresheafFunctor B X hX _ (Type u)).map ψ.hom)
    have : IsIso (etaleStalkRestrictionMap B X hX U t _ ≫
        (etaleStalkPresheafFunctor B X hX _ (Type u)).map ψ.hom) := by
      rw [← hn]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
        (isIso_etaleStalkRestrictionMap B X hX U t _)
    exact IsIso.of_isIso_comp_left (etaleStalkRestrictionMap B X hX U t _) _
  · have h1 := isEmpty_sheafFiber_representedSheaf_postcompose U Y x hx
    have h2 := hG x hx
    exact ⟨fun a ↦ isEmptyElim a, fun b ↦ isEmptyElim b⟩

/-- **FK I.3: a sheaf representable off a closed set, with empty stalks on it, is
representable.** Let `A ⊆ X`, and let `U ⟶ X` be an open immersion in the small étale site with
image `X ∖ A` (so `A` is closed and `U` is the open subscheme `X ∖ A`). Let `G` be an étale sheaf
of sets on `X` and `Y` an étale `U`-scheme with an isomorphism `Ỹ ≅ G|_U`, and suppose that
`G_x = ∅` for every geometric point `x` of `X` whose image lies in `A`. Then `G ≅ Ỹ'`, where
`Y'` is `Y` regarded as an étale `X`-scheme through `U ⟶ X`. -/
@[weil "lem_fk103_representable_off_closed_with_empty_stalks"]
theorem nonempty_iso_representedSheaf_postcompose_of_range_eq_compl (A : Set X)
    [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (hU : Set.range (B.inclusion.map U.obj.hom) = Aᶜ) (G : smallEtaleTopos.{u, u} B X hX)
    (Y : SmallEtale B U.obj.left.1 U.obj.left.property)
    (φ : (representedSheaf Y).obj ≅ (smallEtalePostcompose B X hX U).op ⋙ G.obj)
    (hG : ∀ x : GeometricPoint X, x.hom default ∈ A →
      IsEmpty (((geometricPointSitePoint B X hX x).sheafFiber (A := Type u)).obj G)) :
    Nonempty (representedSheaf ((smallEtalePostcompose B X hX U).obj Y) ≅ G) :=
  nonempty_iso_representedSheaf_postcompose_of_isEmpty_sheafFiber U G Y φ fun x hx ↦
    hG x (by rwa [hU, Set.mem_compl_iff, not_not] at hx)

/-- **FK I.3, in particular.** Under the hypotheses of
`nonempty_iso_representedSheaf_postcompose_of_range_eq_compl`, with `Y` noetherian and
separated (an object of `Et(X ∖ A)`), the sheaf `G` is representable. -/
@[weil "lem_fk103_representable_off_closed_with_empty_stalks"]
theorem isRepresentableInEt_of_range_eq_compl (A : Set X)
    [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (hU : Set.range (B.inclusion.map U.obj.hom) = Aᶜ) (G : smallEtaleTopos.{u, u} B X hX)
    (Y : SmallEtale B U.obj.left.1 U.obj.left.property)
    (hY : IsNoetherianSeparated B U.obj.left.1 U.obj.left.property Y)
    (φ : (representedSheaf Y).obj ≅ (smallEtalePostcompose B X hX U).op ⋙ G.obj)
    (hG : ∀ x : GeometricPoint X, x.hom default ∈ A →
      IsEmpty (((geometricPointSitePoint B X hX x).sheafFiber (A := Type u)).obj G)) :
    IsRepresentableInEt G.obj := by
  obtain ⟨e⟩ := nonempty_iso_representedSheaf_postcompose_of_range_eq_compl U A hU G Y φ hG
  exact ⟨(smallEtalePostcompose B X hX U).obj Y, hY, ⟨(sheafToPresheaf _ _).mapIso e⟩⟩

end SmallEtale

end AlgebraicGeometry
