module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Weil.Attr
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# The universal property of the derived category

Let `A` be an abelian category and `Q : K(A) ⥤ D(A)` the localization functor from the homotopy
category of cochain complexes to the derived category (`DerivedCategory.Qh`). A functor
`G : K(A) ⥤ E` which sends every quasi-isomorphism to an isomorphism factors through `D(A)`, and
the factorization is unique: any two factorizations `G₁, G₂ : D(A) ⥤ E`, each with an
isomorphism `Q ⋙ Gᵢ ≅ G`, are related by exactly one natural isomorphism `G₁ ≅ G₂` compatible
with the given isomorphisms.

## Main results

* `DerivedCategory.exists_lifting_Qh`: existence of a factorization through `D(A)`.
* `DerivedCategory.existsUnique_iso_of_lifting_Qh`: two factorizations are related by a unique
  compatible natural isomorphism.
* `DerivedCategory.Qh_universal_property`: both together; this is the theorem.

## Implementation notes

A factorization of `G` through `D(A)` is a functor `G'` together with an isomorphism
`Qh ⋙ G' ≅ G` (this is Mathlib's `CategoryTheory.Localization.Lifting`), rather than an equality
of functors `Qh ⋙ G' = G`. The derived category is characterized by its universal property
only up to equivalence, so equality of functors out of it is not meaningful; "exactly one
factorization" accordingly means "unique up to a unique compatible isomorphism". Existence is
`CategoryTheory.Localization.lift`, uniqueness is the full faithfulness of precomposition
with `Qh`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

/- FK's statement asks for strict equality `G' ∘ Q = G`
and literal uniqueness; for Mathlib's `DerivedCategory` (a localization fixed only up to
equivalence through `HasDerivedCategory`) strict existence and strict uniqueness are both false
in general (a localization functor need be neither injective nor surjective on objects). The
standard meaning (unique up to unique iso) is stated. -/

@[expose] public section

open CategoryTheory

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {E : Type*} [Category* E]

/-- A functor `G : K(A) ⥤ E` inverting quasi-isomorphisms factors through the derived category:
there is `G' : D(A) ⥤ E` with `Qh ⋙ G' ≅ G`. -/
theorem exists_lifting_Qh (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E)
    (hG : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy G) :
    ∃ G' : DerivedCategory C ⥤ E, Nonempty (Qh ⋙ G' ≅ G) :=
  ⟨Localization.lift G hG Qh, ⟨Localization.fac G hG Qh⟩⟩

/-- Two factorizations `G₁, G₂` of a functor `G : K(A) ⥤ E` through the derived category, with
isomorphisms `e₁ : Qh ⋙ G₁ ≅ G` and `e₂ : Qh ⋙ G₂ ≅ G`, are related by exactly one natural
isomorphism `τ : G₁ ≅ G₂` such that `Qh ⋙ τ` followed by `e₂` is `e₁`. -/
theorem existsUnique_iso_of_lifting_Qh {G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E}
    {G₁ G₂ : DerivedCategory C ⥤ E} (e₁ : Qh ⋙ G₁ ≅ G) (e₂ : Qh ⋙ G₂ ≅ G) :
    ∃! τ : G₁ ≅ G₂, Functor.isoWhiskerLeft Qh τ ≪≫ e₂ = e₁ := by
  let Φ := (Functor.whiskeringLeft _ _ E).obj (Qh (C := C))
  have hΦ : Φ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Φ
  refine ⟨hΦ.preimageIso (e₁ ≪≫ e₂.symm), ?_, fun τ hτ => ?_⟩
  · ext X
    have := congr_app (hΦ.map_preimage (e₁.hom ≫ e₂.inv)) X
    dsimp [Φ] at this
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.FullyFaithful.preimageIso_hom, Iso.symm_hom]
    rw [this]
    simp
  · ext : 1
    apply hΦ.map_injective
    simp only [Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
    rw [← hτ]
    ext X
    simp [Φ]

/-- The universal property of the derived category: a functor `G : K(A) ⥤ E` sending
quasi-isomorphisms to isomorphisms has a factorization through `D(A)`, and any two
factorizations are related by a unique compatible natural isomorphism. -/
@[weil "lem_fka2_derived_category_universal_property"]
theorem Qh_universal_property (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E)
    (hG : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy G) :
    (∃ G' : DerivedCategory C ⥤ E, Nonempty (Qh ⋙ G' ≅ G)) ∧
      ∀ (G₁ G₂ : DerivedCategory C ⥤ E) (e₁ : Qh ⋙ G₁ ≅ G) (e₂ : Qh ⋙ G₂ ≅ G),
        ∃! τ : G₁ ≅ G₂, Functor.isoWhiskerLeft Qh τ ≪≫ e₂ = e₁ :=
  ⟨exists_lifting_Qh G hG, fun _ _ e₁ e₂ => existsUnique_iso_of_lifting_Qh e₁ e₂⟩

end DerivedCategory

end

/-! ### The shift functor of the derived category descends from the homotopy category -/

/-!
# The shift functor of the derived category descends from the homotopy category

Let `A` be an abelian category, `K(A)` its homotopy category of `ℤ`-indexed cochain complexes,
`D(A)` its derived category and `Qh : K(A) ⥤ D(A)` the localization functor at the
quasi-isomorphisms. The shift `T = [n]` of `K(A)` preserves quasi-isomorphisms, so it descends
to `D(A)`: the shift functor of `D(A)` is additive, it commutes with `Qh` through the canonical
isomorphism `Qh.commShiftIso n : [n] ⋙ Qh ≅ Qh ⋙ [n]`, and on a roof `f / s` it is given by the
roof `f[n] / s[n]`. Moreover, it is the unique functor commuting with `Qh` in this way: any
functor `T' : D(A) ⥤ D(A)` with an isomorphism `Qh ⋙ T' ≅ [n] ⋙ Qh` is isomorphic to the shift,
by a unique isomorphism compatible with the given ones.

## Main definitions

* `CategoryTheory.MorphismProperty.RightFraction.shift`: the shift of a roof, for a class of
  morphisms compatible with the shift.

## Main results

* `CategoryTheory.MorphismProperty.RightFraction.shift_map_map`: a localization functor
  commuting with the shifts sends the shifted roof to the shift of the image of the roof.
* `DerivedCategory.shiftFunctor_additive`: the shift functors of `D(A)` are additive.
* `DerivedCategory.shiftFunctor_map_rightFraction_map`: the shift of `f / s` in `D(A)` is
  `f[n] / s[n]`, up to the isomorphisms `Qh.commShiftIso n`.
* `DerivedCategory.existsUnique_iso_shiftFunctor`: uniqueness of the shift functor of `D(A)`
  among the functors commuting with `Qh`.

## Implementation notes

Freitag–Kiehl construct `D(A)` with the same objects as `K(A)` and state `T ∘ Q = Q ∘ T` as an
equality of functors, and uniqueness as an equality. In Mathlib, `D(A)` is any localization of
`K(A)`, the shift of `D(A)` is induced through `Functor.CommShift.localized`, and `T ∘ Q = Q ∘ T`
is the canonical isomorphism `Qh.commShiftIso n`. Accordingly, uniqueness is stated as the
existence of a unique isomorphism `T' ≅ [n]` whose whiskering by `Qh` is the composite of the
given isomorphism and `Qh.commShiftIso n`. The shift is stated for every `n : ℤ`; Freitag–Kiehl's
`T` is the case `n = 1`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

namespace CategoryTheory

open Category

namespace MorphismProperty

variable {C D : Type*} [Category* C] [Category* D] {W : MorphismProperty C}
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [W.IsCompatibleWithShift A]

/-- The shift by `a` of a roof `X ← X' → Y`, for a class `W` compatible with the shift: the roof
`X⟦a⟧ ← X'⟦a⟧ → Y⟦a⟧`. -/
@[simps]
def RightFraction.shift {X Y : C} (φ : W.RightFraction X Y) (a : A) :
    W.RightFraction (X⟦a⟧) (Y⟦a⟧) where
  X' := φ.X'⟦a⟧
  s := φ.s⟦a⟧'
  hs := (IsCompatibleWithShift.iff W φ.s a).2 φ.hs
  f := φ.f⟦a⟧'

/-- A functor `L` inverting `W` and commuting with the shifts sends the shift of a roof `f / s`
to the shift of `L(f) ∘ L(s)⁻¹`, up to the isomorphisms `L.commShiftIso a`. -/
lemma RightFraction.shift_map_map {X Y : C} (φ : W.RightFraction X Y) (L : C ⥤ D)
    (hL : W.IsInvertedBy L) [L.CommShift A] (a : A) :
    (φ.map L hL)⟦a⟧' = (L.commShiftIso a).inv.app X ≫
      (φ.shift a).map L hL ≫ (L.commShiftIso a).hom.app Y := by
  have := hL _ φ.hs
  have h₁ : (L.map φ.s)⟦a⟧' ≫ (φ.map L hL)⟦a⟧' = (L.map φ.f)⟦a⟧' := by
    rw [← Functor.map_comp, map_s_comp_map]
  have h₂ : L.map (φ.s⟦a⟧') ≫ (φ.shift a).map L hL = L.map (φ.f⟦a⟧') :=
    map_s_comp_map (φ.shift a) L hL
  rw [← cancel_epi ((L.map φ.s)⟦a⟧'), h₁]
  have e₁ := (L.commShiftIso a).hom.naturality φ.s
  have e₂ := (L.commShiftIso a).hom.naturality φ.f
  dsimp at e₁ e₂
  rw [← cancel_epi ((L.commShiftIso a).hom.app φ.X'), ← e₂, ← reassoc_of% e₁,
    Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂]

end MorphismProperty

end CategoryTheory

namespace DerivedCategory

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The shift functors of the derived category are additive. -/
@[weil "lem_fka2_shift_descends_derived"]
theorem shiftFunctor_additive (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive :=
  inferInstance

/-- The shift of a morphism `f / s` of `D(A)` is the morphism `f[n] / s[n]`, up to the
isomorphisms `Qh.commShiftIso n : [n] ⋙ Qh ≅ Qh ⋙ [n]` expressing `T ∘ Q = Q ∘ T`. -/
@[weil "lem_fka2_shift_descends_derived"]
theorem shiftFunctor_map_rightFraction_map {X Y : HomotopyCategory C (ComplexShape.up ℤ)}
    (φ : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).RightFraction X Y) (n : ℤ) :
    (φ.map Qh (Localization.inverts _ _))⟦n⟧' =
      (Qh.commShiftIso n).inv.app X ≫ (φ.shift n).map Qh (Localization.inverts _ _) ≫
        (Qh.commShiftIso n).hom.app Y :=
  φ.shift_map_map Qh _ n

/-- The shift functor `[n]` of `D(A)` is the unique functor commuting with `Qh` and the shift
`[n]` of `K(A)`: for any functor `T'` with an isomorphism `e : Qh ⋙ T' ≅ [n] ⋙ Qh`, there is a
unique isomorphism `T' ≅ [n]` whose whiskering by `Qh` is `e` followed by `Qh.commShiftIso n`. -/
@[weil "lem_fka2_shift_descends_derived"]
theorem existsUnique_iso_shiftFunctor (n : ℤ) (T' : DerivedCategory C ⥤ DerivedCategory C)
    (e : Qh ⋙ T' ≅ shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh) :
    ∃! e' : T' ≅ shiftFunctor (DerivedCategory C) n,
      Functor.whiskerLeft Qh e'.hom = e.hom ≫ (Qh.commShiftIso n).hom := by
  let G := (Functor.whiskeringLeft _ _ (DerivedCategory C)).obj
    (Qh (C := C))
  refine ⟨G.preimageIso (e ≪≫ Qh.commShiftIso n), ?_, ?_⟩
  · exact G.map_preimage (e ≪≫ Qh.commShiftIso n).hom
  · intro e'' h
    ext1
    apply G.map_injective
    exact h.trans (G.map_preimage (e ≪≫ Qh.commShiftIso n).hom).symm

end DerivedCategory
