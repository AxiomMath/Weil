module

public import Weil.Defs.CategoryTheory.ObjectProperty.MittagLefflerArtinRees
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.MittagLefflerArtinReesSheaves
public import Weil.Defs.CategoryTheory.Subobject.Limits
public import Weil.Attr

/-!
# Under MLAR the universal image is the stable image

Let `F = (F_n)_{n ∈ ℤ}` be a projective system in an abelian category and let
`ε_{t,n} : F_{n+t} ⟶ F_n` be its maps. Since `ε_{t',n} = ε_{t,n} ∘ ε_{t'-t,n+t}` for `t ≤ t'`,
the images `im(ε_{t,n})` decrease in `t`. If they are constant for `t ≥ r` (in every degree,
the Mittag-Leffler–Artin–Rees condition with constant `r`), their intersection, the universal
image `F̄_n`, equals `im(ε_{t,n})` for every `t ≥ r`.

## Main results

* `CategoryTheory.ProjectiveSystem.IsMittagLefflerArtinReesWith.subobjectModule_universalImage`:
  for a projective system of `l`-power torsion modules satisfying MLAR with constant `r`, the
  universal image `F̄_n` is the image of `ε^t_{F,n}` for all `n` and all `t ≥ r`.
* `IsMittagLefflerArtinReesWith.universalImage_eq` (namespace
  `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem`): the same for a projective system
  of `l`-torsion sheaves on the small étale site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u v v₁ u₁

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] (F : ℤᵒᵖ ⥤ C)

/-- The images of the maps `ε_{t,n} : F_{n+t} ⟶ F_n` decrease in `t`. -/
private theorem imageSubobject_mapAddNat_antitone (n : ℤ) :
    Antitone fun t : ℕ ↦ imageSubobject (F.mapAddNat n t) := by
  intro s t hst
  have h : F.mapAddNat n t =
      F.map (homOfLE (by omega : n + s ≤ n + t)).op ≫ F.mapAddNat n s := by
    rw [← F.map_comp]
    rfl
  simp only [h]
  exact imageSubobject_comp_le _ _

variable [HasProductsOfShape ℕ C]

/-- If the images of the maps `ε_{t,n}` are constant for `t ≥ r`, then the universal image
`F̄_n` is the image of `ε_{t,n}` for every `t ≥ r`. -/
private theorem universalImage_eq_imageSubobject_of_forall_eq {n : ℤ} {r : ℕ}
    (h : ∀ t, r ≤ t → imageSubobject (F.mapAddNat n t) = imageSubobject (F.mapAddNat n r))
    {t : ℕ} (ht : r ≤ t) :
    F.universalImage n = imageSubobject (F.mapAddNat n t) := by
  refine le_antisymm (F.universalImage_le_imageSubobject n t) ?_
  rw [le_universalImage_iff]
  intro s
  rcases le_total r s with hs | hs
  · rw [h t ht, h s hs]
  · exact (F.imageSubobject_mapAddNat_antitone n (hs.trans ht))

end Functor

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- **Under MLAR the universal image is the stable image.** If a projective system `F` of
`l`-power torsion `Λ`-modules satisfies MLAR with constant `r`, then the universal image
`F̄_n ⊆ F_n` is the image of `ε^t_{F,n} : F_{n+t} ⟶ F_n` for all `n` and all `t ≥ r`. -/
@[weil "lem_fk112_universal_image_system_eq_image"]
theorem IsMittagLefflerArtinReesWith.subobjectModule_universalImage
    {F : ProjectiveSystem.{v} Λ l} {r : ℕ} (hF : F.IsMittagLefflerArtinReesWith r) (n : ℤ)
    {t : ℕ} (ht : r ≤ t) :
    ModuleCat.subobjectModule _ (F.obj.universalImage n) = imageNatMap F t n := by
  rw [ProjectiveSystem.subobjectModule_universalImage]
  refine le_antisymm (iInf_le_of_le t le_rfl) (le_iInf fun s ↦ ?_)
  change imageNatMap F t n ≤ imageNatMap F s n
  rcases le_total r s with hs | hs
  · rw [hF.imageNatMap_eq_of_le ht hs]
  · exact imageNatMap_antitone F n (hs.trans ht)

end ProjectiveSystem

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

/-- **Under MLAR the universal image is the stable image.** If a projective system `F` of
`l`-torsion sheaves on the small étale site satisfies MLAR with constant `r`, then the universal
image `F̄_n` is the image of `ε_{t,n} : F_{n+t} ⟶ F_n` for all `n` and all `t ≥ r`. -/
@[weil "lem_fk112_universal_image_system_eq_image"]
theorem IsMittagLefflerArtinReesWith.universalImage_eq
    {F : LTorsionProjectiveSystem.{u} B S hS l} {r : ℕ} (hF : IsMittagLefflerArtinReesWith F r)
    (n : ℤ) {t : ℕ} (ht : r ≤ t) :
    F.obj.universalImage n = imageShiftι F t n :=
  F.obj.universalImage_eq_imageSubobject_of_forall_eq (fun s hs ↦ hF s hs n) ht

end AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem
