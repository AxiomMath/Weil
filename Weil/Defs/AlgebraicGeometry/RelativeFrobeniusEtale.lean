module

public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
public import Weil.Defs.AlgebraicGeometry.Frobenius
public import Weil.Attr

/-!
# Relative Frobenius morphisms over a finite field

Let `κ` be a finite field with `q` elements and `u : U ⟶ X` a morphism of schemes over `κ`.
Write `Fr_X` for the Frobenius endomorphism of `X` with respect to `κ`
(`AlgebraicGeometry.frobeniusOver`) and `Fr_X⁻¹(U) = U ×_{u, X, Fr_X} X` for the base change of
`U` along it. A morphism `φ : U ⟶ Fr_X⁻¹(U)` is a *relative Frobenius of `U` over `X`* if it is
a morphism over `X` (its projection to `X` is `u`) and its projection to `U` is the Frobenius
`Fr_U` of `U`.

If `q = p ^ f` with `p` the characteristic of `κ`, then `Fr_X` is the `f`-fold absolute
Frobenius of `X`, so `Fr_X⁻¹(U)` is the `f`-fold Frobenius twist of `U` over `X` and the
relative Frobenius is the `f`-fold relative Frobenius of the Stacks Project,
`AlgebraicGeometry.nFoldRelativeFrobenius`.

## Main definitions

* `AlgebraicGeometry.IsRelativeFrobenius u φ`: the morphism `φ : U ⟶ Fr_X⁻¹(U)` is a relative
  Frobenius of `U` over `X`.

## Main results

* `AlgebraicGeometry.isRelativeFrobenius_iff_eq_nFoldRelativeFrobenius`: for every presentation
  `q = p ^ f`, a morphism is a relative Frobenius of `U` over `X` if and only if, under the
  identification of `Fr_X⁻¹(U)` with the `f`-fold Frobenius twist, it is the `f`-fold relative
  Frobenius.

## Implementation notes

The fibre product `Fr_X⁻¹(U)` is Mathlib's `pullback u Fr_X`, whose first projection goes to
`U` and whose second projection goes to `X`; the source writes the factors in the other order,
so its `pr₁` is `pullback.snd` and its `pr₂` is `pullback.fst`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter II, § 3.
* [Stacks Project, Tag 0CCG](https://stacks.math.columbia.edu/tag/0CCG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {κ : Type u} [Field κ] [Fintype κ]

/-- A morphism `φ : U ⟶ Fr_X⁻¹(U) = U ×_{u, X, Fr_X} X` is a **relative Frobenius** of `U`
over `X`, for a morphism `u : U ⟶ X` of schemes over the finite field `κ`, if it is a morphism
over `X` (its projection to `X` is `u`) and its projection to `U` is the Frobenius of `U`. -/
@[weil "def_fk203_relative_frobenius_etale"]
structure IsRelativeFrobenius {U X : Over (Spec (.of κ))} (u : U ⟶ X)
    (φ : U.left ⟶ pullback u.left (frobeniusOver κ X).left) : Prop where
  /-- The relative Frobenius is a morphism over `X`. -/
  comp_snd : φ ≫ pullback.snd u.left (frobeniusOver κ X).left = u.left
  /-- The projection of the relative Frobenius to `U` is the Frobenius of `U`. -/
  comp_fst : φ ≫ pullback.fst u.left (frobeniusOver κ X).left = (frobeniusOver κ U).left

variable {U X : Over (Spec (.of κ))} {u : U ⟶ X}

lemma isRelativeFrobenius_iff (φ : U.left ⟶ pullback u.left (frobeniusOver κ X).left) :
    IsRelativeFrobenius u φ ↔
      φ ≫ pullback.snd u.left (frobeniusOver κ X).left = u.left ∧
        φ ≫ pullback.fst u.left (frobeniusOver κ X).left = (frobeniusOver κ U).left :=
  ⟨fun h ↦ ⟨h.comp_snd, h.comp_fst⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Two relative Frobenius morphisms of `U` over `X` are equal. -/
lemma IsRelativeFrobenius.eq {φ ψ : U.left ⟶ pullback u.left (frobeniusOver κ X).left}
    (hφ : IsRelativeFrobenius u φ) (hψ : IsRelativeFrobenius u ψ) : φ = ψ :=
  pullback.hom_ext (hφ.comp_fst.trans hψ.comp_fst.symm) (hφ.comp_snd.trans hψ.comp_snd.symm)

/-- **Comparison with the Stacks Project.** If `Fintype.card κ = p ^ f`, then, under the
identification of `Fr_X⁻¹(U)` with the `f`-fold Frobenius twist of `U` over `X` (the Frobenius
of `X` is the `f`-fold absolute Frobenius), a morphism `φ : U ⟶ Fr_X⁻¹(U)` is a relative
Frobenius of `U` over `X` if and only if it is the `f`-fold relative Frobenius
`nFoldRelativeFrobenius` of `U`, regarded as a scheme over `X` through `u`. -/
@[weil "def_fk203_relative_frobenius_etale"]
theorem isRelativeFrobenius_iff_eq_nFoldRelativeFrobenius (p f : ℕ) [Fact p.Prime] [CharP κ p]
    (hcard : Fintype.card κ = p ^ f)
    (φ : U.left ⟶ pullback u.left (frobeniusOver κ X).left) :
    IsRelativeFrobenius u φ ↔
      φ ≫ (pullback.congrHom rfl (frobeniusOver_left_eq X p f hcard)).hom =
        (nFoldRelativeFrobenius X.left p (Stacks.Frobenius.isInCharacteristic_of_over X) f
          (Over.mk u.left)).left := by
  have hX := Stacks.Frobenius.isInCharacteristic_of_over (p := p) X
  have hfst := nFoldRelativeFrobenius_fst X.left p hX f (Over.mk u.left)
  have hsnd := nFoldRelativeFrobenius_snd X.left p hX f (Over.mk u.left)
  have hU : (frobeniusOver κ U).left = absoluteFrobeniusPow U.left p
      (Stacks.Frobenius.isInCharacteristic_of_over U) f :=
    frobeniusOver_left_eq U p f hcard
  constructor
  · intro h
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
        h.comp_fst, hU]
      exact hfst.symm
    · rw [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
        h.comp_snd]
      exact hsnd.symm
  · intro h
    constructor
    · have := congrArg (· ≫ pullback.snd _ _) h
      simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
        Category.comp_id] at this
      exact this.trans hsnd
    · have := congrArg (· ≫ pullback.fst _ _) h
      simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
        Category.comp_id] at this
      rw [hU]
      exact this.trans hfst

end AlgebraicGeometry
