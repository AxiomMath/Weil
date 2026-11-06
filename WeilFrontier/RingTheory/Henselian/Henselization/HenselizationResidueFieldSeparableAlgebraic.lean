module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.Defs

/-!
# The residue field of a Henselization is separable algebraic

Let `A` be a local ring, `φ : A → k` a local homomorphism to a field and `(Ã, ψ)` a Henselization
of `A` with respect to `φ`. Then the residue field of `Ã` is a separable algebraic extension of the
residue field of `A`: it is isomorphic, over `κ(A)`, to the separable closure `κ_φ` of `κ(A)` in
`k`.

## Main results

* `IsLocalRing.IsHenselizationAlong.nonempty_residueFieldAlgEquiv`: a `κ(A)`-isomorphism
  `κ_φ ≃ κ(Ã)`.
* `IsLocalRing.IsHenselizationAlong.isSeparable_residueField`: `κ(Ã)` is separable (in
  particular algebraic) over `κ(A)`.

## Implementation notes

The source assumes `A` noetherian and argues through the colimit description of `Ã`; here the
residue field of `Ã` is identified with `κ_φ` by the characterization of `IsHenselizationAlong`,
and noetherianity is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace IsLocalRing.IsHenselizationAlong

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type v} [Field k] {φ : A →+* k}
  [IsLocalHom φ] {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}

/-- The residue field of a Henselization `Ã` of `A` with respect to `φ` is isomorphic, over the
residue field of `A`, to the separable closure `κ_φ` of `κ(A)` in `k`. -/
theorem nonempty_residueFieldAlgEquiv (h : IsHenselizationAlong φ Ã ψ) :
    letI := h.isLocalHom_algebraMap
    Nonempty (residueSeparableClosure φ ≃ₐ[ResidueField A] ResidueField Ã) := by
  have := h.isHenselization
  have := h.isLocalHom_algebraMap
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := A)
    (L := residueSeparableClosure φ) (Rh := Ã)
  refine ⟨{ e with commutes' := fun x => ?_ }⟩
  obtain ⟨a, rfl⟩ := residue_surjective x
  change e (algebraMap _ _ (residue A a)) = _
  rw [he]
  rfl

/-- **The residue field of a Henselization is separable algebraic.** For a Henselization `Ã` of
the local ring `A` with respect to a local homomorphism `φ : A → k` to a field, the residue field
of `Ã` is a separable algebraic extension of the residue field of `A`. -/
@[weil "lem_fk107_henselization_residue_field_separable_algebraic"]
theorem isSeparable_residueField (h : IsHenselizationAlong φ Ã ψ) :
    letI := h.isLocalHom_algebraMap
    Algebra.IsSeparable (ResidueField A) (ResidueField Ã) := by
  have := h.isLocalHom_algebraMap
  obtain ⟨e⟩ := h.nonempty_residueFieldAlgEquiv
  exact AlgEquiv.Algebra.isSeparable e

/-- The residue field of a Henselization of `A` is algebraic over the residue field of `A`. -/
theorem isAlgebraic_residueField (h : IsHenselizationAlong φ Ã ψ) :
    letI := h.isLocalHom_algebraMap
    Algebra.IsAlgebraic (ResidueField A) (ResidueField Ã) := by
  have := h.isLocalHom_algebraMap
  have := h.isSeparable_residueField
  infer_instance

end IsLocalRing.IsHenselizationAlong
