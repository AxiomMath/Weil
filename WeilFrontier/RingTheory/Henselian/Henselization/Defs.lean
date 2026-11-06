module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.Defs

/-!
# The Henselization with respect to a map to a field is local

Let `A` be a local ring, `φ : A → k` a local homomorphism to a field and `(Ã, ψ)` a Henselization
of `A` with respect to `φ`. Then `Ã` is a local ring, the structure map `A → Ã` and the map
`ψ : Ã → k` are local homomorphisms, the kernel of `ψ` is the maximal ideal of `Ã`, and `ψ`
induces an embedding of the residue field of `Ã` into `k`.

## Main results

* `IsLocalRing.IsHenselizationAlong.isLocalRing_and_isLocalHom`: `Ã` is local, `A → Ã` and `ψ`
  are local, and `ker ψ = 𝔪(Ã)`.
* `IsLocalRing.IsHenselizationAlong.injective_residueField_lift`: the map `Ã / 𝔪(Ã) → k`
  induced by `ψ` is injective.

## Implementation notes

The Henselization `IsLocalRing.IsHenselizationAlong` is characterized by its universal
properties (Stacks 08HT) rather than built as the colimit of the `φ`-diagrams; locality of `Ã` is
then part of the data, and locality of `A → Ã` and of `ψ` follow from the henselization being
generated over `A` by `𝔪(A)` (`IsLocalRing.IsHenselization.map_maximalIdeal`). The source assumes
`A` noetherian; the results do not need it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace IsLocalRing.IsHenselizationAlong

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type v} [Field k] {φ : A →+* k}
  [IsLocalHom φ] {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}

/-- **The Henselization is local.** For a Henselization `(Ã, ψ)` of `A` with respect to a local
homomorphism `φ : A → k` to a field, `Ã` is a local ring, the structure map `A → Ã` and `ψ` are
local homomorphisms, and the maximal ideal of `Ã` is the kernel of `ψ`. -/
@[weil "lem_fk101_henselization_local"]
theorem isLocalRing_and_isLocalHom (h : IsHenselizationAlong φ Ã ψ) :
    IsLocalRing Ã ∧ IsLocalHom (algebraMap A Ã) ∧ IsLocalHom ψ ∧
      RingHom.ker ψ = maximalIdeal Ã :=
  ⟨inferInstance, h.isLocalHom_algebraMap, h.isLocalHom_ψ, h.ker_ψ⟩

/-- **The residue field of the Henselization embeds in `k`.** The map `ψ : Ã → k` of a
Henselization of `A` with respect to `φ` induces an injective map `Ã / 𝔪(Ã) → k`. -/
@[weil "lem_fk101_henselization_local"]
theorem injective_residueField_lift (h : IsHenselizationAlong φ Ã ψ) :
    Function.Injective (@ResidueField.lift _ _ _ _ _ ψ h.isLocalHom_ψ) :=
  (@ResidueField.lift _ _ _ _ _ ψ h.isLocalHom_ψ).injective

end IsLocalRing.IsHenselizationAlong
