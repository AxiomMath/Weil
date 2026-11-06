module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# The Henselization along a map to a field is faithfully flat

Let `A` be a local ring and `φ : A → k` a local homomorphism to a field. If `(Ã, ψ)` is a
Henselization of `A` with respect to `φ`, then the structure map `A → Ã` is faithfully flat: `Ã`
is a flat `A`-module, being a filtered colimit of étale `A`-algebras, and a flat local
homomorphism of local rings is faithfully flat.

## Main results

* `IsLocalRing.IsHenselizationAlong.faithfullyFlat_algebraMap`: the ring map `A → Ã` is
  faithfully flat; equivalently (`RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`) it is flat
  and `Spec Ã → Spec A` is surjective.

## Implementation notes

The source assumes `A` noetherian; the statement does not need it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
* [StacksProject 07QM](https://stacks.math.columbia.edu/tag/07QM)
-/

public section

namespace IsLocalRing.IsHenselizationAlong

universe u v w

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type v} [Field k] {φ : A →+* k}
  [IsLocalHom φ] {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}

/-- **The Henselization is faithfully flat.** For a local homomorphism `φ : A → k` from a local
ring to a field and a Henselization `(Ã, ψ)` of `A` with respect to `φ`, the structure map
`A → Ã` is faithfully flat. -/
@[weil "lem_fk101_henselization_faithfully_flat"]
theorem faithfullyFlat_algebraMap (h : IsHenselizationAlong φ Ã ψ) :
    (algebraMap A Ã).FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr h.faithfullyFlat

end IsLocalRing.IsHenselizationAlong
