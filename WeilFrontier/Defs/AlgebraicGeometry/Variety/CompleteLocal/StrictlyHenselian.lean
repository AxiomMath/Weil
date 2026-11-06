module

public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import Weil.Attr

/-!
# Strictly Henselian local rings

A Henselian local ring `A` is *strictly Henselian* if its residue field `A ⧸ 𝔪(A)` is separably
closed. The notion is the class `StrictlyHenselianLocalRing`, which extends
`HenselianLocalRing A` and `IsSepClosed (IsLocalRing.ResidueField A)`; this file identifies it
with the conjunction of those two properties.

## Main results

* `strictlyHenselianLocalRing_iff`: a local ring is strictly Henselian if and only if it is
  a Henselian local ring with separably closed residue field.
* `StrictlyHenselianLocalRing.of_isSepClosed_residueField`: a Henselian local ring with separably
  closed residue field is strictly Henselian.

## Implementation notes

The source defines strict Henselianity only for noetherian local rings. The class used here
carries no noetherian hypothesis; where it is needed it is the separate instance
`IsNoetherianRing A`. Henselian is `HenselianLocalRing` (lifting of simple roots of monic
polynomials over the residue field), which for noetherian local rings is equivalent to the
source's characterization by finiteness of quasi-finite local homomorphisms.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK], I.1
* [Stacks Project, Tag 03QK](https://stacks.math.columbia.edu/tag/03QK)
-/

@[expose] public section

open IsLocalRing

variable (A : Type*) [CommRing A]

/-- A local ring is strictly Henselian if and only if it is Henselian and its
residue field is separably closed. -/
@[weil "def_fk101_strictly_henselian_local_ring"]
theorem strictlyHenselianLocalRing_iff [IsLocalRing A] :
    StrictlyHenselianLocalRing A ↔
      HenselianLocalRing A ∧ IsSepClosed (ResidueField A) :=
  ⟨fun h => ⟨h.toHenselianLocalRing, h.toIsSepClosed⟩, fun ⟨h₁, h₂⟩ => { h₁, h₂ with }⟩

/-- A Henselian local ring with separably closed residue field is strictly Henselian. -/
theorem StrictlyHenselianLocalRing.of_isSepClosed_residueField [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] : StrictlyHenselianLocalRing A :=
  (strictlyHenselianLocalRing_iff A).2 ⟨inferInstance, inferInstance⟩

end
