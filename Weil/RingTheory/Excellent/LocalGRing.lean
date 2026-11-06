module

public import StacksFrontier.RingTheory.Excellent.LocalGRing
public import Weil.Attr

/-!
# Excellent local rings

A Noetherian ring is *excellent* if it is a G-ring, J-2 and universally catenary
(`IsExcellent`, Stacks Tag 07QT). For a Noetherian local ring the J-2 condition is a
consequence of the G-ring condition (`isJ2_of_isGRing_of_isLocalRing`), so a Noetherian local
ring is excellent exactly when it is a universally catenary G-ring: universally catenary, and
the map from each localization `A_𝔭` to its completion is regular. This is the notion of an
excellent local ring used by Freitag and Kiehl.

## Main results

* `IsExcellent.iff_isGRing_and_isUniversallyCatenary`: a Noetherian local ring is excellent if
  and only if it is a universally catenary G-ring.
* `IsExcellent.isGRing`, `IsExcellent.isUniversallyCatenary`, `IsExcellent.of_isGRing`: the
  two directions, in the form consumers use.

## Implementation notes

Excellence of a local ring is not a new definition: it is `IsExcellent A` for a ring carrying
`[IsLocalRing A]`. Universal catenarity is `Ring.IsUniversallyCatenary`, which agrees with the
dimension-formula formulation by `Ring.isUniversallyCatenary_iff_forall_ringKrullDim_eq`. The
second condition is the standard G-ring condition on formal fibres (EGA IV 7.8.2), which is
the condition the cited source [Matsumura] intends.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1]
* [Stacks Project, Tag 07QT](https://stacks.math.columbia.edu/tag/07QT)
* [Matsumura, *Commutative Algebra*, §34]
-/

/- FK's printed clause (b) (regular locus of Spec B̂ is the
preimage of that of Spec B for every finitely generated local A → B) is replaced by the standard
G-ring condition, following the standard (EGA/Stacks) meaning. -/

@[expose] public section

universe u

namespace IsExcellent

variable {A : Type u} [CommRing A]

/-- An excellent ring is a G-ring. -/
theorem isGRing (h : IsExcellent A) : IsGRing A :=
  h.1.2.1

/-- An excellent ring is Noetherian. -/
theorem isNoetherianRing (h : IsExcellent A) : IsNoetherianRing A :=
  h.1.1

/-- An excellent ring is universally catenary. -/
theorem isUniversallyCatenary (h : IsExcellent A) : Ring.IsUniversallyCatenary A :=
  h.2

/-- A universally catenary Noetherian local G-ring is excellent. -/
theorem of_isGRing [IsNoetherianRing A] [IsLocalRing A] (hG : IsGRing A)
    (hC : Ring.IsUniversallyCatenary A) : IsExcellent A :=
  ⟨isQuasiExcellent_of_isGRing_of_isLocalRing A hG, hC⟩

/-- **Excellent local rings.** A Noetherian local ring is excellent if and only if it is a
G-ring and universally catenary. -/
@[weil "def_fk101_excellent_local_ring"]
theorem iff_isGRing_and_isUniversallyCatenary [IsNoetherianRing A] [IsLocalRing A] :
    IsExcellent A ↔ IsGRing A ∧ Ring.IsUniversallyCatenary A :=
  ⟨fun h => ⟨h.isGRing, h.isUniversallyCatenary⟩, fun h => of_isGRing h.1 h.2⟩

end IsExcellent

end
