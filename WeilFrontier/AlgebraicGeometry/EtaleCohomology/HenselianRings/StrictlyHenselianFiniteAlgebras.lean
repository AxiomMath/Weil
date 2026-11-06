module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import WeilFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras

/-!
# Finite local algebras over a strictly henselian local ring

Let `A` be a strictly henselian local ring and `B` a local `A`-algebra which is finite as an
`A`-module. Then `B` is strictly henselian.

`B` is henselian, being the localization of the finite `A`-algebra `B` at its maximal ideal.
Since `B` is integral over `A`, the map `A → B` is local, so the residue field of `B` is a
finite extension of the separably closed residue field of `A`, hence separably closed
(`strictlyHenselianLocalRing_of_module_finite`).

## Main results

* `StrictlyHenselianLocalRing.of_module_finite`: a local ring which is finite over a strictly
  henselian local ring is strictly henselian.

## Implementation notes

The source assumes `A → B` local; this is automatic for a finite (hence integral) algebra, and
the hypothesis is omitted. No noetherian hypothesis is needed.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7.
-/

@[expose] public section

open IsLocalRing

universe u v

/-- Let `A` be a strictly henselian local ring and `B` a local `A`-algebra which is finitely
generated as an `A`-module. Then `B` is strictly henselian. -/
@[weil "lem_fk107_finite_local_over_strictly_henselian"]
theorem StrictlyHenselianLocalRing.of_module_finite
    (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A]
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B] :
    StrictlyHenselianLocalRing B := by
  have : IsLocalization.AtPrime B (maximalIdeal B) :=
    IsLocalization.self fun x hx => (IsLocalRing.notMem_maximalIdeal (R := B)).1 hx
  have : HenselianLocalRing B :=
    HenselianLocalRing.of_isLocalization_atPrime_of_finite (R := A) (maximalIdeal B) B
  have : IsLocalHom (algebraMap A B) := by
    have : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    exact ((local_hom_TFAE (algebraMap A B)).out 1 5).2 this
  exact strictlyHenselianLocalRing_of_module_finite A B

end
