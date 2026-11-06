module

public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# The étale category `Et(X)` is essentially small

The category `Et(S)` of noetherian separated étale `S`-schemes has a set of objects such that
every object is isomorphic to a member of it. Here this is the statement that
`AlgebraicGeometry.SmallNoetherianSeparatedEtale B S hS` is `u`-essentially small, which it
inherits, as a full subcategory, from the small étale category of `S`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.essentiallySmall`: `Et(S)` is
  `EssentiallySmall.{u}`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_small_set_nonempty_iso`: there is a
  `u`-small set `R` of objects of `Et(S)` such that every object is isomorphic to a member of `R`.

## Implementation notes

Freitag–Kiehl prove this by bounding the gluing data of a noetherian étale `S`-scheme
(finitely many affine pieces, each a quotient of a polynomial ring over a ring of a fixed affine
cover of `S`). Here the objects of `Et(S)` lie below the size cutoff of the ambient big étale
site, and the essential smallness of the small étale category of `S`
(`AlgebraicGeometry.SmallEtale.essentiallySmall`) is used instead.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`Et(S)` is essentially small**, being a full subcategory of the small étale category of
`S`. -/
@[weil "lem_fk102_etale_site_essentially_small"]
instance essentiallySmall : EssentiallySmall.{u} (SmallNoetherianSeparatedEtale B S hS) :=
  essentiallySmall_of_fully_faithful (inclusion B S hS)

/-- **There is a set of objects of `Et(S)` such that every object of `Et(S)` is isomorphic to a
member of it.** -/
@[weil "lem_fk102_etale_site_essentially_small"]
theorem exists_small_set_nonempty_iso :
    ∃ R : Set (SmallNoetherianSeparatedEtale B S hS), Small.{u} R ∧
      ∀ U : SmallNoetherianSeparatedEtale B S hS, ∃ V ∈ R, Nonempty (U ≅ V) := by
  have hsmall := ((essentiallySmall_iff.{u} (SmallNoetherianSeparatedEtale B S hS)).1
    inferInstance).1
  exact ⟨Set.range (fromSkeleton (SmallNoetherianSeparatedEtale B S hS)).obj,
    small_range _, fun U ↦ ⟨_, ⟨toSkeleton U, rfl⟩,
      (Quotient.mk_out (s := isIsomorphicSetoid _) U).map Iso.symm⟩⟩

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
