module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.FiniteExistence
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite partitions of a scheme of finite type into affine locally closed pieces

Let `X` be a scheme of finite type over a field `k`. Then `X` is the disjoint union of finitely
many locally closed subsets `Y₁, …, Yᵣ` such that each `Yᵢ`, with its reduced induced scheme
structure, is an affine scheme of finite type over `k` (via `Yᵢ → X → Spec k`).

## Main results

* `AlgebraicGeometry.exists_affine_locallyClosed_partition`: a quasi-compact quasi-separated
  scheme is a finite disjoint union of locally closed subsets whose reduced induced schemes are
  affine, with affine inclusions.
* `AlgebraicGeometry.exists_affine_locallyClosed_partition_of_finiteType`: the statement above
  for a scheme of finite type over a field, with each stratum of finite type over the field.

## Implementation notes

The partition is obtained from a finite affine stratification of the quasi-compact
quasi-separated scheme `X` (Stacks, Tag 0F2U), reindexed by `Fin r`. This replaces the
noetherian-induction argument of the source; the stratification gives in addition that each
inclusion of a stratum is an affine morphism. "Of finite type" is `LocallyOfFiniteType` together
with `QuasiCompact`. The reduced structure on a locally closed subset is the reduced induced
scheme `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*][FK]
* [Stacks Project, Tag 0F2U](https://stacks.math.columbia.edu/tag/0F2U)
-/

@[expose] public section

open CategoryTheory Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-- A quasi-compact quasi-separated scheme is the disjoint union of finitely many locally closed
subsets whose reduced induced schemes are affine, with affine inclusions. -/
theorem exists_affine_locallyClosed_partition (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (r : ℕ) (Y : Fin r → Set X) (hY : ∀ i, IsLocallyClosed (Y i)),
      Pairwise (fun i j => Disjoint (Y i) (Y j)) ∧ (⋃ i, Y i) = Set.univ ∧
      ∀ i, IsAffine (reducedInducedScheme (Y i) (hY i)) ∧
        IsAffineHom (reducedInducedInclusion (Y i) (hY i)) := by
  obtain ⟨I, hI, order, ⟨s⟩⟩ :=
    (hasFiniteAffineStratification_iff.{u, 0} X).2 ⟨inferInstance, inferInstance⟩
  let : PartialOrder I := order
  have hP := s.isLocallyFiniteStratification.isStratification.isPartition
  let e : I ≃ Fin (Nat.card I) := Finite.equivFin I
  refine ⟨Nat.card I, fun i => s.strata (e.symm i), fun i => hP.locallyClosed _, ?_, ?_, ?_⟩
  · intro i j hij
    exact hP.disjoint _ _ (e.symm.injective.ne hij)
  · rw [← hP.cover]
    exact e.symm.surjective.iUnion_comp s.strata
  · intro i
    exact ⟨s.isAffine _, s.isAffineHom _⟩

/-- **Partition of a scheme of finite type over a field into affine pieces.** A scheme `X` of
finite type over a field `k` is the disjoint union of finitely many locally closed subsets
`Y₁, …, Yᵣ` such that each `Yᵢ`, with its reduced induced scheme structure, is an affine scheme
of finite type over `k` via `Yᵢ → X → Spec k`. -/
@[weil "lem_fk0_finite_type_scheme_affine_locally_closed_partition"]
theorem exists_affine_locallyClosed_partition_of_finiteType {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (r : ℕ) (Y : Fin r → Set X) (hY : ∀ i, IsLocallyClosed (Y i)),
      Pairwise (fun i j => Disjoint (Y i) (Y j)) ∧ (⋃ i, Y i) = Set.univ ∧
      ∀ i, IsAffine (reducedInducedScheme (Y i) (hY i)) ∧
        LocallyOfFiniteType (reducedInducedInclusion (Y i) (hY i) ≫ f) ∧
        QuasiCompact (reducedInducedInclusion (Y i) (hY i) ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨r, Y, hY, hdisj, hcover, hY'⟩ := exists_affine_locallyClosed_partition X
  refine ⟨r, Y, hY, hdisj, hcover, fun i => ?_⟩
  have : IsAffine (reducedInducedScheme (Y i) (hY i)) := (hY' i).1
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
