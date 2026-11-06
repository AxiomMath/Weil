module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Weil.Attr

/-!
# Faithful flatness from a finite affine cover

Let `f : T ⟶ S` be a flat surjective morphism of schemes, `U ⊆ S` an affine open and
`V₁, …, Vₙ` finitely many affine opens of `T` covering `f⁻¹(U)`. Then the ring map
`Γ(S, U) → ∏ₖ Γ(T, Vₖ)` induced by `f` is faithfully flat.

## Main results

* `AlgebraicGeometry.faithfullyFlat_piRingHom_appLE`: the ring map
  `Γ(S, U) → ∏ₖ Γ(T, Vₖ)` is faithfully flat.

## Implementation notes

The cover is given by two hypotheses, `Vₖ ≤ f⁻¹(U)` for every `k` and
`f⁻¹(U) ≤ ⨆ₖ Vₖ`, which together say `f⁻¹(U) = ⋃ₖ Vₖ`. Quasi-compactness of `f` is
only needed for such a finite cover to exist and is not a hypothesis here. The proof
works with prime ideals directly: each `Γ(T, Vₖ)` is flat over `Γ(S, U)`, a finite
product of flat modules is flat, and the induced map on prime spectra is surjective
because `f` is.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.III.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {T S : Scheme.{u}} (f : T ⟶ S) {U : S.Opens} {ι : Type*} {V : ι → T.Opens}

/-- If `f : T ⟶ S` is flat and surjective, `U ⊆ S` is an affine open and finitely many
affine opens `V i` of `T` cover `f⁻¹(U)`, then the ring map `Γ(S, U) → ∏ i, Γ(T, V i)`
induced by `f` is faithfully flat. -/
@[weil "lem_fka3_affine_cover_faithfully_flat"]
theorem faithfullyFlat_piRingHom_appLE [Flat f] [Surjective f] [Finite ι]
    (hU : IsAffineOpen U) (hV : ∀ i, IsAffineOpen (V i)) (hle : ∀ i, V i ≤ f ⁻¹ᵁ U)
    (hcov : f ⁻¹ᵁ U ≤ ⨆ i, V i) :
    (RingHom.pi fun i => (f.appLE U (V i) (hle i)).hom).FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · have hflat : ∀ i, (f.appLE U (V i) (hle i)).hom.Flat := fun i =>
      HasRingHomProperty.appLE @Flat f inferInstance ⟨U, hU⟩ ⟨V i, hV i⟩ (hle i)
    let _ : ∀ i, Algebra Γ(S, U) Γ(T, V i) := fun i => (f.appLE U (V i) (hle i)).hom.toAlgebra
    have _ : ∀ i, Module.Flat Γ(S, U) Γ(T, V i) := hflat
    have := Fintype.ofFinite ι
    exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := Γ(S, U))).symm
  · intro p
    let p' : Spec Γ(S, U) := p
    obtain ⟨t, ht⟩ := f.surjective (hU.fromSpec p')
    have htU : t ∈ f ⁻¹ᵁ U := by
      change f t ∈ U
      rw [ht]
      exact hU.range_fromSpec.le ⟨p', rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov htU)
    obtain ⟨q, hq⟩ : t ∈ Set.range (hV i).fromSpec := by rw [(hV i).range_fromSpec]; exact hi
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom _ i) q, ?_⟩
    have key := congrArg (fun g => g.base q) (hU.SpecMap_appLE_fromSpec f (hV i) (hle i))
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at key
    rw [hq, ht] at key
    exact hU.fromSpec.isOpenEmbedding.injective key

end AlgebraicGeometry

end
