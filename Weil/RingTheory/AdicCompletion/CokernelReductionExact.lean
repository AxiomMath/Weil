module

public import Weil.CategoryTheory.Abelian.Subcategory
public import Weil.Defs.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Weil.Attr

/-!
# The projective system of a module is right exact

Let `Λ` be a commutative ring, `l ∈ Λ`, and let `S : ModuleCat Λ ⥤ ProjectiveSystem Λ l` be the
functor `M ↦ (M / l^{n+1} M)_n`. If `M → N → K → 0` is an exact sequence of `Λ`-modules, then
`S(M) → S(N) → S(K) → 0` is exact in the abelian category of projective systems. Exactness is
checked degreewise: in degree `n` the sequence is
`M / l^{n+1} M → N / l^{n+1} N → K / l^{n+1} K → 0`, which is exact because reduction modulo an
ideal is right exact (for `n < 0` all terms are `0`).
In particular, for a linear map `φ : M → N` with cokernel `K̄`, the sequence
`S(M) → S(N) → S(K̄) → 0` is exact.

## Main results

* `CategoryTheory.ProjectiveSystem.ofModule_map_exact_of_exact`: `S` sends a right exact sequence
  to a right exact sequence.
* `CategoryTheory.ProjectiveSystem.ofModule_cokernel_exact`: `S(M) → S(N) → S(coker φ) → 0` is
  exact.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- Reduction modulo an ideal is right exact: if `f, g` is exact with `g` surjective, then so is
the pair of induced maps on the quotients by `I • ⊤`. -/
private lemma exact_mapQ_smul_top {M N K : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup N]
    [Module Λ N] [AddCommGroup K] [Module Λ K] (I : Ideal Λ) {f : M →ₗ[Λ] N} {g : N →ₗ[Λ] K}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f))
      (Submodule.mapQ _ _ g (Submodule.smul_top_le_comap_smul_top I g)) := by
  rw [hfg.exact_mapQ_iff, Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
  exact inf_le_right

/-- `S` sends the zero map to the zero map. -/
private lemma ofModule_map_zero {M N : ModuleCat.{v} Λ} :
    (ofModule l).map (0 : M ⟶ N) = 0 :=
  hom_ext fun n => by
    ext x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [ofModule_map_app_mk]
    rfl

/-- The functor `S : M ↦ (M / l^{n+1} M)_n` sends an exact sequence `M → N → K → 0` of
`Λ`-modules to an exact sequence `S(M) → S(N) → S(K) → 0` of projective systems. -/
theorem ofModule_map_exact_of_exact (T : ShortComplex (ModuleCat.{v} Λ)) (hT : T.Exact)
    [Epi T.g] :
    (ShortComplex.mk ((ofModule l).map T.f) ((ofModule l).map T.g)
        (by rw [← Functor.map_comp, T.zero]; exact ofModule_map_zero)).Exact ∧
      Epi ((ofModule l).map T.g) := by
  have hg : Function.Surjective T.g := (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hfg : Function.Exact T.f T.g := by
    rw [LinearMap.exact_iff]
    exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hT).symm
  refine ⟨(shortComplex_exact_iff _).2 fun n => ?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (exact_mapQ_smul_top (Ideal.span {l} ^ (n + 1).toNat) hfg hg).linearMap_ker_eq.symm
  · have : Epi ((isTorsionBounded.{v} Λ l).ι.map ((ofModule l).map T.g)) := by
      rw [NatTrans.epi_iff_epi_app']
      intro n
      rw [ModuleCat.epi_iff_surjective]
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨x, rfl⟩ := hg y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    exact (isTorsionBounded.{v} Λ l).ι.epi_of_epi_map this

/-- **`S` is right exact on cokernels.** For a homomorphism `φ : M → N` of `Λ`-modules with
cokernel `K̄`, the sequence `S(M) → S(N) → S(K̄) → 0` is exact in the category of projective
systems: `S(M) → S(N) → S(K̄)` is exact and `S(N) → S(K̄)` is an epimorphism. -/
@[weil "lem_fk112_cokernel_reduction_exact"]
theorem ofModule_cokernel_exact {M N : ModuleCat.{v} Λ} (φ : M ⟶ N) :
    (ShortComplex.mk ((ofModule l).map φ) ((ofModule l).map (cokernel.π φ))
        (by rw [← Functor.map_comp, cokernel.condition]; exact ofModule_map_zero)).Exact ∧
      Epi ((ofModule l).map (cokernel.π φ)) :=
  ofModule_map_exact_of_exact (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ))
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ))

end ProjectiveSystem

end CategoryTheory
