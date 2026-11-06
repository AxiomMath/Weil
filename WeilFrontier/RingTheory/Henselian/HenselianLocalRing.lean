module

public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.TFAE
public import WeilFrontier.Defs.RingTheory.EssentialFiniteness
public import WeilFrontier.Defs.RingTheory.QuasiFinite.Basic
public import Weil.Attr

/-!
# Henselian local rings via quasi-finite local homomorphisms

A local ring `(R, 𝔪)` is henselian (Mathlib's `HenselianLocalRing`: simple roots of monic
polynomials modulo `𝔪` lift to roots) if and only if every finitely generated local
homomorphism `R → B` to a local ring `B` (a localization at a prime of a finitely generated
`R`-algebra) which is quasi-finite (the closed fibre `B ⧸ 𝔪 B` is finite over `R ⧸ 𝔪`) is
finite. This is Freitag–Kiehl's definition of a henselian local ring, a form of Zariski's main
theorem.

## Main results

* `HenselianLocalRing.finite_of_isFinitelyGeneratedLocal_of_isQuasiFiniteLocalHom`: over a
  henselian local ring, a finitely generated, quasi-finite local homomorphism is finite.
* `henselianLocalRing_of_forall_finite_of_isQuasiFiniteLocalHom`: conversely, a local ring over
  which every such homomorphism is finite is henselian.
* `henselianLocalRing_iff_forall_finite_of_isQuasiFiniteLocalHom`: the equivalence of the two
  descriptions.

## Implementation notes

The definition of a henselian local ring is Mathlib's `HenselianLocalRing`; the description by
quasi-finite local homomorphisms is the theorem
`henselianLocalRing_iff_forall_finite_of_isQuasiFiniteLocalHom`. Freitag–Kiehl assume `R`
noetherian; the equivalence holds for every local ring.

The forward direction is item (3) of Stacks 04GH: the closed fibre condition makes the
finitely generated algebra quasi-finite at the prime in question (by Zariski's main theorem),
so its localization is finite. For the converse we verify item (7) of Stacks 04GG: if `S` is
étale over `R` and `q` is a prime of `S` over `𝔪` with trivial residue field extension, then
`S_q` is finitely generated, local and quasi-finite over `R` (its closed fibre is the residue
field, as `R → S_q` is unramified), hence finite; being flat it is free, so `R → S_q` is
injective, and by Nakayama it is surjective. The inverse of `R ≅ S_q` composed with
`S → S_q` is the required retraction. The universe of the algebras `B` in the equivalence is
that of `R`, as in Stacks 04GG; the forward direction holds in any universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Tag 04GH](https://stacks.math.columbia.edu/tag/04GH)
-/

public section

universe u v

open IsLocalRing

/-- Over a henselian local ring `R`, a finitely generated local homomorphism `R → B` to a local
ring which is quasi-finite (its closed fibre `B ⧸ 𝔪 B` is finite over `R ⧸ 𝔪`) is finite. -/
theorem HenselianLocalRing.finite_of_isFinitelyGeneratedLocal_of_isQuasiFiniteLocalHom
    {R : Type u} {B : Type v} [CommRing R] [HenselianLocalRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] (hfg : Algebra.IsFinitelyGeneratedLocal R B)
    [Algebra.IsQuasiFiniteLocalHom R B] : Module.Finite R B := by
  obtain ⟨C, _, _, _, q, _, ⟨e⟩⟩ :=
    Algebra.essFiniteType_iff_exists_algEquiv_localization_atPrime.mp hfg.essFiniteType
  have hloc : IsLocalHom (algebraMap R B) := hfg.isLocalHom
  have hloc' : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
    refine ⟨fun r hr ↦ hloc.map_nonunit r ?_⟩
    simpa using hr.map e
  have hq : q.LiesOver (maximalIdeal R) := by
    constructor
    have h1 := ((local_hom_TFAE (algebraMap R (Localization.AtPrime q))).out 1 5).mp hloc'
    have h2 : (maximalIdeal (Localization.AtPrime q)).comap
        (algebraMap C (Localization.AtPrime q)) = q :=
      Localization.AtPrime.under_maximalIdeal (I := q)
    rw [IsScalarTower.algebraMap_eq R C (Localization.AtPrime q), ← Ideal.comap_comap, h2] at h1
    exact h1.symm
  have hw : Algebra.WeaklyQuasiFiniteAt R q := by
    rw [Algebra.weaklyQuasiFiniteAt_iff, ← Ideal.over_def q (maximalIdeal R)]
    have e' : (Localization.AtPrime q ⧸
        (maximalIdeal R).map (algebraMap R (Localization.AtPrime q))) ≃ₐ[R]
        (B ⧸ (maximalIdeal R).map (algebraMap R B)) :=
      Ideal.quotientEquivAlg _ _ e (by
        rw [Ideal.map_map]; congr 1; ext r; simp)
    exact (Algebra.QuasiFinite.iff_of_algEquiv e').mpr inferInstance
  have hqf : Algebra.QuasiFiniteAt R q := Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt q
  have hfin : Module.Finite R (Localization.AtPrime q) :=
    ((HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt R).2.2.1 C
      inferInstance q hqf (Localization.AtPrime q)).2
  exact Module.Finite.equiv e.toLinearEquiv

/-- A local ring `R` over which every finitely generated, quasi-finite local homomorphism
`R → B` to a local ring `B` is finite is henselian. -/
theorem henselianLocalRing_of_forall_finite_of_isQuasiFiniteLocalHom (R : Type u) [CommRing R]
    [IsLocalRing R]
    (H : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B],
      Algebra.IsFinitelyGeneratedLocal R B → Algebra.IsQuasiFiniteLocalHom R B →
        Module.Finite R B) :
    HenselianLocalRing R := by
  refine ((HenselianLocalRing.TFAE_factorization_etale_quasiFinite R).out 7 1).mp ?_
  intro S _ _ _ q _ _ hbij
  let T := Localization.AtPrime q
  have hloc : IsLocalHom (algebraMap R T) := by
    refine ((local_hom_TFAE (algebraMap R T)).out 5 1).mp ?_
    rw [IsScalarTower.algebraMap_eq R S T, ← Ideal.comap_comap]
    have : (maximalIdeal T).comap (algebraMap S T) = q :=
      Localization.AtPrime.under_maximalIdeal (I := q)
    rw [this]
    exact (Ideal.over_def q (maximalIdeal R)).symm
  have hmax : (maximalIdeal R).map (algebraMap R T) = maximalIdeal T :=
    Algebra.FormallyUnramified.map_maximalIdeal
  -- Every element of `T` is congruent to an element of `R` modulo `𝔪 T`.
  have hres : ∀ s : T, ∃ r : R, s - algebraMap R T r ∈ (maximalIdeal R).map (algebraMap R T) := by
    intro s
    obtain ⟨x, hx⟩ := hbij.2 (residue T s)
    obtain ⟨z, rfl⟩ :=
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R)).2 x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨r, ?_⟩
    rw [hmax, ← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hx]
    exact AlgHom.commutes _ r
  have hqf : Algebra.IsQuasiFiniteLocalHom R T := by
    have : Module.Finite R (T ⧸ (maximalIdeal R).map (algebraMap R T)) := by
      refine ⟨⟨{1}, eq_top_iff.mpr fun x _ ↦ ?_⟩⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨r, hr⟩ := hres s
      rw [Finset.coe_singleton, Submodule.mem_span_singleton]
      refine ⟨r, ?_⟩
      have h1 : r • (1 : T ⧸ (maximalIdeal R).map (algebraMap R T)) =
          Ideal.Quotient.mk _ (algebraMap R T r) := by
        rw [Ideal.Quotient.mk_algebraMap]; exact (Algebra.algebraMap_eq_smul_one r).symm
      rw [h1, Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
      exact hr
    exact Algebra.IsQuasiFiniteLocalHom.of_finite_restrictScalars
  have hfin : Module.Finite R T := H T ⟨hloc, inferInstance⟩ hqf
  have : Module.Free R T := Module.free_of_flat_of_isLocalRing
  have hinj : Function.Injective (algebraMap R T) := FaithfulSMul.algebraMap_injective R T
  have hsurj : Function.Surjective (algebraMap R T) := by
    have htop : (⊤ : Submodule R T) ≤ Submodule.span R {1} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
        (Module.Finite.fg_top) (maximalIdeal_le_jacobson ⊥) fun s _ ↦ ?_
      obtain ⟨r, hr⟩ := hres s
      refine Submodule.mem_sup.mpr ⟨algebraMap R T r, ?_, s - algebraMap R T r, ?_, by ring⟩
      · exact Submodule.mem_span_singleton.mpr ⟨r, (Algebra.algebraMap_eq_smul_one r).symm⟩
      · rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        exact hr
    intro s
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (htop Submodule.mem_top : s ∈ _)
    exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, hr]⟩
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId R T) ⟨hinj, hsurj⟩).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R S T)⟩

/-- **Henselian local rings, after Freitag–Kiehl.** A local ring `R` is henselian if and only if
every finitely generated local homomorphism `R → B` to a local ring `B` (a localization at a
prime of a finitely generated `R`-algebra) which is quasi-finite (the closed fibre `B ⧸ 𝔪 B` is
finite over `R ⧸ 𝔪`) is finite. -/
@[weil "def_fk101_henselian_local_ring"]
theorem henselianLocalRing_iff_forall_finite_of_isQuasiFiniteLocalHom (R : Type u) [CommRing R]
    [IsLocalRing R] :
    HenselianLocalRing R ↔ ∀ (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B],
      Algebra.IsFinitelyGeneratedLocal R B → Algebra.IsQuasiFiniteLocalHom R B →
        Module.Finite R B :=
  ⟨fun _ _ _ _ _ hfg _ ↦
      HenselianLocalRing.finite_of_isFinitelyGeneratedLocal_of_isQuasiFiniteLocalHom hfg,
    henselianLocalRing_of_forall_finite_of_isQuasiFiniteLocalHom R⟩

end
