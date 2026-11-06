module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.OverField
public import Mathlib.FieldTheory.IsSepClosed
public import Weil.Attr

/-!
# Étale schemes over a separably closed field

Let `Ω` be a separably closed field. A scheme `X` étale over `Spec Ω` is a disjoint union of
copies of `Spec Ω`, over `Spec Ω`; if the structure morphism is moreover quasi-compact, the
number of copies is finite, so `X ≅ ∐_{v=1}^r Spec Ω` over `Spec Ω` for some `r : ℕ`.

The proof starts from the classification of schemes étale over a field `k` as disjoint unions
of spectra of finite separable field extensions of `k` (Stacks, Tag 024X), and observes that a
separable algebraic extension of a separably closed field is trivial, so each factor
`Spec K_i → Spec Ω` is an isomorphism.

## Main results

* `AlgebraicGeometry.exists_iso_sigma_spec_of_etale_of_isSepClosed`: a scheme étale over the
  spectrum of a separably closed field `Ω` is, over `Spec Ω`, a coproduct of copies of `Spec Ω`.
* `AlgebraicGeometry.exists_iso_sigma_fin_spec_of_etale_of_isSepClosed`: if the structure
  morphism is also quasi-compact, it is a coproduct of finitely many copies, indexed by
  `Fin r`.

## Implementation notes

Freitag and Kiehl work with noetherian schemes throughout, which is where finiteness of the
number of copies comes from; here it is the hypothesis that the structure morphism is
quasi-compact (it holds, e.g., when the underlying space of `X` is noetherian). Without it the
statement with finitely many copies is false (an infinite disjoint union of copies of `Spec Ω`
is étale over `Spec Ω`), and the general statement is
`AlgebraicGeometry.exists_iso_sigma_spec_of_etale_of_isSepClosed`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FK88]
* [Stacks Project, Tag 024X](https://stacks.math.columbia.edu/tag/024X)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- For a separable extension `K` of a separably closed field `Ω`, the morphism
`Spec K ⟶ Spec Ω` is an isomorphism. -/
instance isIso_spec_map_algebraMap_of_isSepClosed (Ω K : Type u) [Field Ω] [IsSepClosed Ω]
    [Field K] [Algebra Ω K] [Algebra.IsSeparable Ω K] :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap Ω K))) := by
  have hbij : Function.Bijective (algebraMap Ω K) :=
    ⟨(algebraMap Ω K).injective, IsSepClosed.algebraMap_surjective Ω K⟩
  have : IsIso (CommRingCat.ofHom (algebraMap Ω K)) :=
    (RingEquiv.ofBijective (algebraMap Ω K) hbij).toCommRingCatIso.isIso_hom
  infer_instance

/-- Gluing step: a coproduct of spectra of separable extensions of a separably closed field `Ω`,
reindexed along `σ : J ≃ I`, is isomorphic over `Spec Ω` to the coproduct of copies of
`Spec Ω` indexed by `J`. -/
private theorem exists_iso_sigma_spec_of_iso_sigma_spec_separable (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (p : X ⟶ Spec (.of Ω)) {I : Type u} (K : I → Type u)
    [∀ i, Field (K i)] [∀ i, Algebra Ω (K i)] [∀ i, Algebra.IsSeparable Ω (K i)]
    (e : X ≅ ∐ fun i ↦ Spec (.of (K i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap Ω (K i)))) = p)
    {J : Type*} (σ : J ≃ I) [HasCoproduct fun _ : J ↦ Spec (.of Ω)] :
    ∃ E : (∐ fun _ : J ↦ Spec (.of Ω)) ≅ X, E.hom ≫ p = Sigma.desc fun _ ↦ 𝟙 _ := by
  let w : ∀ j, Spec (.of (K (σ j))) ≅ Spec (.of Ω) := fun j ↦
    asIso (Spec.map (CommRingCat.ofHom (algebraMap Ω (K (σ j)))))
  refine ⟨Sigma.whiskerEquiv σ w ≪≫ e.symm, ?_⟩
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  rw [← he]
  simp [w]

/-- A scheme étale over the spectrum of a separably closed field `Ω` is, over `Spec Ω`, a
coproduct of copies of `Spec Ω`. -/
theorem exists_iso_sigma_spec_of_etale_of_isSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of Ω)) [Etale p] :
    ∃ (I : Type u) (E : (∐ fun _ : I ↦ Spec (.of Ω)) ≅ X),
      E.hom ≫ p = Sigma.desc fun _ ↦ 𝟙 _ := by
  obtain ⟨I, K, hK, hA, -, hS, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable Ω p).mp inferInstance
  exact ⟨I, exists_iso_sigma_spec_of_iso_sigma_spec_separable Ω p K e he (Equiv.refl I)⟩

/-- **Étale schemes over a separably closed field split.** Let `Ω` be a separably closed field
and `p : X ⟶ Spec Ω` étale and quasi-compact. Then there are `r : ℕ` and an isomorphism of
`Spec Ω`-schemes `∐_{v : Fin r} Spec Ω ≅ X`. -/
@[weil "lem_fk108_etale_over_separably_closed_field_split"]
theorem exists_iso_sigma_fin_spec_of_etale_of_isSepClosed (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (p : X ⟶ Spec (.of Ω)) [Etale p] [QuasiCompact p] :
    ∃ (r : ℕ) (E : (∐ fun _ : Fin r ↦ Spec (.of Ω)) ≅ X),
      E.hom ≫ p = Sigma.desc fun _ ↦ 𝟙 _ := by
  obtain ⟨I, hI, K, hK, hA, -, hS, e, he⟩ :=
    (unramified_quasiCompact_iff_iso_finite_coproduct_spectra_finite_separable Ω p).mp
      ⟨(etale_iff_unramified_over_field Ω p).mp inferInstance, inferInstance⟩
  exact ⟨Nat.card I,
    exists_iso_sigma_spec_of_iso_sigma_spec_separable Ω p K e he (Finite.equivFin I).symm⟩

end AlgebraicGeometry

end
