module

public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Weil.Attr

/-!
# Lifting a finite residue field extension to a finite free local algebra

Let `A` be a local ring with residue field `k` and let `L / k` be a finite field extension.
Then there is a local `A`-algebra `A₁` which is free of finite rank as an `A`-module, with
`A → A₁` a local homomorphism, whose residue field is `k`-isomorphic to `L`.

The finite free ring map `φ : A → A₁` with `κ(𝔪 A₁) ≅ L` is Stacks Tag 07NE
(`exists_isFiniteFree_residueField_equiv`). Locality of `A₁` follows: the prime `𝔪 A₁` lies
over the maximal ideal `𝔪` of `A` and `A₁` is integral over `A`, so `𝔪 A₁` is maximal; every
maximal ideal of `A₁` contracts to `𝔪`, hence contains `𝔪 A₁`, hence equals it.

## Main results

* `IsLocalRing.exists_finite_free_isLocalHom_residueField_algEquiv`: the lift `A → A₁`.

## Implementation notes

The source states the lemma for a noetherian local ring and a finite *purely inseparable*
extension `L / k`. Neither hypothesis is needed: the statement here holds for every local ring
and every finite extension, and contains the source's case.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7.
* [Stacks] The Stacks Project, Tag 07NE.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsLocalRing

/-- **Finite free local lift of a finite residue field extension.** For a local ring `A` with
residue field `k` and a finite field extension `L / k`, there is a local `A`-algebra `A₁`, free
of finite rank as an `A`-module, with `A → A₁` local and residue field `k`-isomorphic to `L`. -/
@[weil "lem_fk107_purely_inseparable_residue_lift"]
theorem exists_finite_free_isLocalHom_residueField_algEquiv (A : Type u) [CommRing A]
    [IsLocalRing A] (L : Type v) [Field L] [Algebra (ResidueField A) L]
    [Module.Finite (ResidueField A) L] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsLocalRing A₁) (_ : Algebra A A₁),
      Module.Free A A₁ ∧ Module.Finite A A₁ ∧ ∃ (_ : IsLocalHom (algebraMap A A₁)),
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A] L) := by
  set p := maximalIdeal A
  -- `κ(𝔪) ≃ k`
  let e : p.ResidueField ≃+* ResidueField A :=
    (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField p)).symm
  let : Algebra p.ResidueField L := ((algebraMap (ResidueField A) L).comp e.toRingHom).toAlgebra
  let : Algebra (ResidueField A) p.ResidueField := e.symm.toRingHom.toAlgebra
  have : IsScalarTower (ResidueField A) p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have : Module.Finite p.ResidueField L :=
    Module.Finite.of_restrictScalars_finite (ResidueField A) p.ResidueField L
  obtain ⟨S, _, φ, ⟨hfree, hfin⟩, hprime, hpq, Φ, hΦ⟩ :=
    exists_isFiniteFree_residueField_equiv A p L
  let : Algebra A S := φ.toAlgebra
  set q := Ideal.map φ p
  have : Algebra.IsIntegral A S := Algebra.IsIntegral.of_finite A S
  have hcomap : q.comap (algebraMap A S) = p := hpq.symm
  have hqmax : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q (by rw [hcomap]; infer_instance)
  have huniq : ∀ M : Ideal S, M.IsMaximal → M = q := by
    intro M hM
    have hc : M.comap (algebraMap A S) = p :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    have hle : q ≤ M := Ideal.map_le_iff_le_comap.mpr (by rw [← hc]; rfl)
    exact (hqmax.eq_of_le hM.ne_top hle).symm
  let : IsLocalRing S := IsLocalRing.of_unique_max_ideal ⟨q, hqmax, huniq⟩
  have hmax : maximalIdeal S = q := huniq _ (maximalIdeal.isMaximal S)
  have hloc : IsLocalHom (algebraMap A S) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : algebraMap A S a ∈ q := Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr hna)
    rw [← hmax] at this
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨S, inferInstance, inferInstance, inferInstance, hfree, hfin, hloc, ⟨?_⟩⟩
  let ψ : ResidueField S ≃+* L :=
    ((Ideal.quotEquivOfEq hmax).trans
      (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField q))).trans Φ
  refine AlgEquiv.ofRingEquiv (f := ψ) fun x => ?_
  obtain ⟨a, rfl⟩ := residue_surjective x
  have h1 := congrArg (fun f => f (algebraMap A p.ResidueField a)) hΦ
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h1
  rw [inducedResidueMap_algebraMap] at h1
  have h2 : algebraMap (ResidueField A) (ResidueField S) (residue A a) = residue S (φ a) :=
    ResidueField.map_residue _ a
  have h3 : ψ (residue S (φ a)) = Φ (algebraMap (S ⧸ q) q.ResidueField
      (Ideal.Quotient.mk q (φ a))) := rfl
  rw [h2, h3, h1, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  congr 1
  apply e.symm.injective
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  exact IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField a

end IsLocalRing
