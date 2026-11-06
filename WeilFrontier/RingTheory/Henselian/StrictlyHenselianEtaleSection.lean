module

public import Weil.Attr
public import WeilFrontier.RingTheory.Henselian.QuasiFinite

/-!
# Faithfully flat étale algebras over a strictly henselian local ring have a section

Let `A` be a strictly henselian local ring and `B` a faithfully flat étale `A`-algebra. Then the
structure map `A → B` has a retraction: there is an `A`-algebra homomorphism `B → A`.

Indeed, faithful flatness gives a prime `𝔭` of `B` lying over the maximal ideal of `A`. The
composite `A → B → B_𝔭` is a local homomorphism which is flat, formally unramified and
essentially of finite type, hence bijective since `A` is henselian with separably closed residue
field (`Algebra.bijective_algebraMap_of_flat_of_formallyUnramified`). Composing `B → B_𝔭` with
the inverse of this isomorphism gives the section.

## Main results

* `Algebra.Etale.exists_algHom_of_faithfullyFlat`: a faithfully flat étale algebra over a
  strictly henselian local ring admits an `A`-algebra homomorphism to `A`.
* `RingHom.Etale.exists_comp_eq_id_of_faithfullyFlat`: the same for a ring homomorphism
  `φ : A →+* B`, in the form `ψ.comp φ = RingHom.id A`.

## Implementation notes

The source assumes `A` noetherian; the argument does not need it, and the results are stated
without it. Étale is `Algebra.Etale` (formally étale and of finite presentation), which for
noetherian rings is the source's notion (finitely generated, flat, unramified at every prime).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK], I.1
-/

@[expose] public section

open IsLocalRing

namespace Algebra.Etale

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `A` be a strictly henselian local ring and `B` a faithfully flat étale `A`-algebra.
Then there is an `A`-algebra homomorphism `B → A`, i.e. a retraction of `A → B`. -/
@[weil "lem_fk101_strictly_henselian_etale_section"]
theorem exists_algHom_of_faithfullyFlat [StrictlyHenselianLocalRing A]
    [Module.FaithfullyFlat A B] [Algebra.Etale A B] : Nonempty (B →ₐ[A] A) := by
  obtain ⟨P, hP, hPm⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := B) (maximalIdeal A)
  let Bp := Localization.AtPrime P
  have hlocal : IsLocalHom (algebraMap A Bp) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ P.under A := by
      rw [← Ideal.over_def P (maximalIdeal A)]
      exact hna
    have hmem : algebraMap B Bp (algebraMap A B a) ∈ maximalIdeal Bp :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Bp P _).2 hm
    rw [← IsScalarTower.algebraMap_apply] at hmem
    exact hmem ha
  have : Module.Flat A Bp := Module.Flat.trans A B Bp
  have : Algebra.FormallyUnramified B Bp :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  have : Algebra.FormallyUnramified A Bp := Algebra.FormallyUnramified.comp A B Bp
  have : Algebra.EssFiniteType B Bp := Algebra.EssFiniteType.of_isLocalization Bp P.primeCompl
  have : Algebra.EssFiniteType A Bp := Algebra.EssFiniteType.comp A B Bp
  have hbij := Algebra.bijective_algebraMap_of_flat_of_formallyUnramified A Bp
  let e : A ≃ₐ[A] Bp := AlgEquiv.ofBijective (Algebra.ofId A Bp) hbij
  exact ⟨e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B Bp)⟩

end Algebra.Etale

namespace RingHom.Etale

/-- Let `A` be a strictly henselian local ring and `φ : A →+* B` a faithfully flat étale ring
homomorphism. Then there is a ring homomorphism `ψ : B →+* A` with `ψ ∘ φ = id`. -/
theorem exists_comp_eq_id_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B]
    [StrictlyHenselianLocalRing A] {φ : A →+* B} (hff : φ.FaithfullyFlat) (he : φ.Etale) :
    ∃ ψ : B →+* A, ψ.comp φ = RingHom.id A := by
  let _ : Algebra A B := φ.toAlgebra
  have : Module.FaithfullyFlat A B := hff
  have : Algebra.Etale A B := he
  obtain ⟨ψ⟩ := Algebra.Etale.exists_algHom_of_faithfullyFlat (A := A) (B := B)
  exact ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩

end RingHom.Etale

end
