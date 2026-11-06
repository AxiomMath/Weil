module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.AffineEtale
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleFiniteProduct
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtaleCoveringFk101
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# The product of an étale covering is faithfully flat

Let `A` be a commutative ring and `(gᵢ : B → Bᵢ)ᵢ` an étale covering in the étale category
`Et(A)`. Then the ring homomorphism `g = (gᵢ)ᵢ : B → ∏ᵢ Bᵢ` is faithfully flat: the finite
product is a finite direct sum of flat `B`-modules, hence flat, and every prime ideal of `B` is
the preimage of a prime of some `Bᵢ`, hence of the prime `Bᵢ`-component of `∏ᵢ Bᵢ`. Since the
product is again an object of `Et(A)`, `g` is a faithfully flat morphism of `Et(A)`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.piObjLift`: the morphism `B ⟶ ∏ᵢ Bᵢ` of `Et(A)` induced by a
  finite family `gᵢ : B ⟶ Bᵢ`.

## Main results

- `Module.Flat.pi_of_finite`: a finite product of flat modules is flat.
- `RingHom.faithfullyFlat_pi`: for a finite family of flat ring homomorphisms `fᵢ : R → Sᵢ`
  whose maps of spectra are jointly surjective, `R → ∏ᵢ Sᵢ` is faithfully flat.
- `AlgebraicGeometry.EtaleCategory.IsCovering.faithfullyFlat_pi`: for an étale covering
  `(gᵢ)ᵢ`, the ring homomorphism `B → ∏ᵢ Bᵢ` is faithfully flat.
- `AlgebraicGeometry.EtaleCategory.IsCovering.faithfullyFlat_piObjLift`: the morphism
  `piObjLift g` of `Et(A)` is faithfully flat.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory Opposite

/-- A finite product of flat modules is flat. -/
theorem Module.Flat.pi_of_finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  classical
  have := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := M)).symm

/-- Let `fᵢ : R → Sᵢ` be a finite family of flat ring homomorphisms such that every prime of
`R` is the preimage of a prime of some `Sᵢ`. Then `R → ∏ᵢ Sᵢ` is faithfully flat. -/
theorem RingHom.faithfullyFlat_pi {R : Type*} [CommRing R] {ι : Type*} [_root_.Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R →+* S i) (hf : ∀ i, (f i).Flat)
    (hsurj : ∀ p : PrimeSpectrum R, ∃ (i : ι) (q : PrimeSpectrum (S i)),
      PrimeSpectrum.comap (f i) q = p) :
    (RingHom.pi f).FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨?_, fun p ↦ ?_⟩
  · let : ∀ i, Algebra R (S i) := fun i ↦ (f i).toAlgebra
    have : ∀ i, Module.Flat R (S i) := hf
    have h : algebraMap R (∀ i, S i) = RingHom.pi f := rfl
    rw [← h, RingHom.flat_algebraMap_iff]
    exact Module.Flat.pi_of_finite S
  · obtain ⟨i, q, rfl⟩ := hsurj p
    exact ⟨PrimeSpectrum.comap (Pi.evalRingHom S i) q, by
      rw [← PrimeSpectrum.comap_comp_apply]; rfl⟩

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{max u w}} {B : EtaleCategory A} {ι : Type w} {C : ι → EtaleCategory A}
  (g : ∀ i, B ⟶ C i)

/-- For an étale covering `(gᵢ : B ⟶ Cᵢ)ᵢ` of `Et(A)`, the ring homomorphism
`(gᵢ)ᵢ : B → ∏ᵢ Cᵢ` is faithfully flat. -/
@[weil "lem_fk101_etale_covering_product_faithfully_flat"]
theorem IsCovering.faithfullyFlat_pi (hg : IsCovering g) :
    (RingHom.pi fun i ↦ (ringHom (g i)).hom).FaithfullyFlat :=
  haveI := hg.finite
  RingHom.faithfullyFlat_pi _
    (fun i ↦ (RingHom.Etale.iff_flat_and_formallyUnramified.1 (etale_hom (g i))).1)
    hg.exists_comap_eq

/-- The morphism `B ⟶ ∏ᵢ Cᵢ` of `Et(A)` induced by a finite family `gᵢ : B ⟶ Cᵢ`, into the
product `piObj`. (`AlgebraicGeometry.EtaleCategory.piLift` is the analogous map into
`finiteProductObj`, for index types in `Type`.) -/
def piObjLift [Finite ι] : B ⟶ piObj (fun i ↦ toAlgebra (C i)) :=
  (ofAlgebraToAlgebraIso B).inv ≫ homOfAlgebra (ObjectProperty.homMk
    (X := toAlgebra B) (Y := piAlgebra fun i ↦ toAlgebra (C i))
    (ConcreteCategory.ofHom (C := CommAlgCat A)
      (AlgHom.pi fun i ↦ algHomOfHom
        ((ofAlgebraToAlgebraIso B).hom ≫ g i ≫ (ofAlgebraToAlgebraIso (C i)).inv))))

lemma ringHom_piObjLift [Finite ι] :
    (ringHom (piObjLift g)).hom = RingHom.pi fun i ↦ (ringHom (g i)).hom := by
  ext x
  rfl

/-- For an étale covering `(gᵢ : B ⟶ Cᵢ)ᵢ` of `Et(A)`, the induced morphism `B ⟶ ∏ᵢ Cᵢ` of
`Et(A)` is faithfully flat. -/
@[weil "lem_fk101_etale_covering_product_faithfully_flat"]
theorem IsCovering.faithfullyFlat_piObjLift [Finite ι] (hg : IsCovering g) :
    (ringHom (piObjLift g)).hom.FaithfullyFlat := by
  rw [ringHom_piObjLift]
  exact hg.faithfullyFlat_pi g

end EtaleCategory

end AlgebraicGeometry
