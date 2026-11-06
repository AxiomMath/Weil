module

public import Weil.Attr
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Fields large enough for a finite ring homomorphism

Let `A → B` be a ring homomorphism and `k` a field which is an `A`-algebra. The field `k` is
*large enough for* `A → B` if for every maximal ideal `𝔫` of `B` and every maximal ideal `𝔐` of
`k ⊗[A] B ⧸ 𝔫`, the canonical map `k → (k ⊗[A] B ⧸ 𝔫) ⧸ 𝔐` is bijective, i.e. every residue field
of the fibre of `Spec B → Spec A` over `Spec k`, at a closed point of `Spec B`, is `k` itself.

## Main definitions

* `IsLargeEnoughFor A B k`: the field `k` is large enough for `A → B`.

## Main results

* `IsLargeEnoughFor.iff_residueField`: when `A` is local, `k` is a `κ(A)`-algebra compatibly with
  its `A`-algebra structure and `A → B` is finite, the condition may be read with the tensor
  product `k ⊗[κ(A)] B ⧸ 𝔫` over the residue field, as in [FK, I.3].
* `IsLargeEnoughFor.of_isAlgClosed`: an algebraically closed field is large enough for every
  finite `A → B`.

## Implementation notes

[FK] states the definition for a noetherian local ring `A`, a finite `A → B`, a separably closed
field `k` and a local homomorphism `φ : A → k`, and forms the tensor product over the residue
field `κ(A)`, through which `φ` factors. The definition here uses the tensor product over `A`,
which needs none of these hypotheses; `IsLargeEnoughFor.iff_residueField` shows that under
[FK]'s hypotheses the two conditions agree (every maximal ideal of `B` lies over `𝔪(A)`, so
`B ⧸ 𝔫` is a `κ(A)`-algebra and `k ⊗[A] B ⧸ 𝔫 = k ⊗[κ(A)] B ⧸ 𝔫`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
-/

@[expose] public section

open TensorProduct

universe u v w

variable (A : Type u) (B : Type v) (k : Type w) [CommRing A] [CommRing B] [Algebra A B]
  [Field k] [Algebra A k]

/-- The field `k` (an `A`-algebra) is *large enough for* `A → B` if for every maximal ideal `𝔫`
of `B` and every maximal ideal `𝔐` of `k ⊗[A] B ⧸ 𝔫`, the canonical map
`k → (k ⊗[A] B ⧸ 𝔫) ⧸ 𝔐` is bijective. -/
@[weil "def_fk103_large_enough_separably_closed_field"]
def IsLargeEnoughFor : Prop :=
  ∀ (𝔫 : Ideal B) [𝔫.IsMaximal] (𝔐 : Ideal (k ⊗[A] (B ⧸ 𝔫))) [𝔐.IsMaximal],
    Function.Bijective (algebraMap k _ : k →+* (k ⊗[A] (B ⧸ 𝔫)) ⧸ 𝔐)

variable {A B k}

namespace IsLargeEnoughFor

theorem bijective (h : IsLargeEnoughFor A B k) (𝔫 : Ideal B) [𝔫.IsMaximal]
    (𝔐 : Ideal (k ⊗[A] (B ⧸ 𝔫))) [𝔐.IsMaximal] :
    Function.Bijective (algebraMap k _ : k →+* (k ⊗[A] (B ⧸ 𝔫)) ⧸ 𝔐) :=
  h 𝔫 𝔐

theorem surjective (h : IsLargeEnoughFor A B k) (𝔫 : Ideal B) [𝔫.IsMaximal]
    (𝔐 : Ideal (k ⊗[A] (B ⧸ 𝔫))) [𝔐.IsMaximal] :
    Function.Surjective (algebraMap k _ : k →+* (k ⊗[A] (B ⧸ 𝔫)) ⧸ 𝔐) :=
  (h 𝔫 𝔐).2

/-- `k` is large enough for `A → B` as soon as the canonical maps to the residue fields are
surjective (injectivity is automatic, `k` being a field). -/
theorem of_surjective
    (h : ∀ (𝔫 : Ideal B) [𝔫.IsMaximal] (𝔐 : Ideal (k ⊗[A] (B ⧸ 𝔫))) [𝔐.IsMaximal],
      Function.Surjective (algebraMap k _ : k →+* (k ⊗[A] (B ⧸ 𝔫)) ⧸ 𝔐)) :
    IsLargeEnoughFor A B k := fun 𝔫 _ 𝔐 _ =>
  ⟨(algebraMap k _).injective, h 𝔫 𝔐⟩


/-- An algebraically closed field is large enough for every finite `A → B`. -/
theorem of_isAlgClosed [IsAlgClosed k] [Module.Finite A B] : IsLargeEnoughFor A B k :=
  fun 𝔫 _ 𝔐 _ => by
    have : Module.Finite k ((k ⊗[A] (B ⧸ 𝔫)) ⧸ 𝔐) := inferInstance
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end IsLargeEnoughFor

/-- The condition "every residue field at a maximal ideal is `k`" is invariant under
`k`-algebra isomorphisms. -/
theorem bijective_algebraMap_quotient_of_algEquiv {K C D : Type*} [Field K] [CommRing C]
    [CommRing D] [Algebra K C] [Algebra K D] (e : C ≃ₐ[K] D)
    (h : ∀ (𝔐 : Ideal D) [𝔐.IsMaximal], Function.Bijective (algebraMap K _ : K →+* D ⧸ 𝔐))
    (𝔐 : Ideal C) [𝔐.IsMaximal] : Function.Bijective (algebraMap K _ : K →+* C ⧸ 𝔐) := by
  have : (𝔐.map (e : C →+* D)).IsMaximal := Ideal.map_isMaximal_of_equiv (e : C ≃+* D)
  let f := Ideal.quotientEquivAlg 𝔐 (𝔐.map (e : C →+* D)) e rfl
  have hf : ⇑(algebraMap K _ : K →+* C ⧸ 𝔐) = f.symm ∘ algebraMap K _ :=
    funext fun x => (f.symm.commutes x).symm
  rw [hf]
  exact f.symm.bijective.comp (h _)

theorem forall_bijective_algebraMap_quotient_congr {K C D : Type*} [Field K] [CommRing C]
    [CommRing D] [Algebra K C] [Algebra K D] (e : C ≃ₐ[K] D) :
    (∀ (𝔐 : Ideal C) [𝔐.IsMaximal], Function.Bijective (algebraMap K _ : K →+* C ⧸ 𝔐)) ↔
      ∀ (𝔐 : Ideal D) [𝔐.IsMaximal], Function.Bijective (algebraMap K _ : K →+* D ⧸ 𝔐) :=
  ⟨bijective_algebraMap_quotient_of_algEquiv e.symm,
    bijective_algebraMap_quotient_of_algEquiv e⟩

namespace IsLocalRing

open IsLocalRing

/-- For `k` and `C` algebras over the residue field `κ(A)` of a local ring `A`, the tensor
product over `A` agrees with the tensor product over `κ(A)`. -/
noncomputable def tensorEquivTensorResidueField (k C : Type*) [CommRing k] [CommRing C]
    [IsLocalRing A] [Algebra A k] [Algebra A C]
    [Algebra (ResidueField A) k] [IsScalarTower A (ResidueField A) k]
    [Algebra (ResidueField A) C] [IsScalarTower A (ResidueField A) C] :
    k ⊗[A] C ≃ₐ[k] k ⊗[ResidueField A] C :=
  haveI : CompatibleSMul A (ResidueField A) k C := ⟨fun r m n => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul,
      TensorProduct.smul_tmul]⟩
  (Algebra.TensorProduct.equivOfCompatibleSMul A (ResidueField A) k k C).symm

@[simp]
theorem tensorEquivTensorResidueField_tmul (k C : Type*) [CommRing k] [CommRing C]
    [IsLocalRing A] [Algebra A k] [Algebra A C]
    [Algebra (ResidueField A) k] [IsScalarTower A (ResidueField A) k]
    [Algebra (ResidueField A) C] [IsScalarTower A (ResidueField A) C] (x : k) (y : C) :
    tensorEquivTensorResidueField (A := A) k C (x ⊗ₜ y) = x ⊗ₜ y :=
  rfl

/-- Over a local ring `A`, every maximal ideal of a finite `A`-algebra `B` lies over the maximal
ideal of `A`. -/
theorem maximalIdeal_le_comap_of_isMaximal [IsLocalRing A] [Module.Finite A B] (𝔫 : Ideal B)
    [𝔫.IsMaximal] : maximalIdeal A ≤ 𝔫.comap (algebraMap A B) :=
  (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A 𝔫)).ge

/-- The `κ(A)`-algebra structure on `B ⧸ 𝔫`, for `𝔫` a maximal ideal of a finite algebra `B`
over a local ring `A`. -/
noncomputable abbrev algebraResidueFieldQuotient [IsLocalRing A] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] : Algebra (ResidueField A) (B ⧸ 𝔫) :=
  Ideal.Quotient.algebraQuotientOfLEComap (maximalIdeal_le_comap_of_isMaximal 𝔫)

theorem isScalarTower_residueField_quotient [IsLocalRing A] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] :
    letI := algebraResidueFieldQuotient (A := A) 𝔫
    IsScalarTower A (ResidueField A) (B ⧸ 𝔫) :=
  let := algebraResidueFieldQuotient (A := A) 𝔫
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end IsLocalRing

open IsLocalRing in
/-- [FK]'s form of `IsLargeEnoughFor`: for `A` local, `A → B` finite and `k` a `κ(A)`-algebra
compatibly with its `A`-algebra structure, `k` is large enough for `A → B` iff for every maximal
ideal `𝔫` of `B` and every maximal ideal `𝔐` of the finite `k`-algebra `k ⊗[κ(A)] B ⧸ 𝔫`, the
canonical map `k → (k ⊗[κ(A)] B ⧸ 𝔫) ⧸ 𝔐` is bijective. -/
@[weil "def_fk103_large_enough_separably_closed_field"]
theorem IsLargeEnoughFor.iff_residueField [IsLocalRing A] [Module.Finite A B]
    [Algebra (ResidueField A) k] [IsScalarTower A (ResidueField A) k] :
    IsLargeEnoughFor A B k ↔
      ∀ (𝔫 : Ideal B) [𝔫.IsMaximal],
        letI := algebraResidueFieldQuotient (A := A) 𝔫
        ∀ (𝔐 : Ideal (k ⊗[ResidueField A] (B ⧸ 𝔫))) [𝔐.IsMaximal],
          Function.Bijective
            (algebraMap k _ : k →+* (k ⊗[ResidueField A] (B ⧸ 𝔫)) ⧸ 𝔐) := by
  refine forall_congr' fun 𝔫 => forall_congr' fun _ => ?_
  let := algebraResidueFieldQuotient (A := A) 𝔫
  have := isScalarTower_residueField_quotient (A := A) 𝔫
  exact forall_bijective_algebraMap_quotient_congr (tensorEquivTensorResidueField k (B ⧸ 𝔫))

end
