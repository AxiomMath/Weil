/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import WeilFrontier.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Etale.Height
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# The Henselian line is a directed colimit of smooth curves

Let `A` be a local ring and let `A{t}` be the Henselization of the polynomial ring `A[t]` at the
origin `(𝔪(A), t)`. Then `A{t}` is, as an `A[t]`-algebra, the colimit of a directed system
`(B_i)_{i ∈ I}`, indexed by a directed preorder, of étale `A[t]`-algebras. Each `B_i` is a smooth
`A`-algebra of relative dimension one: for every field `K` and every ring map `A → K`, every
irreducible component of `Spec (K ⊗_A B_i)` has dimension one, that is, the quotient of
`K ⊗_A B_i` by each of its minimal primes has Krull dimension one.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.exists_directed_etale_smooth_curves_isColimit`: the
  presentation of `A{t}` as a directed colimit of étale `A[t]`-algebras which are smooth curves
  over `A`.

## Implementation notes

The étale `A[t]`-algebras are those of an ind-étale presentation of `A{t}` over `A[t]`, which is
the composite of the localization `A[t] → A[t]_{(𝔪, t)}` and the ind-étale map
`A[t]_{(𝔪, t)} → A{t}`; the filtered indexing category is replaced by a cofinal directed poset.
The dimension of the fibres is computed with the invariance of heights of primes under étale
maps: over `K[t]`, whose maximal ideals have height one, every prime of an étale algebra `C` has
height at most one, and no minimal prime of `C` is maximal, because its contraction to `K[t]`
would be a maximal ideal of height zero.

The source assumes `A` strictly henselian; the argument uses no hypothesis on `A` beyond being
local, so none is made. Directed systems are functors from a directed preorder to the category of
commutative `A[t]`-algebras, and `A{t} ≅ colim B_i` is a colimit cocone with vertex `A{t}`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.7
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Stacks Project, Tag 07QP](https://stacks.math.columbia.edu/tag/07QP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u v

namespace MvPolynomial

/-- For an étale ring map `K[t] → C`, the quotient of `C` by a minimal prime has dimension one. -/
private theorem ringKrullDim_quotient_eq_one_of_etale {K C : Type*} [Field K] [CommRing C]
    (f : MvPolynomial (Fin 1) K →+* C) (hf : f.Etale) {q : Ideal C} (hq : q ∈ minimalPrimes C) :
    ringKrullDim (C ⧸ q) = 1 := by
  have hdimP : ringKrullDim (MvPolynomial (Fin 1) K) = 1 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Field.toIsField K)]
    simp
  have hqp : q.IsPrime := hq.1.1
  have hle : ringKrullDim (C ⧸ q) ≤ 1 := by
    refine (ringKrullDim_quotient_le q).trans ?_
    rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro m hm
    rw [← hf.height_eq_height (m.comap f) m rfl, ← hdimP]
    exact Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)
  have hnmax : ¬ q.IsMaximal := by
    intro hmax
    have h0 : (q.comap f).height = 0 := by
      rw [hf.height_eq_height (q.comap f) q rfl]
      exact Ideal.height_eq_zero_iff.mpr hq
    have hbot : q.comap f = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h0
    have hmax' : (q.comap f).IsMaximal := by
      algebraize [f]
      let := Ideal.Quotient.field q
      have : Algebra.FiniteType (MvPolynomial (Fin 1) K) C := by
        have := hf.finitePresentation
        infer_instance
      have : Algebra.FiniteType (MvPolynomial (Fin 1) K) (C ⧸ q) :=
        Algebra.FiniteType.trans (S := C) inferInstance inferInstance
      have : Module.Finite (MvPolynomial (Fin 1) K) (C ⧸ q) :=
        finite_of_finite_type_of_isJacobsonRing _ _
      have hb := Ideal.IsMaximal.under (MvPolynomial (Fin 1) K) (⊥ : Ideal (C ⧸ q))
      have heq : q.comap f = (⊥ : Ideal (C ⧸ q)).under (MvPolynomial (Fin 1) K) := by
        ext x
        simp [Ideal.under, Ideal.Quotient.eq_zero_iff_mem, RingHom.algebraMap_toAlgebra,
          IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) K) C (C ⧸ q)]
      rw [heq]
      exact hb
    rw [hbot] at hmax'
    have h1 := ringKrullDim_eq_zero_of_isField (Ring.isField_iff_maximal_bot.mpr hmax')
    rw [hdimP] at h1
    exact one_ne_zero h1
  have hge : ¬ ringKrullDim (C ⧸ q) ≤ 0 := by
    intro h
    have : Ring.KrullDimLE 0 (C ⧸ q) := (Ring.krullDimLE_iff).mpr (by exact_mod_cast h)
    exact hnmax (Ideal.Quotient.maximal_of_isField q Ring.KrullDimLE.isField_of_isDomain)
  generalize ringKrullDim (C ⧸ q) = d at hle hge ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le hge
  | coe n =>
    norm_cast at hle hge ⊢
    induction n using ENat.recTopCoe with
    | top => exact absurd hle (by decide)
    | coe n =>
      norm_cast at hle hge ⊢
      omega

/-- For an étale `R`-algebra `E` over an `A`-algebra `R` and an `A`-algebra `K`, the ring map
`R ⊗_A K → K ⊗_A E` obtained by base change is étale. -/
private theorem exists_etale_tensorProduct (A R E K : Type*) [CommRing A] [CommRing R]
    [CommRing E] [CommRing K] [Algebra A R] [Algebra R E] [Algebra A E] [IsScalarTower A R E]
    [Algebra.Etale R E] [Algebra A K] :
    ∃ f : R ⊗[A] K →+* K ⊗[A] E, f.Etale := by
  let e1 : (R ⊗[A] K) ⊗[R] E ≃+* E ⊗[R] (R ⊗[A] K) :=
    (Algebra.TensorProduct.comm R (R ⊗[A] K) E).toRingEquiv
  let e2 : E ⊗[R] (R ⊗[A] K) ≃+* E ⊗[A] K :=
    (Algebra.TensorProduct.cancelBaseChange A R R E K).toRingEquiv
  let e3 : E ⊗[A] K ≃+* K ⊗[A] E := (Algebra.TensorProduct.comm A E K).toRingEquiv
  have hQ : (algebraMap (R ⊗[A] K) ((R ⊗[A] K) ⊗[R] E)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  have h1 : e1.toRingHom.Etale := RingHom.Etale.of_bijective e1.bijective
  have h2 : e2.toRingHom.Etale := RingHom.Etale.of_bijective e2.bijective
  have h3 : e3.toRingHom.Etale := RingHom.Etale.of_bijective e3.bijective
  exact ⟨_, StacksDraft.etale_comp _ _ hQ
    (StacksDraft.etale_comp _ _ h1 (StacksDraft.etale_comp _ _ h2 h3))⟩

/-- For an étale `A[t]`-algebra `E`, the fibre `K ⊗_A E` over a field `K` is étale over `K[t]`:
there is an étale ring map `K[t] → K ⊗_A E`. -/
private theorem exists_etale_mvPolynomial_tensorProduct (A : Type*) [CommRing A]
    (E : Type*) [CommRing E] [Algebra (MvPolynomial (Fin 1) A) E] [Algebra A E]
    [IsScalarTower A (MvPolynomial (Fin 1) A) E] [Algebra.Etale (MvPolynomial (Fin 1) A) E]
    (K : Type*) [Field K] [Algebra A K] :
    ∃ f : MvPolynomial (Fin 1) K →+* K ⊗[A] E, f.Etale := by
  let e0 : MvPolynomial (Fin 1) K ≃+* MvPolynomial (Fin 1) A ⊗[A] K :=
    ((Algebra.TensorProduct.comm A (MvPolynomial (Fin 1) A) K).trans
      ((MvPolynomial.algebraTensorAlgEquiv A K).restrictScalars A)).symm.toRingEquiv
  have h0 : e0.toRingHom.Etale := RingHom.Etale.of_bijective e0.bijective
  obtain ⟨g, hg⟩ := exists_etale_tensorProduct A (MvPolynomial (Fin 1) A) E K
  exact ⟨_, StacksDraft.etale_comp _ _ h0 hg⟩

namespace IsHenselianPolynomialRing

/-- **The Henselian line is a directed colimit of smooth curves.** Let `A` be a local ring and
`A{t}` the Henselization of `A[t]` at the origin. There are a directed preorder `I` and a directed
system `(B_i)_{i ∈ I}` of étale `A[t]`-algebras with colimit `A{t}` as an `A[t]`-algebra, such
that each `B_i` is a smooth `A`-algebra whose fibres have pure dimension one: for every field `K`
with a ring map `A → K`, the quotient of `K ⊗_A B_i` by every minimal prime has Krull dimension
one. -/
@[weil "lem_fk107_henselian_line_colimit_smooth_curves"]
theorem exists_directed_etale_smooth_curves_isColimit {A : Type u} [CommRing A] [IsLocalRing A]
    {Ah : Type u} [CommRing Ah] [IsLocalRing Ah] [Algebra (LocalizationAtOrigin A (Fin 1)) Ah]
    [Algebra (MvPolynomial (Fin 1) A) Ah]
    [IsScalarTower (MvPolynomial (Fin 1) A) (LocalizationAtOrigin A (Fin 1)) Ah]
    (h : IsHenselianPolynomialRing A (Fin 1) Ah) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirectedOrder I) (_ : Nonempty I)
      (B : I ⥤ CommAlgCat.{u} (MvPolynomial (Fin 1) A))
      (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of (MvPolynomial (Fin 1) A) Ah)),
      Nonempty (IsColimit (Cocone.mk _ ι)) ∧
      ∀ i, Algebra.Etale (MvPolynomial (Fin 1) A) (B.obj i) ∧
        letI : Algebra A (B.obj i) :=
          ((algebraMap (MvPolynomial (Fin 1) A) (B.obj i)).comp
            (algebraMap A (MvPolynomial (Fin 1) A))).toAlgebra
        Algebra.Smooth A (B.obj i) ∧
        ∀ (K : Type v) [Field K] [Algebra A K], ∀ q ∈ minimalPrimes (K ⊗[A] B.obj i),
          ringKrullDim ((K ⊗[A] B.obj i) ⧸ q) = 1 := by
  have hi : StacksDraft.IndEtale (MvPolynomial (Fin 1) A) Ah :=
    StacksDraft.indEtale_comp (B := LocalizationAtOrigin A (Fin 1))
      (StacksDraft.indEtale_atPrime (originIdeal A (Fin 1))) h.ind_etale
  obtain ⟨J, _, _, pres, hJ⟩ := StacksDraft.indEtale_iff.mp hi
  obtain ⟨α, _, _, _, F, _⟩ := IsFiltered.exists_directed J
  refine ⟨α, inferInstance, ‹_›, ‹_›, F ⋙ pres.diag, Functor.whiskerLeft F pres.ι,
    ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm pres.isColimit⟩, fun i => ?_⟩
  have het : Algebra.Etale (MvPolynomial (Fin 1) A) ((F ⋙ pres.diag).obj i) := hJ (F.obj i)
  refine ⟨het, ?_⟩
  let : Algebra A ((F ⋙ pres.diag).obj i) :=
    ((algebraMap (MvPolynomial (Fin 1) A) ((F ⋙ pres.diag).obj i)).comp
      (algebraMap A (MvPolynomial (Fin 1) A))).toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin 1) A) ((F ⋙ pres.diag).obj i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨Algebra.Smooth.of_etale_of_smooth A (MvPolynomial (Fin 1) A) _, ?_⟩
  intro K _ _ q hq
  obtain ⟨f, hf⟩ := exists_etale_mvPolynomial_tensorProduct A ((F ⋙ pres.diag).obj i) K
  exact ringKrullDim_quotient_eq_one_of_etale f hf hq

end IsHenselianPolynomialRing

end MvPolynomial
