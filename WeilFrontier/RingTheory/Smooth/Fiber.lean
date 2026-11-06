module

public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.LocalRing
public import Weil.Attr
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Field.ULift
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.FieldTheory.Separable.PerfectField

/-!
# Étale algebras via their fibres

Let `A → B` be a flat ring homomorphism of finite presentation. Then `B` is étale over `A` if and
only if, for every prime `q` of `A`, the fibre `κ(q) ⊗[A] B` is étale over the residue field
`κ(q)`, i.e. is a finite product of finite separable field extensions of `κ(q)`
(`Algebra.Etale.iff_exists_algEquiv_prod`).

The forward direction is base change. For the converse, a prime `Q` of `B` over `q` corresponds
to a prime `Q'` of the fibre, and `(κ(q) ⊗[A] B)_{Q'} ≅ B_Q ⧸ q B_Q`. If the fibre is unramified
at `Q'`, this quotient is a field, unramified over `κ(q)`; hence `q B_Q` is the maximal ideal of
`B_Q` and `κ(Q)/κ(q)` is separable, which is unramifiedness of `B` at `Q`. A flat, finitely
presented, formally unramified algebra is étale.

## Main results

- `Algebra.isUnramifiedAt_of_formallyUnramified_fiber`: if the fibre over `p` is unramified at
  the prime corresponding to `Q`, then `S` is unramified at `Q`.
- `Algebra.formallyUnramified_of_forall_fiber`: formally unramified fibres imply formally
  unramified, for an essentially finite type algebra.
- `Algebra.etale_iff_forall_etale_fiber`: a flat, finitely presented algebra is étale if and only
  if all its fibres are étale.
- `RingHom.etale_algebraMap_iff_forall_etale_fiber`: the same for a flat, finite type algebra over
  a noetherian ring.

## Implementation notes

A finite separable algebra over a field `k` is expressed as `Algebra.Etale k _`. The noetherian
hypothesis on `B` in the classical statement is not needed, and the noetherian hypothesis on `A`
is only used to turn finite type into finite presentation.

## References

* [FK88] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

public section

open TensorProduct IsLocalRing

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `Q` be a prime of the fibre `κ(p) ⊗[R] S` such that the fibre is formally unramified over
`κ(p)` at `Q`, and let `r` be the corresponding prime of `S`. Then `S` is unramified over `R`
at `r`. -/
lemma isUnramifiedAt_of_formallyUnramified_fiber [EssFiniteType R S]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    [FormallyUnramified p.ResidueField (Localization.AtPrime Q)] (r : Ideal S) [r.IsPrime]
    (hr : Q.comap (TensorProduct.includeRight (R := R) (A := p.ResidueField) (B := S)) = r) :
    IsUnramifiedAt R r := by
  subst hr
  set r := Q.comap (TensorProduct.includeRight (R := R) (A := p.ResidueField) (B := S))
  have : r.LiesOver p := ⟨by
    refine (Ideal.over_def Q p).trans ?_
    ext x
    simp only [Ideal.mem_comap, r]
    rw [AlgHom.commutes]⟩
  let := Localization.AtPrime.algebraOfLiesOver p r
  have hQ : IsField (Localization.AtPrime Q) := by
    have := FormallyUnramified.map_maximalIdeal (R := p.ResidueField) (S := Localization.AtPrime Q)
    rw [maximalIdeal_eq_bot, Ideal.map_bot, eq_comm] at this
    exact (isField_iff_maximalIdeal_eq).mpr this
  let e := Ideal.Fiber.localizationAlgEquivQuotient p Q
  have hT := (MulEquiv.isField hQ e.toMulEquiv.symm)
  have hmax : (p.map (algebraMap R (Localization.AtPrime r))) = maximalIdeal _ :=
    eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hT)
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime Q) :=
    .comp _ p.ResidueField _
  let e' := e.trans (Ideal.quotientEquivAlgOfEq (Localization.AtPrime p) hmax)
  have : FormallyUnramified (Localization.AtPrime p) r.ResidueField := by
    have h := FormallyUnramified.of_equiv (R := Localization.AtPrime p)
      (A := Localization.AtPrime Q) (B := r.ResidueField) e'
    exact h
  clear e e'
  have : FormallyUnramified p.ResidueField r.ResidueField :=
    .of_restrictScalars (Localization.AtPrime p) _ _
  have : EssFiniteType R r.ResidueField := .comp _ (Localization.AtPrime r) _
  have : EssFiniteType p.ResidueField r.ResidueField := .of_comp R _ _
  have : Algebra.IsSeparable p.ResidueField r.ResidueField :=
    FormallyUnramified.isSeparable p.ResidueField r.ResidueField
  exact (isUnramifiedAt_iff_map_eq R p r).mpr ⟨this, hmax⟩

/-- An essentially finite type algebra whose fibres are all formally unramified over the residue
fields is formally unramified. -/
theorem formallyUnramified_of_forall_fiber [EssFiniteType R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], FormallyUnramified p.ResidueField (p.Fiber S)) :
    FormallyUnramified R S := by
  refine formallyUnramified_iff_forall.mpr fun Q ↦ ?_
  let p := Q.asIdeal.under R
  let Q' := PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨Q.asIdeal, ⟨inferInstance, ⟨rfl⟩⟩⟩
  have hQ : Q'.asIdeal.comap TensorProduct.includeRight = Q.asIdeal := by
    rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  have := H p
  exact isUnramifiedAt_of_formallyUnramified_fiber p Q'.asIdeal Q.asIdeal hQ

/-- A flat, finitely presented algebra is étale if and only if every fibre `κ(p) ⊗[R] S` is étale
over the residue field `κ(p)`. -/
theorem etale_iff_forall_etale_fiber [FinitePresentation R S] [Module.Flat R S] :
    Etale R S ↔ ∀ (p : Ideal R) [p.IsPrime], Etale p.ResidueField (p.Fiber S) := by
  refine ⟨fun _ _ _ ↦ inferInstance, fun H ↦ ?_⟩
  have : FormallyUnramified R S := formallyUnramified_of_forall_fiber fun p _ ↦ inferInstance
  exact .of_formallyUnramified_of_flat

end Algebra

/-- Let `A → B` be a flat ring homomorphism of finite type, with `A` noetherian. Then `A → B` is
étale if and only if, for every prime `q` of `A`, the fibre `κ(q) ⊗[A] B` is étale (that is,
finite separable) over `κ(q)`. -/
@[weil "lem_fk101_etale_iff_fibres_finite_separable"]
theorem RingHom.etale_algebraMap_iff_forall_etale_fiber {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] [Module.Flat A B] :
    (algebraMap A B).Etale ↔
      ∀ (q : Ideal A) [q.IsPrime], Algebra.Etale q.ResidueField (q.ResidueField ⊗[A] B) := by
  have := Algebra.FinitePresentation.of_finiteType.mp ‹Algebra.FiniteType A B›
  exact RingHom.etale_algebraMap.trans Algebra.etale_iff_forall_etale_fiber

/-! ### Smooth algebras over a noetherian ring: flatness and regular geometric fibres -/

/-!
# Smooth algebras over a noetherian ring: flatness and regular geometric fibres

Let `A` be a noetherian ring and `B` a finitely generated `A`-algebra. Then `B` is smooth over `A`
(formally smooth and of finite presentation, `Algebra.Smooth`) if and only if `B` is a flat
`A`-module and, for every prime `𝔭 ⊂ A` and every field extension `K ⊇ κ(𝔭)`, the ring
`B ⊗[A] K` is regular. The right-hand side is the definition of a smooth algebra in
Freitag–Kiehl; the theorem identifies it with Mathlib's notion.

The forward implication holds without any noetherian hypothesis and for every regular
`A`-algebra `K`: `K ⊗[A] B` is smooth over `K` by base change, hence regular because regularity
ascends along smooth maps. For the converse, let `𝔭` be a prime and `L` an algebraic closure of
`κ(𝔭)`. The base change `L ⊗[κ(𝔭)] (κ(𝔭) ⊗[A] B) ≅ L ⊗[A] B` of the fibre is a regular finite
type algebra over the perfect field `L`, so all its residue fields are separable over `L` and it
is smooth over `L` at every prime; thus it is smooth over `L`, and smoothness of the fibre over
`κ(𝔭)` descends along the faithfully flat extension `κ(𝔭) → L`. A flat algebra of finite
presentation all of whose fibres are smooth is smooth.

## Main results

* `Algebra.isRegularRing_tensorProduct_of_smooth`: base changes of a smooth algebra to regular
  rings are regular.
* `Algebra.smooth_of_isRegularRing_tensorProduct_algebraicClosure`: a flat finitely generated
  algebra over a noetherian ring whose fibres become regular over an algebraic closure of each
  residue field is smooth.
* `Algebra.smooth_iff_flat_and_isRegularRing_tensorProduct`: smoothness of a finitely generated
  algebra over a noetherian ring is flatness together with regularity of every geometric fibre
  `B ⊗[A] K`.

## Implementation notes

No new notion of smooth algebra is introduced: Freitag–Kiehl's definition is the characterisation
`Algebra.smooth_iff_flat_and_isRegularRing_tensorProduct` of Mathlib's `Algebra.Smooth`. The field
`K` of the characterisation ranges over every universe `max u w` containing that of `A`; for the
converse only an algebraic closure of `κ(𝔭)`, transported to `Type (max u w)` by `ULift`, is used.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §7.
* [Stacks 07NF], [Stacks 00TV], [Stacks 00TF].
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- The base change `B ⊗[A] K` of a smooth `A`-algebra `B` to a regular `A`-algebra `K` (for
instance a field) is a regular ring. -/
theorem isRegularRing_tensorProduct_of_smooth {A : Type u} {B : Type v} (K : Type w) [CommRing A]
    [CommRing B] [CommRing K] [Algebra A B] [Algebra A K] [Algebra.Smooth A B] [IsRegularRing K] :
    IsRegularRing (B ⊗[A] K) :=
  have : IsRegularRing (K ⊗[A] B) := Algebra.isRegularRing_of_smooth K (K ⊗[A] B)
  .of_ringEquiv (Algebra.TensorProduct.comm A K B).toRingEquiv

/-- A finite type algebra `S` over a field `k` whose base change to an algebraic closure of `k`
is a regular ring is smooth over `k`. -/
theorem smooth_of_isRegularRing_algebraicClosure_tensorProduct (k : Type u) (S : Type v)
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [IsRegularRing (AlgebraicClosure k ⊗[k] S)] : Algebra.Smooth k S := by
  set L := AlgebraicClosure k
  have : Algebra.FinitePresentation L (L ⊗[k] S) := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have hsm : Algebra.Smooth L (L ⊗[k] S) := by
    refine ⟨?_, inferInstance⟩
    rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro q
    have : Algebra.IsSeparableExtension L q.asIdeal.ResidueField :=
      Algebra.isSeparableExtension_of_perfectField L _
    exact (Algebra.isSmoothAt_iff_isRegularLocalRing q.asIdeal
      (Localization.AtPrime q.asIdeal)).mpr inferInstance
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat L

/-- Let `A` be a noetherian ring and `B` a flat finitely generated `A`-algebra such that for every
prime `𝔭 ⊂ A` the ring `B ⊗[A] L` is regular, `L` an algebraic closure of `κ(𝔭)`. Then `B` is
smooth over `A`. -/
theorem smooth_of_isRegularRing_tensorProduct_algebraicClosure {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Flat A B]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsRegularRing (B ⊗[A] AlgebraicClosure p.ResidueField)) :
    Algebra.Smooth A B := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  refine Algebra.Smooth.of_formallySmooth_fiber fun p _ ↦ ?_
  have : IsRegularRing (AlgebraicClosure p.ResidueField ⊗[p.ResidueField] p.Fiber B) :=
    have := h p
    .of_ringEquiv ((Algebra.TensorProduct.comm A B _).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField
        (AlgebraicClosure p.ResidueField) B).symm.toRingEquiv)
  exact (smooth_of_isRegularRing_algebraicClosure_tensorProduct p.ResidueField
    (p.Fiber B)).formallySmooth

/-- **Smooth algebras over a noetherian ring** (Freitag–Kiehl, Definition I.7). Let `A` be a
noetherian ring and `B` a finitely generated `A`-algebra. Then `B` is a smooth `A`-algebra if and
only if `B` is a flat `A`-module and for every prime ideal `𝔭 ⊂ A` and every field extension
`K ⊇ κ(𝔭)` the ring `B ⊗[A] K` is regular. -/
@[weil "def_fk107_smooth_algebra"]
theorem smooth_iff_flat_and_isRegularRing_tensorProduct {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] :
    Algebra.Smooth A B ↔ Module.Flat A B ∧
      ∀ (p : Ideal A) [p.IsPrime] (K : Type (max u w)) [Field K] [Algebra p.ResidueField K]
        [Algebra A K] [IsScalarTower A p.ResidueField K], IsRegularRing (B ⊗[A] K) := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun p _ K _ _ _ _ ↦ isRegularRing_tensorProduct_of_smooth K⟩,
    fun ⟨_, h⟩ ↦ smooth_of_isRegularRing_tensorProduct_algebraicClosure fun p _ ↦ ?_⟩
  have := h p (ULift.{w} (AlgebraicClosure p.ResidueField))
  exact .of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := B)) ULift.algEquiv).toRingEquiv

end Algebra
