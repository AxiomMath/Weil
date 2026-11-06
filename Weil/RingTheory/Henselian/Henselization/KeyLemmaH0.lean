module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.RingTheory.Henselian.Henselization.SmoothStrictlyHenselianAlgebra
public import Weil.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.Henselian.NormalDomainOfHenselization

/-!
# The key lemma in degree zero

Let `A` be an excellent strictly Henselian local ring, `𝔭 ⊂ A` a prime ideal, `K` a field
extension of the residue field `κ(𝔭)` (in the source, a separable closure), `M` an abelian group
and `B` an `A`-algebra which is sh-smooth over `A` (`Algebra.IsShSmooth`). For a finite
subextension `κ(𝔭) ⊆ L ⊆ K` put `X_L = Spec (B ⊗[A] L)`. Then the constant sections induce a
bijection `M → H⁰(X_L, M_{X_L})` for every such `L`; in particular the transition maps of the
directed system `L ↦ H⁰(X_L, M_{X_L})` are bijective and compatible with the constant sections,
so `M → colim_L H⁰(X_L, M_{X_L})` is bijective.

The proof shows that `B ⊗[A] L` is a domain. Let `A_L` be the integral closure of `A ⧸ 𝔭` in
`L`. As `A` is excellent, `A ⧸ 𝔭` is Japanese, so `A_L` is a finite `A`-algebra; it is a normal
domain with fraction field `L`, and, being integral over the Henselian ring `A`, it is a local
ring. By finite base change, `A_L ⊗[A] B` is sh-smooth over `A_L`, hence the strict
Henselization of a localization of a smooth algebra over the normal domain `A_L`; smooth algebras
over normal rings are normal (Stacks 033C) and strict Henselizations of normal local domains are
normal domains (Stacks 06DI), so `A_L ⊗[A] B` is a domain. It is flat and local over `A_L`, hence
faithfully flat, so `A_L → A_L ⊗[A] B` is injective, and `B ⊗[A] L ≅ (A_L ⊗[A] B) ⊗[A_L] L` is
a localization of `A_L ⊗[A] B` at a multiplicative set of nonzero elements, hence a domain.
Therefore `X_L` is irreducible, in particular nonempty and connected, and every locally constant
map `X_L → M` is constant; `H⁰(X_L, M_{X_L})` is the group of such maps
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.hZeroLocallyConstantSheafAbAddEquiv`).

## Main results

* `Algebra.IsShSmooth.bijective_const_hZero`: the constant sections `M → H⁰(X_L, M_{X_L})` are
  bijective for every finite extension `L` of `κ(𝔭)` inside `K`.

## Implementation notes

The source states the bijectivity of `M → colim_L H⁰(X_L, M_{X_L})`; the result here is the
bijectivity for each `L`, from which the colimit statement follows, the transition maps being
compatible with the constant sections. The source's hypotheses that `B` is strictly Henselian with
`A → B` local, that the residue field extension is algebraic, that `dim B/𝔪_A B ≤ 1`, that `K` is
a separable closure of `κ(𝔭)`, and that `M` is finite of order invertible in `A` are not used,
and are omitted. The source proves the statement by reduction to the Henselian line over a normal
domain; the argument above uses instead that sh-smooth algebras over normal local domains are
domains, which needs only finite base change.

The cohomology `H⁰` is taken on the small étale site `SmallEtale E X_L hX` of a big étale site
`E` containing `X_L`, with `Ext`-groups in an arbitrary universe `w`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe w u v

namespace Algebra.IsShSmooth

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem isNormalRing_of_isDomain_of_isIntegrallyClosed' (R : Type*) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] : IsNormalRing R := by
  intro p hp
  exact ⟨IsLocalization.isDomain_of_local_atPrime hp,
    isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
      (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors⟩

/-- An algebra which is sh-smooth over a normal local domain is a normal domain. -/
private theorem isDomain_and_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A]
    (h : IsShSmooth A B) : IsDomain B ∧ IsIntegrallyClosed B := by
  obtain ⟨C, _, _, _, hC, -, Csh, _, _, _, _, _, hsh, ⟨e⟩⟩ := isShSmooth_iff_isHenselization.mp h
  obtain ⟨C₀, _, _, _, q, _, ⟨f⟩⟩ := hC
  have hC₀ : IsNormalRing C₀ :=
    Algebra.isNormalRing_of_smooth A C₀ (isNormalRing_of_isDomain_of_isIntegrallyClosed' A)
  obtain ⟨h₁, h₂⟩ := hC₀ q
  have : IsDomain C := f.toRingEquiv.symm.injective.isDomain _
  have : IsIntegrallyClosed C := IsIntegrallyClosed.of_equiv f.toRingEquiv
  let κ := SeparableClosure (ResidueField C)
  let T := henselizationTower C κ
  have : IsHenselization C κ Csh := hsh
  have hT : IsDomain Csh ∧ IsIntegrallyClosed Csh :=
    ((isNormalDomain_tfae_henselization_strictHenselization C T.henselization Csh κ).out
      1 3).mp (⟨inferInstance, inferInstance⟩ : IsDomain C ∧ IsIntegrallyClosed C)
  have := hT.1
  have := hT.2
  exact ⟨e.toRingEquiv.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv.symm⟩

/-- An algebra which is sh-smooth over `A` is flat over `A`. -/
private theorem flat (h : IsShSmooth A B) : Module.Flat A B := by
  obtain ⟨C, _, _, _, hC, -, Csh, _, _, _, _, _, hsh, ⟨e⟩⟩ := isShSmooth_iff_isHenselization.mp h
  obtain ⟨C₀, _, _, _, q, _, ⟨f⟩⟩ := hC
  have : Module.FaithfullyFlat C Csh := IsHenselization.faithfullyFlat
    (L := SeparableClosure (ResidueField C))
  have : Module.Flat A (Localization.AtPrime q) := Module.Flat.trans A C₀ _
  have : Module.Flat A C := Module.Flat.of_linearEquiv f.symm.toLinearEquiv
  have : Module.Flat A Csh := Module.Flat.trans A C Csh
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- **Generic fibres of sh-smooth algebras are domains.** Let `A` be an excellent strictly
Henselian local ring, `𝔭` a prime ideal of `A`, `B` an `A`-algebra which is sh-smooth over `A`,
and `L` a finite field extension of the residue field `κ(𝔭)`. Then `B ⊗[A] L` is a domain. -/
private theorem isDomain_tensorProduct_of_finiteDimensional [StrictlyHenselianLocalRing A]
    (hA : IsExcellent A) (p : Ideal A) [p.IsPrime] (h : IsShSmooth A B) (L : Type u) [Field L]
    [Algebra A L] [Algebra p.ResidueField L] [IsScalarTower A p.ResidueField L]
    [FiniteDimensional p.ResidueField L] : IsDomain (B ⊗[A] L) := by
  let R := A ⧸ p
  let κ := p.ResidueField
  let : Algebra R L := ((algebraMap κ L).comp (algebraMap R κ)).toAlgebra
  have : IsScalarTower R κ L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A R L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A κ L, IsScalarTower.algebraMap_apply A R κ]
    rfl
  let A₁ := integralClosure R L
  have hR : IsJapaneseRing R := (isNagataRing_of_isQuasiExcellent hA.1).isJapaneseRing_quotient p
  have : Module.Finite R A₁ := module_finite_integralClosure_of_isJapaneseRing hR κ L
  have : Module.Finite A A₁ := Module.Finite.trans R A₁
  have : Algebra.IsIntegral A A₁ := inferInstance
  obtain ⟨hA₁, -, -⟩ := RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
    (algebraMap A A₁) (Algebra.IsIntegral.isIntegral (R := A) (A := A₁))
  have : IsIntegrallyClosed A₁ := integralClosure.isIntegrallyClosedOfFiniteExtension κ
  have : IsFractionRing A₁ L := integralClosure.isFractionRing_of_finite_extension κ L
  obtain ⟨-, hB₁, hloc, h₁⟩ := tensorProduct_of_module_finite (A₁ := A₁) h
  have : IsDomain (A₁ ⊗[A] B) := h₁.isDomain_and_isIntegrallyClosed.1
  have : Module.Flat A₁ (A₁ ⊗[A] B) := h₁.flat
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A₁) (B := A₁ ⊗[A] B)
  have hinj : Function.Injective (algebraMap A₁ (A₁ ⊗[A] B)) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr this).injective
  have := IsLocalization.tensor (S := A₁ ⊗[A] B) (A := L) (nonZeroDivisors A₁)
  have : IsDomain ((A₁ ⊗[A] B) ⊗[A₁] L) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid
      (A₁ ⊗[A] B) (nonZeroDivisors A₁)) ((A₁ ⊗[A] B) ⊗[A₁] L)
      (map_le_nonZeroDivisors_of_injective _ hinj le_rfl)
  let e : L ⊗[A₁] (A₁ ⊗[A] B) ≃ₐ[L] L ⊗[A] B := Algebra.TensorProduct.cancelBaseChange A A₁ L L B
  exact ((((Algebra.TensorProduct.comm A₁ (A₁ ⊗[A] B) L).toRingEquiv.trans
    e.toRingEquiv).trans (Algebra.TensorProduct.comm A L B).toRingEquiv).symm.injective).isDomain _

end Algebra.IsShSmooth

namespace Algebra.IsShSmooth

open AlgebraicGeometry CategoryTheory

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]

/-- **Key lemma in degree zero.** Let `A` be an excellent strictly Henselian local ring, `𝔭` a
prime ideal of `A`, `K` a field extension of `κ(𝔭)`, `B` an `A`-algebra sh-smooth over `A`, `M` an
abelian group, and `L` a finite subextension of `K / κ(𝔭)`. Then the constant sections
`M → H⁰(X_L, M_{X_L})`, `X_L = Spec (B ⊗[A] L)`, form a bijection. -/
@[weil "lem_fk107_key_lemma_h0"]
theorem bijective_const_hZero [StrictlyHenselianLocalRing A] (hA : IsExcellent A)
    (p : Ideal A) [p.IsPrime] (h : IsShSmooth A B) (K : Type u) [Field K]
    [Algebra p.ResidueField K] [Algebra A K] [IsScalarTower A p.ResidueField K]
    (L : IntermediateField p.ResidueField K) [FiniteDimensional p.ResidueField L]
    (M : Type u) [AddCommGroup M] (E : BigEtaleSite.{u})
    (hX : E.Contains (Spec (.of (B ⊗[A] L))))
    [HasExt.{w} (Sheaf (SmallEtale.topology E _ hX) AddCommGrpCat.{u})] :
    Function.Bijective fun m : M =>
      (SmallNoetherianSeparatedEtale.hZeroLocallyConstantSheafAbAddEquiv E _ hX M).symm
        (LocallyConstant.const _ m) := by
  have : IsDomain (B ⊗[A] L) := isDomain_tensorProduct_of_finiteDimensional hA p h L
  have hirr : IrreducibleSpace (Spec (.of (B ⊗[A] L))) := inferInstance
  have : PreconnectedSpace (Spec (.of (B ⊗[A] L))) :=
    ⟨(IrreducibleSpace.isIrreducible_univ _).isConnected.isPreconnected⟩
  refine (AddEquiv.bijective _).comp ⟨fun m₁ m₂ hm => ?_, fun g => ?_⟩
  · obtain ⟨x⟩ := hirr.toNonempty
    simpa using congrArg (fun g : LocallyConstant _ M => g x) hm
  · obtain ⟨x⟩ := hirr.toNonempty
    exact ⟨g x, LocallyConstant.ext fun y =>
      (g.isLocallyConstant.apply_eq_of_preconnectedSpace y x).symm⟩

end Algebra.IsShSmooth
