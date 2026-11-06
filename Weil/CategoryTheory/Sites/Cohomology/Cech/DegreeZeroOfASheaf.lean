module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyCovering
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor

/-!
# Injective étale sheaves are Čech-acyclic

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, `I` an injective
object of the category of abelian sheaves on `Et(S)`, `U` an object of `Et(S)` and
`𝔘 = (Uᵢ → U)_{i}` a family of morphisms of `Et(S)` with target `U`. Then the Čech cohomology
`Ȟ^p(𝔘, I)` vanishes for every `p ≥ 1`.

The proof is the classical one. Mapping the integral Čech complex `K_•`,
`K_p = ⊕_{ν ∈ I^{p+1}} ℤ[h_{U_ν}]`, into a presheaf `G` gives, by the Yoneda lemma, the Čech
complex `Č^•(𝔘, G)`; the complex `K_•` is exact in positive degrees, objectwise; and an
injective sheaf is an injective presheaf, sheafification being left adjoint to the inclusion of
sheaves, so `Hom(-, I)` carries the exact complex `K_•` to an exact complex.

## Main results

* `CategoryTheory.isZero_cechCohomology_of_injective_presheaf`: the positive-degree Čech
  cohomology of an injective presheaf of abelian groups on any category vanishes, with the
  coefficient universe containing only the morphism and index universes.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isZero_cechCohomology_of_injective`: for an
  injective abelian sheaf `I` on `Et(S)`, `Ȟ^p(𝔘, I) = 0` for every `p ≥ 1`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_d_eq_of_injective`: the same in terms
  of cochains: every Čech `p`-cocycle of `I`, `p ≥ 1`, is a coboundary.

## Implementation notes

The vanishing for injective presheaves is Stacks 03OR
(`Stacks.CechSite.injective_presheaf_cechCohomology_isZero`), whose coefficient universe must
also contain the *object* universe of the category, because the abelian group of morphisms of
presheaves lives there. The objects of `Et(S)` form a large type while its morphisms are small,
so that version would only apply to sheaves with values in abelian groups of the next universe.
The version proved here lifts the Čech complex of `I` along `AddCommGrpCat.uliftFunctor`,
which is additive, preserves products and homology and is fully faithful, so it reflects the
vanishing; the coefficients then need only contain the morphism and index universes, which
covers sheaves of `u`-small abelian groups on `Et(S)`.

The statement holds for any family of morphisms with target `U`; that the family is an étale
covering is not used. Sheafification on `Et(S)` exists because `Et(S)` is essentially small.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe a w v u₀ u

namespace CategoryTheory

/-- **Injective presheaves are Čech-acyclic.** For a family `E = (Xᵢ ⟶ X)_{i}` (indexed in
universe `w`) in a category with `v`-small hom-sets and an injective presheaf `I` of abelian
groups whose universe contains `v` and `w`, the Čech cohomology `Ȟ^p(E, I)` vanishes for every
`p ≥ 1`. -/
theorem isZero_cechCohomology_of_injective_presheaf {C : Type u₀} [Category.{v} C] {X : C}
    (E : PreZeroHypercover.{w} X)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (I : Cᵒᵖ ⥤ AddCommGrpCat.{max v w a}) [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E I p) := by
  have : (preadditiveYoneda.obj I).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj I).1 inferInstance
  have : (preadditiveYoneda.obj I).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hHom :
      ((Stacks.CechSite.homComplexFunctor.{v, u₀, max w a}
        (Stacks.CechSite.integralCechComplex.{w, v, u₀, max w a} E)).obj I).ExactAt p :=
    ShortComplex.Exact.map ((HomologicalComplex.exactAt_iff_isZero_homology _ p).2
      (Stacks.CechSite.integralCechComplex_homology_isZero.{w, v, u₀, max w a} E p hp)).op
      (preadditiveYoneda.obj I)
  have hLift : (Stacks.CechSite.cechComplex E
      (I ⋙ AddCommGrpCat.uliftFunctor.{u₀, max v w a})).ExactAt p :=
    hHom.of_iso ((Stacks.CechSite.homIntegralCechComplexIso.{w, v, u₀, max w a} E).app I)
  have hZ : IsZero (Stacks.CechSite.cechCohomology E
      (I ⋙ AddCommGrpCat.uliftFunctor.{u₀, max v w a}) p) := hLift.isZero_homology
  have h' : IsZero (AddCommGrpCat.uliftFunctor.{u₀, max v w a}.obj
      (Stacks.CechSite.cechCohomology E I p)) :=
    hZ.of_iso (Stacks.CechSite.sliceCechCohomologyCompCoefficientsIso E
      AddCommGrpCat.uliftFunctor.{u₀, max v w a} ((Over.forget X).op ⋙ I) p).symm
  exact IsZero.of_full_of_faithful_of_isZero AddCommGrpCat.uliftFunctor.{u₀, max v w a} _ h'

end CategoryTheory

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{w} U)

/-- An injective abelian sheaf on `Et(S)` is an injective presheaf: sheafification, which exists
because `Et(S)` is essentially small, is left adjoint to the inclusion of sheaves into
presheaves and preserves monomorphisms. -/
theorem injective_obj_of_injective (I : Sheaf (topology B S hS) AddCommGrpCat.{max u a})
    [Injective I] : Injective I.obj := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u a}) :=
    preservesFilteredColimitsOfSize_shrink.{u, max u a, u, max u a} _
  have := hasSheafifyEssentiallySmallSite.{u} (topology B S hS) AddCommGrpCat.{max u a}
  exact Sheaf.injective_obj I

/-- **Injective étale sheaves are Čech-acyclic.** For an injective abelian sheaf `I` on `Et(S)`
and a family `𝔘 = (Uᵢ ⟶ U)_{i}` of morphisms of `Et(S)` with target `U` (an étale covering of
`U`, say), the Čech cohomology `Ȟ^p(𝔘, I)` vanishes for every `p ≥ 1`. -/
@[weil "lem_fk102_cech_injective_acyclic"]
theorem isZero_cechCohomology_of_injective
    (I : Sheaf (topology B S hS) AddCommGrpCat.{max u w a}) [Injective I] (p : ℕ) (hp : 1 ≤ p) :
    IsZero (cechCohomology (A := AddCommGrpCat.{max u w a}) E I.obj p) := by
  have := injective_obj_of_injective.{max w a} I
  exact isZero_cechCohomology_of_injective_presheaf.{a} E I.obj p hp

/-- **Every positive-degree Čech cocycle of an injective étale sheaf is a coboundary.** For an
injective abelian sheaf `I` on `Et(S)`, a family `𝔘` with target `U`, `p ≥ 1` and a cochain
`x ∈ Č^p(𝔘, I)` with `d^p x = 0`, there is `y ∈ Č^{p-1}(𝔘, I)` with `d^{p-1} y = x`. -/
theorem exists_d_eq_of_injective
    (I : Sheaf (topology B S hS) AddCommGrpCat.{max u w a}) [Injective I] {p : ℕ} (hp : 1 ≤ p)
    (x : (cechComplex E I.obj).X p) (hx : (cechComplex E I.obj).d p (p + 1) x = 0) :
    ∃ y, (cechComplex E I.obj).d (p - 1) p y = x := by
  have hZ := isZero_cechCohomology_of_injective.{a} E I p hp
  have hsub : Subsingleton
      (cechCycles E I.obj p ⧸ (cechBoundaries E I.obj p).addSubgroupOf (cechCycles E I.obj p)) :=
    have := AddCommGrpCat.isZero_iff_subsingleton.mp hZ
    (cechCohomologyAddEquiv E I.obj p).symm.injective.subsingleton
  have hmem : (⟨x, hx⟩ : cechCycles E I.obj p) ∈
      (cechBoundaries E I.obj p).addSubgroupOf (cechCycles E I.obj p) :=
    (QuotientAddGroup.eq_zero_iff _).mp (Subsingleton.elim _ _)
  rw [AddSubgroup.mem_addSubgroupOf, cechBoundaries_eq_range] at hmem
  exact hmem

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
