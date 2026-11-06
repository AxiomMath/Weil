module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
public import WeilFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition

/-!
# Injective sheaves on the étale category are flabby

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes. An injective object
`I` of any of the following categories is flabby, i.e. `Ȟ^i(𝔘, I) = 0` for every `i > 0` and
every étale covering `𝔘` of every object of `Et(S)`:

* (a) the abelian sheaves on `Et(S)`;
* (b) the torsion sheaves `𝒯(S)` on the small étale site of `S` (for `S` locally noetherian),
  restricted to `Et(S)`;
* (c) the sheaves of `R`-modules on `Et(S)`, for a ring `R` (for instance `R = ℤ/nℤ`).

Cases (a) and (c) follow from the vanishing of positive-degree Čech cohomology of presheaves
injective in the presheaf category, since an injective sheaf is an injective presheaf. For (b),
let `z` be a Čech cocycle of positive degree of `I` on a covering `𝔘`. Each `𝔘`-term of the Čech
complex is a finite product of groups of sections over noetherian schemes, which are torsion
groups, so `n • z = 0` for some `n ≥ 1`. Hence `z` is a cocycle of the kernel `I_n` of
multiplication by `n`, which is an injective sheaf of `ℤ/nℤ`-modules; by (c) it is a coboundary
in `I_n`, hence in `I`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isFlabby_of_injective_addCommGrp`: case (a).
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.isFlabby_restrict_of_injective`: case (b).
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isFlabby_of_injective_moduleCat`: case (c),
  for a ring `R` small with respect to the universe of the sheaves.
* `CategoryTheory.Sheaf.injective_kernel_ι_hom_app`,
  `CategoryTheory.Sheaf.exists_kernel_ι_hom_app_eq`: the sections of the kernel of a morphism of
  abelian sheaves are the sections of the source which it sends to zero.

## Implementation notes

The source deduces (b) by writing `I` as the filtered colimit of its `n`-torsion subsheaves and
passing to the colimit in Čech cohomology. Here the colimit is replaced by an argument on one
cocycle: since the covering is finite, a cocycle is already killed by a single `n`, and lifting
it to `I_n` uses only that the kernel of a morphism of sheaves is computed sectionwise.

Case (c) is stated for a ring `R : Type w` with `Small.{u} R` and sheaves valued in
`ModuleCat.{u} R`, so that it applies to `ℤ/nℤ : Type` as well as to rings in the universe `u`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u' u

namespace CategoryTheory.Sheaf

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) [HasKernel f] (X : Cᵒᵖ)

/-- The sections of the kernel of a morphism of abelian sheaves inject into the sections of its
source. -/
theorem injective_kernel_ι_hom_app : Function.Injective ((kernel.ι f).hom.app X) := by
  let Φ := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj X
  have hs := KernelFork.mapIsLimit _ (kernelIsKernel f) Φ
  have : Mono (Φ.map (kernel.ι f)) := Fork.IsLimit.mono hs
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- A section of the source of a morphism of abelian sheaves which the morphism sends to zero is
a section of its kernel. -/
theorem exists_kernel_ι_hom_app_eq (x : F.obj.obj X) (hx : f.hom.app X x = 0) :
    ∃ y, (kernel.ι f).hom.app X y = x := by
  let Φ := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj X
  have hs := KernelFork.mapIsLimit _ (kernelIsKernel f) Φ
  let T := ShortComplex.mk (Φ.map (kernel.ι f)) (Φ.map f)
    (by rw [← Φ.map_comp, kernel.condition, Φ.map_zero])
  exact (ShortComplex.ab_exact_iff T).1 (T.exact_of_f_is_kernel hs) x hx

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An injective sheaf on `Et(S)` with values in an abelian category with products, in which
sheafification exists, is flabby. -/
theorem isFlabby_of_injective_of_hasSheafify {A : Type*} [Category.{u} A] [Abelian A]
    [HasProducts.{u} A] [HasSheafify (topology B S hS) A]
    (I : Sheaf (topology B S hS) A) [Injective I] : IsFlabby I.obj := by
  have : Injective I.obj := I.injective_obj
  intro U E _ ν hν
  let e := equivSmallModel.{u} (SmallNoetherianSeparatedEtale B S hS)
  exact Stacks.CechSite.isZero_cechCohomology_of_injective_presheaf e.inverse.obj
    (fun W ↦ ⟨e.functor.obj W, ⟨(e.unitIso.app W).symm⟩⟩) E I.obj ν hν

/-- **Injective abelian sheaves are flabby.** An injective object `I` of the category of abelian
sheaves on `Et(S)` satisfies `Ȟ^i(𝔘, I) = 0` for every `i > 0` and every étale covering `𝔘` of
every object of `Et(S)`. -/
@[weil "lem_fk104_injective_sheaf_cech_acyclic"]
theorem isFlabby_of_injective_addCommGrp
    (I : Sheaf (topology B S hS) AddCommGrpCat.{u}) [Injective I] : IsFlabby I.obj := by
  have : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  exact isFlabby_of_injective_of_hasSheafify I

/-- **Injective sheaves of `R`-modules are flabby.** For a ring `R` (for instance `ℤ/nℤ`), an
injective object `I` of the category of sheaves of `R`-modules on `Et(S)` satisfies
`Ȟ^i(𝔘, I) = 0` for every `i > 0` and every étale covering `𝔘` of every object of `Et(S)`. -/
@[weil "lem_fk104_injective_sheaf_cech_acyclic"]
theorem isFlabby_of_injective_moduleCat {R : Type w} [Ring R] [Small.{u} R]
    (I : Sheaf (topology B S hS) (ModuleCat.{u} R)) [Injective I] : IsFlabby I.obj := by
  have : PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by
    let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (Shrink.ringEquiv R : Shrink.{u} R ≃+* R)
    change PreservesFilteredColimits (e.functor ⋙ forget (ModuleCat.{u} (Shrink.{u} R)))
    infer_instance
  have : HasSheafify ((equivSmallModel.{u} (SmallNoetherianSeparatedEtale B S hS)).inverse
      |>.inducedTopology (topology B S hS)) (ModuleCat.{u} R) := inferInstance
  have : HasSheafify (topology B S hS) (ModuleCat.{u} R) :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  exact isFlabby_of_injective_of_hasSheafify I

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

namespace AlgebraicGeometry.SmallEtale.TorsionSheafCategory

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Injective torsion sheaves are flabby.** Let `S` be locally noetherian and `I` an injective
object of the category `𝒯(S)` of torsion sheaves on the small étale site of `S`. Then the
restriction of `I` to `Et(S)` satisfies `Ȟ^i(𝔘, I) = 0` for every `i > 0` and every étale
covering `𝔘` of every object of `Et(S)`. -/
@[weil "lem_fk104_injective_sheaf_cech_acyclic"]
theorem isFlabby_restrict_of_injective [IsLocallyNoetherian S] (I : TorsionSheafCategory B S hS)
    [Injective I] :
    IsFlabby ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ I.obj.obj) := by
  intro U E hE ν hν
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  have hI := (isTorsionSheaf_iff_forall_isAddTorsion I.obj).1 I.property
  have : Finite E.I₀ := hE.finite
  let P := (SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ I.obj.obj
  have hexact : ∀ (Q : EtalePresheaf B S hS AddCommGrpCat.{u}),
      IsZero (cechCohomology E Q (m + 1)) ↔ ∀ z : (cechComplex E Q).X (m + 1),
        (cechComplex E Q).d (m + 1) (m + 2) z = 0 →
          ∃ y, (cechComplex E Q).d m (m + 1) y = z := fun Q ↦ by
    rw [cechCohomology, Stacks.CechSite.cechCohomology,
      ← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    rfl
  rw [hexact]
  intro z hz
  let zc := Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor E P (m + 1)) z
  have : Fintype (Fin (m + 2) → E.I₀) := Fintype.ofFinite _
  let n : ℕ := ∏ k, addOrderOf (zc k)
  have hn : 0 < n := Finset.prod_pos fun k _ ↦ (hI _ (zc k)).addOrderOf_pos
  have hnz : ∀ k, n • zc k = 0 := fun k ↦
    addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
  let K := Sheaf.nTorsion (SmallEtale.topology B S hS) n I.obj
  have : Injective K := injective_nTorsion B S hS hn I
  let M := (SmallNoetherianSeparatedEtale.sheafEquiv B S hS (ModuleCat.{u} (ZMod n))).inverse.obj K
  have : Injective M := inferInstance
  have hM := isFlabby_of_injective_moduleCat M E hE (m + 1) hν
  have hQ := Stacks.CechSite.isZero_cechCohomology_comp_coefficients E
    (forget₂ (ModuleCat.{u} (ZMod n)) AddCommGrpCat.{u}) M.obj (m + 1) hM
  let Q : EtalePresheaf B S hS AddCommGrpCat.{u} :=
    (SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ (kernel (n • 𝟙 I.obj)).obj
  change IsZero (cechCohomology E Q (m + 1)) at hQ
  let k : Q ⟶ P := Functor.whiskerLeft (SmallNoetherianSeparatedEtale.inclusion B S hS).op
    (kernel.ι (n • 𝟙 I.obj)).hom
  have hlift : ∀ V (x : P.obj V), n • x = 0 → ∃ y, k.app V y = x := fun V x hx ↦
    Sheaf.exists_kernel_ι_hom_app_eq _ _ x (by
      have h1 := ((sheafToPresheaf _ AddCommGrpCat.{u}) ⋙
        (evaluation _ AddCommGrpCat.{u}).obj
          (op ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj V.unop))).map_nsmul
            (f := 𝟙 I.obj) (n := n)
      refine (ConcreteCategory.congr_hom h1 x).trans ?_
      simpa using hx)
  choose y hy using fun kk ↦ hlift _ (zc kk) (hnz kk)
  let w := (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor E Q (m + 1))).symm y
  let φ := (Stacks.CechSite.cechComplexFunctor E).map k
  have hkw : φ.f (m + 1) w = z := by
    apply (Stacks.CechSite.productAddEquiv _).injective
    funext kk
    refine (Stacks.CechSite.cechComplexFunctor_map_f_π_apply E k (m + 1) kk w).trans ?_
    exact (congrArg (k.app _) (congrFun
      ((Stacks.CechSite.productAddEquiv _).apply_symm_apply y) kk)).trans (hy kk)
  have hinj : ∀ p, Function.Injective (φ.f p) := by
    intro p a b hab
    apply (Stacks.CechSite.productAddEquiv _).injective
    funext kk
    have := congrArg (Pi.π (Stacks.CechSite.cochainFactor E P p) kk) hab
    exact Sheaf.injective_kernel_ι_hom_app _ _
      ((Stacks.CechSite.cechComplexFunctor_map_f_π_apply E k p kk a).symm.trans
        (this.trans (Stacks.CechSite.cechComplexFunctor_map_f_π_apply E k p kk b)))
  have hcomm : ∀ p q (x : (cechComplex E Q).X p),
      (cechComplex E P).d p q (φ.f p x) = φ.f q ((cechComplex E Q).d p q x) := fun p q x ↦ by
    have h := ConcreteCategory.congr_hom (φ.comm p q) x
    simpa only [ConcreteCategory.comp_apply] using h
  have hw : (cechComplex E Q).d (m + 1) (m + 2) w = 0 := by
    apply hinj (m + 2)
    rw [map_zero]
    exact (hcomm _ _ w).symm.trans (by rw [hkw]; exact hz)
  obtain ⟨y', hy'⟩ := (hexact Q).1 hQ w hw
  exact ⟨φ.f m y', by rw [hcomm, hy', hkw]⟩

end AlgebraicGeometry.SmallEtale.TorsionSheafCategory
