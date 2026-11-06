module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SoftAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.NativeCohomologyCocones
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Sheaves of modules over the sheaf of smooth functions are soft

Let `M` be a Hausdorff, σ-compact, finite-dimensional real `C^∞` manifold and let `𝒪` be the sheaf
of smooth functions on `M` with values in a normed `ℝ`-algebra `A` (for instance `ℝ` or `ℂ`).
Smooth bump functions exist on `M`: for a closed set `K` inside an open set `U` there is a smooth
`χ : M → A` equal to `1` on a neighbourhood of `K` and to `0` on a neighbourhood of the complement
of `U`. Multiplying a section over `U` by `χ` and extending it by zero turns it into a global
section agreeing with it near `K`. Hence every sheaf of `𝒪`-modules is soft. When `M` is compact,
a soft sheaf of abelian groups has vanishing cohomology in positive degrees, so
`Hⁿ(M, F) = 0` for every sheaf of `𝒪`-modules `F` and every `n ≥ 1`.

The argument uses nothing about `𝒪` except the existence of such cut-off sections, so it is
stated first for an arbitrary sheaf of rings with that property (`SheafOfModules.HasBumpSections`)
on an arbitrary topological space, and then specialised to smooth functions.

## Main definitions

* `SheafOfModules.HasBumpSections`: a sheaf of rings `R` on a space `Z` has bump sections if for
  every closed `K ⊆ U` open there is a global section equal to `1` on an open neighbourhood of
  `K` contained in `U` and to `0` on an open set which together with `U` covers `Z`.

## Main results

* `NormedAlgebra.contMDiffRing`: a normed `𝕜`-algebra is a `C^n` ring for its self model.
* `SheafOfModules.isSoft_toSheaf_of_hasBumpSections`: over a sheaf of rings with bump sections,
  the underlying abelian sheaf of every sheaf of modules is soft.
* `TopCat.Sheaf.subsingleton_H_of_isSoft`: on a compact Hausdorff space a soft abelian sheaf
  has `Hⁿ = 0` for `n > 0` (`CategoryTheory.Sheaf.H`).
* `SheafOfModules.subsingleton_H_toSheaf_of_hasBumpSections`: the two together.
* `SheafOfModules.hasBumpSections_smoothSheafRing`,
  `SheafOfModules.hasBumpSections_smoothSheafCommRing`: smooth `A`-valued functions on a
  Hausdorff σ-compact finite-dimensional real manifold have bump sections.
* `SheafOfModules.subsingleton_H_toSheaf_smoothSheafRing`,
  `SheafOfModules.subsingleton_H_toSheaf_smoothSheafCommRing`: on a compact Hausdorff
  finite-dimensional real manifold, every sheaf of modules over the sheaf of smooth `A`-valued
  functions has vanishing cohomology in positive degrees. The case of the structure sheaf itself
  is `SheafOfModules.subsingleton_H_smoothSheafCommRing_unit`.

## Implementation notes

Softness is `Stacks.Topology.IsSoft`: a section on an open neighbourhood of a closed set agrees
near that closed set with a global section. The vanishing of cohomology of soft sheaves is
`Stacks.Topology.rightAcyclic_sections_of_isSoft`, read through the identification of right
derived global sections with `CategoryTheory.Sheaf.H`; it is stated here for an arbitrary `Ext`
universe.

A sheaf of modules is a `SheafOfModules` over the sheaf of rings `smoothSheafRing I 𝓘(ℝ, A) M A`,
or, for commutative `A`, over the image of `smoothSheafCommRing I 𝓘(ℝ, A) M A` in sheaves of
rings. The real model is essential: bump functions are real-valued, and a complex manifold must
be viewed as a real one for this.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat Limits
open scoped AlgebraicGeometry Manifold ContDiff

universe w' v u

noncomputable section

section NormedAlgebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
  {n : ℕ∞ω}

/-- A normed `𝕜`-algebra is a `C^n` ring for its model `𝓘(𝕜, A)`: multiplication is a bounded
bilinear map. -/
instance NormedAlgebra.contMDiffRing : ContMDiffRing 𝓘(𝕜, A) n A :=
  { instNormedSpaceLieAddGroup with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps, chartAt_self_eq]
      rw [contDiffOn_univ]
      exact contDiff_mul }

end NormedAlgebra

namespace TopCat.Sheaf

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A soft sheaf on a compact Hausdorff space has no higher cohomology.** For a soft abelian
sheaf `F` on a compact Hausdorff space and `n > 0`, `Hⁿ(F) = 0`, in any `Ext` universe. -/
theorem subsingleton_H_of_isSoft {Z : TopCat.{u}} [CompactSpace Z] [T2Space Z]
    [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (hF : Stacks.Topology.IsSoft F)
    (n : ℕ) (hn : 0 < n) : Subsingleton (CategoryTheory.Sheaf.H.{w'} F n) := by
  let _ := HasDerivedCategory.standard
    (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
  let _ := HasDerivedCategory.standard AddCommGrpCat.{u}
  have hac := Stacks.Topology.rightAcyclic_sections_of_isSoft F hF
  have hiff := (Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (Stacks.Topology.sectionsFunctor Z) F).2 inferInstance
  have hzero : IsZero (((Stacks.Topology.sectionsFunctor Z).rightDerived n).obj F) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n F).2
      (hiff.1 hac (n : ℤ) (by exact_mod_cast hn))
  have hH' : IsZero (CategoryTheory.Sheaf.H'.{u, u, u} F n ⊤) :=
    hzero.of_iso (Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections F n ⊤)
  have : Subsingleton (CategoryTheory.Sheaf.H'.{u, u, u} F n ⊤) :=
    AddCommGrpCat.subsingleton_of_isZero hH'
  have : Subsingleton (CategoryTheory.Sheaf.H.{u} F n) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top.{u, u} F n).2 this
  exact (Abelian.Ext.chgUniv.{w', u}).symm.subsingleton

end TopCat.Sheaf

namespace SheafOfModules

section General

variable {Z : TopCat.{u}}

/-- A sheaf of rings `R` on `Z` **has bump sections** if for every closed set `K` contained in an
open set `U` there are a global section `χ`, an open `V` with `K ⊆ V ≤ U` and an open `W` with
`U ⊔ W = ⊤` such that `χ` restricts to `1` on `V` and to `0` on `W`. -/
def HasBumpSections (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{v}) : Prop :=
  ∀ K : Set Z, IsClosed K → ∀ U : Opens Z, K ⊆ (U : Set Z) →
    ∃ (χ : R.obj.obj (op ⊤)) (V W : Opens Z), V ≤ U ∧ K ⊆ (V : Set Z) ∧ U ⊔ W = ⊤ ∧
      R.obj.map (homOfLE (le_top : V ≤ ⊤)).op χ = 1 ∧
      R.obj.map (homOfLE (le_top : W ≤ ⊤)).op χ = 0

/-- **Modules over a sheaf of rings with bump sections are soft.** A section `s` over an open
neighbourhood `U` of a closed set `K` is multiplied by a bump section `χ` that is `1` near `K`
and `0` on an open `W` with `U ⊔ W = ⊤`; `χ • s` and `0` glue to a global section that agrees
with `s` near `K`. -/
theorem isSoft_toSheaf_of_hasBumpSections [UnivLE.{u, v}]
    {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{v}} (hR : HasBumpSections R)
    (F : SheafOfModules.{v} R) :
    Stacks.Topology.IsSoft ((SheafOfModules.toSheaf R).obj F) := by
  intro K hK U hKU s
  obtain ⟨χ, V, W, hVU, hKV, hUW, hχV, hχW⟩ := hR K hK U hKU
  let s₀ : F.val.obj (op U) := s
  let s' : ToType (((SheafOfModules.toSheaf R).obj F).obj.obj (op U)) :=
    (R.obj.map (homOfLE (le_top : U ≤ ⊤)).op χ • s₀ : F.val.obj (op U))
  have hagree : s' |_ (U ⊓ W) =
      (0 : ToType (((SheafOfModules.toSheaf R).obj F).obj.obj (op W))) |_ (U ⊓ W) := by
    delta Presheaf.restrictOpen Presheaf.restrict
    simp only [s']
    change F.val.map (homOfLE inf_le_left).op
      (R.obj.map (homOfLE (le_top : U ≤ ⊤)).op χ • s₀) = _
    change _ = F.val.map (homOfLE inf_le_right).op 0
    rw [map_zero, PresheafOfModules.map_smul]
    have : R.obj.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op
        (R.obj.map (homOfLE (le_top : U ≤ ⊤)).op χ) = 0 := by
      rw [← RingCat.comp_apply, ← Functor.map_comp]
      rw [show (homOfLE (le_top : U ≤ ⊤)).op ≫ (homOfLE (inf_le_left : U ⊓ W ≤ U)).op =
        (homOfLE (le_top : W ≤ ⊤)).op ≫ (homOfLE (inf_le_right : U ⊓ W ≤ W)).op from rfl]
      rw [Functor.map_comp, RingCat.comp_apply, hχW, map_zero]
    rw [this, zero_smul]
    rfl
  obtain ⟨σ, hσU, -⟩ := Stacks.Topology.exists_glue_pair _ _ _ hagree
  refine ⟨σ |_ₗ ⊤ ⟪hUW.ge⟫, V, hVU, hKV, ?_⟩
  have h1 : (σ |_ₗ ⊤ ⟪hUW.ge⟫) |_ V = (σ |_ U) |_ V := by
    rw [Presheaf.restrict_restrict, Presheaf.restrict_restrict]
  rw [h1, hσU]
  change F.val.map (homOfLE hVU).op (R.obj.map (homOfLE (le_top : U ≤ ⊤)).op χ • s₀) =
    F.val.map (homOfLE hVU).op s₀
  rw [PresheafOfModules.map_smul, ← RingCat.comp_apply, ← Functor.map_comp]
  rw [show (homOfLE (le_top : U ≤ ⊤)).op ≫ (homOfLE hVU).op =
    (homOfLE (le_top : V ≤ ⊤)).op from rfl, hχV, one_smul]

/-- **Modules over a sheaf of rings with bump sections have no higher cohomology** on a compact
Hausdorff space: `Hⁿ(Z, F) = 0` for `n > 0`. -/
theorem subsingleton_H_toSheaf_of_hasBumpSections [CompactSpace Z] [T2Space Z]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]
    {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}} (hR : HasBumpSections R)
    (F : SheafOfModules.{u} R) (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{w'} ((SheafOfModules.toSheaf R).obj F) n) :=
  TopCat.Sheaf.subsingleton_H_of_isSoft _ (isSoft_toSheaf_of_hasBumpSections hR F) n hn

end General

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
include I in
/-- A Hausdorff σ-compact manifold over a finite-dimensional real model is normal. -/
theorem _root_.Manifold.normalSpace_of_finiteDimensional [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] : NormalSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **Smooth functions have bump sections.** On a Hausdorff σ-compact finite-dimensional real
manifold, the sheaf of smooth functions with values in a normed `ℝ`-algebra `A` has bump
sections: for closed `K ⊆ U` open, a smooth bump function is `1` on a neighbourhood `V` of `K`
with `closure V ⊆ U'`, `closure U' ⊆ U`, and vanishes off `U'`. -/
theorem hasBumpSections_smoothSheafRing (A : Type u) [NormedRing A] [NormedAlgebra ℝ A] :
    HasBumpSections (smoothSheafRing I 𝓘(ℝ, A) M A) := by
  have : NormalSpace M := Manifold.normalSpace_of_finiteDimensional I M
  intro K hK U hKU
  obtain ⟨V, hVo, hKV, hVU⟩ := normal_exists_closure_subset hK U.isOpen hKU
  obtain ⟨U', hU'o, hVU', hU'U⟩ := normal_exists_closure_subset isClosed_closure U.isOpen hVU
  obtain ⟨f, hf, -, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff I (n := (⊤ : ℕ∞)) hU'o isClosed_closure hVU'
  have hg : ContMDiff I 𝓘(ℝ, A) ∞ (fun x : M => f x • (1 : A)) := hf.smul contMDiff_const
  let χ : C^∞⟮I, ((⊤ : Opens (TopCat.of M)) : Opens M); 𝓘(ℝ, A), A⟯ :=
    ⟨fun x => f x.1 • (1 : A), hg.comp contMDiff_subtype_val⟩
  refine ⟨χ, ⟨V, hVo⟩, ⟨(closure U')ᶜ, isClosed_closure.isOpen_compl⟩,
    fun x hx => hVU (subset_closure hx), hKV, ?_, ?_, ?_⟩
  · refine eq_top_iff.2 fun x _ => ?_
    by_cases hx : x ∈ closure U'
    · exact Or.inl (hU'U hx)
    · exact Or.inr hx
  · apply ContMDiffMap.ext
    intro x
    change f x.1 • (1 : A) = 1
    rw [(hone x.1).1 (subset_closure x.2), one_smul]
  · apply ContMDiffMap.ext
    intro x
    change f x.1 • (1 : A) = 0
    have : f x.1 = 0 := by
      rw [← Function.notMem_support, hsupp]
      exact fun h => x.2 (subset_closure h)
    rw [this, zero_smul]

/-- **Smooth functions have bump sections**, for the sheaf of commutative rings
`smoothSheafCommRing` viewed as a sheaf of rings. -/
theorem hasBumpSections_smoothSheafCommRing (A : Type u) [NormedCommRing A]
    [NormedAlgebra ℝ A] :
    HasBumpSections ((sheafCompose (Opens.grothendieckTopology (TopCat.of M))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (smoothSheafCommRing I 𝓘(ℝ, A) M A)) :=
  hasBumpSections_smoothSheafRing I M A

variable [CompactSpace M]

/-- **Sheaves of modules over the smooth functions on a compact manifold are acyclic.** For a
compact Hausdorff finite-dimensional real `C^∞` manifold `M`, a normed `ℝ`-algebra `A` and a
sheaf `F` of modules over the sheaf of smooth `A`-valued functions, `Hⁿ(M, F) = 0` for `n > 0`. -/
theorem subsingleton_H_toSheaf_smoothSheafRing (A : Type u) [NormedRing A] [NormedAlgebra ℝ A]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} (smoothSheafRing I 𝓘(ℝ, A) M A)) (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{w'} ((SheafOfModules.toSheaf _).obj F) n) :=
  subsingleton_H_toSheaf_of_hasBumpSections (hasBumpSections_smoothSheafRing I M A) F n hn

/-- **Sheaves of modules over the smooth functions on a compact manifold are acyclic**, for the
sheaf of commutative rings `smoothSheafCommRing` (for instance `A = ℝ` or `A = ℂ`). -/
theorem subsingleton_H_toSheaf_smoothSheafCommRing (A : Type u) [NormedCommRing A]
    [NormedAlgebra ℝ A]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology (TopCat.of M))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (smoothSheafCommRing I 𝓘(ℝ, A) M A))) (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{w'} ((SheafOfModules.toSheaf _).obj F) n) :=
  subsingleton_H_toSheaf_of_hasBumpSections (hasBumpSections_smoothSheafCommRing I M A) F n hn

/-- **The sheaf of smooth functions on a compact manifold is acyclic**: the underlying abelian
sheaf of `smoothSheafCommRing I 𝓘(ℝ, A) M A`, as a module over itself, has `Hⁿ = 0` for
`n > 0`. -/
theorem subsingleton_H_smoothSheafCommRing_unit (A : Type u) [NormedCommRing A]
    [NormedAlgebra ℝ A]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{w'} ((SheafOfModules.toSheaf _).obj
      (SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology (TopCat.of M))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (smoothSheafCommRing I 𝓘(ℝ, A) M A)))) n) :=
  subsingleton_H_toSheaf_smoothSheafCommRing I M A _ n hn

end Smooth

end SheafOfModules

end
