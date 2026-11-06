module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.EuclideanEmbedding
public import WeilFrontier.Topology.Sheaves.Cohomology.FiniteAcyclicCover
public import WeilFrontier.Topology.Sheaves.Cohomology.HomotopyInvariance
public import WeilFrontier.Topology.Sheaves.Cohomology.OpenSubspace

/-!
# Finite generation of the integral cohomology of `Y(ℂ)`

Let `Y` be a smooth projective scheme over `ℂ`. Its complex points `Y(ℂ)`, with the analytic
topology, are homeomorphic to a compact subset `K` of a Euclidean space `ℝᴹ` which is a retract
of an open neighbourhood `T ⊇ K`. This file deduces that every sheaf cohomology group
`Hᵛ(Y(ℂ), ℤ)` of the constant sheaf `ℤ` is a finitely generated abelian group.

The argument is elementary. By compactness, `K` is covered by finitely many open balls contained
in `T`; let `W` be their union. Every finite intersection of balls is convex, hence empty or
contractible, so it has no cohomology in positive degrees, and its sections of a constant sheaf
`A` are `A` (or `0`). The cover of `W` by the balls therefore computes `Hⁿ(W, A)` through a
finite Čech complex of finitely generated groups (Leray's theorem). Finally `K ⊆ W` and the
retraction `T → K` restricts to `W → K`, so `Hⁿ(K, A)` is a direct summand of `Hⁿ(W, A)`.

## Main results

* `TopCat.SheafCohomology.moduleFinite_sheafH_iUnion_of_convex`: a finite union of open convex
  subsets of a real normed space has finitely generated cohomology with coefficients in a
  finitely generated abelian group.
* `TopCat.SheafCohomology.moduleFinite_sheafH_of_isCompact_of_retraction`: the same for a
  compact subset that is a retract of an open neighbourhood.
* `AlgebraicGeometry.Scheme.integralCohomologyFG_of_smooth_of_isProjective`: `Hᵛ(Y(ℂ), ℤ)` is
  finitely generated for `Y` smooth projective over `ℂ`.
* `AlgebraicGeometry.Scheme.integralCohomologyFGOfProjective`: the proposition
  `AlgebraicGeometry.Scheme.IntegralCohomologyFGOfProjective`.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H` on the site of opens, with coefficients in
`AddCommGrpCat.{0}`. Open balls replace the cubes of a cubical cover: all that is used is that
finite intersections of the members are convex. No triangulation of `Y(ℂ)` and no comparison with
singular cohomology is needed.

## References

* [Hatcher] A. Hatcher, *Algebraic Topology*, Appendix (Euclidean neighbourhood retracts).
* [Bredon] G. Bredon, *Sheaf Theory*, Chapter III.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Metric

namespace TopCat.SheafCohomology

/-- Every sheaf cohomology group of an empty space vanishes. -/
theorem subsingleton_sheafH_of_isEmpty (X : TopCat.{0}) [IsEmpty X]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F n) := by
  refine Opens.CechAcyclic.subsingleton_sheafH_of_iInf_eq_bot (ι := PEmpty.{1})
    (fun i ↦ i.elim) F ?_ (fun s hs ↦ ?_) 0 (fun s _ ↦ ?_) (Nat.zero_le n)
  · ext x; exact isEmptyElim x
  · obtain ⟨i, _⟩ := hs; exact i.elim
  · ext x; exact isEmptyElim x


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex subset of a real normed space, empty or not, has no cohomology in positive degrees
with constant coefficients. -/
theorem subsingleton_H_of_convex' {s : Set E} (hs : Convex ℝ s) (A : AddCommGrpCat.{0}) (n : ℕ)
    (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of s)) AddCommGrpCat.{0}).obj A) n) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have : IsEmpty (TopCat.of (∅ : Set E)) := Set.isEmpty_coe_sort.2 rfl
    exact subsingleton_sheafH_of_isEmpty _ _ n
  · exact subsingleton_H_of_convex A hs hne n hn

/-- **A finite union of open convex sets has finitely generated cohomology.** If `V : ι → Set E`
is a finite family of open convex subsets of a real normed space and `A` is a finitely generated
abelian group, then every `Hⁿ(⋃ i, V i, A)` is finitely generated: the cover by the `V i` has
convex, hence acyclic, finite intersections, so it computes the cohomology through a finite Čech
complex. -/
theorem moduleFinite_sheafH_iUnion_of_convex {ι : Type} [Finite ι] (V : ι → Set E)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (V i)) (A : AddCommGrpCat.{0})
    [Module.Finite ℤ A] (n : ℕ) :
    Module.Finite ℤ (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of (⋃ i, V i))) AddCommGrpCat.{0}).obj
        A) n) := by
  set W := ⋃ i, V i
  let X := TopCat.of W
  let U : ι → Opens X := fun i ↦ ⟨Subtype.val ⁻¹' V i, (hV i).preimage continuous_subtype_val⟩
  have hU : ⨆ i, U i = ⊤ := by
    ext x
    simp only [Opens.coe_iSup, Opens.coe_top, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.2
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  -- the intersection of the members indexed by `s` is the preimage of `⋂ i ∈ s, V i`
  have hcoe : ∀ s : Finset ι, ((⨅ i ∈ s, U i : Opens X) : Set X) =
      Subtype.val ⁻¹' ⋂ i ∈ s, V i := by
    intro s
    let V' : Opens X := ⟨Subtype.val ⁻¹' ⋂ i ∈ s, V i,
      (isOpen_biInter_finset fun i _ ↦ hV i).preimage continuous_subtype_val⟩
    have h₁ : V' ≤ ⨅ i ∈ s, U i := le_iInf₂ fun i hi x hx ↦
      Set.mem_iInter₂.1 (show x.1 ∈ ⋂ j ∈ s, V j from hx) i hi
    have h₂ : ⨅ i ∈ s, U i ≤ V' := fun x hx ↦
      show x.1 ∈ ⋂ j ∈ s, V j from Set.mem_iInter₂.2 fun i hi ↦
        show x.1 ∈ V i from (iInf₂_le i hi : (⨅ j ∈ s, U j) ≤ U i) hx
    exact congrArg (fun O : Opens X ↦ (O : Set X)) (le_antisymm h₂ h₁)
  have hsub : ∀ s : Finset ι, s.Nonempty → ⋂ i ∈ s, V i ⊆ W := by
    rintro s ⟨i, hi⟩ x hx
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iInter₂.1 hx i hi⟩
  have hconv : ∀ s : Finset ι, Convex ℝ (⋂ i ∈ s, V i) := fun s ↦
    convex_iInter₂ fun i _ ↦ hc i
  have homeo : ∀ s : Finset ι, s.Nonempty →
      (↥(⨅ i ∈ s, U i : Opens X) ≃ₜ ↥(⋂ i ∈ s, V i)) := by
    intro s hs
    have hemb : Topology.IsEmbedding (fun v : ↥(⨅ i ∈ s, U i : Opens X) ↦ (v.1.1 : E)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    refine hemb.toHomeomorph.trans (Homeomorph.setCongr ?_)
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      have hv : v.1 ∈ ((⨅ i ∈ s, U i : Opens X) : Set X) := v.2
      rw [hcoe s] at hv
      exact hv
    · intro hz
      have hz' : (⟨z, hsub s hs hz⟩ : W) ∈ ((⨅ i ∈ s, U i : Opens X) : Set X) := by
        rw [hcoe s]; exact hz
      exact ⟨⟨⟨z, hsub s hs hz⟩, hz'⟩, rfl⟩
  refine Opens.CechAcyclic.finite_sheafH U _ hU (fun s hs q hq ↦ ?_) (fun s hs ↦ ?_) n
  · refine (subsingleton_H'_constantSheaf_iff (⨅ i ∈ s, U i) A q).2 ?_
    have h := subsingleton_H_of_convex' (hconv s) A q hq
    exact (constantCohomologyPullback_bijective_of_iso
      (TopCat.isoOfHomeo (X := TopCat.of ↥(⨅ i ∈ s, U i : Opens X))
        (Y := TopCat.of ↥(⋂ i ∈ s, V i)) (homeo s hs)) A q).2.subsingleton
  · rcases (⋂ i ∈ s, V i).eq_empty_or_nonempty with he | hne
    · have hbot : (⨅ i ∈ s, U i : Opens X) = ⊥ := by
        ext x
        rw [hcoe s, he]
        simp
      rw [hbot]
      have := Opens.CechAcyclic.subsingleton_obj_bot
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj A)
      exact Module.Finite.of_finite
    · have : ConnectedSpace ↥(⋂ i ∈ s, V i) :=
        isConnected_iff_connectedSpace.1 ((hconv s).isConnected hne)
      have hconn : IsConnected ((⨅ i ∈ s, U i : Opens X) : Set X) :=
        isConnected_iff_connectedSpace.2
          ((homeo s hs).symm.surjective.connectedSpace (homeo s hs).symm.continuous)
      have : Module.Finite ℤ ((WeilFrontier.ConstantSheafSections.constPresheaf (X := X) A).obj
          (op (⨅ i ∈ s, U i))) := ‹Module.Finite ℤ A›
      exact Module.Finite.of_surjective
        ((WeilFrontier.ConstantSheafSections.toConst (X := X) A).app _).hom.toIntLinearMap
        (WeilFrontier.ConstantSheafSections.constSection_bijective A hconn).2


/-- **A compact neighbourhood retract in a real normed space has finitely generated
cohomology.** Let `K ⊆ E` be compact and a retract of an open `T ⊇ K`. Then for every finitely
generated abelian group `A`, every `Hⁿ(K, A)` is finitely generated. Finitely many open balls
contained in `T` cover `K`; their union `W` has finitely generated cohomology
(`moduleFinite_sheafH_iUnion_of_convex`), and `K` is a retract of `W`. -/
theorem moduleFinite_sheafH_of_isCompact_of_retraction {K T : Set E} (hK : IsCompact K)
    (hT : IsOpen T) (hKT : K ⊆ T) (r : C(T, K)) (hr : ∀ x : K, r (Set.inclusion hKT x) = x)
    (A : AddCommGrpCat.{0}) [Module.Finite ℤ A] (n : ℕ) :
    Module.Finite ℤ (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of K)) AddCommGrpCat.{0}).obj A) n) := by
  have hball : ∀ x ∈ T, ∃ ε > 0, Metric.ball x ε ⊆ T := Metric.isOpen_iff.1 hT
  choose! ε hε hεT using hball
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.ball x (ε x))
    (fun x hx ↦ ball_mem_nhds x (hε x (hKT hx)))
  let V : t → Set E := fun i ↦ Metric.ball (i : E) (ε i)
  have hWT : ⋃ i, V i ⊆ T := Set.iUnion_subset fun i ↦ hεT i (hKT (htK i i.2))
  have hKW : K ⊆ ⋃ i, V i := fun x hx ↦ by
    obtain ⟨i, hi, hx'⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hx'⟩
  have := moduleFinite_sheafH_iUnion_of_convex V (fun _ ↦ isOpen_ball) (fun _ ↦ convex_ball _ _)
    A n
  let i : TopCat.of K ⟶ TopCat.of (⋃ i, V i) :=
    TopCat.ofHom ⟨Set.inclusion hKW, continuous_inclusion hKW⟩
  let ρ : TopCat.of (⋃ i, V i) ⟶ TopCat.of K :=
    TopCat.ofHom (r.comp ⟨Set.inclusion hWT, continuous_inclusion hWT⟩)
  have hiρ : i ≫ ρ = 𝟙 _ := by
    ext x
    exact congrArg Subtype.val (hr x)
  exact moduleFinite_of_retract i ρ hiρ A n

end TopCat.SheafCohomology

namespace AlgebraicGeometry.Scheme

/-- **The integral cohomology of the complex points of a smooth projective scheme over `ℂ` is
finitely generated** in every degree. `Y(ℂ)` is homeomorphic to a compact neighbourhood retract
in a Euclidean space. -/
theorem integralCohomologyFG_of_smooth_of_isProjective {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}
    (hs : Smooth y) (hy : IsProjective y) : IntegralCohomologyFG y := by
  intro ν
  obtain ⟨M, K, hK, hloc, ⟨e⟩⟩ := ComplexPoints.exists_homeomorph_isCompact_regularZeroSet hy
  obtain ⟨T, hT, hKT, r, hr⟩ := hK.exists_isOpen_retraction_of_regularZeroSet hloc
  have : Module.Finite ℤ (AddCommGrpCat.of ℤ) :=
    Module.Finite.iff_addGroup_fg.2 (inferInstanceAs (AddGroup.FG ℤ))
  have hKfg := TopCat.SheafCohomology.moduleFinite_sheafH_of_isCompact_of_retraction hK hT hKT r
    hr (AddCommGrpCat.of ℤ) ν
  have hb := TopCat.SheafCohomology.constantCohomologyPullback_bijective_of_iso
    (TopCat.isoOfHomeo (X := TopCat.of (ComplexPoints y)) (Y := TopCat.of K) e)
    (AddCommGrpCat.of ℤ) ν
  have hfin := Module.Finite.of_surjective
    (TopCat.SheafCohomology.constantCohomologyPullback _ (AddCommGrpCat.of ℤ) ν).toIntLinearMap
    hb.2
  exact Module.Finite.iff_addGroup_fg.1 hfin

/-- **Finiteness of integral cohomology** for smooth projective schemes over `ℂ`: the named
input `IntegralCohomologyFGOfProjective` holds. -/
theorem integralCohomologyFGOfProjective : IntegralCohomologyFGOfProjective :=
  fun _ _ hs hy ↦ integralCohomologyFG_of_smooth_of_isProjective hs hy

end AlgebraicGeometry.Scheme
