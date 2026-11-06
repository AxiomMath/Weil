module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratumPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcAmalgamation
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Constructibility is étale local on reduced irreducible closed subschemes

Let `X` be a scheme whose underlying space is Noetherian and `F` a sheaf of sets on the small
étale site of `X`. Then `F` is constructible if and only if for every reduced irreducible closed
subscheme `Y ⊆ X` there is a nonempty scheme `V` and an étale morphism `V ⟶ Y` such that the
inverse image of `F` along `V ⟶ Y ⟶ X` is constructible on `V`.

One direction is immediate: the inverse image of a constructible sheaf along any morphism is
constructible, so `V = Y` works. For the converse, constructibility of `F` is equivalent to the
existence of finitely many immersions `Yⱼ ⟶ X`, jointly surjective, along which `F` becomes
finite locally constant; we produce such a family by Noetherian induction on closed subsets of
`X`. On an irreducible closed subset `C`, with its reduced induced structure `Y`, choose `V ⟶ Y`
as in the hypothesis and replace `V` by a nonempty affine open of it. The image `W` of `V` in
`Y` is open, `V ⟶ W` is surjective, and both are quasi-compact and quasi-separated, so the
inverse image of `F` to `W` is constructible by descent of constructibility along surjections.
This covers a nonempty relatively open part of `C`, which is what the induction needs.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_iff_forall_exists_etale_isConstructibleSetSheaf`:
  the criterion above.

## Implementation notes

A reduced irreducible closed subscheme of `X` is an object `Y` of the big étale site with a
morphism `Y ⟶ X` which is a closed immersion, `Y` reduced and its underlying space irreducible.

The converse does not pass through the generic-point criterion with finite locally constant
restrictions: it uses descent of constructibility along the surjection from `V` onto its open
image instead (Stacks, Tag 095Q (1)), which makes the purely inseparable comparison between `Y`
and its reduction unnecessary.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

section Topology

variable {α : Type*} [TopologicalSpace α]

/-- In a Noetherian space, a nonempty closed set `Z` contains an irreducible closed set `C`
which contains a nonempty relatively open part of `Z`. -/
theorem exists_isIrreducible_inter_subset_of_isClosed [NoetherianSpace α] {Z : Set α}
    (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ C O : Set α, IsClosed C ∧ IsIrreducible C ∧ C ⊆ Z ∧ IsOpen O ∧ (O ∩ Z).Nonempty ∧
      O ∩ Z ⊆ C := by
  classical
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  obtain ⟨x₀, s₀, hs₀, -⟩ := hne
  obtain ⟨t, ht⟩ := hSf.exists_maximal ⟨s₀, hs₀⟩
  let D : Set α := ⋃₀ {s ∈ S | ¬ t ⊆ s}
  have hDf : {s ∈ S | ¬ t ⊆ s}.Finite := hSf.subset fun s hs => hs.1
  have hD : IsClosed D := hDf.isClosed_sUnion fun s hs => hScl s hs.1
  have hsub : Dᶜ ∩ ⋃₀ S ⊆ t := by
    rintro x ⟨hxD, s, hs, hxs⟩
    by_cases hts : t ⊆ s
    · exact ht.2 hs hts hxs
    · exact absurd ⟨s, ⟨hs, hts⟩, hxs⟩ hxD
  refine ⟨t, Dᶜ, hScl t ht.1, hSirr t ht.1, Set.subset_sUnion_of_mem ht.1, hD.isOpen_compl,
    ?_, hsub⟩
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have htD : t ⊆ ⋃₀ (hDf.toFinset : Set (Set α)) := by
    intro x hx
    rw [Set.Finite.coe_toFinset]
    by_contra hxD
    have : x ∈ Dᶜ ∩ ⋃₀ S := ⟨hxD, t, ht.1, hx⟩
    rw [hempty] at this
    exact this
  obtain ⟨z, hz, htz⟩ := isIrreducible_iff_sUnion_isClosed.mp (hSirr t ht.1) hDf.toFinset
    (fun z hz => hScl z ((Set.Finite.mem_toFinset _).mp hz).1) htD
  exact ((Set.Finite.mem_toFinset _).mp hz).2 htz

/-- The source of an embedding whose image is irreducible is an irreducible space. -/
theorem irreducibleSpace_of_isEmbedding {β : Type*} [TopologicalSpace β] {f : β → α}
    (hf : IsEmbedding f) (h : IsIrreducible (Set.range f)) : IrreducibleSpace β := by
  rw [irreducibleSpace_def]
  obtain ⟨⟨_, ⟨b, rfl⟩⟩, hpre⟩ := h
  refine ⟨⟨b, trivial⟩, ?_⟩
  rintro u v hu hv ⟨x, -, hxu⟩ ⟨y, -, hyv⟩
  obtain ⟨u', hu', rfl⟩ := hf.isInducing.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.isInducing.isOpen_iff.mp hv
  obtain ⟨_, ⟨c, rfl⟩, hcu, hcv⟩ := hpre u' v' hu' hv' ⟨f x, ⟨x, rfl⟩, hxu⟩ ⟨f y, ⟨y, rfl⟩, hyv⟩
  exact ⟨c, trivial, hcu, hcv⟩

end Topology

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- A set `T` of points of `X` is covered by finitely many immersions `Yⱼ ⟶ X` along which the
inverse image of `F` is finite locally constant. -/
private def IsCoveredByFLCImmersions
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) (T : Set X.obj) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (Y : ι → B.Scheme) (j : ∀ k, Y k ⟶ X),
    (∀ k, IsImmersion (B.inclusion.map (j k))) ∧
    (∀ k, SmallEtale.IsFiniteLocallyConstant B (Y k).obj (Y k).property
      ((smallEtaleSetPullback B (j k)).obj F)) ∧
    T ⊆ ⋃ k, Set.range (B.inclusion.map (j k)).base

private theorem IsCoveredByFLCImmersions.mono
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} {S T : Set X.obj}
    (hST : S ⊆ T) (h : IsCoveredByFLCImmersions B X F T) : IsCoveredByFLCImmersions B X F S := by
  obtain ⟨ι, hι, Y, j, hj, hF, hT⟩ := h
  exact ⟨ι, hι, Y, j, hj, hF, hST.trans hT⟩

private theorem isCoveredByFLCImmersions_iUnion
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} {n : ℕ}
    (A : Fin n → Set X.obj) (h : ∀ i, IsCoveredByFLCImmersions B X F (A i)) :
    IsCoveredByFLCImmersions B X F (⋃ i, A i) := by
  choose ι hι Y j hj hF hT using h
  refine ⟨Σ i, ι i, inferInstance, fun k => Y k.1 k.2, fun k => j k.1 k.2, fun k => hj _ _,
    fun k => hF _ _, ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hT i hxi)
  exact Set.mem_iUnion.mpr ⟨⟨i, k⟩, hk⟩

private theorem isConstructibleSetSheaf_of_isCoveredByFLCImmersions_univ [NoetherianSpace X.obj]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (h : IsCoveredByFLCImmersions B X F Set.univ) : IsConstructibleSetSheaf B X F := by
  obtain ⟨ι, hι, Y, j, hj, hF, hT⟩ := h
  let e := Finite.equivFin ι
  refine (isConstructibleSetSheaf_iff_exists_immersion_cover B X F).mpr
    ⟨Nat.card ι, fun k => Y (e.symm k), fun k => j (e.symm k), fun k => hj _,
      (Set.univ_subset_iff.mp ?_).symm, fun k => hF _⟩
  intro x _
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ x))
  obtain ⟨k', rfl⟩ := e.symm.surjective k
  exact Set.mem_iUnion.mpr ⟨k', hk⟩

/-- **Descent to the open image.** Let `i : Y ⟶ X` be a closed immersion and `p : V ⟶ Y` an
étale morphism from a nonempty scheme along which the inverse image of `F` is constructible. Then
a nonempty relatively open part `O ∩ i(Y)` of the image of `i` is covered by finitely many
immersions along which `F` becomes finite locally constant. -/
private theorem exists_isOpen_isCoveredByFLCImmersions_of_isClosedImmersion
    [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (Y : B.Scheme) (i : Y ⟶ X) [hiCl : IsClosedImmersion (B.inclusion.map i)]
    (V : B.Scheme) (p : V ⟶ Y) [hp : Etale (B.inclusion.map p)] (v : V.obj)
    (hG : IsConstructibleSetSheaf B V ((smallEtaleSetPullback B (p ≫ i)).obj F)) :
    ∃ O : Set X.obj, IsOpen O ∧ (O ∩ Set.range (B.inclusion.map i).base).Nonempty ∧
      IsCoveredByFLCImmersions B X F (O ∩ Set.range (B.inclusion.map i).base) := by
  have hemb : IsEmbedding (B.inclusion.map i).base := (B.inclusion.map i).isClosedEmbedding.1
  have : NoetherianSpace (B.inclusion.obj X) := ‹NoetherianSpace X.obj›
  have hYnoeth : NoetherianSpace (B.inclusion.obj Y) := hemb.isInducing.noetherianSpace
  -- A nonempty affine open of `V`.
  obtain ⟨U₀, hU₀, hvU₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.inclusion.obj V)
    (U := ⊤) (x := v) trivial
  let V₀ : B.Scheme := BigEtaleSite.openObj B U₀
  let j : V₀ ⟶ V := BigEtaleSite.openObjι B U₀
  have hj : B.inclusion.map j = U₀.ι := rfl
  let q : V₀ ⟶ Y := j ≫ p
  have hqEt : Etale (B.inclusion.map q) := by
    rw [Functor.map_comp]
    exact (inferInstance : Etale (U₀.ι ≫ B.inclusion.map p))
  -- The open image of `V₀` in `Y`.
  obtain ⟨R, hR⟩ : ∃ R : (B.inclusion.obj Y).Opens,
      (R : Set (B.inclusion.obj Y)) = Set.range (B.inclusion.map q).base :=
    ⟨⟨_, (B.inclusion.map q).isOpenMap.isOpen_range⟩, rfl⟩
  let W : B.Scheme := BigEtaleSite.openObj B R
  let ιW : W ⟶ Y := BigEtaleSite.openObjι B R
  have hιW : B.inclusion.map ιW = R.ι := rfl
  have hιWo : IsOpenImmersion (B.inclusion.map ιW) := (inferInstance : IsOpenImmersion R.ι)
  have hιWrange : Set.range (B.inclusion.map ιW).base = R := by rw [hιW]; exact R.range_ι
  let q' : V₀ ⟶ W := B.inclusion.preimage
    (IsOpenImmersion.lift (B.inclusion.map ιW) (B.inclusion.map q) (by rw [hιWrange, hR]))
  have hq' : q' ≫ ιW = q := B.inclusion.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, IsOpenImmersion.lift_fac])
  have hq'surj : Function.Surjective (B.inclusion.map q').base := by
    intro w
    have hw : (B.inclusion.map ιW).base w ∈ Set.range (B.inclusion.map q).base := by
      have hw' : (B.inclusion.map ιW).base w ∈ Set.range (B.inclusion.map ιW).base := ⟨w, rfl⟩
      rw [hιWrange, hR] at hw'
      exact hw'
    obtain ⟨a, ha⟩ := hw
    refine ⟨a, (B.inclusion.map ιW).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hq', ha]
  -- Constructibility on `V₀` and descent to `W`.
  have hGV₀ : IsConstructibleSetSheaf B V₀
      ((smallEtaleSetPullback B q').obj ((smallEtaleSetPullback B (ιW ≫ i)).obj F)) := by
    have h₁ := isConstructibleFiniteSheaf_pullback B j _ hG
    have e₁ := (smallEtaleSheafPullbackCompIso B V₀ V X j (p ≫ i) (Type (u + 1))).app F
    have e₂ := (smallEtaleSheafPullbackCompIso B V₀ W X q' (ιW ≫ i) (Type (u + 1))).app F
    have heq : q' ≫ ιW ≫ i = j ≫ p ≫ i := by
      rw [← Category.assoc, hq', Category.assoc]
    rw [heq] at e₂
    exact isConstructibleSetSheaf_congr B V₀ (e₁ ≪≫ e₂.symm) h₁
  have hV₀c : CompactSpace V₀.obj := by
    have : IsAffine U₀.toScheme := hU₀
    exact inferInstanceAs (CompactSpace U₀.toScheme)
  have hV₀q : QuasiSeparatedSpace V₀.obj := by
    have : IsAffine U₀.toScheme := hU₀
    exact inferInstanceAs (QuasiSeparatedSpace U₀.toScheme)
  have hWnoeth : NoetherianSpace W.obj :=
    (B.inclusion.map ιW).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hFW : IsConstructibleSetSheaf B W ((smallEtaleSetPullback B (ιW ≫ i)).obj F) :=
    (isConstructibleSetSheaf_pullback_iff_unconditional B q' hq'surj hV₀c hV₀q
      inferInstance inferInstance _).mpr hGV₀
  obtain ⟨n, Yk, jk, hjk, hcov, hFk⟩ :=
    (isConstructibleSetSheaf_iff_exists_immersion_cover B W _).mp hFW
  -- The open set of `X` cutting out the image of `W` in `C`.
  obtain ⟨O, hO, hOpre⟩ := hemb.isInducing.isOpen_iff.mp R.2
  have hOC : O ∩ Set.range (B.inclusion.map i).base = (B.inclusion.map i).base '' R := by
    rw [← Set.image_preimage_eq_inter_range, hOpre]
    rfl
  refine ⟨O, hO, ?_, ?_⟩
  · rw [hOC]
    refine ⟨_, ⟨(B.inclusion.map q).base ⟨v, hvU₀⟩, ?_, rfl⟩⟩
    rw [hR]
    exact ⟨⟨v, hvU₀⟩, rfl⟩
  · refine ⟨Fin n, inferInstance, Yk, fun k => jk k ≫ ιW ≫ i, fun k => ?_, fun k => ?_, ?_⟩
    · have := hjk k
      rw [Functor.map_comp, Functor.map_comp]
      infer_instance
    · exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
        ((smallEtaleSheafPullbackCompIso B (Yk k) W X (jk k) (ιW ≫ i) (Type (u + 1))).app F)
        (hF := hFk k)
    · rw [hOC]
      rintro _ ⟨y, hyR, rfl⟩
      have hyW : y ∈ Set.range (B.inclusion.map ιW).base := by rw [hιWrange]; exact hyR
      obtain ⟨w, rfl⟩ := hyW
      have hw : w ∈ ⋃ k, Set.range (B.inclusion.map (jk k)).base := hcov ▸ Set.mem_univ w
      obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp hw
      refine Set.mem_iUnion.mpr ⟨k, z, ?_⟩
      simp only [Functor.map_comp, Scheme.Hom.comp_apply]

/-- **The irreducible step of the Noetherian induction.** If the criterion holds, then on every
irreducible closed subset `C` of `X` there is a nonempty relatively open part `V ∩ C` covered by
finitely many immersions along which `F` becomes finite locally constant. -/
private theorem exists_isOpen_isCoveredByFLCImmersions_inter [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (H : ∀ (Y : B.Scheme) (i : Y ⟶ X), IsClosedImmersion (B.inclusion.map i) →
        IsReduced (B.inclusion.obj Y) → IrreducibleSpace Y.obj →
        ∃ (V : B.Scheme) (p : V ⟶ Y), Etale (B.inclusion.map p) ∧ Nonempty V.obj ∧
          IsConstructibleSetSheaf B V ((smallEtaleSetPullback B (p ≫ i)).obj F))
    (C : Set X.obj) (hC : IsClosed C) (hCirr : IsIrreducible C) :
    ∃ V : Set X.obj, IsOpen V ∧ (V ∩ C).Nonempty ∧ IsCoveredByFLCImmersions B X F (V ∩ C) := by
  -- The reduced induced closed subscheme on `C`, as an object of the big étale site.
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : Closeds X.obj)
  let Y : B.Scheme := ⟨I.subscheme, Scheme.size_lt_of_mono_of_isStrongPrelimit
    B.cutoff_isStrongPrelimit I.subschemeι X.property⟩
  let i : Y ⟶ X := ObjectProperty.homMk I.subschemeι
  have hi : B.inclusion.map i = I.subschemeι := rfl
  have hrange : Set.range (B.inclusion.map i).base = C := by
    rw [hi, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hiCl : IsClosedImmersion (B.inclusion.map i) := by rw [hi]; infer_instance
  have hemb : IsEmbedding (B.inclusion.map i).base := (B.inclusion.map i).isClosedEmbedding.1
  have hYred : IsReduced (B.inclusion.obj Y) :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hYirr : IrreducibleSpace Y.obj :=
    irreducibleSpace_of_isEmbedding hemb (hrange ▸ hCirr)
  obtain ⟨V, p, hp, ⟨v⟩, hG⟩ := H Y i hiCl hYred hYirr
  obtain ⟨O, hO, hne, hP⟩ :=
    exists_isOpen_isCoveredByFLCImmersions_of_isClosedImmersion B X F Y i V p v hG
  rw [hrange] at hne hP
  exact ⟨O, hO, hne, hP⟩

/-- **Constructibility is étale local on reduced irreducible closed subschemes.** On a scheme `X`
whose underlying space is Noetherian, a sheaf of sets `F` on the small étale site of `X` is
constructible if and only if for every reduced irreducible closed subscheme `i : Y ⟶ X` there is a
nonempty scheme `V` with an étale morphism `p : V ⟶ Y` such that the inverse image of `F` along
`p ≫ i` is constructible on `V`. -/
@[weil "lem_fk104_constructible_iff_etale_locally_constructible_on_closed"]
theorem isConstructibleSetSheaf_iff_forall_exists_etale_isConstructibleSetSheaf
    [NoetherianSpace X.obj] (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∀ (Y : B.Scheme) (i : Y ⟶ X), IsClosedImmersion (B.inclusion.map i) →
        IsReduced (B.inclusion.obj Y) → IrreducibleSpace Y.obj →
        ∃ (V : B.Scheme) (p : V ⟶ Y), Etale (B.inclusion.map p) ∧ Nonempty V.obj ∧
          IsConstructibleSetSheaf B V ((smallEtaleSetPullback B (p ≫ i)).obj F) := by
  constructor
  · intro hF Y i _ _ _
    refine ⟨Y, 𝟙 Y, by rw [CategoryTheory.Functor.map_id]; infer_instance, inferInstance, ?_⟩
    exact isConstructibleFiniteSheaf_pullback B (𝟙 Y ≫ i) F hF
  · intro H
    obtain ⟨n, A, -, -, hPA, -, hcov⟩ :=
      exists_locallyClosed_partition_of_noetherianSpace (Set.univ : Set X.obj) isOpen_univ
        (IsCoveredByFLCImmersions B X F) (fun Z hZ hne => by
          rw [Set.univ_inter] at hne
          simp only [Set.inter_univ]
          obtain ⟨C, O, hC, hCirr, hCZ, hO, hOZ, hOZC⟩ :=
            exists_isIrreducible_inter_subset_of_isClosed hZ hne
          obtain ⟨V, hV, hVC, hP⟩ :=
            exists_isOpen_isCoveredByFLCImmersions_inter B X F H C hC hCirr
          obtain ⟨x, hxO, hxZ⟩ := hOZ
          obtain ⟨y, hyC, hyV, hyO⟩ := hCirr.2 V O hV hO (by simpa [Set.inter_comm] using hVC)
            ⟨x, hOZC ⟨hxO, hxZ⟩, hxO⟩
          refine ⟨V ∩ O, hV.inter hO, ⟨y, ⟨hyV, hyO⟩, hCZ hyC⟩, ?_⟩
          refine IsCoveredByFLCImmersions.mono B X ?_ hP
          exact fun z hz => ⟨hz.1.1, hOZC ⟨hz.1.2, hz.2⟩⟩)
    refine isConstructibleSetSheaf_of_isCoveredByFLCImmersions_univ B X ?_
    rw [hcov]
    exact isCoveredByFLCImmersions_iUnion B X A hPA

end AlgebraicGeometry

end
