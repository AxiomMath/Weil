module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import WeilFrontier.AlgebraicGeometry.Scheme.Reduction
public import WeilFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmoothIrreducibleStratification

/-!
# Constructibility is finite local constancy on a dense open of every closed subscheme

Let `X` be a scheme whose underlying space is Noetherian. A sheaf of sets `F` on the small étale
site of `X` is constructible if and only if every nonempty closed subscheme `Y ⊆ X` contains a
nonempty open subscheme `U ⊆ Y` such that the restriction `F|_U` is finite locally constant.

If `F` is constructible, with `|X| = |Y₁| ∪ ⋯ ∪ |Yᵣ|` and every `F|_{Yⱼ}` finite locally constant,
and `Y ⊆ X` is a nonempty closed subscheme, then some nonempty open part `U` of `Y` has `|U|`
inside one `|Yⱼ|`. The reduction `U_red` then factors through the immersion `Yⱼ ⟶ X`, so
`F|_{U_red}` is an inverse image of `F|_{Yⱼ}` and is finite locally constant; since
`U_red ⟶ U` is purely inseparable, `F|_U` is finite locally constant.

Conversely, starting from `X` and repeatedly removing from a closed set `Z` (with its reduced
closed subscheme structure) a nonempty open part on which `F` is finite locally constant, one
obtains, by Noetherian induction, finitely many locally closed subschemes covering `X` on which
`F` is finite locally constant.

## Main results

* `AlgebraicGeometry.Scheme.exists_comp_eq_of_isImmersion_of_range_subset`: a morphism from a
  reduced scheme whose image lies in the image of an immersion factors through it.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_of_range_subset_range`: if `F|_Y` is
  finite locally constant for an immersion `Y ⟶ X`, then so is `F|_U` for every morphism
  `U ⟶ X` with image in that of `Y`.
* `AlgebraicGeometry.isConstructibleSetSheaf_iff_forall_isClosedImmersion`: the
  characterization of constructible sheaves of sets.

## Implementation notes

A closed subscheme `Y ⊆ X` is an object `Y` of the big étale site with a morphism `Y ⟶ X` which
is a closed immersion, and an open subscheme `U ⊆ Y` an object `U` with an open immersion
`U ⟶ Y`; the restriction `F|_U` is the inverse image along the composite `U ⟶ Y ⟶ X`. Every
closed set of `X` is the image of a closed subscheme of `X` in the site (its reduced closed
subscheme structure), since the site contains every scheme with a closed immersion into `X`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Factoring a morphism from a reduced scheme through an immersion.** Let `g : Y ⟶ X` be an
immersion and `f : Z ⟶ X` a morphism from a reduced scheme whose image lies in the image of `g`.
Then `f` factors through `g`. -/
theorem Scheme.exists_comp_eq_of_isImmersion_of_range_subset {Z X Y : Scheme.{u}} [IsReduced Z]
    (f : Z ⟶ X) (g : Y ⟶ X) [IsImmersion g] (h : Set.range f ⊆ Set.range g) :
    ∃ a : Z ⟶ Y, a ≫ g = f := by
  have hsurj : Surjective (pullback.fst f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.preimage_eq_univ_iff]
    exact h⟩
  have : IsClosedImmersion (pullback.fst f g) :=
    IsClosedImmersion.of_isPreimmersion _ <| by
      rw [Set.range_eq_univ.mpr hsurj.surj]
      exact isClosed_univ
  have : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst f g) ≫ pullback.snd f g, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

namespace SmallEtale

variable (B : BigEtaleSite.{u})

/-- **Finite local constancy passes to morphisms with image inside an immersion.** Let
`j : Y ⟶ X` be an immersion and `F` a sheaf of sets on the small étale site of `X` whose
restriction `F|_Y` is finite locally constant. Then for every morphism `k : U ⟶ X` whose image
lies in the image of `j`, the restriction `F|_U` is finite locally constant. -/
theorem isFiniteLocallyConstant_of_range_subset_range {X Y U : B.Scheme} (j : Y ⟶ X)
    [IsImmersion (B.inclusion.map j)] (k : U ⟶ X)
    (hk : Set.range (B.inclusion.map k) ⊆ Set.range (B.inclusion.map j))
    (F : Sheaf (topology B X.obj X.property) (Type (u + 1)))
    (hF : IsFiniteLocallyConstant B Y.obj Y.property ((smallEtaleSetPullback B j).obj F)) :
    IsFiniteLocallyConstant B U.obj U.property ((smallEtaleSetPullback B k).obj F) := by
  let R : B.Scheme := B.obj U.obj.reduction
    (Scheme.size_lt_of_isClosedImmersion U.obj.reductionι U.property)
  let r : R ⟶ U := ObjectProperty.homMk U.obj.reductionι
  have hR : IsReduced (B.inclusion.obj R) := inferInstanceAs (IsReduced U.obj.reduction)
  obtain ⟨a, ha⟩ := Scheme.exists_comp_eq_of_isImmersion_of_range_subset
    (B.inclusion.map (r ≫ k)) (B.inclusion.map j) <| by
      rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact (Set.image_subset_range _ _).trans hk
  let a' : R ⟶ Y := ObjectProperty.homMk a
  have ha' : a' ≫ j = r ≫ k := B.inclusion.map_injective (by rw [Functor.map_comp]; exact ha)
  have h1 : IsFiniteLocallyConstant B R.obj R.property
      ((smallEtaleInverseImage B (a' ≫ j) (Type (u + 1))).obj F) :=
    (isFiniteLocallyConstant_iff_of_iso
      ((smallEtaleInverseImageCompObjIso B a' j (Type (u + 1)) F))).mpr
      (isFiniteLocallyConstant_smallEtaleInverseImage B a' _ hF)
  rw [ha'] at h1
  have h2 : IsFiniteLocallyConstant B R.obj R.property
      ((smallEtaleInverseImage B r (Type (u + 1))).obj
        ((smallEtaleInverseImage B k (Type (u + 1))).obj F)) :=
    (isFiniteLocallyConstant_iff_of_iso
      ((smallEtaleInverseImageCompObjIso B r k (Type (u + 1)) F))).mp h1
  exact (isFiniteLocallyConstant_iff_smallEtaleInverseImage_of_isPurelyInseparable r
    (Scheme.isPurelyInseparable_reductionι U.obj) _).mpr h2

end SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Constructible sheaves are generically finite locally constant on closed subschemes.** On a
scheme `X` whose underlying space is Noetherian, a sheaf of sets `F` on the small étale site of
`X` is constructible if and only if for every nonempty closed subscheme `i : Y ⟶ X` there is a
nonempty open subscheme `j : U ⟶ Y` such that the restriction `F|_U` (the inverse image along
`U ⟶ Y ⟶ X`) is finite locally constant. -/
@[weil "lem_fk104_constructible_iff_open_dense_flc_on_closed"]
theorem isConstructibleSetSheaf_iff_forall_isClosedImmersion [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∀ (Y : B.Scheme) (i : Y ⟶ X), IsClosedImmersion (B.inclusion.map i) → Nonempty Y.obj →
        ∃ (U : B.Scheme) (j : U ⟶ Y), IsOpenImmersion (B.inclusion.map j) ∧ Nonempty U.obj ∧
          SmallEtale.IsFiniteLocallyConstant B U.obj U.property
            ((smallEtaleSetPullback B (j ≫ i)).obj F) := by
  have : NoetherianSpace (B.inclusion.obj X) := ‹NoetherianSpace X.obj›
  rw [isConstructibleSetSheaf_iff_exists_immersion_cover]
  constructor
  · rintro ⟨n, Yc, jc, hjc, hcov, hF⟩ Y i hi ⟨y⟩
    have hZ : IsClosed (Set.range (B.inclusion.map i)) :=
      (B.inclusion.map i).isClosedEmbedding.isClosed_range
    obtain ⟨V, hV, hirr, m, hsub⟩ := exists_isOpen_isIrreducible_inter_subset
      (fun m => Set.range (B.inclusion.map (jc m)))
      (fun m => (hjc m).isLocallyClosed_range) hcov.symm hZ ⟨_, y, rfl⟩
    let O : Y.obj.Opens := (B.inclusion.map i) ⁻¹ᵁ ⟨V, hV⟩
    let U : B.Scheme := B.obj O.toScheme (Scheme.size_lt_of_isOpenImmersion O.ι Y.property)
    let o : U ⟶ Y := ObjectProperty.homMk O.ι
    have hrange : Set.range (B.inclusion.map (o ≫ i)) ⊆ V ∩ Set.range (B.inclusion.map i) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.2, _, rfl⟩
    refine ⟨U, o, inferInstanceAs (IsOpenImmersion O.ι), ?_, ?_⟩
    · obtain ⟨_, hxV, x, rfl⟩ := hirr.nonempty
      exact ⟨⟨x, hxV⟩⟩
    · have := hjc m
      exact SmallEtale.isFiniteLocallyConstant_of_range_subset_range B (jc m) (o ≫ i)
        (hrange.trans hsub) F (hF m)
  · intro H
    obtain ⟨n, Yf, h0, hn, -, -, hstr⟩ := exists_closed_filtration_of_noetherianSpace
      (fun T : Set X.obj => ∃ (U : B.Scheme) (k : U ⟶ X), IsImmersion (B.inclusion.map k) ∧
        Set.range (B.inclusion.map k) = T ∧
        SmallEtale.IsFiniteLocallyConstant B U.obj U.property ((smallEtaleSetPullback B k).obj F))
      (by
        intro Z hZ hne
        let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : Closeds X.obj)
        let Y : B.Scheme := B.obj I.subscheme
          (Scheme.size_lt_of_isClosedImmersion I.subschemeι X.property)
        let i : Y ⟶ X := ObjectProperty.homMk I.subschemeι
        have : IsClosedImmersion (B.inclusion.map i) :=
          inferInstanceAs (IsClosedImmersion I.subschemeι)
        have hYZ : Set.range (B.inclusion.map i) = Z := by
          change Set.range I.subschemeι = Z
          rw [Scheme.IdealSheafData.range_subschemeι,
            Scheme.IdealSheafData.coe_support_vanishingIdeal]
          rfl
        have hYne : Nonempty Y.obj := by
          obtain ⟨z, hz⟩ := hne
          rw [← hYZ] at hz
          obtain ⟨y, -⟩ := hz
          exact ⟨y⟩
        obtain ⟨U, j, hj, hUne, hflc⟩ := H Y i (inferInstanceAs (IsClosedImmersion I.subschemeι))
          hYne
        obtain ⟨V, hV, hVeq⟩ := (B.inclusion.map i).isClosedEmbedding.isInducing.isOpen_iff.mp
          (B.inclusion.map j).isOpenEmbedding.isOpen_range
        have hVZ : V ∩ Z = Set.range (B.inclusion.map (j ≫ i)) := by
          rw [← hYZ, Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
            ← hVeq, Set.image_preimage_eq_inter_range]
        refine ⟨V, hV, ?_, U, j ≫ i, ?_, hVZ.symm, hflc⟩
        · obtain ⟨u⟩ := hUne
          rw [hVZ]
          exact ⟨_, u, rfl⟩
        · rw [Functor.map_comp]
          infer_instance)
    choose U k hk hrange hflc using fun t : Fin n => (hstr t t.2).2
    refine ⟨n, U, k, hk, ?_, hflc⟩
    symm
    rw [Set.eq_univ_iff_forall]
    intro x
    have hex : ∃ t, x ∉ Yf t := ⟨n, by rw [hn n le_rfl]; exact Set.notMem_empty x⟩
    classical
    have hm0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, h0] at this
      exact this (Set.mem_univ x)
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have htn : t < n := by
      have : Nat.find hex ≤ n := Nat.find_min' hex (by rw [hn n le_rfl]; exact Set.notMem_empty x)
      omega
    refine Set.mem_iUnion.mpr ⟨⟨t, htn⟩, ?_⟩
    rw [hrange]
    refine ⟨?_, ?_⟩
    · by_contra hxt
      exact Nat.find_min hex (by omega : t < Nat.find hex) hxt
    · have := Nat.find_spec hex
      rwa [ht] at this

end AlgebraicGeometry
