module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import Weil.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import Weil.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Constructibility via étale neighbourhoods of generic points

Let `X` be a scheme whose underlying space is Noetherian and `F` a sheaf of sets on the small
étale site of `X`. Then `F` is constructible if and only if for every irreducible closed
subscheme `Y ⊆ X`, with generic point `η_Y`, there is an étale morphism `p : U ⟶ Y` with
`η_Y ∈ p(U)` such that the inverse image of `F` along `U ⟶ Y ⟶ X` is finite locally constant.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_of_smallEtaleInverseImage`: finite local
  constancy descends along a surjective étale morphism.
* `AlgebraicGeometry.isConstructibleSetSheaf_iff_forall_exists_etale_isFiniteLocallyConstant`:
  the criterion above; its two implications are
  `AlgebraicGeometry.exists_etale_isFiniteLocallyConstant_of_isConstructibleSetSheaf` and
  `AlgebraicGeometry.isConstructibleSetSheaf_of_forall_exists_etale_isFiniteLocallyConstant`.

## Implementation notes

A closed subscheme `Y ⊆ X` is an object `Y` of the big étale site with a closed immersion
`Y ⟶ X`; the étale `Y`-scheme `U` is an object of the big étale site as well, since sheaves on
the small étale sites are only evaluated on such objects. This is no restriction: an étale
neighbourhood of `η_Y` can always be shrunk to an affine one, which lies below the size cutoff.

The forward implication restricts `F` to a nonempty open subscheme `W` of `Y` which lies in the
image of one stratum `Yᵢ ⟶ X` of a finite cover of `X` by locally closed subschemes on which `F`
is finite locally constant; the base change `Yᵢ ×_X W ⟶ W` is a surjective closed immersion,
hence purely inseparable, and finite local constancy passes along it.

The converse is a Noetherian induction on the closed subsets `Z` of `X`. For the generic point
`η` of an irreducible component `C` of `Z`, apply the hypothesis to `C` with its reduced
closed subscheme structure: the open image `V = p(U)` of the étale neighbourhood is a locally
closed subscheme of `X` on which `F` is finite locally constant, by descent along the surjective
étale morphism `U ⟶ V`, and `V` contains a nonempty open subset of `Z`. This produces the finite
cover by locally closed subschemes directly, without passing through the criterion by nonempty
open subschemes of all closed subschemes.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

/- FK proves the converse through the characterization of constructible sheaves by an open dense
subset on which they are finite locally constant; the Noetherian induction is done here directly on
the immersion-cover form of constructibility, which makes the reduction step (FK's `V₁ = (V_Y)_red`)
unnecessary. -/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}}

namespace SmallEtale

/-- **Finite local constancy descends along surjective étale morphisms.** Let `p : U ⟶ T` be a
surjective étale morphism and `F` a sheaf of sets on the small étale site of `T`. If `p^* F` is
finite locally constant, then so is `F`. -/
theorem isFiniteLocallyConstant_of_smallEtaleInverseImage {T U : B.Scheme} (p : U ⟶ T)
    [Etale (B.inclusion.map p)] (hp : Function.Surjective (B.inclusion.map p))
    (F : Sheaf (topology B T.obj T.property) (Type (u + 1)))
    (hF : IsFiniteLocallyConstant B U.obj U.property
      ((smallEtaleInverseImage B p (Type (u + 1))).obj F)) :
    IsFiniteLocallyConstant B T.obj T.property F := by
  obtain ⟨I, W, hW, hc⟩ := (isFiniteLocallyConstant_iff_exists_cover _).mp hF
  rw [isFiniteLocallyConstant_iff_exists_cover]
  let W' : I → SmallEtale B T.obj T.property := fun i =>
    ⟨Over.mk ((W i).obj.hom ≫ p), by
      have : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
      change Etale (B.inclusion.map ((W i).obj.hom ≫ p))
      rw [Functor.map_comp]
      infer_instance⟩
  refine ⟨I, W', fun x => ?_, fun i => ?_⟩
  · obtain ⟨y, rfl⟩ := hp x
    obtain ⟨i, z, hz⟩ := hW y
    refine ⟨i, z, ?_⟩
    change (B.inclusion.map ((W i).obj.hom ≫ p)) z = _
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]
  · obtain ⟨M, hM, ⟨e⟩⟩ := hc i
    refine ⟨M, hM, ?_⟩
    obtain ⟨e'⟩ := (nonempty_constantSheafIso_over_iff B U.obj U.property (W i) _ _ M).mp ⟨e⟩
    exact (nonempty_constantSheafIso_over_iff B T.obj T.property (W' i) _ F M).mpr
      ⟨e' ≪≫ (smallEtaleInverseImageCompObjIso B (W i).obj.hom p _ F).symm⟩

end SmallEtale

/-- An immersion into a scheme of a big étale site has its source in the site. -/
theorem BigEtaleSite.contains_of_isImmersion {T Y : _root_.AlgebraicGeometry.Scheme.{u}}
    (hY : B.Contains Y) (f : T ⟶ Y) [IsImmersion f] : B.Contains T :=
  Scheme.size_lt_of_isClosedImmersion f.liftCoborder
    (Scheme.size_lt_of_isOpenImmersion f.coborderRange.ι hY)

/-- A space admitting an inducing map onto an irreducible subset is irreducible. -/
theorem irreducibleSpace_of_isInducing {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → Z} (hf : IsInducing f) (h : IsIrreducible (Set.range f)) : IrreducibleSpace Y := by
  rw [irreducibleSpace_def]
  refine ⟨?_, ?_⟩
  · obtain ⟨-, ⟨x, rfl⟩⟩ := h.nonempty
    exact ⟨x, trivial⟩
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.mp hv
  obtain ⟨-, ⟨w, rfl⟩, hwu, hwv⟩ := h.2 u' v' hu' hv' ⟨f x, ⟨x, rfl⟩, hx⟩ ⟨f y, ⟨y, rfl⟩, hy⟩
  exact ⟨w, trivial, hwu, hwv⟩

variable (B) (X : B.Scheme)

/-- **Constructible sheaves are finite locally constant on an étale neighbourhood of every
generic point.** -/
theorem exists_etale_isFiniteLocallyConstant_of_isConstructibleSetSheaf [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) (Y : B.Scheme) (j : Y ⟶ X)
    [IsClosedImmersion (B.inclusion.map j)] [IrreducibleSpace Y.obj] :
    ∃ (U : B.Scheme) (p : U ⟶ Y), Etale (B.inclusion.map p) ∧
      genericPoint Y.obj ∈ Set.range (B.inclusion.map p) ∧
      SmallEtale.IsFiniteLocallyConstant B U.obj U.property
        ((smallEtaleInverseImage B (p ≫ j) (Type (u + 1))).obj F) := by
  obtain ⟨n, Z, i, hi, hcov, hflc⟩ :=
    (isConstructibleSetSheaf_iff_exists_immersion_cover B X F).mp hF
  set η := genericPoint Y.obj
  obtain ⟨k, hk⟩ : ∃ k, (B.inclusion.map j) η ∈ Set.range (B.inclusion.map (i k)) := by
    have : (B.inclusion.map j) η ∈ (Set.univ : Set X.obj) := trivial
    rw [hcov, Set.mem_iUnion] at this
    exact this
  have := hi k
  have hlc : IsLocallyClosed ((B.inclusion.map j) ⁻¹' Set.range (B.inclusion.map (i k))) := by
    rw [← Scheme.Pullback.range_snd]
    exact Scheme.Hom.isLocallyClosed_range (pullback.snd _ _)
  obtain ⟨O, C, hO, hC, hOC⟩ := hlc
  have hkη : η ∈ O ∩ C := hOC ▸ hk
  have hCuniv : ∀ y, y ∈ C := fun y =>
    ((genericPoint_spec Y.obj).specializes trivial).mem_closed hC hkη.2
  let W : Y.obj.Opens := ⟨O, hO⟩
  have hWsub : ∀ y ∈ (W : Set Y.obj),
      (B.inclusion.map j) y ∈ Set.range (B.inclusion.map (i k)) := by
    intro y hy
    have : y ∈ O ∩ C := ⟨hy, hCuniv y⟩
    rw [← hOC] at this
    exact this
  let Wb : B.Scheme := B.obj W.toScheme (Scheme.size_lt_of_isOpenImmersion W.ι Y.property)
  let ιW : Wb ⟶ Y := ⟨W.ι⟩
  let g : W.toScheme ⟶ X.obj := W.ι ≫ B.inclusion.map j
  have hP : B.Contains (pullback (B.inclusion.map (i k)) g) :=
    BigEtaleSite.contains_of_isImmersion Wb.property (pullback.snd _ _)
  let Pb : B.Scheme := B.obj _ hP
  let s : Pb ⟶ Wb := ⟨pullback.snd (B.inclusion.map (i k)) g⟩
  let f : Pb ⟶ Z k := ⟨pullback.fst (B.inclusion.map (i k)) g⟩
  have hsf : f ≫ i k = s ≫ ιW ≫ j := B.inclusion.map_injective (by
    simp only [Functor.map_comp]
    exact pullback.condition)
  have hsurj : Function.Surjective (B.inclusion.map s) := by
    rw [← Set.range_eq_univ]
    change Set.range (pullback.snd (B.inclusion.map (i k)) g) = _
    rw [Scheme.Pullback.range_snd, Set.eq_univ_iff_forall]
    intro w
    have hw : W.ι w ∈ Set.range W.ι := ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι] at hw
    exact hWsub _ hw
  have hs : (B.inclusion.map s).IsPurelyInseparable := by
    have : IsImmersion (B.inclusion.map s) :=
      inferInstanceAs (IsImmersion (pullback.snd (B.inclusion.map (i k)) g))
    have : IsClosedImmersion (B.inclusion.map s) :=
      IsClosedImmersion.of_isPreimmersion _ (by
        rw [Set.range_eq_univ.mpr hsurj]
        exact isClosed_univ)
    exact ⟨inferInstance, inferInstance, ⟨hsurj⟩⟩
  have : Etale (B.inclusion.map ιW) := inferInstanceAs (Etale W.ι)
  refine ⟨Wb, ιW, inferInstance, ?_, ?_⟩
  · change η ∈ Set.range W.ι
    rw [Scheme.Opens.range_ι]
    exact hkη.1
  rw [SmallEtale.isFiniteLocallyConstant_iff_smallEtaleInverseImage_of_isPurelyInseparable s hs]
  have h1 := SmallEtale.isFiniteLocallyConstant_smallEtaleInverseImage B f _ (hflc k)
  refine (SmallEtale.isFiniteLocallyConstant_iff_of_iso ?_).mp h1
  exact (smallEtaleInverseImageCompObjIso B f (i k) _ F).symm ≪≫ eqToIso (by rw [hsf]) ≪≫
    smallEtaleInverseImageCompObjIso B s (ιW ≫ j) _ F

/-- The étale-neighbourhood condition at one irreducible closed subset `C` of `X` gives a locally
closed subscheme `T ⟶ X`, on which `F` is finite locally constant, whose image contains `C ∩ O`
for an open `O` containing the generic point of `C`. -/
theorem exists_isImmersion_isFiniteLocallyConstant_of_isIrreducible
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (H : ∀ (Y : B.Scheme) (j : Y ⟶ X), IsClosedImmersion (B.inclusion.map j) →
      ∀ [IrreducibleSpace Y.obj], ∃ (U : B.Scheme) (p : U ⟶ Y), Etale (B.inclusion.map p) ∧
        genericPoint Y.obj ∈ Set.range (B.inclusion.map p) ∧
        SmallEtale.IsFiniteLocallyConstant B U.obj U.property
          ((smallEtaleInverseImage B (p ≫ j) (Type (u + 1))).obj F))
    {C : Set X.obj} (hCc : IsClosed C) (hC : IsIrreducible C) :
    ∃ (T : B.Scheme) (t : T ⟶ X), IsImmersion (B.inclusion.map t) ∧
      SmallEtale.IsFiniteLocallyConstant B T.obj T.property
        ((smallEtaleInverseImage B t (Type (u + 1))).obj F) ∧
      ∃ O : Set X.obj, IsOpen O ∧ hC.genericPoint ∈ O ∧ C ∩ O ⊆ Set.range (B.inclusion.map t) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨C, hCc⟩ : Closeds X.obj)
  let jY : I.subscheme ⟶ X.obj := I.subschemeι
  have hrange : Set.range jY = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let Yb : B.Scheme := B.obj I.subscheme (Scheme.size_lt_of_isClosedImmersion jY X.property)
  let jb : Yb ⟶ X := ⟨jY⟩
  have : IsClosedImmersion (B.inclusion.map jb) := inferInstanceAs (IsClosedImmersion jY)
  have hemb : IsClosedEmbedding jY := jY.isClosedEmbedding
  have : IrreducibleSpace Yb.obj :=
    irreducibleSpace_of_isInducing hemb.isInducing (hrange ▸ hC)
  obtain ⟨U, p, hpet, hgen, hflc⟩ := H Yb jb inferInstance
  let V : Yb.obj.Opens :=
    ⟨Set.range (B.inclusion.map p), (B.inclusion.map p).isOpenMap.isOpen_range⟩
  let Tb : B.Scheme := B.obj V.toScheme (Scheme.size_lt_of_isOpenImmersion V.ι Yb.property)
  let ιT : Tb ⟶ Yb := ⟨V.ι⟩
  have hpV : Set.range (B.inclusion.map p) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact subset_rfl
  let p' : U ⟶ Tb := ⟨IsOpenImmersion.lift V.ι (B.inclusion.map p) hpV⟩
  have hp' : p' ≫ ιT = p := B.inclusion.map_injective (IsOpenImmersion.lift_fac _ _ hpV)
  have : Etale (B.inclusion.map p') := by
    have : Etale (B.inclusion.map p' ≫ V.ι) := by
      change Etale (IsOpenImmersion.lift V.ι (B.inclusion.map p) hpV ≫ V.ι)
      rw [IsOpenImmersion.lift_fac]
      exact hpet
    exact Etale.of_comp _ V.ι
  have hp'surj : Function.Surjective (B.inclusion.map p') := by
    intro y
    have hy : V.ι y ∈ Set.range V.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← Scheme.Hom.comp_apply]
    change (IsOpenImmersion.lift V.ι (B.inclusion.map p) hpV ≫ V.ι) x = _
    rw [IsOpenImmersion.lift_fac]
  have : IsImmersion (B.inclusion.map (ιT ≫ jb)) := by
    rw [Functor.map_comp]
    exact inferInstanceAs (IsImmersion (V.ι ≫ jY))
  refine ⟨Tb, ιT ≫ jb, inferInstance, ?_, ?_⟩
  · refine SmallEtale.isFiniteLocallyConstant_of_smallEtaleInverseImage p' hp'surj _ ?_
    refine (SmallEtale.isFiniteLocallyConstant_iff_of_iso ?_).mp hflc
    exact eqToIso (by rw [← hp', Category.assoc]) ≪≫
      smallEtaleInverseImageCompObjIso B p' (ιT ≫ jb) _ F
  obtain ⟨O, hO, hOV⟩ := hemb.isInducing.isOpen_iff.mp V.isOpen
  have hη : jY (genericPoint Yb.obj) = hC.genericPoint := by
    have h1 : IsGenericPoint (jY (genericPoint Yb.obj)) C := by
      have := (genericPoint_spec Yb.obj).image (f := jY) jY.continuous
      rwa [Set.image_univ, hrange, hCc.closure_eq] at this
    have h2 := hC.isGenericPoint_genericPoint_closure
    rw [hCc.closure_eq] at h2
    exact h1.eq h2
  refine ⟨O, hO, ?_, ?_⟩
  · rw [← hη]
    change genericPoint Yb.obj ∈ jY ⁻¹' O
    rw [hOV]
    exact hgen
  · rintro x ⟨hxC, hxO⟩
    rw [← hrange] at hxC
    obtain ⟨y, rfl⟩ := hxC
    have hyV : y ∈ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rw [← hOV]
      exact hxO
    obtain ⟨v, rfl⟩ := hyV
    exact ⟨v, rfl⟩

/-- **The étale-neighbourhood criterion implies constructibility.** On a scheme with Noetherian
underlying space, a sheaf of sets which is finite locally constant on an étale neighbourhood of
the generic point of every irreducible closed subscheme is constructible. -/
theorem isConstructibleSetSheaf_of_forall_exists_etale_isFiniteLocallyConstant
    [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (H : ∀ (Y : B.Scheme) (j : Y ⟶ X), IsClosedImmersion (B.inclusion.map j) →
      ∀ [IrreducibleSpace Y.obj], ∃ (U : B.Scheme) (p : U ⟶ Y), Etale (B.inclusion.map p) ∧
        genericPoint Y.obj ∈ Set.range (B.inclusion.map p) ∧
        SmallEtale.IsFiniteLocallyConstant B U.obj U.property
          ((smallEtaleInverseImage B (p ≫ j) (Type (u + 1))).obj F)) :
    IsConstructibleSetSheaf B X F := by
  have claim : ∀ Z : Closeds X.obj, ∃ (I : Type) (_ : Finite I) (T : I → B.Scheme)
      (t : ∀ i, T i ⟶ X), (∀ i, IsImmersion (B.inclusion.map (t i))) ∧
      (Z : Set X.obj) ⊆ ⋃ i, Set.range (B.inclusion.map (t i)) ∧
      ∀ i, SmallEtale.IsFiniteLocallyConstant B (T i).obj (T i).property
        ((smallEtaleInverseImage B (t i) (Type (u + 1))).obj F) := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | _ Z ih =>
    by_cases hZ : (Z : Set X.obj) = ∅
    · exact ⟨PEmpty, inferInstance, PEmpty.elim, fun i => i.elim, fun i => i.elim,
        by simp [hZ], fun i => i.elim⟩
    obtain ⟨S, hSfin, hScl, hSirr, hZS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible Z.isClosed
    have hSne : S.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [hZS, h, Set.sUnion_empty] at hZ
      exact hZ rfl
    obtain ⟨C, hCmax⟩ := hSfin.exists_maximal hSne
    have hCS : C ∈ S := hCmax.1
    have hCc := hScl C hCS
    have hCirr := hSirr C hCS
    set η := hCirr.genericPoint
    have hη : closure {η} = C := by
      have := hCirr.isGenericPoint_genericPoint_closure
      rw [hCc.closure_eq] at this
      exact this
    have hηC : η ∈ C := hη ▸ subset_closure rfl
    let O' : Set X.obj := (⋃₀ (S \ {C}))ᶜ
    have hO' : IsOpen O' :=
      ((hSfin.sdiff).isClosed_sUnion fun D hD => hScl D hD.1).isOpen_compl
    have hηO' : η ∈ O' := by
      rintro ⟨D, ⟨hDS, hDC⟩, hηD⟩
      have hCD : C ⊆ D := hη ▸ closure_minimal (Set.singleton_subset_iff.mpr hηD) (hScl D hDS)
      exact hDC (le_antisymm (hCmax.2 hDS hCD) hCD)
    have hZO' : (Z : Set X.obj) ∩ O' ⊆ C := by
      rintro x ⟨hxZ, hxO'⟩
      rw [hZS] at hxZ
      obtain ⟨D, hDS, hxD⟩ := hxZ
      by_contra hxC
      have hDC : D ≠ C := by rintro rfl; exact hxC hxD
      exact hxO' ⟨D, ⟨hDS, hDC⟩, hxD⟩
    obtain ⟨T, t, ht, htF, O, hO, hηO, hCO⟩ :=
      exists_isImmersion_isFiniteLocallyConstant_of_isIrreducible B X F H hCc hCirr
    let Z' : Closeds X.obj := ⟨(Z : Set X.obj) ∩ (O ∩ O')ᶜ,
      Z.isClosed.inter (hO.inter hO').isClosed_compl⟩
    have hZ' : Z' < Z := by
      rw [SetLike.lt_iff_le_and_exists]
      refine ⟨fun x hx => hx.1, η, ?_, fun h => h.2 ⟨hηO, hηO'⟩⟩
      have : C ⊆ (Z : Set X.obj) := by rw [hZS]; exact Set.subset_sUnion_of_mem hCS
      exact this hηC
    obtain ⟨I, hI, T', t', ht', hcov', hF'⟩ := ih Z' hZ'
    refine ⟨Option I, inferInstance, fun o => o.elim T T',
      fun o => match o with | none => t | some i => t' i, fun o => ?_, ?_, fun o => ?_⟩
    · cases o with
      | none => exact ht
      | some i => exact ht' i
    · intro x hxZ
      rw [Set.mem_iUnion]
      by_cases hx : x ∈ O ∩ O'
      · exact ⟨none, hCO ⟨hZO' ⟨hxZ, hx.2⟩, hx.1⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov' ⟨hxZ, hx⟩)
        exact ⟨some i, hi⟩
    · cases o with
      | none => exact htF
      | some i => exact hF' i
  obtain ⟨I, hI, T, t, ht, hcov, hF⟩ := claim ⊤
  let e := Finite.equivFin I
  refine (isConstructibleSetSheaf_iff_exists_immersion_cover B X F).mpr
    ⟨Nat.card I, fun k => T (e.symm k), fun k => t (e.symm k), fun k => ht _, ?_,
      fun k => hF _⟩
  refine Set.Subset.antisymm (fun x _ => ?_) (Set.subset_univ _)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
  obtain ⟨k, rfl⟩ := e.symm.surjective i
  exact Set.mem_iUnion.mpr ⟨k, hi⟩

/-- **Constructibility via étale neighbourhoods of generic points.** On a scheme `X` with
Noetherian underlying space, a sheaf of sets `F` on the small étale site of `X` is constructible
if and only if for every irreducible closed subscheme `j : Y ⟶ X`, with generic point `η_Y`,
there is an étale morphism `p : U ⟶ Y` with `η_Y ∈ p(U)` such that the inverse image of `F`
along `U ⟶ Y ⟶ X` is finite locally constant. -/
@[weil "lem_fk104_constructible_iff_generic_etale_nbhd_flc"]
theorem isConstructibleSetSheaf_iff_forall_exists_etale_isFiniteLocallyConstant
    [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∀ (Y : B.Scheme) (j : Y ⟶ X), IsClosedImmersion (B.inclusion.map j) →
        ∀ [IrreducibleSpace Y.obj], ∃ (U : B.Scheme) (p : U ⟶ Y), Etale (B.inclusion.map p) ∧
          genericPoint Y.obj ∈ Set.range (B.inclusion.map p) ∧
          SmallEtale.IsFiniteLocallyConstant B U.obj U.property
            ((smallEtaleInverseImage B (p ≫ j) (Type (u + 1))).obj F) :=
  ⟨fun hF Y j _ _ => exists_etale_isFiniteLocallyConstant_of_isConstructibleSetSheaf B X F hF Y j,
    isConstructibleSetSheaf_of_forall_exists_etale_isFiniteLocallyConstant B X F⟩

end AlgebraicGeometry
