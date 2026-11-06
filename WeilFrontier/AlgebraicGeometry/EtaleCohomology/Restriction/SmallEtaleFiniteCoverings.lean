module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Sections of étale sheaves commute with filtered colimits

Let `S` be a scheme, `I` a filtered category and `(F_ν)_{ν ∈ I}` a diagram of sheaves of sets
(resp. of abelian groups) on the small étale site of `S`. For every object `U` of the site whose
underlying scheme is quasi-compact and quasi-separated, the canonical map
`colim_ν F_ν(U) ⟶ (colim_ν F_ν)(U)`
is bijective, where the colimit on the right is formed in the category of sheaves.

The proof is part (4) of Stacks 0738: every covering of such a `U` is refined by a finite
covering by affine étale `U`-schemes, whose pairwise fibre products over `U` are quasi-compact
because `U` is quasi-separated. The abelian case follows from the case of sets, because the
forgetful functor from abelian sheaves to sheaves of sets preserves filtered colimits (it is,
up to sheafification, the forgetful functor of presheaves) and the forgetful functor from
abelian groups to sets preserves filtered colimits and reflects isomorphisms.

## Main results

* `AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings_of_compactSpace` — every covering
  sieve of an object with quasi-compact quasi-separated underlying scheme is refined by a finite
  covering family with quasi-compact pairwise fibre products, with no hypothesis on `S`.
* `AlgebraicGeometry.SmallEtale.bijective_colimit_post_sheafSections` — sections over such an
  object commute with filtered colimits of sheaves of sets.
* `AlgebraicGeometry.SmallEtale.bijective_colimit_post_sheafSections_addCommGrp` — the same for
  sheaves of abelian groups.

## Implementation notes

The étale category of Freitag–Kiehl consists of étale `S`-schemes whose source is noetherian and
separated; such a scheme is quasi-compact and quasi-separated, so the results here, stated for
the small étale site `AlgebraicGeometry.SmallEtale B S hS` of Stacks 021B and any object with
quasi-compact quasi-separated underlying scheme, contain the case of the source. The canonical
map is `CategoryTheory.Limits.colimit.post` for the sections functor.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₂ w₁ u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering sieve of an object of the small étale site with quasi-compact underlying scheme
is refined by a finite covering family with affine sources. -/
theorem exists_finite_affine_refinement_of_compactSpace (U : SmallEtale B S hS)
    (hU : CompactSpace ((SmallEtale.toScheme B S hS).obj U)) :
    ∀ R ∈ SmallEtale.topology B S hS U,
      ∃ 𝒱 : PreZeroHypercover.{u + 1} U,
        Finite 𝒱.I₀ ∧ 𝒱.sieve₀ ∈ SmallEtale.topology B S hS U ∧
          𝒱.sieve₀ ≤ R ∧
          ∀ i, _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B S hS).obj (𝒱.X i)) := by
  classical
  let X : B.Scheme := ⟨S, hS⟩
  intro R hR
  obtain ⟨V, hV, hAffineV, hlift⟩ := exists_affine_covering_lifting_mem_topology B X U hR
  let Vsite : PreZeroHypercover U := {
    I₀ := (V.map B.inclusion).I₀
    X i := by
      change V.I₀ at i
      have : Etale (B.inclusion.map (V.f i)) :=
        ((Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).mp hV.1).2 i
      have : Etale (B.inclusion.map U.obj.hom) := U.property
      exact ⟨Over.mk (V.f i ≫ U.obj.hom), by
        change Etale (B.inclusion.map (V.f i) ≫ B.inclusion.map U.obj.hom)
        infer_instance⟩
    f i := by
      change V.I₀ at i
      exact ObjectProperty.homMk (Over.homMk (V.f i) rfl)
  }
  obtain ⟨F, hF⟩ := exists_finset_isCovering_restrictIndex B X U hU V hV
  let K := {i : V.I₀ // i ∈ F}
  let 𝒱 : PreZeroHypercover U := {
    I₀ := K
    X i := Vsite.X i.1
    f i := Vsite.f i.1
  }
  have h𝒱scheme : 𝒱.sieve₀ ∈ SmallEtale.topology B S hS U := by
    change (SmallEtale.precoverage B S hS).Saturate U 𝒱.sieve₀
    apply Precoverage.Saturate.of
    refine ⟨𝒱, rfl, ?_⟩
    change B.IsCovering ⟨U.obj.left,
      (𝒱.map (SmallEtale.inclusion B S hS)).map (BigEtaleOver.forget B S hS)⟩
    have hmap :
        (𝒱.map (SmallEtale.inclusion B S hS)).map (BigEtaleOver.forget B S hS) =
          V.restrictIndex (fun i : K => i.1) := by
      ext <;> rfl
    rw [hmap]
    exact hF
  have hle : 𝒱.sieve₀ ≤ R := by
    intro Y f hf
    obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff 𝒱.X 𝒱.f f).mp hf
    obtain ⟨Z, k, hk, w, hw⟩ := hlift i.1
    exact R.downward_closed (mem_of_comp_toScheme_map_eq B X R (f := 𝒱.f i) hk w hw) g
  exact ⟨𝒱, inferInstance, h𝒱scheme, hle, fun i => by
    change _root_.AlgebraicGeometry.IsAffine (B.inclusion.obj (V.X i.1))
    exact hAffineV i.1⟩

/-- **The hypothesis of part (4) of Stacks 0738 on the small étale site.** Every covering sieve of
an object whose underlying scheme is quasi-compact and quasi-separated is refined by a finite
covering family whose pairwise fibre products exist and are quasi-compact objects of the site. -/
theorem hasFiniteQuasiCompactCoverings_of_compactSpace (U : SmallEtale B S hS)
    (hU : CompactSpace ((SmallEtale.toScheme B S hS).obj U))
    (hQS : QuasiSeparatedSpace ((SmallEtale.toScheme B S hS).obj U)) :
    (SmallEtale.topology B S hS).HasFiniteQuasiCompactCoverings U := by
  classical
  let T := SmallEtale.toScheme B S hS
  intro R hR
  obtain ⟨𝒱, hfin, hcover, hle, hAffine⟩ :=
    exists_finite_affine_refinement_of_compactSpace B S hS U hU R hR
  refine ⟨𝒱, hfin, hcover, hle, fun j j' => ?_⟩
  have : _root_.AlgebraicGeometry.IsAffine (T.obj (𝒱.X j)) := hAffine j
  have : _root_.AlgebraicGeometry.IsAffine (T.obj (𝒱.X j')) := hAffine j'
  have : CompactSpace (T.obj (𝒱.X j)) := Scheme.compactSpace_of_isAffine _
  have : CompactSpace (T.obj (𝒱.X j')) := Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace (T.obj U) := hQS
  let Wsite := pullback (𝒱.f j) (𝒱.f j')
  have : CompactSpace (T.obj Wsite) := by
    have : QuasiCompact (T.map (𝒱.f j)) := inferInstance
    have : CompactSpace
        (Limits.pullback (C := Scheme) (T.map (𝒱.f j)) (T.map (𝒱.f j'))) := inferInstance
    exact isCompact_univ_iff.mp
      ((PreservesPullback.iso T (𝒱.f j) (𝒱.f j')).hom.homeomorph.isCompact_preimage.mpr
        isCompact_univ)
  exact ⟨Wsite, pullback.fst _ _, pullback.snd _ _, IsPullback.of_hasPullback _ _,
    isQuasiCompactObject_of_compactSpace B S hS Wsite inferInstance⟩

/-- **Sections of étale sheaves of sets commute with filtered colimits.** Let `F` be a filtered
diagram of sheaves of sets on the small étale site of `S` and `U` an object of the site whose
underlying scheme is quasi-compact and quasi-separated. Then the canonical map
`colim_ν F_ν(U) ⟶ (colim_ν F_ν)(U)` is bijective. -/
@[weil "lem_fk104_sections_commute_filtered_colimits"]
theorem bijective_colimit_post_sheafSections {I : Type w₁} [Category.{w₂} I] [IsFiltered I]
    [HasColimitsOfShape I (Type (u + 1))]
    (F : I ⥤ Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) (U : SmallEtale B S hS)
    (hU : CompactSpace ((SmallEtale.toScheme B S hS).obj U))
    (hQS : QuasiSeparatedSpace ((SmallEtale.toScheme B S hS).obj U)) :
    Function.Bijective
      (colimit.post F ((sheafSections (SmallEtale.topology B S hS) (Type (u + 1))).obj (op U))) :=
  (Sheaf.injective_and_bijective_colimit_post_sheafSections _ F U).2.2.2
    (hasFiniteQuasiCompactCoverings_of_compactSpace B S hS U hU hQS)

/-- The forgetful functor from abelian étale sheaves to étale sheaves of sets preserves filtered
colimits: up to sheafification it is the forgetful functor of presheaves, which preserves
them objectwise. -/
instance preservesColimit_sheafCompose_forget {I : Type (u + 1)} [SmallCategory I]
    [IsFiltered I] (F : I ⥤ Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    PreservesColimit F
      (sheafCompose (SmallEtale.topology B S hS) (forget AddCommGrpCat.{u + 1})) := by
  let J := SmallEtale.topology B S hS
  let L := presheafToSheaf J AddCommGrpCat.{u + 1}
  let R := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let V := sheafCompose J (forget AddCommGrpCat.{u + 1})
  have h : PreservesColimit (F ⋙ R) (L ⋙ V) :=
    preservesColimit_of_natIso (F ⋙ R)
      (sheafComposeNatIso J (forget AddCommGrpCat.{u + 1})
        (sheafificationAdjunction J AddCommGrpCat.{u + 1})
        (sheafificationAdjunction J (Type (u + 1))))
  have h' : PreservesColimit ((F ⋙ R) ⋙ L) V :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (F ⋙ R)))
      (isColimitOfPreserves (L ⋙ V) (colimit.isColimit (F ⋙ R)))
  exact preservesColimit_of_iso_diagram V
    ((Functor.associator F R L) ≪≫
      Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit) ≪≫
      Functor.rightUnitor F)

/-- **Sections of abelian étale sheaves commute with filtered colimits.** Let `F` be a filtered
diagram of sheaves of abelian groups on the small étale site of `S` and `U` an object of the
site whose underlying scheme is quasi-compact and quasi-separated. Then the canonical map
`colim_ν F_ν(U) ⟶ (colim_ν F_ν)(U)` is bijective. -/
@[weil "lem_fk104_sections_commute_filtered_colimits"]
theorem bijective_colimit_post_sheafSections_addCommGrp {I : Type (u + 1)} [SmallCategory I]
    [IsFiltered I] (F : I ⥤ Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS)
    (hU : CompactSpace ((SmallEtale.toScheme B S hS).obj U))
    (hQS : QuasiSeparatedSpace ((SmallEtale.toScheme B S hS).obj U)) :
    Function.Bijective
      (colimit.post F
        ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}).obj (op U))) := by
  let J := SmallEtale.topology B S hS
  let V := sheafCompose J (forget AddCommGrpCat.{u + 1})
  let T := (sheafSections J (Type (u + 1))).obj (op U)
  let Sec := (sheafSections J AddCommGrpCat.{u + 1}).obj (op U)
  have : IsIso (colimit.post (F ⋙ V) T) :=
    (isIso_iff_bijective _).2 (bijective_colimit_post_sheafSections B S hS (F ⋙ V) U hU hQS)
  have : PreservesColimit (F ⋙ V) T := preservesColimit_of_isIso_post _ _
  have : PreservesColimit F (Sec ⋙ forget AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesColimit F (V ⋙ T))
  have : ReflectsColimit (F ⋙ Sec) (forget AddCommGrpCat.{u + 1}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have : PreservesColimit F Sec := preservesColimit_of_reflects_of_preserves Sec
    (forget AddCommGrpCat.{u + 1})
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

end AlgebraicGeometry.SmallEtale

end
