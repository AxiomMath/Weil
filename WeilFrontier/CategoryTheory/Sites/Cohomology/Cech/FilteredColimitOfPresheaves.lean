module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyCovering
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import StacksFrontier.Homology.HomologyColimit
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Čech cohomology of a finite covering commutes with filtered colimits

Let `𝔘 = (U_α → U)_{α = 1, …, m}` be a finite family of morphisms with target `U` and let
`(F_ν)_{ν ∈ I}` be a filtered diagram of abelian presheaves with a cocone `F_ν ⟶ F` such that, on
each of the finitely many iterated fibre products `U_{α₀} ×_U ⋯ ×_U U_{α_p}`, the sections of `F`
are the colimit of the sections of the `F_ν`. Then each Čech cochain group
`Č^p(𝔘, F) = ∏_α F(U_α)` is the colimit of the `Č^p(𝔘, F_ν)`, because a finite product of
filtered colimits of abelian groups is the filtered colimit of the products; hence
`Č^•(𝔘, F) = colim_ν Č^•(𝔘, F_ν)` as complexes, and since filtered colimits of abelian groups are
exact, the canonical map `colim_ν Ȟ^i(𝔘, F_ν) ⟶ Ȟ^i(𝔘, F)` is an isomorphism for every `i ≥ 0`.

For sheaves of abelian groups on the étale category `Et(S)` of a locally noetherian scheme and a
colimit `F = colim_ν F_ν` formed in the category of sheaves, the hypothesis holds because every
object of `Et(S)` is noetherian, so that sections over it commute with filtered colimits of
sheaves.

## Main results

* `Stacks.CechSite.isColimitMapCoconeCechComplexFunctor`: the Čech complexes of the `F_ν` have
  the Čech complex of `F` as colimit.
* `Stacks.CechSite.isIso_colimitDesc_cechCohomology`: the canonical map
  `colim_ν Ȟ^n(𝔘, F_ν) ⟶ Ȟ^n(𝔘, F)` is an isomorphism, for presheaves on any category.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isIso_colimitDesc_cechCohomology`: the same
  for a filtered colimit of sheaves of abelian groups on `Et(S)`, the colimit being formed in
  sheaves.
* `AlgebraicGeometry.SmallEtale.isIso_colimitDesc_cechCohomology`: the same on the small étale
  site of `S`, for a finite family whose iterated fibre products are quasi-compact and
  quasi-separated.

## Implementation notes

The source states the result for an étale covering; only the finiteness of the covering is used,
so the statements are for any finite family with fixed target, jointly surjective or not. The
Čech cohomology group `Ȟ^n(𝔘, G)` is
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomology E G n`, the value at `G` of the
functor `Stacks.CechSite.cechComplexFunctor E ⋙ HomologicalComplex.homologyFunctor _ _ n` that
appears in the statements. The sheaves take values in `AddCommGrpCat.{u + 1}` and the index
category lives in `Type (u + 1)`, the universe in which the sections of étale sheaves are known
to commute with filtered colimits.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w v u

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasProducts.{w} AddCommGrpCat.{a}]
  {I : Type a} [SmallCategory I] [IsFiltered I] {P : I ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{a}}
  (c : Cocone P)

/-- **Degreewise, the Čech complex commutes with filtered colimits.** For a finite family `E` and a
filtered cocone `c` over presheaves of abelian groups that is a colimit on every iterated fibre
product of `E`, the degree-`p` Čech cochains of `c.pt` are the colimit of those of the diagram. -/
noncomputable def isColimitMapCoconeEvalCechComplexFunctor [Finite E.I₀]
    (hc : ∀ (n : ℕ) (k : Fin (n + 1) → E.I₀),
      IsColimit (((evaluation Cᵒᵖ AddCommGrpCat.{a}).obj
        (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))).mapCocone c))
    (p : ℕ) :
    IsColimit ((HomologicalComplex.eval _ _ p).mapCocone
      ((cechComplexFunctor E).mapCocone c)) := by
  classical
  have : Fintype (Fin (p + 1) → E.I₀) := Fintype.ofFinite _
  have : ReflectsColimit ((P ⋙ cechComplexFunctor E) ⋙ HomologicalComplex.eval _ _ p)
      (forget AddCommGrpCat.{a}) := reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget AddCommGrpCat.{a})
    (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro x
    choose ν y hy using fun k ↦
      Concrete.isColimit_exists_rep _ (hc p k) (Pi.π (cochainFactor E c.pt p) k x)
    obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.univ.image ν)
    have hk : ∀ k, Nonempty (ν k ⟶ m) := fun k ↦
      hm (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    refine ⟨m, (productAddEquiv (cochainFactor E (P.obj m) p)).symm
      fun k ↦ (P.map (hk k).some).app _ (y k), ?_⟩
    apply (productAddEquiv (cochainFactor E c.pt p)).injective
    funext k
    change Pi.π (cochainFactor E c.pt p) k x = Pi.π (cochainFactor E c.pt p) k
      (((cechComplexFunctor E).map (c.ι.app m)).f p _)
    refine Eq.trans ?_ (cechComplexFunctor_map_f_π_apply E (c.ι.app m) p k _).symm
    change _ = (c.ι.app m).app _ (productAddEquiv (cochainFactor E (P.obj m) p)
      ((productAddEquiv (cochainFactor E (P.obj m) p)).symm
        fun k ↦ (P.map (hk k).some).app _ (y k)) k)
    rw [AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      c.w, ← hy k]
    rfl
  · intro ν x y hxy
    have h : ∀ k, (c.ι.app ν).app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))
        (Pi.π (cochainFactor E (P.obj ν) p) k x) =
        (c.ι.app ν).app _ (Pi.π (cochainFactor E (P.obj ν) p) k y) := fun k ↦
      (cechComplexFunctor_map_f_π_apply E (c.ι.app ν) p k x).symm.trans
        ((congrArg (Pi.π (cochainFactor E c.pt p) k) hxy).trans
          (cechComplexFunctor_map_f_π_apply E (c.ι.app ν) p k y))
    choose l f g hfg using fun k ↦ Concrete.isColimit_exists_of_rep_eq _ (hc p k) _ _ (h k)
    let O : Finset I := insert ν (Finset.univ.image l)
    have hν : ν ∈ O := Finset.mem_insert_self _ _
    have hl : ∀ k, l k ∈ O := fun k ↦
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    let H : Finset ((A : I) ×' (B : I) ×' (_ : A ∈ O) ×' (_ : B ∈ O) ×' (A ⟶ B)) :=
      Finset.univ.image (fun k ↦ ⟨ν, l k, hν, hl k, f k⟩) ∪
        Finset.univ.image (fun k ↦ ⟨ν, l k, hν, hl k, g k⟩)
    refine ⟨IsFiltered.sup O H, IsFiltered.toSup O H hν, ?_⟩
    apply (productAddEquiv (cochainFactor E (P.obj (IsFiltered.sup O H)) p)).injective
    funext k
    have hf : f k ≫ IsFiltered.toSup O H (hl k) = IsFiltered.toSup O H hν :=
      IsFiltered.toSup_commutes O H hν (hl k)
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
    have hg : g k ≫ IsFiltered.toSup O H (hl k) = IsFiltered.toSup O H hν :=
      IsFiltered.toSup_commutes O H hν (hl k)
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
    refine (cechComplexFunctor_map_f_π_apply E (P.map (IsFiltered.toSup O H hν)) p k x).trans
      (Eq.trans ?_ (cechComplexFunctor_map_f_π_apply E (P.map (IsFiltered.toSup O H hν)) p k
        y).symm)
    have := congrArg ((P.map (IsFiltered.toSup O H (hl k))).app
      (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))) (hfg k)
    calc _ = (P.map (f k ≫ IsFiltered.toSup O H (hl k))).app _
          (Pi.π (cochainFactor E (P.obj ν) p) k x) := by rw [hf]
      _ = (P.map (g k ≫ IsFiltered.toSup O H (hl k))).app _
          (Pi.π (cochainFactor E (P.obj ν) p) k y) := by
        simp only [Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply]
        exact this
      _ = _ := by rw [hg]

/-- **The Čech complex commutes with filtered colimits.** Under the hypotheses of
`Stacks.CechSite.isColimitMapCoconeEvalCechComplexFunctor`, the Čech complex of `c.pt` is the
colimit, in cochain complexes, of the Čech complexes of the diagram. -/
noncomputable def isColimitMapCoconeCechComplexFunctor [Finite E.I₀]
    (hc : ∀ (n : ℕ) (k : Fin (n + 1) → E.I₀),
      IsColimit (((evaluation Cᵒᵖ AddCommGrpCat.{a}).obj
        (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))).mapCocone c)) :
    IsColimit ((cechComplexFunctor E).mapCocone c) :=
  HomologicalComplex.isColimitOfEval _ _ (isColimitMapCoconeEvalCechComplexFunctor E c hc)

/-- **Čech cohomology commutes with filtered colimits.** Under the hypotheses of
`Stacks.CechSite.isColimitMapCoconeEvalCechComplexFunctor`, the Čech cohomology groups of `c.pt`
in degree `n` are the colimit of those of the diagram, filtered colimits of abelian groups being
exact. -/
noncomputable def isColimitMapCoconeCechCohomology [Finite E.I₀]
    (hc : ∀ (n : ℕ) (k : Fin (n + 1) → E.I₀),
      IsColimit (((evaluation Cᵒᵖ AddCommGrpCat.{a}).obj
        (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))).mapCocone c))
    (n : ℕ) :
    IsColimit ((cechComplexFunctor E ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) n).mapCocone c) :=
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := AddCommGrpCat.{a}) (J := I) (ComplexShape.up ℕ) n
  isColimitOfPreserves (HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) n)
    (isColimitMapCoconeCechComplexFunctor E c hc)

/-- **The canonical map `colim_ν Ȟ^n(E, P_ν) ⟶ Ȟ^n(E, c.pt)` is an isomorphism** for a finite
family `E` and a filtered cocone `c` of abelian presheaves which is a colimit on every iterated
fibre product of `E`. -/
theorem isIso_colimitDesc_cechCohomology [Finite E.I₀]
    (hc : ∀ (n : ℕ) (k : Fin (n + 1) → E.I₀),
      IsColimit (((evaluation Cᵒᵖ AddCommGrpCat.{a}).obj
        (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))).mapCocone c))
    (n : ℕ) :
    IsIso (colimit.desc (P ⋙ cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) n)
      ((cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) n).mapCocone c)) :=
  (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mp
    ⟨isColimitMapCoconeCechCohomology E c hc n⟩

end Stacks.CechSite

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsLocallyNoetherian S]

/-- **Sections over an object of `Et(S)` commute with filtered colimits of sheaves.** For a
locally noetherian `S`, a filtered colimit of sheaves of abelian groups on `Et(S)` is taken to a
colimit by the sections over any object, every object of `Et(S)` being noetherian. -/
noncomputable def isColimitMapCoconeSheafSections {I : Type (u + 1)} [SmallCategory I]
    [IsFiltered I] {F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) (V : SmallNoetherianSeparatedEtale B S hS) :
    IsColimit
      (((sheafSections (topology B S hS) AddCommGrpCat.{u + 1}).obj (op V)).mapCocone c) := by
  let e := sheafEquiv B S hS AddCommGrpCat.{u + 1}
  let Sec' := (sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}).obj
    (op ((inclusion B S hS).obj V))
  have : IsNoetherian ((SmallEtale.toScheme B S hS).obj ((inclusion B S hS).obj V)) :=
    V.property.1
  have hb := SmallEtale.bijective_colimit_post_sheafSections_addCommGrp B S hS (F ⋙ e.functor)
    ((inclusion B S hS).obj V) inferInstance inferInstance
  have : IsIso (colimit.post (F ⋙ e.functor) Sec') :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have : PreservesColimit (F ⋙ e.functor) Sec' := preservesColimit_of_isIso_post _ _
  let iso : (sheafSections (topology B S hS) AddCommGrpCat.{u + 1}).obj (op V) ≅
      e.functor ⋙ Sec' :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.unitIso _ ≪≫ Functor.associator _ _ _
  exact IsColimit.mapCoconeEquiv iso.symm (isColimitOfPreserves (e.functor ⋙ Sec') hc)

/-- **Čech cohomology of a finite covering commutes with filtered colimits of sheaves.** Let `S` be
locally noetherian, `E = (U_α ⟶ U)_α` a finite family of morphisms of `Et(S)` with target `U`,
and `(F_ν)_{ν ∈ I}` a filtered diagram of sheaves of abelian groups on `Et(S)` with colimit
`c.pt = colim_ν F_ν` in sheaves. Then for every `n`, the canonical map
`colim_ν Ȟ^n(E, F_ν) ⟶ Ȟ^n(E, colim_ν F_ν)` is an isomorphism. -/
@[weil "lem_fk104_cech_finite_covering_commutes_filtered_colimits"]
theorem isIso_colimitDesc_cechCohomology [HasProducts.{w} AddCommGrpCat.{u + 1}]
    {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{w} U) [Finite E.I₀]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) {c : Cocone F} (hc : IsColimit c)
    (n : ℕ) :
    IsIso (colimit.desc (F ⋙ sheafToPresheaf _ _ ⋙ Stacks.CechSite.cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n)
      ((sheafToPresheaf _ _ ⋙ Stacks.CechSite.cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).mapCocone
          c)) :=
  Stacks.CechSite.isIso_colimitDesc_cechCohomology E ((sheafToPresheaf _ _).mapCocone c)
    (fun _ _ ↦ isColimitMapCoconeSheafSections hc _) n

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Sections over an object of the small étale site with quasi-compact quasi-separated underlying
scheme take a filtered colimit of sheaves of abelian groups to a colimit. -/
noncomputable def isColimitMapCoconeSheafSections {I : Type (u + 1)} [SmallCategory I]
    [IsFiltered I] {F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) (V : SmallEtale B S hS) (hV : CompactSpace ((toScheme B S hS).obj V))
    (hV' : QuasiSeparatedSpace ((toScheme B S hS).obj V)) :
    IsColimit (((sheafSections (topology B S hS) AddCommGrpCat.{u + 1}).obj (op V)).mapCocone c) :=
  have : IsIso (colimit.post F ((sheafSections (topology B S hS) AddCommGrpCat.{u + 1}).obj
      (op V))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_colimit_post_sheafSections_addCommGrp B S hS F V hV hV')
  have : PreservesColimit F
      ((sheafSections (topology B S hS) AddCommGrpCat.{u + 1}).obj (op V)) :=
    preservesColimit_of_isIso_post _ _
  isColimitOfPreserves _ hc

/-- **Čech cohomology of a finite family commutes with filtered colimits of sheaves on the small
étale site**, when the iterated fibre products of the family have quasi-compact quasi-separated
underlying schemes: the canonical map `colim_ν Ȟ^n(E, F_ν) ⟶ Ȟ^n(E, colim_ν F_ν)` is an
isomorphism. -/
theorem isIso_colimitDesc_cechCohomology [HasProducts.{w} AddCommGrpCat.{u + 1}]
    {U : SmallEtale B S hS} (E : PreZeroHypercover.{w} U) [Finite E.I₀]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (hE : ∀ (n : ℕ) (k : Fin (n + 1) → E.I₀),
      CompactSpace ((toScheme B S hS).obj ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over U).left)) ∧
        QuasiSeparatedSpace
          ((toScheme B S hS).obj ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over U).left)))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) {c : Cocone F} (hc : IsColimit c)
    (n : ℕ) :
    IsIso (colimit.desc (F ⋙ sheafToPresheaf _ _ ⋙ Stacks.CechSite.cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n)
      ((sheafToPresheaf _ _ ⋙ Stacks.CechSite.cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).mapCocone
          c)) :=
  Stacks.CechSite.isIso_colimitDesc_cechCohomology E ((sheafToPresheaf _ _).mapCocone c)
    (fun m k ↦ isColimitMapCoconeSheafSections hc _ (hE m k).1 (hE m k).2) n

end AlgebraicGeometry.SmallEtale
