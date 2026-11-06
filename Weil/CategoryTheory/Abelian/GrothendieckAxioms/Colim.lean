module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Filtered colimits of short exact sequences of étale sheaves

Let `X` be a scheme. In the category of abelian sheaves on the small étale site of `X`, the
colimit of a filtered diagram of short exact sequences is short exact.

We first prove the general statement: in an abelian category `C` in which colimits of shape `J`
are exact (`HasExactColimitsOfShape J C`), any colimit of a `J`-indexed diagram of short exact
sequences is short exact. The étale case follows, since the category of abelian sheaves on the
small étale site is Grothendieck abelian
(`Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat`), hence satisfies AB5.

## Main results

* `CategoryTheory.ShortComplex.exact_of_forall_exact_map_evaluation`: a short complex in a functor
  category `J ⥤ C` is exact when it is exact at every object of `J`.
* `CategoryTheory.ShortComplex.shortExact_of_isColimit`: if colimits of shape `J` are exact in
  `C`, a colimit of a `J`-diagram of short exact sequences is short exact.
* `AlgebraicGeometry.Scheme.shortExact_of_isColimit_sheaf_smallEtaleTopology`: filtered colimits of
  short exact sequences of abelian étale sheaves are short exact.

## Implementation notes

The source proves exactness by hand: right exactness because the colimit functor is a left
adjoint, left exactness by computing the colimit as the sheafification of the objectwise
colimit. Here both halves come at once from AB5 for abelian sheaves on the small étale site.
The diagram is a functor `J ⥤ ShortComplex _`, and the statement holds for an arbitrary colimit
cocone, not only the chosen one. For `X : Scheme.{u}` the coefficients are `AddCommGrpCat.{w}`
for any universe `w` with `UnivLE.{u, w}`, and the filtered index category `J` is any category
which is essentially small at `w`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §2.
-/

@[expose] public section

open CategoryTheory Limits

universe w' w v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {J : Type w} [Category.{w'} J]

/-- A short complex in a functor category `J ⥤ C` is exact if its evaluation at every object
of `J` is exact. -/
lemma exact_of_forall_exact_map_evaluation (S : ShortComplex (J ⥤ C))
    (hS : ∀ j, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  rw [exact_iff_isZero_homology]
  refine Functor.isZero _ fun j => ?_
  exact ((S.map ((evaluation J C).obj j)).exact_iff_isZero_homology.1 (hS j)).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

/-- If colimits of shape `J` are exact in the abelian category `C`, then the point of any
colimit cocone of a `J`-indexed diagram of short exact sequences is short exact. -/
lemma shortExact_of_isColimit [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    {F : J ⥤ ShortComplex C} (hF : ∀ j, (F.obj j).ShortExact)
    {c : Cocone F} (hc : IsColimit c) : c.pt.ShortExact := by
  let S := (functorEquivalence J C).inverse.obj F
  have hS : S.Exact := exact_of_forall_exact_map_evaluation S fun j => (hF j).exact
  have hc₁ : IsColimit (π₁.mapCocone c) := isColimitOfPreserves π₁ hc
  have hc₂ : IsColimit (π₂.mapCocone c) := isColimitOfPreserves π₂ hc
  have hc₃ : IsColimit (π₃.mapCocone c) := isColimitOfPreserves π₃ hc
  have hf : ∀ j, (π₁.mapCocone c).ι.app j ≫ c.pt.f = S.f.app j ≫ (π₂.mapCocone c).ι.app j :=
    fun j => (c.ι.app j).comm₁₂
  have hg : ∀ j, (π₂.mapCocone c).ι.app j ≫ c.pt.g = S.g.app j ≫ (π₃.mapCocone c).ι.app j :=
    fun j => (c.ι.app j).comm₂₃
  have : ∀ j, Mono (S.f.app j) := fun j => (hF j).mono_f
  have : ∀ j, Epi (S.g.app j) := fun j => (hF j).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app _
  exact
    { exact := Limits.colim.exact_mapShortComplex hS hc₁ hc₂ hc₃ c.pt.f c.pt.g hf hg
      mono_f := Limits.colim.map_mono' S.f hc₁ hc₂ c.pt.f hf
      epi_g := Limits.colim.map_epi' S.g (π₂.mapCocone c) hc₃ c.pt.g hg }

/-- If colimits of shape `J` are exact in the abelian category `C`, then the colimit of a
`J`-indexed diagram of short exact sequences is short exact. -/
lemma shortExact_colimit [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (F : J ⥤ ShortComplex C) (hF : ∀ j, (F.obj j).ShortExact) : (colimit F).ShortExact :=
  shortExact_of_isColimit hF (colimit.isColimit F)

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Scheme

universe t' t

variable (X : Scheme.{u}) [UnivLE.{u, w}] {J : Type t} [Category.{t'} J] [IsFiltered J]
  [EssentiallySmall.{w} J]

/-- Colimits of filtered diagrams which are essentially small at `w` are exact in the category
of abelian sheaves with values in `AddCommGrpCat.{w}` on the small étale site of `X`. -/
theorem hasExactColimitsOfShape_sheaf_smallEtaleTopology
    [HasColimitsOfShape J (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w})] :
    HasExactColimitsOfShape J (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}) := by
  have : IsFiltered (SmallModel.{w} J) := IsFiltered.of_equivalence (equivSmallModel.{w} J)
  have : HasColimitsOfShape (SmallModel.{w} J)
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}) := inferInstance
  exact HasExactColimitsOfShape.of_domain_equivalence _ (equivSmallModel.{w} J).symm

/-- In the category of abelian sheaves on the small étale site of `X`, a colimit of a filtered
diagram of short exact sequences is short exact. -/
@[weil "lem_fk102_etale_sheaves_filtered_colimits_exact"]
theorem shortExact_of_isColimit_sheaf_smallEtaleTopology
    {F : J ⥤ ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w})}
    (hF : ∀ j, (F.obj j).ShortExact) {c : Cocone F} (hc : IsColimit c) :
    c.pt.ShortExact :=
  have := hasColimitsOfShape_of_essentiallySmall.{w} J
    (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w})
  have := hasExactColimitsOfShape_sheaf_smallEtaleTopology X (J := J)
  ShortComplex.shortExact_of_isColimit hF hc

/-- In the category of abelian sheaves on the small étale site of `X`, the colimit of a
filtered diagram of short exact sequences is short exact. -/
theorem shortExact_colimit_sheaf_smallEtaleTopology
    [HasColimitsOfShape J (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w})]
    (F : J ⥤ ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}))
    (hF : ∀ j, (F.obj j).ShortExact) : (colimit F).ShortExact :=
  shortExact_of_isColimit_sheaf_smallEtaleTopology X hF (colimit.isColimit F)

end AlgebraicGeometry.Scheme
