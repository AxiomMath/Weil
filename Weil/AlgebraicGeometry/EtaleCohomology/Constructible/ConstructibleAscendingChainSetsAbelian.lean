module

public import Weil.Attr
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleAscendingChainSetsAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Constructible sheaves are the noetherian torsion sheaves

Let `X` be a noetherian scheme. A sheaf of abelian groups on the small étale site of `X` is
constructible if and only if it is a torsion sheaf and a noetherian object of the category of
abelian sheaves, i.e. every ascending chain of abelian subsheaves stabilizes.

The forward direction is the combination of two facts: a constructible abelian sheaf is torsion
(its stalks are torsion groups), and it is noetherian (Stacks 09YV). For the converse, a torsion
sheaf `F` is a filtered colimit of constructible sheaves `Dᵢ` (Stacks 03SA (2)). The images of
the colimit maps `Dᵢ ⟶ F` form a directed family of subobjects of `F`; since `F` is noetherian
it has a maximal, hence greatest, member, and then the colimit property forces that member to be
all of `F`. So `F` is a quotient of a constructible sheaf, hence constructible (Stacks 09BH (2)).

## Main results

* `CategoryTheory.IsNoetherianObject.exists_epi_ι_of_isColimit`: a noetherian object which is
  the colimit of a filtered diagram receives an epimorphism from one term of the diagram.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_iff_isTorsionSheaf_and_isNoetherianObject`:
  on a noetherian scheme, the constructible abelian sheaves are exactly the noetherian torsion
  sheaves.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace CategoryTheory.IsNoetherianObject

variable {C : Type u} [Category.{v} C] [HasImages C] [HasEqualizers C]

/-- **A noetherian filtered colimit is reached by one term.** If a noetherian object `c.pt` is
the colimit of a filtered diagram `D`, then one of the colimit maps `D.obj i ⟶ c.pt` is an
epimorphism. The images of the colimit maps form a directed family of subobjects, which has a
greatest member by the ascending chain condition, and every colimit map factors through it; the
colimit property then splits the inclusion of that image. -/
theorem exists_epi_ι_of_isColimit {I : Type w} [Category.{w'} I] [IsFiltered I] {D : I ⥤ C}
    {c : Cocone D} (hc : IsColimit c) [IsNoetherianObject c.pt] :
    ∃ i, Epi (c.ι.app i) := by
  let S : I → Subobject c.pt := fun i ↦ imageSubobject (c.ι.app i)
  have hS : ∀ {i j : I} (f : i ⟶ j), S i ≤ S j := fun {i j} f ↦ by
    have h := imageSubobject_comp_le (D.map f) (c.ι.app j)
    rwa [c.w f] at h
  obtain ⟨_, ⟨i₀, rfl⟩, hmax⟩ := (wellFounded_gt (α := Subobject c.pt)).has_min (Set.range S)
    ⟨_, ⟨(IsFiltered.nonempty (C := I)).some, rfl⟩⟩
  have hle : ∀ i, S i ≤ S i₀ := fun i ↦ by
    have h₀ : S i₀ ≤ S (IsFiltered.max i i₀) := hS (IsFiltered.rightToMax i i₀)
    have heq : S (IsFiltered.max i i₀) = S i₀ :=
      (eq_or_lt_of_le h₀).elim Eq.symm fun hlt ↦ (hmax _ ⟨_, rfl⟩ hlt).elim
    exact heq ▸ hS (IsFiltered.leftToMax i i₀)
  have hfac : ∀ i, (S i₀).Factors (c.ι.app i) := fun i ↦
    Subobject.factors_of_le _ (hle i)
      ((Subobject.factors_iff _ _).mpr ⟨_, imageSubobject_arrow_comp (c.ι.app i)⟩)
  let c' : Cocone D :=
    { pt := (S i₀ : C)
      ι :=
        { app := fun i ↦ (S i₀).factorThru (c.ι.app i) (hfac i)
          naturality := fun i j f ↦ by
            rw [← cancel_mono (S i₀).arrow]
            simp [c.w f] } }
  have hs : hc.desc c' ≫ (S i₀).arrow = 𝟙 c.pt :=
    hc.hom_ext fun j ↦ by
      rw [← Category.assoc, hc.fac]
      simp [c']
  have : IsSplitEpi (S i₀).arrow := IsSplitEpi.mk' ⟨hc.desc c', hs⟩
  have : IsIso (S i₀).arrow := isIso_of_mono_of_isSplitEpi _
  refine ⟨i₀, ?_⟩
  rw [← imageSubobject_arrow_comp (c.ι.app i₀)]
  infer_instance

end CategoryTheory.IsNoetherianObject

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **A noetherian torsion sheaf is constructible.** On a noetherian scheme, an abelian sheaf on
the small étale site which is a torsion sheaf and a noetherian object is constructible: it is a
filtered colimit of constructible sheaves, one of which surjects onto it. -/
theorem isConstructibleAbelianSheaf_of_isTorsionSheaf_of_isNoetherianObject
    [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hT : SmallEtale.IsTorsionSheaf B X.obj X.property F) [IsNoetherianObject F] :
    IsConstructibleAbelianSheaf B X F := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have : CompactSpace X.1 := hN.2
  have : IsLocallyNoetherian X.1 := hN.1
  have : QuasiSeparatedSpace X.1 := IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X F hT
  obtain ⟨i, hi⟩ := IsNoetherianObject.exists_epi_ι_of_isColimit hc
  exact isConstructibleAbelianSheaf_of_epi B X (smallEtaleUnderlyingSetCommutes B X)
    (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X) (ι.app i) (hD i)

/-- **Constructible sheaves are the noetherian torsion sheaves.** On a noetherian scheme `X`, a
sheaf of abelian groups on the small étale site of `X` is constructible if and only if it is a
torsion sheaf and a noetherian object of the category of abelian sheaves (every ascending chain
of abelian subsheaves stabilizes). -/
@[weil "prop_fk104_constructible_iff_noetherian_torsion"]
theorem isConstructibleAbelianSheaf_iff_isTorsionSheaf_and_isNoetherianObject
    [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B X F ↔
      SmallEtale.IsTorsionSheaf B X.obj X.property F ∧ IsNoetherianObject F :=
  ⟨fun hF ↦ ⟨torsionSheafProperty_of_isConstructibleAbelianSheaf B X F hF,
      isNoetherianObject_of_isConstructibleAbelianSheaf' B X F hF⟩,
    fun ⟨hT, _⟩ ↦ isConstructibleAbelianSheaf_of_isTorsionSheaf_of_isNoetherianObject B X F hT⟩

end AlgebraicGeometry

end
