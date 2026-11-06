module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import WeilFrontier.AlgebraicGeometry.Sites.Etale
public import WeilFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# The étale category `Et(S)` of Freitag–Kiehl as a dense subsite of the small étale site

Freitag–Kiehl work on the category `Et(S)` of étale `S`-schemes which are noetherian and
separated, formalized as the full subcategory
`AlgebraicGeometry.SmallNoetherianSeparatedEtale B S hS` of the small étale site
`AlgebraicGeometry.SmallEtale B S hS` of [Stacks, Tag 021B], with FK's sheaf condition
`AlgebraicGeometry.EtalePresheaf.IsEtaleSheaf` (finite disjoint unions and surjective descent).
This file puts a Grothendieck topology on `Et(S)` and compares it with the small étale site, so
that results stated by FK on `Et(S)` can be read on `SmallEtale` and conversely.

* The topology `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology` is the one restricted
  from the small étale site along the inclusion.
* For `S` locally noetherian (FK assume `S` noetherian), the inclusion is cover dense, so it is
  a dense subsite inclusion and the two sites have equivalent sheaf categories
  (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`), hence also equivalent to
  Mathlib's small étale site (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquivEtale`).
* Its covering sieves are the jointly surjective ones, and also the sieves containing a *finite*
  jointly surjective family, which is FK's notion of covering.
* A presheaf of sets is a sheaf for this topology exactly when it is an étale sheaf in FK's
  sense (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.isSheaf_iff_isEtaleSheaf`).

## Implementation notes

FK's sheaf condition is matched against the coverage
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.finiteCoverage` of finite jointly surjective
families, via Mathlib's `CategoryTheory.Presieve.isSheaf_coverage`; the coverage generates the
restricted topology because objects of `Et(S)` are quasi-compact and étale morphisms are open,
so every jointly surjective family has a finite jointly surjective subfamily.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v' u' u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The Grothendieck topology on `Et(S)` restricted from the small étale site along the
inclusion: the coarsest topology in which a sieve is covering when its image generates a covering
sieve of the small étale site. -/
def topology : GrothendieckTopology (SmallNoetherianSeparatedEtale B S hS) :=
  (inclusion B S hS).restrictedTopology (SmallEtale.topology B S hS)

/-- The coverage of `Et(S)` by finite jointly surjective families: FK's étale coverings. -/
def finiteCoverage : Coverage (SmallNoetherianSeparatedEtale B S hS) where
  coverings X := {R | ∃ (ι : Type u) (_ : Finite ι) (V : ι → SmallNoetherianSeparatedEtale B S hS)
    (φ : ∀ i, V i ⟶ X), R = Presieve.ofArrows V φ ∧
      ⋃ i, Set.range ((toScheme B S hS).map (φ i)) = Set.univ}
  pullback := by
    rintro X Y f R ⟨ι, _, V, φ, rfl, hφ⟩
    refine ⟨Presieve.ofArrows (fun i ↦ pullbackObj f (φ i)) (fun i ↦ pullbackFst f (φ i)),
      ⟨ι, inferInstance, _, _, rfl, ?_⟩, ?_⟩
    · refine Set.eq_univ_of_forall fun y ↦ ?_
      obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp (hφ ▸ Set.mem_univ ((toScheme B S hS).map f y))
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y v hv.symm
      exact Set.mem_iUnion.mpr ⟨i, z, by rw [toScheme_map_pullbackFst]; exact hz⟩
    · rintro Z g ⟨i⟩
      exact ⟨V i, pullbackSnd f (φ i), φ i, Presieve.ofArrows.mk i,
        (isPullback_pullbackFst_pullbackSnd f (φ i)).w.symm⟩

variable {B S hS}

lemma mem_finiteCoverage_iff {X : SmallNoetherianSeparatedEtale B S hS}
    (R : Presieve X) : R ∈ finiteCoverage B S hS X ↔
      ∃ (ι : Type u) (_ : Finite ι) (V : ι → SmallNoetherianSeparatedEtale B S hS)
        (φ : ∀ i, V i ⟶ X), R = Presieve.ofArrows V φ ∧
          ⋃ i, Set.range ((toScheme B S hS).map (φ i)) = Set.univ :=
  Iff.rfl

variable (B S hS)

section LocallyNoetherian

variable [IsLocallyNoetherian S]

/-- Every point of an object of the small étale site of a locally noetherian scheme `S` lies in
the image of an object of `Et(S)`: an affine open neighbourhood of the point is étale over `S`,
hence noetherian, and separated, and lies below the size cutoff. -/
theorem exists_obj_mem_range (V : SmallEtale B S hS) (x : (SmallEtale.toScheme B S hS).obj V) :
    ∃ (U : SmallNoetherianSeparatedEtale B S hS) (g : (inclusion B S hS).obj U ⟶ V),
      x ∈ Set.range ((SmallEtale.toScheme B S hS).map g) := by
  obtain ⟨R, j, _, hj, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) (by simp)
  have hjf : Etale (j ≫ B.inclusion.map V.obj.hom) := inferInstance
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj S hS)) := ‹IsLocallyNoetherian S›
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ B.inclusion.map V.obj.hom)).trans_lt hS
  have : IsLocallyNoetherian (Spec R) :=
    LocallyOfFiniteType.isLocallyNoetherian (j ≫ B.inclusion.map V.obj.hom)
  have : IsNoetherian (Spec R) := {}
  refine ⟨mk (Spec R) hR (j ≫ B.inclusion.map V.obj.hom),
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk j) rfl), ?_⟩
  exact hj

/-- **`Et(S)` is cover dense in the small étale site** of a locally noetherian scheme. -/
instance isCoverDense_inclusion :
    (inclusion B S hS).IsCoverDense (SmallEtale.topology B S hS) where
  is_cover V := by
    choose U g hg using exists_obj_mem_range B S hS V
    refine (SmallEtale.topology B S hS).superset_covering ?_
      (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B S hS _ g
        fun x ↦ ⟨x, hg x⟩)
    rw [Sieve.generate_le_iff]
    rintro W f ⟨t⟩
    exact Presieve.in_coverByImage _ (g t)

/-- **`Et(S)` is a dense subsite of the small étale site** of a locally noetherian scheme. -/
instance isDenseSubsite_inclusion :
    (inclusion B S hS).IsDenseSubsite (topology B S hS) (SmallEtale.topology B S hS) :=
  inferInstanceAs ((inclusion B S hS).IsDenseSubsite
    ((inclusion B S hS).restrictedTopology (SmallEtale.topology B S hS)) _)

/-- **The covering sieves of `Et(S)` are the jointly surjective sieves.** -/
theorem mem_topology_iff {U : SmallNoetherianSeparatedEtale B S hS} (R : Sieve U) :
    R ∈ topology B S hS U ↔ ∀ x : (toScheme B S hS).obj U,
      ∃ (V : SmallNoetherianSeparatedEtale B S hS) (f : V ⟶ U), R f ∧
        x ∈ Set.range ((toScheme B S hS).map f) := by
  rw [topology, Functor.mem_restrictedTopology_iff]
  constructor
  · intro hR x
    obtain ⟨W, g, ⟨V, f, h, hf, rfl⟩, hx⟩ := SmallEtale.exists_mem_arrows_mem_range B S hS hR x
    obtain ⟨w, rfl⟩ := hx
    exact ⟨V, f, hf, (SmallEtale.toScheme B S hS).map h w, by
      simp only [Functor.map_comp, Scheme.Hom.comp_apply]; rfl⟩
  · intro hR
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    obtain ⟨V, f, hf, hx⟩ := hR x
    exact ⟨(inclusion B S hS).obj V, (inclusion B S hS).map f,
      Sieve.image_mem_functorPushforward _ R hf, hx⟩

/-- A jointly surjective family of morphisms of `Et(S)` into a noetherian target has a finite
jointly surjective subfamily: the images are open and the target is quasi-compact. -/
theorem exists_finite_subfamily {U : SmallNoetherianSeparatedEtale B S hS} (R : Sieve U)
    (hR : R ∈ topology B S hS U) :
    ∃ P ∈ finiteCoverage B S hS U, P ≤ R.arrows := by
  rw [mem_topology_iff] at hR
  choose V f hf hx using hR
  have hopen (x : (toScheme B S hS).obj U) : IsOpen (Set.range ((toScheme B S hS).map (f x))) :=
    ((toScheme B S hS).map (f x)).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen
    fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩
  refine ⟨Presieve.ofArrows (fun i : t ↦ V i.1) (fun i ↦ f i.1),
    ⟨t, inferInstance, _, _, rfl, ?_⟩, ?_⟩
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hy⟩
  · rintro W g ⟨i⟩
    exact hf i.1

/-- **The topology of `Et(S)` is generated by finite jointly surjective families**, FK's étale
coverings. -/
theorem topology_eq_toGrothendieck_finiteCoverage :
    topology B S hS = (finiteCoverage B S hS).toGrothendieck := by
  refine le_antisymm (fun U R hR ↦ ?_) (((Coverage.gi _).gc _ _).mpr ?_)
  · obtain ⟨P, hP, hle⟩ := exists_finite_subfamily B S hS R hR
    exact Coverage.mem_toGrothendieck_sieves_of_superset _ hle hP
  · rintro U R ⟨ι, _, V, φ, rfl, hφ⟩
    change Sieve.generate _ ∈ topology B S hS U
    rw [mem_topology_iff]
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hφ ▸ Set.mem_univ x)
    exact ⟨V i, φ i, Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i), hi⟩

/-- **Sheaves on `Et(S)` in FK's sense are the sheaves of the topology.** A presheaf of sets on
`Et(S)` is a sheaf for `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology` if and only if
it satisfies FK's sheaf axioms `AlgebraicGeometry.EtalePresheaf.IsEtaleSheaf`. -/
theorem isSheaf_iff_isEtaleSheaf (F : EtalePresheaf B S hS (Type v)) :
    Presieve.IsSheaf (topology B S hS) F ↔ EtalePresheaf.IsEtaleSheaf F := by
  rw [topology_eq_toGrothendieck_finiteCoverage, Presieve.isSheaf_coverage,
    EtalePresheaf.isEtaleSheaf_iff_bijective_toPullbackCompatible.{u}]
  constructor
  · intro h U ι V φ hcov
    have := hcov.finite
    exact (Presieve.isSheafFor_ofArrows_iff_bijective_toPullbackCompatible F φ).mp
      (h _ ⟨ι, inferInstance, V, φ, rfl, hcov.iUnion_range⟩)
  · rintro h U R ⟨ι, _, V, φ, rfl, hφ⟩
    exact (Presieve.isSheafFor_ofArrows_iff_bijective_toPullbackCompatible F φ).mpr
      (h V φ ⟨inferInstance, fun _ ↦ inferInstance, hφ⟩)

/-- The comma categories `StructuredArrow X (inclusion B S hS).op` are essentially small. -/
instance hasLimitsOfShape_structuredArrow_inclusion (A : Type u') [Category.{v'} A]
    [HasLimitsOfSize.{u, u} A] (X : (SmallEtale B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (inclusion B S hS).op) A :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- **Sheaves on `Et(S)` are sheaves on the small étale site** of a locally noetherian scheme:
restriction along the inclusion is an equivalence (the comparison lemma). -/
def sheafEquiv (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] :
    Sheaf (topology B S hS) A ≌ Sheaf (SmallEtale.topology B S hS) A :=
  Functor.IsDenseSubsite.sheafEquiv (J := topology B S hS) (K := SmallEtale.topology B S hS)
    (G := inclusion B S hS) (A := A)

/-- The inverse of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv` is restriction of
sheaves along the inclusion. -/
theorem sheafEquiv_inverse (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] :
    (sheafEquiv B S hS A).inverse =
      (inclusion B S hS).sheafPushforwardContinuous A (topology B S hS)
        (SmallEtale.topology B S hS) :=
  rfl

/-- **Sheaves on `Et(S)` are sheaves on Mathlib's small étale site** of a locally noetherian
scheme. -/
def sheafEquivEtale (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] :
    Sheaf (topology B S hS) A ≌ Sheaf S.smallEtaleTopology A :=
  (sheafEquiv B S hS A).trans (SmallEtale.sheafEquiv B S hS A)

end LocallyNoetherian

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
