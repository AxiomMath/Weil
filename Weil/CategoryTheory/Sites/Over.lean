module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.SliceSiteIso
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact

/-!
# Restriction to an object of `Et(S)` preserves injective sheaves

Let `U = (U, u)` be an object of the étale category `Et(S)` of noetherian separated étale
`S`-schemes. The functor `Et(U) ⥤ Et(S)/U`, `(V, v) ↦ ((V, u ∘ v), v)`, is an equivalence of
categories, and it identifies the étale topology of `Et(U)` with the topology of the localized
site `Et(S)/U`: in both, a sieve covers when its arrows are jointly surjective. Hence the
restriction `F ↦ F|_U` of a sheaf on `Et(S)`, `F|_U(V, v) = F(V, u ∘ v)`, is a sheaf on `Et(U)`,
and restriction of sheaves is the composite of restriction to the localized site with the
equivalence of sheaf categories induced by the equivalence of sites.

Restriction of abelian sheaves to a localized site preserves injective objects, since its left
adjoint, extension by zero, preserves monomorphisms; so does an equivalence of categories.
Therefore the restriction `I|_U` of an injective abelian sheaf `I` on `Et(S)` is an injective
abelian sheaf on `Et(U)`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.restrictSheafFunctor` — restriction of sheaves
  from `Et(S)` to `Et(U)`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology_eq_inducedTopology_toOver'` — the
  topology of `Et(U)` is induced from the localized topology on `Et(S)/U`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.restrictSheafFunctor_obj_obj` — the underlying
  presheaf of the restricted sheaf is `AlgebraicGeometry.EtalePresheaf.restrict`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.injective_restrictSheafFunctor_obj` — the
  restriction of an injective abelian sheaf is injective.

## Implementation notes

The equivalence `Et(U) ≌ Et(S)/U` is the inverse of
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.overEquivalence`
(`Weil.Defs.AlgebraicGeometry.Topologies.Etale.SliceSiteIso`), whose inverse functor is
`toOver'`.

The coefficients are abelian groups in a universe `w` with `UnivLE.{u + 1, w}`, the objects of
`Et(S)` forming a `Type (u + 1)`; this is the hypothesis under which extension by zero is known
to preserve monomorphisms (`extensionByZero_preservesMonos`). The extension-by-zero argument of
Freitag–Kiehl is carried out once, for an arbitrary site and its localization at an object.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every point of an étale `S`-scheme `W` mapping to an object `X` of `Et(S)` lies in the image
of an object of `Et(S)` mapping to `W`: an affine open neighbourhood of the point is étale over
the noetherian scheme `X`, hence noetherian, and separated. -/
theorem exists_obj_mem_range_of_hom (X : SmallNoetherianSeparatedEtale B S hS)
    {W : SmallEtale B S hS} (g : W ⟶ (inclusion B S hS).obj X)
    (w : (SmallEtale.toScheme B S hS).obj W) :
    ∃ (V : SmallNoetherianSeparatedEtale B S hS) (a : (inclusion B S hS).obj V ⟶ W),
      w ∈ Set.range ((SmallEtale.toScheme B S hS).map a) := by
  obtain ⟨R, j, _, hj, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := w) (U := ⊤) (by simp)
  have hjf : Etale (j ≫ B.inclusion.map W.obj.hom) := inferInstance
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ B.inclusion.map W.obj.hom)).trans_lt hS
  have hg : Etale ((SmallEtale.toScheme B S hS).map g) := by
    have hw : (SmallEtale.toScheme B S hS).map g ≫ B.inclusion.map X.obj.obj.hom =
        B.inclusion.map W.obj.hom := by
      change B.inclusion.map g.hom.left ≫ _ = _
      rw [← Functor.map_comp]
      exact congrArg B.inclusion.map (Over.w g.hom)
    have : Etale ((SmallEtale.toScheme B S hS).map g ≫ B.inclusion.map X.obj.obj.hom) := by
      rw [hw]; exact W.property
    have : Etale (B.inclusion.map X.obj.obj.hom) := X.obj.property
    exact Etale.of_comp _ (B.inclusion.map X.obj.obj.hom)
  have : IsLocallyNoetherian ((SmallEtale.toScheme B S hS).obj ((inclusion B S hS).obj X)) :=
    inferInstanceAs (IsLocallyNoetherian ((toScheme B S hS).obj X))
  have : IsLocallyNoetherian (Spec R) :=
    LocallyOfFiniteType.isLocallyNoetherian (j ≫ (SmallEtale.toScheme B S hS).map g)
  have : IsNoetherian (Spec R) := {}
  exact ⟨mk (Spec R) hR (j ≫ B.inclusion.map W.obj.hom),
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk j) rfl), hj⟩

/-- The inclusion of `Et(S)` into the small étale site is locally cover dense, with no hypothesis
on `S`: the objects of `Et(S)` are noetherian. -/
instance locallyCoverDense_inclusion :
    (inclusion B S hS).LocallyCoverDense (SmallEtale.topology B S hS) where
  functorPushforward_functorPullback_mem X T := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    obtain ⟨W, g, hg, w, rfl⟩ := SmallEtale.exists_mem_arrows_mem_range B S hS T.2 x
    obtain ⟨V, a, v, rfl⟩ := exists_obj_mem_range_of_hom X g w
    refine ⟨(inclusion B S hS).obj V, a ≫ g, ?_, v, by simp⟩
    exact ⟨V, ObjectProperty.homMk (a ≫ g), 𝟙 _, T.1.downward_closed hg a,
      (Category.id_comp _).symm⟩

/-- The covering sieves of `Et(S)` are the jointly surjective sieves (no hypothesis on `S`). -/
theorem mem_topology_iff_forall_exists {U : SmallNoetherianSeparatedEtale B S hS} (R : Sieve U) :
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

variable (U : SmallNoetherianSeparatedEtale B S hS)

/-- **The topology of `Et(U)` is that of the localized site `Et(S)/U`**, transported along the
equivalence `Et(U) ⥤ Et(S)/U`. -/
theorem topology_eq_inducedTopology_toOver' :
    topology B U.obj.obj.left.1 U.obj.obj.left.property =
      (toOver' U).inducedTopology ((topology B S hS).over U) := by
  ext V R
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, GrothendieckTopology.mem_over_iff,
    mem_topology_iff_forall_exists, mem_topology_iff_forall_exists]
  constructor
  · intro hR x
    obtain ⟨W, f, hf, hx⟩ := hR x
    refine ⟨(postcompose U).obj W, (postcompose U).map f, ?_, hx⟩
    exact (Sieve.overEquiv_iff _ _).mpr ⟨W, f, Over.homMk (𝟙 _)
      ((Category.id_comp _).trans (postcompose_map_comp_postcomposeToBase U f).symm), hf,
      by ext1; exact (Category.id_comp _).symm⟩
  · intro hR x
    obtain ⟨W, g, hg, hx⟩ := hR x
    obtain ⟨W', f, h, hf, hfac⟩ := (Sieve.overEquiv_iff _ _).mp hg
    refine ⟨W', f, hf, ?_⟩
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(toScheme B S hS).map h.left y, ?_⟩
    have := congrArg (fun φ => (toScheme B S hS).map (CommaMorphism.left φ) y) hfac
    simp only [Over.comp_left, Functor.map_comp, Scheme.Hom.comp_apply] at this
    exact this.symm

instance isDenseSubsite_overEquivalence_symm_inverse :
    (overEquivalence U).symm.inverse.IsDenseSubsite ((topology B S hS).over U)
      (topology B U.obj.obj.left.1 U.obj.obj.left.property) := by
  rw [topology_eq_inducedTopology_toOver']
  exact inferInstanceAs ((overEquivalence U).functor.IsDenseSubsite _
    ((overEquivalence U).inverse.inducedTopology _))

variable (A : Type*) [Category A]

/-- **Restriction of sheaves to an object of `Et(S)`.** The sheaf `F|_U` on `Et(U)`,
`F|_U(V, v) = F(V, u ∘ v)`: restriction to the localized site `Et(S)/U` followed by the
equivalence of sheaf categories induced by `Et(U) ≌ Et(S)/U`. -/
@[weil "lem_fk102_injective_restriction_injective"]
def restrictSheafFunctor :
    Sheaf (topology B S hS) A ⥤ Sheaf (topology B U.obj.obj.left.1 U.obj.obj.left.property) A :=
  (topology B S hS).overPullback A U ⋙
    ((overEquivalence U).symm.sheafCongr _ ((topology B S hS).over U) A).inverse

/-- The underlying presheaf of the restricted sheaf is the restricted presheaf. -/
@[simp]
lemma restrictSheafFunctor_obj_obj (F : Sheaf (topology B S hS) A) :
    ((restrictSheafFunctor U A).obj F).obj = EtalePresheaf.restrict F.obj U :=
  rfl

/-- **The restriction of an étale sheaf is an étale sheaf.** -/
lemma isSheaf_restrict (F : Sheaf (topology B S hS) A) :
    Presheaf.IsSheaf (topology B U.obj.obj.left.1 U.obj.obj.left.property)
      (EtalePresheaf.restrict F.obj U) :=
  ((restrictSheafFunctor U A).obj F).property

/-- **Restriction to an object of `Et(S)` preserves injective abelian sheaves.** For
`U ∈ Et(S)` and an injective object `I` of the category of abelian sheaves on `Et(S)`, the
restriction `I|_U` is an injective object of the category of abelian sheaves on `Et(U)`. -/
@[weil "lem_fk102_injective_restriction_injective"]
theorem injective_restrictSheafFunctor_obj [UnivLE.{u + 1, w}]
    [HasSheafify (topology B S hS) AddCommGrpCat.{w}]
    [∀ V, HasSheafify ((topology B S hS).over V) AddCommGrpCat.{w}]
    (I : Sheaf (topology B S hS) AddCommGrpCat.{w}) [Injective I] :
    Injective ((restrictSheafFunctor U AddCommGrpCat.{w}).obj I) := by
  have : Injective (((topology B S hS).overPullback AddCommGrpCat.{w} U).obj I) :=
    overPullback_preservesInjective _ U I
  exact Functor.PreservesInjectiveObjects.injective_obj (F :=
    ((overEquivalence U).symm.sheafCongr _ ((topology B S hS).over U)
      AddCommGrpCat.{w}).inverse) this

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
