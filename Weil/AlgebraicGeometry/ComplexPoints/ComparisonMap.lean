module

public import Weil.AlgebraicGeometry.ComplexPoints.AnalyticInverseImage
public import Weil.AlgebraicGeometry.ComplexPoints.AnalyticSpace
public import Weil.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import Weil.CategoryTheory.Abelian.EffaceableComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The comparison map between étale and analytic cohomology

Let `X` be a scheme locally of finite type over `ℂ`, `X(ℂ)` its complex points with the analytic
topology, and `ε^* : F ↦ F_an` the analytic inverse image of abelian étale sheaves, an exact
functor with `ε^* ℤ ≅ ℤ`. Applying `ε^*` to `Ext^ν(ℤ, F)` gives the comparison map
`c^ν(X, F) : H^ν_et(X, F) → H^ν(X(ℂ), F_an)`. It is natural in `F` and compatible with the
connecting maps of short exact sequences. On a constant sheaf `M` it becomes a map
`H^ν_et(X, M) → H^ν(X(ℂ), M)`, natural in `M`, so that Artin's comparison theorem for `X` follows
from bijectivity of `c^ν` on the constant sheaves with finite values.

For a morphism `f : X' ⟶ X` over `ℂ`, the analytic inverse images commute with inverse images:
`ε'^* ∘ f^* ≅ f_an^* ∘ ε^*`. By uniqueness of adjoints this is the statement for the right adjoints,
`f_* ∘ ε'_* ≅ ε_* ∘ f_an,*`. Evaluated on an étale `U → X`, it says that morphisms from the sheaf of
sections of `(U ×_X X')(ℂ) → X'(ℂ)` to a sheaf `H` on `X'(ℂ)` are the morphisms from the sheaf of
sections of `U(ℂ) → X(ℂ)` to `f_an,* H`: every section of the base change is, near each point,
the base change `w ↦ (σ (f w), w)` of a section `σ` of `U(ℂ) → X(ℂ)`, and two such presentations
agree where both apply, so the images of the `σ` glue. The mate of this isomorphism is the base
change map `ε^* f_* ⟶ f_an,* ε'^*`.

For an isomorphism `f`, both `f^*` and `f_an^*` are equivalences, so `c^ν(X', f^* F)` is bijective
exactly when `c^ν(X, F)` is; the predicate `PC(X)` (bijectivity of `c^ν(X, F)` for all torsion
`F` and all `ν`) is invariant under isomorphisms over `ℂ`.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap`: `c^ν(X, F)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.constantComparison`: `c^ν` on constant coefficients,
  `H^ν_et(X, M) → H^ν(X(ℂ), M)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.ComparisonBijectiveOn`, `PC`: bijectivity of `c^ν` on
  a class of sheaves, and on torsion sheaves.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticMap`: `f_an : X'(ℂ) → X(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.inverseImageIso`: `ε'^* ∘ f^* ≅ f_an^* ∘ ε^*`.
* `AlgebraicGeometry.Scheme.ComplexPoints.pushforwardBaseChange`: `ε^* f_* ⟶ f_an,* ε'^*`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_naturality`,
  `comparisonMap_comp_extClass`: naturality and compatibility with connecting maps.
* `AlgebraicGeometry.Scheme.ComplexPoints.constantComparison_naturality`,
  `artinComparisonAt_of_bijective`: Artin's comparison for `X` from bijectivity of `c^ν` on
  finite constant sheaves.
* `AlgebraicGeometry.Scheme.ComplexPoints.baseChangeSections_comp_bijective`: the sheaf of
  sections of a base change is the inverse image of the sheaf of sections.
* `AlgebraicGeometry.Scheme.ComplexPoints.directImageBaseChangeIso`: `f_* ∘ ε'_* ≅ ε_* ∘ f_an,*`.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_bijective_iff_of_isIso`,
  `pc_iff_of_iso`: invariance under isomorphisms.
* `CategoryTheory.Functor.mapExtAddHom_bijective_iff_of_natIso`: bijectivity on `Ext` transports
  along a square of exact functors whose two other sides are equivalences.

## Implementation notes

The comparison map is `Functor.mapExtOfIso` of the exact functor `ε^*`, with the isomorphism
`ε^* ℤ ≅ ℤ` of `constantSheafIso`; no injective resolutions and no derived categories are used.
The étale inverse image is `Stacks.EtaleCohomology.etaleAbelianInverseImage` and the analytic one
`TopCat.Sheaf.pullback`, both on sheaves with values in `AddCommGrpCat.{1}`.

## References

* [SGA 4, Exposé XI, §4 and Exposé XVI, §4]
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

/-! ### Bijectivity of maps on `Ext` along exact functors -/

namespace CategoryTheory.Functor

open Abelian

universe w

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {ℬ : Type*} [Category ℬ] [Abelian ℬ]
  {𝒜' : Type*} [Category 𝒜'] [Abelian 𝒜'] {ℬ' : Type*} [Category ℬ'] [Abelian ℬ']
  [HasExt.{w} 𝒜] [HasExt.{w} ℬ] [HasExt.{w} 𝒜'] [HasExt.{w} ℬ']

/-- Bijectivity of `ε.mapExtAddHom A F n` only depends on `A` up to isomorphism. -/
theorem mapExtAddHom_bijective_iff_of_iso (ε : 𝒜 ⥤ ℬ) [ε.Additive] [PreservesFiniteLimits ε]
    [PreservesFiniteColimits ε] {A A' : 𝒜} (i : A ≅ A') (F : 𝒜) (n : ℕ) :
    Function.Bijective (ε.mapExtAddHom A F n) ↔ Function.Bijective (ε.mapExtAddHom A' F n) := by
  have preA : Function.Bijective (fun y : Ext.{w} A' F n => (Ext.mk₀ i.hom).comp y (zero_add n)) :=
    Function.bijective_iff_has_inverse.2 ⟨fun y => (Ext.mk₀ i.inv).comp y (zero_add n),
      fun y => by
        simp only
        rw [Ext.mk₀_comp_mk₀_assoc, i.inv_hom_id, Ext.mk₀_id_comp],
      fun y => by
        simp only
        rw [Ext.mk₀_comp_mk₀_assoc, i.hom_inv_id, Ext.mk₀_id_comp]⟩
  have preB : Function.Bijective (fun y : Ext.{w} (ε.obj A') (ε.obj F) n =>
      (Ext.mk₀ (ε.map i.hom)).comp y (zero_add n)) :=
    Function.bijective_iff_has_inverse.2 ⟨fun y => (Ext.mk₀ (ε.map i.inv)).comp y (zero_add n),
      fun y => by
        simp only
        rw [Ext.mk₀_comp_mk₀_assoc, ← ε.map_comp, i.inv_hom_id, ε.map_id, Ext.mk₀_id_comp],
      fun y => by
        simp only
        rw [Ext.mk₀_comp_mk₀_assoc, ← ε.map_comp, i.hom_inv_id, ε.map_id, Ext.mk₀_id_comp]⟩
  have hsq : (fun y : Ext.{w} (ε.obj A') (ε.obj F) n => (Ext.mk₀ (ε.map i.hom)).comp y
      (zero_add n)) ∘ ε.mapExtAddHom A' F n =
      ε.mapExtAddHom A F n ∘ (fun y : Ext.{w} A' F n => (Ext.mk₀ i.hom).comp y (zero_add n)) := by
    funext y
    simp only [Function.comp_apply, mapExtAddHom_apply, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀]
  constructor
  · intro h
    exact (Function.Bijective.of_comp_iff' preB _).1 (hsq ▸ h.comp preA)
  · intro h
    exact (Function.Bijective.of_comp_iff _ preA).1 (hsq ▸ preB.comp h)

/-- Postcomposition `Ext^n(B, C) → Ext^n(B, C')` with an isomorphism `C ≅ C'` is bijective. -/
theorem bijective_extComp_mk₀_hom {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt.{w} 𝒞]
    {B C C' : 𝒞} (j : C ≅ C') (n : ℕ) :
    Function.Bijective (fun y : Ext.{w} B C n => y.comp (Ext.mk₀ j.hom) (add_zero n)) :=
  Function.bijective_iff_has_inverse.2 ⟨fun y => y.comp (Ext.mk₀ j.inv) (add_zero n),
    fun y => by
      simp only
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, j.hom_inv_id, Ext.comp_mk₀_id],
    fun y => by
      simp only
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, j.inv_hom_id, Ext.comp_mk₀_id]⟩

/-- Precomposition `Ext^n(B', C) → Ext^n(B, C)` with an isomorphism `B ≅ B'` is bijective. -/
theorem bijective_mk₀_hom_extComp {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt.{w} 𝒞]
    {B B' C : 𝒞} (j : B ≅ B') (n : ℕ) :
    Function.Bijective (fun y : Ext.{w} B' C n => (Ext.mk₀ j.hom).comp y (zero_add n)) :=
  Function.bijective_iff_has_inverse.2 ⟨fun y => (Ext.mk₀ j.inv).comp y (zero_add n),
    fun y => by
      simp only
      rw [Ext.mk₀_comp_mk₀_assoc, j.inv_hom_id, Ext.mk₀_id_comp],
    fun y => by
      simp only
      rw [Ext.mk₀_comp_mk₀_assoc, j.hom_inv_id, Ext.mk₀_id_comp]⟩

/-- **Transport of bijectivity on `Ext` along a square of exact functors.** If `Φ ⋙ ε' ≅ ε ⋙ Ψ`
with `Φ` and `Ψ` equivalences, then `ε'` is bijective on `Ext^n(Φ A, Φ F)` exactly when `ε` is
bijective on `Ext^n(A, F)`. -/
theorem mapExtAddHom_bijective_iff_of_natIso [EnoughInjectives 𝒜] [EnoughInjectives ℬ]
    (Φ : 𝒜 ⥤ 𝒜') (hΦ' : Φ.IsEquivalence)
    (ε : 𝒜 ⥤ ℬ) [ε.Additive] [PreservesFiniteLimits ε] [PreservesFiniteColimits ε]
    (ε' : 𝒜' ⥤ ℬ') [ε'.Additive] [PreservesFiniteLimits ε'] [PreservesFiniteColimits ε']
    (Ψ : ℬ ⥤ ℬ') (hΨ' : Ψ.IsEquivalence) (β : Φ ⋙ ε' ≅ ε ⋙ Ψ) (A F : 𝒜) (n : ℕ) :
    Function.Bijective (ε'.mapExtAddHom.{w, w} (Φ.obj A) (Φ.obj F) n) ↔
      Function.Bijective (ε.mapExtAddHom.{w, w} A F n) := by
  have := hΦ'
  have := hΨ'
  have : Φ.Additive := Functor.additive_of_preserves_binary_products _
  have : Ψ.Additive := Functor.additive_of_preserves_binary_products _
  have hΦ : ∀ A F n, Function.Bijective (Φ.mapExtAddHom.{w, w} A F n) := fun A F n =>
    Functor.mapExt_bijective_of_preservesInjectiveObjects _ A F n
  have hΨ : ∀ A F n, Function.Bijective (Ψ.mapExtAddHom.{w, w} A F n) := fun A F n =>
    Functor.mapExt_bijective_of_preservesInjectiveObjects _ A F n
  have h₁ : ⇑(ε'.mapExtAddHom.{w, w} (Φ.obj A) (Φ.obj F) n) ∘ ⇑(Φ.mapExtAddHom.{w, w} A F n) =
      fun e => e.mapExactFunctor (Φ ⋙ ε') := by
    funext e
    exact Stacks.ExtFunctorial.mapExactFunctor_comp_functor Φ ε' A n e
  have h₃ : ⇑(Ψ.mapExtAddHom.{w, w} (ε.obj A) (ε.obj F) n) ∘ ⇑(ε.mapExtAddHom.{w, w} A F n) =
      fun e => e.mapExactFunctor (ε ⋙ Ψ) := by
    funext e
    exact Stacks.ExtFunctorial.mapExactFunctor_comp_functor ε Ψ A n e
  have h₂ : (fun y => (Ext.mk₀ (β.app A).hom).comp y (zero_add n)) ∘
      (fun e : Ext.{w} A F n => e.mapExactFunctor (ε ⋙ Ψ)) =
      (fun z => z.comp (Ext.mk₀ (β.app F).hom) (add_zero n)) ∘
      (fun e : Ext.{w} A F n => e.mapExactFunctor (Φ ⋙ ε')) := by
    funext e
    exact Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor β.hom A n e
  have hM : Function.Bijective (fun e : Ext.{w} A F n => e.mapExactFunctor (Φ ⋙ ε')) ↔
      Function.Bijective (fun e : Ext.{w} A F n => e.mapExactFunctor (ε ⋙ Ψ)) := by
    rw [← Function.Bijective.of_comp_iff' (bijective_mk₀_hom_extComp (β.app A) n), h₂,
      Function.Bijective.of_comp_iff' (bijective_extComp_mk₀_hom (β.app F) n)]
  rw [← Function.Bijective.of_comp_iff _ (hΦ A F n), h₁, hM, ← h₃,
    Function.Bijective.of_comp_iff' (hΨ _ _ n)]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-- Base change of étale schemes along a morphism of schemes. -/
local notation "𝔅" => Stacks.EtaleCohomology.smallEtaleBaseChange

/-- `H^n(-)` sends isomorphisms of sheaves to bijections. -/
theorem _root_.CategoryTheory.Sheaf.H.map_bijective_of_isIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{1}]
    [HasExt.{1} (Sheaf J AddCommGrpCat.{1})] {F G : Sheaf J AddCommGrpCat.{1}} (f : F ⟶ G)
    [IsIso f] (n : ℕ) : Function.Bijective (Sheaf.H.map f n) :=
  Function.bijective_iff_has_inverse.2 ⟨Sheaf.H.map (inv f) n,
    fun x => by rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply],
    fun x => by rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]⟩

section Comparison

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

/-- The comparison map `c^n(Y, F) : H^n_et(Y, F) → H^n(Y(ℂ), F_an)`. -/
noncomputable def comparisonMap (F : EtSheaf Y) (n : ℕ) :
    Sheaf.H.{1} F n →+ Sheaf.H.{1} ((analyticInverseImage y).obj F) n :=
  (analyticInverseImage y).mapExtOfIso
    ((constantSheafIso y).app (AddCommGrpCat.of (ULift ℤ))) F n

theorem comparisonMap_apply (F : EtSheaf Y) (n : ℕ) (x : Sheaf.H.{1} F n) :
    comparisonMap y F n x =
      (Ext.mk₀ ((constantSheafIso y).app (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (x.mapExactFunctor (analyticInverseImage y)) (zero_add n) := rfl

theorem comparisonMap_naturality {F G : EtSheaf Y} (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H.{1} F n) :
    comparisonMap y G n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((analyticInverseImage y).map φ) n (comparisonMap y F n x) := by
  rw [comparisonMap_apply, comparisonMap_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ _ _ (by lia)).symm

theorem comparisonMap_comp_extClass {S : ShortComplex (EtSheaf Y)} (hS : S.ShortExact) (n : ℕ)
    (x : Sheaf.H.{1} S.X₃ n) :
    comparisonMap y S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparisonMap y S.X₃ n x).comp (hS.map_of_exact (analyticInverseImage y)).extClass rfl := by
  rw [comparisonMap_apply, comparisonMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ _ _ (by lia)).symm

/-- The comparison map on constant coefficients `M`, from `H^ν_et(Y, M)` to `H^ν(Y(ℂ), M)`:
`comparisonMap` followed by `ε^* M ≅ M` and the universe bridge `analyticConstantAddEquiv`. -/
noncomputable def constantComparison (M : AddCommGrpCat.{0}) (ν : ℕ) :
    etaleCohomologyConstant Y M ν →+ analyticCohomologyConstant y M ν :=
  ((analyticConstantAddEquiv y M ν).symm.toAddMonoidHom.comp
    (Sheaf.H.map ((constantSheafIso y).hom.app (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν)).comp
    (comparisonMap y _ ν)

theorem constantComparison_apply (M : AddCommGrpCat.{0}) (ν : ℕ)
    (x : etaleCohomologyConstant Y M ν) :
    constantComparison y M ν x = (analyticConstantAddEquiv y M ν).symm
      (Sheaf.H.map ((constantSheafIso y).hom.app (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν
        (comparisonMap y ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
          (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν x)) := rfl

theorem constantComparison_naturality {M N : AddCommGrpCat.{0}} (g : M ⟶ N) (ν : ℕ)
    (x : etaleCohomologyConstant Y M ν) :
    constantComparison y N ν (etaleCohomologyConstantMap Y g ν x) =
      analyticCohomologyConstantMap y g ν (constantComparison y M ν x) := by
  have key : ∀ z : Sheaf.H.{1} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν,
      Sheaf.H.map ((constantSheafIso y).hom.app (AddCommGrpCat.uliftFunctor.{1, 0}.obj N)) ν
        (comparisonMap y _ ν (Sheaf.H.map ((constantSheaf Y.smallEtaleTopology
          AddCommGrpCat.{1}).map (AddCommGrpCat.uliftFunctor.{1, 0}.map g)) ν z)) =
      Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology (analyticSpace y))
        AddCommGrpCat.{1}).map (AddCommGrpCat.uliftFunctor.{1, 0}.map g)) ν
        (Sheaf.H.map ((constantSheafIso y).hom.app (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν
          (comparisonMap y _ ν z)) := by
    intro z
    rw [comparisonMap_naturality, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
    congr 2
    exact (constantSheafIso y).hom.naturality (AddCommGrpCat.uliftFunctor.{1, 0}.map g)
  apply (analyticConstantAddEquiv y N ν).injective
  rw [analyticConstantAddEquiv_naturality, constantComparison_apply, constantComparison_apply,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact key x

theorem constantComparison_bijective_iff (M : AddCommGrpCat.{0}) (ν : ℕ) :
    Function.Bijective (constantComparison y M ν) ↔
      Function.Bijective (comparisonMap y
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
          (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν) := by
  have h2 : Function.Bijective (fun z => (analyticConstantAddEquiv y M ν).symm
      (Sheaf.H.map ((constantSheafIso y).hom.app (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν z)) :=
    (analyticConstantAddEquiv y M ν).symm.bijective.comp (Sheaf.H.map_bijective_of_isIso _ ν)
  exact Function.Bijective.of_comp_iff' h2 (comparisonMap y _ ν)

/-- **Artin's comparison for `Y` from bijectivity of `c` on finite constant sheaves.** -/
theorem artinComparisonAt_of_bijective
    (h : ∀ (M : AddCommGrpCat.{0}) [Finite M] (ν : ℕ),
      Function.Bijective (comparisonMap y
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
          (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν)) :
    ArtinComparisonAt y := fun ν =>
  ⟨fun M _ => AddEquiv.ofBijective (constantComparison y M ν)
      ((constantComparison_bijective_iff y M ν).2 (h M ν)),
    fun _ _ _ _ g x => constantComparison_naturality y g ν x⟩

end Comparison

/-! ### Complex points of base changes of étale schemes -/

section BaseChangePoints

set_option backward.isDefEq.respectTransparency false

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ)) (f : X' ⟶ X)
  (hf : f ≫ x = x')

/-- The map of complex points `X'(ℂ) → X(ℂ)` induced by `f` over `ℂ`, on the lifted spaces. -/
noncomputable def analyticMap : analyticSpace x' ⟶ analyticSpace x :=
  TopCat.ofHom ⟨fun p => ULift.up (map f hf p.down),
    continuous_uliftUp.comp ((continuous_map f hf).comp continuous_uliftDown)⟩

@[simp]
theorem analyticMap_apply (p : analyticSpace x') :
    analyticMap x x' f hf p = ULift.up (map f hf p.down) := rfl

include hf in
theorem baseChange_fst_comp (U : X.Etale) :
    pullback.fst U.hom f ≫ U.hom ≫ x = ((𝔅 f).obj U).hom ≫ x' := by
  change pullback.fst U.hom f ≫ U.hom ≫ x = pullback.snd U.hom f ≫ x'
  rw [pullback.condition_assoc, hf]

/-- The projection `(U ×_X X')(ℂ) → U(ℂ)`. -/
noncomputable def baseChangeFst (U : X.Etale) :
    ComplexPoints (((𝔅 f).obj U).hom ≫ x') → ComplexPoints (U.hom ≫ x) :=
  map (pullback.fst U.hom f) (baseChange_fst_comp x x' f hf U)

theorem continuous_baseChangeFst (U : X.Etale) : Continuous (baseChangeFst x x' f hf U) :=
  continuous_map _ _

theorem etaleMap_baseChangeFst (U : X.Etale)
    (z : ComplexPoints (((𝔅 f).obj U).hom ≫ x')) :
    etaleMap x U (baseChangeFst x x' f hf U z) =
      map f hf (etaleMap x' ((𝔅 f).obj U) z) :=
  ext (by
    change (z.hom ≫ pullback.fst U.hom f) ≫ U.hom = (z.hom ≫ pullback.snd U.hom f) ≫ f
    rw [Category.assoc, Category.assoc, pullback.condition])

/-- A complex point of `U` and a complex point of `X'` over the same point of `X` form a complex
point of `U ×_X X'`. -/
noncomputable def baseChangePoint (U : X.Etale) (a : ComplexPoints (U.hom ≫ x))
    (b : ComplexPoints x') (h : etaleMap x U a = map f hf b) :
    ComplexPoints (((𝔅 f).obj U).hom ≫ x') :=
  ⟨pullback.lift a.hom b.hom (congrArg ComplexPoints.hom h), by
    change pullback.lift a.hom b.hom _ ≫ pullback.snd U.hom f ≫ x' = _
    rw [pullback.lift_snd_assoc]
    exact b.2⟩

@[simp]
theorem baseChangeFst_baseChangePoint (U : X.Etale) (a : ComplexPoints (U.hom ≫ x))
    (b : ComplexPoints x') (h : etaleMap x U a = map f hf b) :
    baseChangeFst x x' f hf U (baseChangePoint x x' f hf U a b h) = a :=
  ext (pullback.lift_fst _ _ _)

@[simp]
theorem etaleMap_baseChangePoint (U : X.Etale) (a : ComplexPoints (U.hom ≫ x))
    (b : ComplexPoints x') (h : etaleMap x U a = map f hf b) :
    etaleMap x' ((𝔅 f).obj U) (baseChangePoint x x' f hf U a b h) = b :=
  ext (pullback.lift_snd _ _ _)

theorem baseChange_ext (U : X.Etale)
    {z z' : ComplexPoints (((𝔅 f).obj U).hom ≫ x')}
    (h₁ : baseChangeFst x x' f hf U z = baseChangeFst x x' f hf U z')
    (h₂ : etaleMap x' ((𝔅 f).obj U) z =
      etaleMap x' ((𝔅 f).obj U) z') : z = z' :=
  ext (pullback.hom_ext (congrArg ComplexPoints.hom h₁) (congrArg ComplexPoints.hom h₂))

omit x x' in
theorem baseChangeMap_left {U V : X.Etale} (g : U ⟶ V) :
    ((𝔅 f).map g).left =
      pullback.map _ _ _ _ g.left (𝟙 _) (𝟙 _) (by simp [MorphismProperty.Over.w g])
        (by simp) := rfl

theorem baseChangeFst_etaleHomMap {U V : X.Etale} (g : U ⟶ V)
    (z : ComplexPoints (((𝔅 f).obj U).hom ≫ x')) :
    baseChangeFst x x' f hf V (etaleHomMap x' ((𝔅 f).map g) z) =
      etaleHomMap x g (baseChangeFst x x' f hf U z) :=
  ext (by
    change (z.hom ≫ ((𝔅 f).map g).left) ≫ pullback.fst V.hom f =
      (z.hom ≫ pullback.fst U.hom f) ≫ g.left
    rw [baseChangeMap_left, Category.assoc, pullback.lift_fst, Category.assoc])

theorem etaleHomMap_baseChangePoint {U V : X.Etale} (g : U ⟶ V) (a : ComplexPoints (U.hom ≫ x))
    (b : ComplexPoints x') (h : etaleMap x U a = map f hf b) :
    etaleHomMap x' ((𝔅 f).map g) (baseChangePoint x x' f hf U a b h) =
      baseChangePoint x x' f hf V (etaleHomMap x g a) b (by rw [etaleMap_etaleHomMap, h]) :=
  baseChange_ext x x' f hf V (by simp [baseChangeFst_etaleHomMap])
    (by rw [etaleMap_etaleHomMap, etaleMap_baseChangePoint, etaleMap_baseChangePoint])

/-- **The pair of two continuous maps over the same map to `X(ℂ)` is continuous** into
`(U ×_X X')(ℂ)`: near a point it is the local inverse of the projection to `X'(ℂ)`, which is
étale. -/
theorem continuous_baseChangePoint [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (U : X.Etale)
    {V : Type*} [TopologicalSpace V] {τ₁ : V → ComplexPoints (U.hom ≫ x)}
    {τ₂ : V → ComplexPoints x'} (hτ₁ : Continuous τ₁) (hτ₂ : Continuous τ₂)
    (h : ∀ v, etaleMap x U (τ₁ v) = map f hf (τ₂ v)) :
    Continuous fun v => baseChangePoint x x' f hf U (τ₁ v) (τ₂ v) (h v) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨O, τ, hO, hv₀O, hτv₀, hτO, hτ⟩ := exists_local_lift_of_isLocalHomeomorph
    (isLocalHomeomorph_etaleMap x' ((𝔅 f).obj U)) hτ₂
    (etaleMap_baseChangePoint x x' f hf U _ _ (h v₀))
  have hOn : O ∈ nhds v₀ := hO.mem_nhds hv₀O
  have hτc : ContinuousAt τ v₀ := hτO.continuousAt hOn
  have e₁ : (fun v => baseChangeFst x x' f hf U (τ v)) =ᶠ[nhds v₀] τ₁ := by
    refine eventuallyEq_of_isLocalHomeomorph (isLocalHomeomorph_etaleMap x U)
      ((continuous_baseChangeFst x x' f hf U).continuousAt.comp hτc) hτ₁.continuousAt ?_ ?_
    · filter_upwards [hOn] with w hw
      rw [etaleMap_baseChangeFst, hτ w hw, h w]
    · rw [hτv₀, baseChangeFst_baseChangePoint]
  have e : (fun v => baseChangePoint x x' f hf U (τ₁ v) (τ₂ v) (h v)) =ᶠ[nhds v₀] τ := by
    filter_upwards [hOn, e₁] with w hw hw₁
    exact baseChange_ext x x' f hf U (by rw [baseChangeFst_baseChangePoint, ← hw₁])
      (by rw [etaleMap_baseChangePoint, hτ w hw])
  exact hτc.congr e.symm

end BaseChangePoints

/-! ### Where two sections agree -/

section Agree

variable {Z : Scheme.{0}} (z : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType z] (U : Z.Etale)

/-- Two continuous lifts through a local homeomorphism with the same image agree on an open
set. -/
theorem isOpen_setOf_eq_of_isLocalHomeomorph {E B V : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace V] {q : E → B} (hq : IsLocalHomeomorph q)
    {σ₁ σ₂ : V → E} (h₁ : Continuous σ₁) (h₂ : Continuous σ₂) (h : ∀ v, q (σ₁ v) = q (σ₂ v)) :
    IsOpen {v | σ₁ v = σ₂ v} :=
  isOpen_iff_mem_nhds.2 fun _ hv => eventuallyEq_of_isLocalHomeomorph hq h₁.continuousAt
    h₂.continuousAt (Filter.Eventually.of_forall h) hv

/-- The open set where two sections of `U(ℂ) → Z(ℂ)` agree. -/
def agreeOpens {V₁ V₂ : TopologicalSpace.Opens (analyticSpace z)}
    (σ₁ : (sectionsPresheaf z U).obj (op V₁)) (σ₂ : (sectionsPresheaf z U).obj (op V₂)) :
    TopologicalSpace.Opens (analyticSpace z) where
  carrier := {w | ∃ h : w ∈ V₁ ⊓ V₂, σ₁.1 ⟨w, h.1⟩ = σ₂.1 ⟨w, h.2⟩}
  is_open' := by
    let S := V₁ ⊓ V₂
    have hS : IsOpen {a : S | (σ₁.1 ⟨a.1, a.2.1⟩).down = (σ₂.1 ⟨a.1, a.2.2⟩).down} :=
      isOpen_setOf_eq_of_isLocalHomeomorph (isLocalHomeomorph_etaleMap z U)
        (continuous_uliftDown.comp (σ₁.2.1.comp (continuous_subtype_val.subtype_mk _)))
        (continuous_uliftDown.comp (σ₂.2.1.comp (continuous_subtype_val.subtype_mk _)))
        (fun a => by rw [σ₁.2.2, σ₂.2.2])
    refine isOpen_iff_mem_nhds.2 fun w ⟨h, hw⟩ => ?_
    have h' : ∀ᶠ a in nhds (⟨w, h⟩ : S),
        (σ₁.1 ⟨a.1, a.2.1⟩).down = (σ₂.1 ⟨a.1, a.2.2⟩).down :=
      hS.mem_nhds (congrArg ULift.down hw)
    rw [nhds_subtype_eq_comap, Filter.eventually_comap] at h'
    filter_upwards [h', S.isOpen.mem_nhds h] with b hb hbS
    exact ⟨hbS, ULift.ext _ _ (hb ⟨b, hbS⟩ rfl)⟩

theorem agreeOpens_le_left {V₁ V₂ : TopologicalSpace.Opens (analyticSpace z)}
    (σ₁ : (sectionsPresheaf z U).obj (op V₁)) (σ₂ : (sectionsPresheaf z U).obj (op V₂)) :
    agreeOpens z U σ₁ σ₂ ≤ V₁ := fun _ ⟨h, _⟩ => h.1

theorem agreeOpens_le_right {V₁ V₂ : TopologicalSpace.Opens (analyticSpace z)}
    (σ₁ : (sectionsPresheaf z U).obj (op V₁)) (σ₂ : (sectionsPresheaf z U).obj (op V₂)) :
    agreeOpens z U σ₁ σ₂ ≤ V₂ := fun _ ⟨h, _⟩ => h.2

theorem mem_agreeOpens_iff {V₁ V₂ : TopologicalSpace.Opens (analyticSpace z)}
    (σ₁ : (sectionsPresheaf z U).obj (op V₁)) (σ₂ : (sectionsPresheaf z U).obj (op V₂))
    (w : analyticSpace z) :
    w ∈ agreeOpens z U σ₁ σ₂ ↔ ∃ h : w ∈ V₁ ⊓ V₂, σ₁.1 ⟨w, h.1⟩ = σ₂.1 ⟨w, h.2⟩ := Iff.rfl

theorem agreeOpens_spec {V₁ V₂ : TopologicalSpace.Opens (analyticSpace z)}
    (σ₁ : (sectionsPresheaf z U).obj (op V₁)) (σ₂ : (sectionsPresheaf z U).obj (op V₂))
    (w : agreeOpens z U σ₁ σ₂) :
    σ₁.1 ⟨w.1, agreeOpens_le_left z U σ₁ σ₂ w.2⟩ = σ₂.1 ⟨w.1, agreeOpens_le_right z U σ₁ σ₂ w.2⟩ :=
  w.2.2

end Agree

/-! ### Sections of base changes -/

section BaseChangeSections

set_option backward.isDefEq.respectTransparency false

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ)) (f : X' ⟶ X)
  (hf : f ≫ x = x') [LocallyOfFiniteType x] [LocallyOfFiniteType x']

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
theorem etaleMap_section_analyticMap (U : X.Etale) (W : TopologicalSpace.Opens (analyticSpace x))
    (σ : (sectionsPresheaf x U).obj (op W)) (w : (Opens.map (analyticMap x x' f hf)).obj W) :
    etaleMap x U (σ.1 ⟨analyticMap x x' f hf w.1, w.2⟩).down = map f hf w.1.down :=
  σ.2.2 _

/-- A section `σ` of `U(ℂ) → X(ℂ)` over `W` gives the section `w ↦ (σ (f w), w)` of
`(U ×_X X')(ℂ) → X'(ℂ)` over `f⁻¹ W`. -/
noncomputable def baseChangeSection (U : X.Etale) (W : TopologicalSpace.Opens (analyticSpace x))
    (σ : (sectionsPresheaf x U).obj (op W)) :
    (sectionsPresheaf x' ((𝔅 f).obj U)).obj
      (op ((Opens.map (analyticMap x x' f hf)).obj W)) :=
  ⟨fun w => ULift.up (baseChangePoint x x' f hf U (σ.1 ⟨analyticMap x x' f hf w.1, w.2⟩).down
      w.1.down (etaleMap_section_analyticMap x x' f hf U W σ w)),
    continuous_uliftUp.comp (continuous_baseChangePoint x x' f hf U
      (continuous_uliftDown.comp (σ.2.1.comp
        (((analyticMap x x' f hf).hom.continuous.comp continuous_subtype_val).subtype_mk _)))
      (continuous_uliftDown.comp continuous_subtype_val)
      (fun w => etaleMap_section_analyticMap x x' f hf U W σ w)),
    fun w => etaleMap_baseChangePoint x x' f hf U _ _
      (etaleMap_section_analyticMap x x' f hf U W σ w)⟩

@[simp]
theorem baseChangeSection_apply (U : X.Etale) (W : TopologicalSpace.Opens (analyticSpace x))
    (σ : (sectionsPresheaf x U).obj (op W)) (w : (Opens.map (analyticMap x x' f hf)).obj W) :
    (baseChangeSection x x' f hf U W σ).1 w = ULift.up (baseChangePoint x x' f hf U
      (σ.1 ⟨analyticMap x x' f hf w.1, w.2⟩).down w.1.down
        (etaleMap_section_analyticMap x x' f hf U W σ w)) := by
  unfold baseChangeSection
  rfl

/-- `σ ↦ (σ ∘ f, id)`, as a morphism of sheaves `Φ U ⟶ f_* Φ (U ×_X X')`. -/
noncomputable def baseChangeSections (U : X.Etale) :
    (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1) (analyticMap x x' f hf)).obj
      ((sectionsFunctor x').obj ((𝔅 f).obj U)) :=
  ObjectProperty.homMk
    { app W := ↾(baseChangeSection x x' f hf U W.unop)
      naturality _ _ _ := by
        ext σ
        exact Subtype.ext (funext fun _ => rfl) }

theorem baseChangeSections_app (U : X.Etale) (W : (TopologicalSpace.Opens (analyticSpace x))ᵒᵖ)
    (σ : (sectionsPresheaf x U).obj W) :
    (baseChangeSections x x' f hf U).hom.app W σ = baseChangeSection x x' f hf U W.unop σ := rfl

theorem baseChangeSections_naturality {U V : X.Etale} (g : U ⟶ V) :
    (sectionsFunctor x).map g ≫ baseChangeSections x x' f hf V =
      baseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward (Type 1)
        (analyticMap x x' f hf)).map ((sectionsFunctor x').map ((𝔅 f).map g)) := by
  ext W σ
  refine Subtype.ext (funext fun w => ULift.ext _ _ ?_)
  exact (etaleHomMap_baseChangePoint x x' f hf g (σ.1 ⟨analyticMap x x' f hf w.1, w.2⟩).down
    w.1.down (σ.2.2 _)).symm

/-! ### Morphisms out of the sheaf of sections of a base change -/

section Bijective

variable (U : X.Etale) {H : Sheaf (Opens.grothendieckTopology (analyticSpace x')) (Type 1)}

/-- The open set on which a section `τ` of `(U ×_X X')(ℂ) → X'(ℂ)` is the base change of a
section `σ` of `U(ℂ) → X(ℂ)`. -/
noncomputable abbrev chartOpens {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    {W : TopologicalSpace.Opens (analyticSpace x)} (σ : (sectionsPresheaf x U).obj (op W)) :
    TopologicalSpace.Opens (analyticSpace x') :=
  agreeOpens x' ((𝔅 f).obj U) τ (baseChangeSection x x' f hf U W σ)

/-- Every section of `(U ×_X X')(ℂ) → X'(ℂ)` is, near each point, the base change of a section
of `U(ℂ) → X(ℂ)`. -/
theorem exists_mem_chartOpens {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    (v : analyticSpace x') (hv : v ∈ V) :
    ∃ (W : TopologicalSpace.Opens (analyticSpace x)) (σ : (sectionsPresheaf x U).obj (op W)),
      v ∈ chartOpens x x' f hf U τ σ := by
  obtain ⟨φ, haφ, hφ⟩ := isLocalHomeomorph_etaleMap x U
    (baseChangeFst x x' f hf U (τ.1 ⟨v, hv⟩).down)
  let W : TopologicalSpace.Opens (analyticSpace x) :=
    ⟨ULift.down ⁻¹' φ.target, φ.open_target.preimage continuous_uliftDown⟩
  let σ : (sectionsPresheaf x U).obj (op W) :=
    ⟨fun w => ULift.up (φ.symm w.1.down),
      continuous_uliftUp.comp (φ.continuousOn_symm.comp_continuous
        (continuous_uliftDown.comp continuous_subtype_val) fun w => w.2),
      fun w => by
        change etaleMap x U (φ.symm w.1.down) = w.1.down
        rw [hφ]
        exact φ.right_inv w.2⟩
  have hfv : map f hf v.down = φ (baseChangeFst x x' f hf U (τ.1 ⟨v, hv⟩).down) := by
    rw [← hφ, etaleMap_baseChangeFst, τ.2.2]
  have hW : analyticMap x x' f hf v ∈ W := by
    change map f hf v.down ∈ φ.target
    rw [hfv]
    exact φ.map_source haφ
  refine ⟨W, σ, ⟨hv, hW⟩, ULift.ext _ _ (baseChange_ext x x' f hf U ?_ ?_)⟩
  · rw [baseChangeSection_apply, baseChangeFst_baseChangePoint]
    change _ = φ.symm (map f hf v.down)
    rw [hfv, φ.left_inv haφ]
  · rw [baseChangeSection_apply, etaleMap_baseChangePoint]
    exact τ.2.2 _

/-- Where `τ` is the base change of both `σ₁` and `σ₂`, the images of `σ₁` and `σ₂` under a
morphism `Φ U ⟶ f_* H` agree. -/
theorem chartOpens_compat
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    {W₁ W₂ : TopologicalSpace.Opens (analyticSpace x)} (σ₁ : (sectionsPresheaf x U).obj (op W₁))
    (σ₂ : (sectionsPresheaf x U).obj (op W₂)) :
    H.obj.map (homOfLE (inf_le_left.trans (agreeOpens_le_right x' _ τ _)) :
        chartOpens x x' f hf U τ σ₁ ⊓ chartOpens x x' f hf U τ σ₂ ⟶
          (Opens.map (analyticMap x x' f hf)).obj W₁).op (ψ.hom.app (op W₁) σ₁) =
      H.obj.map (homOfLE (inf_le_right.trans (agreeOpens_le_right x' _ τ _)) :
        chartOpens x x' f hf U τ σ₁ ⊓ chartOpens x x' f hf U τ σ₂ ⟶
          (Opens.map (analyticMap x x' f hf)).obj W₂).op (ψ.hom.app (op W₂) σ₂) := by
  let A := agreeOpens x U σ₁ σ₂
  have hle : chartOpens x x' f hf U τ σ₁ ⊓ chartOpens x x' f hf U τ σ₂ ≤
      (Opens.map (analyticMap x x' f hf)).obj A := by
    intro w hw
    obtain ⟨⟨h₁, e₁⟩, ⟨h₂, e₂⟩⟩ := hw
    refine ⟨⟨h₁.2, h₂.2⟩, ULift.ext _ _ ?_⟩
    have := congrArg (fun t => baseChangeFst x x' f hf U t.down) (e₁.symm.trans e₂)
    simpa only [baseChangeSection_apply, baseChangeFst_baseChangePoint] using this
  have hres : (sectionsPresheaf x U).map (homOfLE (agreeOpens_le_left x U σ₁ σ₂)).op σ₁ =
      (sectionsPresheaf x U).map (homOfLE (agreeOpens_le_right x U σ₁ σ₂)).op σ₂ :=
    Subtype.ext (funext fun a => agreeOpens_spec x U σ₁ σ₂ a)
  have n₁ := sectionsFunctor_hom_app_map x _ ψ (homOfLE (agreeOpens_le_left x U σ₁ σ₂)).op σ₁
  have n₂ := sectionsFunctor_hom_app_map x _ ψ (homOfLE (agreeOpens_le_right x U σ₁ σ₂)).op σ₂
  change H.obj.map ((Opens.map (analyticMap x x' f hf)).map
    (homOfLE (agreeOpens_le_left x U σ₁ σ₂))).op (ψ.hom.app (op W₁) σ₁) = _ at n₁
  change H.obj.map ((Opens.map (analyticMap x x' f hf)).map
    (homOfLE (agreeOpens_le_right x U σ₁ σ₂))).op (ψ.hom.app (op W₂) σ₂) = _ at n₂
  rw [← presheaf_map_map_apply x' H.obj ((Opens.map (analyticMap x x' f hf)).map
      (homOfLE (agreeOpens_le_left x U σ₁ σ₂))).op (homOfLE hle).op,
    ← presheaf_map_map_apply x' H.obj ((Opens.map (analyticMap x x' f hf)).map
      (homOfLE (agreeOpens_le_right x U σ₁ σ₂))).op (homOfLE hle).op, n₁, n₂, hres]

theorem chartOpens_le {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    {W : TopologicalSpace.Opens (analyticSpace x)} (σ : (sectionsPresheaf x U).obj (op W)) :
    chartOpens x x' f hf U τ σ ≤ V :=
  agreeOpens_le_left x' _ τ _

theorem chartOpens_le_base {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    {W : TopologicalSpace.Opens (analyticSpace x)} (σ : (sectionsPresheaf x U).obj (op W)) :
    chartOpens x x' f hf U τ σ ≤ (Opens.map (analyticMap x x' f hf)).obj W :=
  agreeOpens_le_right x' _ τ _

/-- A choice of a section of `U(ℂ) → X(ℂ)` whose base change is `τ` near `v`. -/
noncomputable def chartBase {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) (v : V) :
    TopologicalSpace.Opens (analyticSpace x) :=
  (exists_mem_chartOpens x x' f hf U τ v.1 v.2).choose

/-- A choice of a section of `U(ℂ) → X(ℂ)` whose base change is `τ` near `v`. -/
noncomputable def baseChangeChartSection {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) (v : V) :
    (sectionsPresheaf x U).obj (op (chartBase x x' f hf U τ v)) :=
  (exists_mem_chartOpens x x' f hf U τ v.1 v.2).choose_spec.choose

theorem mem_chartOpens_baseChangeChartSection {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) (v : V) :
    v.1 ∈ chartOpens x x' f hf U τ (baseChangeChartSection x x' f hf U τ v) :=
  (exists_mem_chartOpens x x' f hf U τ v.1 v.2).choose_spec.choose_spec

theorem le_iSup_chartOpens {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) :
    V ≤ ⨆ v : V, chartOpens x x' f hf U τ (baseChangeChartSection x x' f hf U τ v) := fun v hv =>
  TopologicalSpace.Opens.mem_iSup.2 ⟨⟨v, hv⟩, mem_chartOpens_baseChangeChartSection x x' f hf U τ ⟨v, hv⟩⟩

/-- The local images of `τ` under `ψ` are compatible. -/
theorem isCompatible_baseChangeChartSection
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) :
    TopCat.Presheaf.IsCompatible H.obj
      (fun v : V => chartOpens x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))
      (fun v => H.obj.map (homOfLE (chartOpens_le_base x x' f hf U τ
        (baseChangeChartSection x x' f hf U τ v))).op (ψ.hom.app _ (baseChangeChartSection x x' f hf U τ v))) := by
  intro i j
  rw [presheaf_map_map_apply, presheaf_map_map_apply]
  exact chartOpens_compat x x' f hf U ψ τ _ _

theorem existsUnique_baseChangeGlue
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) :
    ∃! s : H.obj.obj (op V), ∀ v : V,
      H.obj.map (homOfLE (chartOpens_le x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))).op s =
        H.obj.map (homOfLE (chartOpens_le_base x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))).op
          (ψ.hom.app _ (baseChangeChartSection x x' f hf U τ v)) :=
  TopCat.Sheaf.existsUnique_gluing' H
    (fun v : V => chartOpens x x' f hf U τ (baseChangeChartSection x x' f hf U τ v)) V
    (fun v => homOfLE (chartOpens_le x x' f hf U τ (baseChangeChartSection x x' f hf U τ v)))
    (le_iSup_chartOpens x x' f hf U τ) _ (isCompatible_baseChangeChartSection x x' f hf U ψ τ)

/-- The section of `H` over `V` glued from the local images of `τ` under `ψ`. -/
noncomputable def baseChangeGlue
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) : H.obj.obj (op V) :=
  (existsUnique_baseChangeGlue x x' f hf U ψ τ).exists.choose

theorem baseChangeGlue_spec
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) (v : V) :
    H.obj.map (homOfLE (chartOpens_le x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))).op
        (baseChangeGlue x x' f hf U ψ τ) =
      H.obj.map (homOfLE (chartOpens_le_base x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))).op
        (ψ.hom.app _ (baseChangeChartSection x x' f hf U τ v)) :=
  (existsUnique_baseChangeGlue x x' f hf U ψ τ).exists.choose_spec v

/-- **The glued section restricts to `ψ σ` wherever `τ` is the base change of `σ`.** -/
theorem baseChangeGlue_map
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V : TopologicalSpace.Opens (analyticSpace x')}
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    {W : TopologicalSpace.Opens (analyticSpace x)} (σ : (sectionsPresheaf x U).obj (op W)) :
    H.obj.map (homOfLE (chartOpens_le x x' f hf U τ σ)).op (baseChangeGlue x x' f hf U ψ τ) =
      H.obj.map (homOfLE (chartOpens_le_base x x' f hf U τ σ)).op (ψ.hom.app _ σ) := by
  refine TopCat.Sheaf.eq_of_locally_eq' H
    (fun v : V => chartOpens x x' f hf U τ σ ⊓
      chartOpens x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))
    (chartOpens x x' f hf U τ σ) (fun v : V => homOfLE inf_le_left)
    (fun w hw => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨w, chartOpens_le x x' f hf U τ σ hw⟩,
      hw, mem_chartOpens_baseChangeChartSection x x' f hf U τ _⟩) _ _ fun v => ?_
  have hc := chartOpens_compat x x' f hf U ψ τ σ (baseChangeChartSection x x' f hf U τ v)
  have hs := baseChangeGlue_spec x x' f hf U ψ τ v
  rw [presheaf_map_map_apply x' H.obj _ _ (homOfLE (inf_le_left.trans
      (chartOpens_le x x' f hf U τ σ))).op,
    presheaf_map_map_apply x' H.obj _ _ (homOfLE (inf_le_left.trans
      (chartOpens_le_base x x' f hf U τ σ))).op, hc,
    ← presheaf_map_map_apply x' H.obj (homOfLE (chartOpens_le x x' f hf U τ
      (baseChangeChartSection x x' f hf U τ v))).op (homOfLE inf_le_right).op, hs,
    presheaf_map_map_apply]

theorem chartOpens_map_le {V V' : TopologicalSpace.Opens (analyticSpace x')} (i : op V ⟶ op V')
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V))
    {W : TopologicalSpace.Opens (analyticSpace x)} (σ : (sectionsPresheaf x U).obj (op W)) :
    chartOpens x x' f hf U ((sectionsPresheaf x' _).map i τ) σ ≤ chartOpens x x' f hf U τ σ :=
  fun _ ⟨h, e⟩ => ⟨⟨i.unop.le h.1, h.2⟩, e⟩

theorem baseChangeGlue_naturality
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H)
    {V V' : TopologicalSpace.Opens (analyticSpace x')} (i : op V ⟶ op V')
    (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)) :
    baseChangeGlue x x' f hf U ψ ((sectionsPresheaf x' _).map i τ) =
      H.obj.map i (baseChangeGlue x x' f hf U ψ τ) := by
  refine TopCat.Sheaf.eq_of_locally_eq' H
    (fun v : V' => chartOpens x x' f hf U ((sectionsPresheaf x' _).map i τ)
      (baseChangeChartSection x x' f hf U ((sectionsPresheaf x' _).map i τ) v)) V'
    (fun v => homOfLE (chartOpens_le x x' f hf U _ _)) (le_iSup_chartOpens x x' f hf U _) _ _
    fun v => ?_
  rw [baseChangeGlue_spec, presheaf_map_map_apply x' H.obj _ _
      (homOfLE ((chartOpens_map_le x x' f hf U i τ _).trans (chartOpens_le x x' f hf U τ _))).op,
    ← presheaf_map_map_apply x' H.obj (homOfLE (chartOpens_le x x' f hf U τ _)).op
      (homOfLE (chartOpens_map_le x x' f hf U i τ _)).op, baseChangeGlue_map,
    presheaf_map_map_apply]

/-- The morphism `Φ (U ×_X X') ⟶ H` glued from a morphism `Φ U ⟶ f_* H`. -/
noncomputable def baseChangeLift
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H) :
    (sectionsFunctor x').obj ((𝔅 f).obj U) ⟶ H :=
  ObjectProperty.homMk
    { app V := ↾(fun τ => baseChangeGlue x x' f hf U ψ τ)
      naturality V V' i := by
        ext τ
        exact baseChangeGlue_naturality x x' f hf U ψ i τ }

theorem baseChangeSections_comp_baseChangeLift
    (ψ : (sectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).obj H) :
    baseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward (Type 1)
      (analyticMap x x' f hf)).map (baseChangeLift x x' f hf U ψ) = ψ := by
  ext W σ
  change baseChangeGlue x x' f hf U ψ (baseChangeSection x x' f hf U W.unop σ) = ψ.hom.app W σ
  refine TopCat.Sheaf.eq_of_locally_eq' H
    (fun _ : Unit => chartOpens x x' f hf U (baseChangeSection x x' f hf U W.unop σ) σ) _
    (fun _ => homOfLE (chartOpens_le x x' f hf U _ σ))
    (fun w hw => TopologicalSpace.Opens.mem_iSup.2 ⟨(), ⟨hw, hw⟩, rfl⟩) _ _
    fun _ => baseChangeGlue_map x x' f hf U ψ _ σ

theorem baseChangeSections_comp_injective :
    Function.Injective (fun φ : (sectionsFunctor x').obj ((𝔅 f).obj U) ⟶ H =>
      baseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward (Type 1)
        (analyticMap x x' f hf)).map φ) := by
  intro φ₁ φ₂ h
  have key : ∀ (V : TopologicalSpace.Opens (analyticSpace x'))
      (τ : (sectionsPresheaf x' ((𝔅 f).obj U)).obj (op V)),
      φ₁.hom.app (op V) τ = φ₂.hom.app (op V) τ := by
    intro V τ
    refine TopCat.Sheaf.eq_of_locally_eq' H
      (fun v : V => chartOpens x x' f hf U τ (baseChangeChartSection x x' f hf U τ v)) V
      (fun v => homOfLE (chartOpens_le x x' f hf U _ _)) (le_iSup_chartOpens x x' f hf U τ) _ _
      fun v => ?_
    have hτ : (sectionsPresheaf x' _).map (homOfLE (chartOpens_le x x' f hf U τ
        (baseChangeChartSection x x' f hf U τ v))).op τ = (sectionsPresheaf x' _).map
          (homOfLE (chartOpens_le_base x x' f hf U τ (baseChangeChartSection x x' f hf U τ v))).op
          (baseChangeSection x x' f hf U _ (baseChangeChartSection x x' f hf U τ v)) :=
      Subtype.ext (funext fun w => agreeOpens_spec x' _ τ _ w)
    have hφ := congrArg (fun α => α.hom.app (op (chartBase x x' f hf U τ v))
      (baseChangeChartSection x x' f hf U τ v)) h
    change φ₁.hom.app _ (baseChangeSection x x' f hf U _ _) =
      φ₂.hom.app _ (baseChangeSection x x' f hf U _ _) at hφ
    rw [sectionsFunctor_hom_app_map, sectionsFunctor_hom_app_map, hτ,
      ← sectionsFunctor_hom_app_map, ← sectionsFunctor_hom_app_map, hφ]
  ext V τ
  exact key V.unop τ

/-- **Morphisms out of the sheaf of sections of a base change.** For every sheaf of sets `H` on
`X'(ℂ)`, composition with `Φ U ⟶ f_* Φ (U ×_X X')` is a bijection
`Hom(Φ (U ×_X X'), H) ≃ Hom(Φ U, f_* H)`: the sheaf of sections of `(U ×_X X')(ℂ) → X'(ℂ)` is the
inverse image of the sheaf of sections of `U(ℂ) → X(ℂ)`. -/
theorem baseChangeSections_comp_bijective :
    Function.Bijective (fun φ : (sectionsFunctor x').obj ((𝔅 f).obj U) ⟶ H =>
      baseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward (Type 1)
        (analyticMap x x' f hf)).map φ) :=
  ⟨baseChangeSections_comp_injective x x' f hf U,
    fun ψ => ⟨_, baseChangeSections_comp_baseChangeLift x x' f hf U ψ⟩⟩

end Bijective

/-! ### The direct images commute with base change -/

section DirectImage

variable (U : X.Etale)

set_option hygiene false in
/-- The free–forgetful adjunction for sheaves on `X(ℂ)`. -/
local notation "adjX" => Sheaf.adjunction (Opens.grothendieckTopology (analyticSpace x))
  AddCommGrpCat.adj.{1}

set_option hygiene false in
/-- The free–forgetful adjunction for sheaves on `X'(ℂ)`. -/
local notation "adjX'" => Sheaf.adjunction (Opens.grothendieckTopology (analyticSpace x'))
  AddCommGrpCat.adj.{1}

/-- `ℤ[Φ U] ⟶ f_* ℤ[Φ (U ×_X X')]`, adjoint to `Φ U ⟶ f_* Φ (U ×_X X') ⟶ f_* ℤ[Φ (U ×_X X')]`. -/
noncomputable def freeBaseChangeSections :
    (freeSectionsFunctor x).obj U ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{1}
      (analyticMap x x' f hf)).obj ((freeSectionsFunctor x').obj ((𝔅 f).obj U)) :=
  ((adjX).homEquiv _ _).symm (baseChangeSections x x' f hf U ≫
    (TopCat.Sheaf.pushforward (Type 1) (analyticMap x x' f hf)).map
      ((adjX').unit.app ((sectionsFunctor x').obj ((𝔅 f).obj U))))

theorem homEquiv_freeBaseChangeSections_comp {G : AnSheaf x'}
    (φ : (freeSectionsFunctor x').obj ((𝔅 f).obj U) ⟶ G) :
    (adjX).homEquiv _ _ (freeBaseChangeSections x x' f hf U ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map φ) =
      baseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward (Type 1)
        (analyticMap x x' f hf)).map ((adjX').homEquiv _ _ φ) := by
  rw [Adjunction.homEquiv_naturality_right, freeBaseChangeSections, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit, Category.assoc, Functor.map_comp]
  rfl

theorem freeBaseChangeSections_comp_bijective (G : AnSheaf x') :
    Function.Bijective (fun φ : (freeSectionsFunctor x').obj ((𝔅 f).obj U) ⟶ G =>
      freeBaseChangeSections x x' f hf U ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map φ) := by
  have : (fun φ : (freeSectionsFunctor x').obj ((𝔅 f).obj U) ⟶ G =>
      freeBaseChangeSections x x' f hf U ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map φ) =
      ((adjX).homEquiv _ _).symm ∘ (fun φ => baseChangeSections x x' f hf U ≫
        (TopCat.Sheaf.pushforward (Type 1) (analyticMap x x' f hf)).map φ) ∘
        ((adjX').homEquiv _ _) := by
    funext φ
    simp only [Function.comp_apply]
    rw [← homEquiv_freeBaseChangeSections_comp, Equiv.symm_apply_apply]
  rw [this]
  exact ((adjX).homEquiv _ _).symm.bijective.comp
    ((baseChangeSections_comp_bijective x x' f hf U).comp ((adjX').homEquiv _ _).bijective)

theorem freeBaseChangeSections_naturality {U V : X.Etale} (g : U ⟶ V) :
    (freeSectionsFunctor x).map g ≫ freeBaseChangeSections x x' f hf V =
      freeBaseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{1}
        (analyticMap x x' f hf)).map ((freeSectionsFunctor x').map ((𝔅 f).map g)) := by
  apply ((adjX).homEquiv _ _).injective
  rw [homEquiv_freeBaseChangeSections_comp]
  change (adjX).homEquiv _ _ ((Sheaf.composeAndSheafify _ AddCommGrpCat.free.{1}).map
    ((sectionsFunctor x).map g) ≫ freeBaseChangeSections x x' f hf V) = _
  rw [Adjunction.homEquiv_naturality_left, freeBaseChangeSections, Equiv.apply_symm_apply,
    ← Category.assoc, baseChangeSections_naturality, Category.assoc, ← Functor.map_comp,
    Adjunction.homEquiv_unit]
  congr 2
  exact ((adjX').unit.naturality ((sectionsFunctor x').map ((𝔅 f).map g)))

/-- The comparison
`ε'_* G (U ×_X X') = Hom(ℤ[Φ (U ×_X X')], G) ⟶ Hom(ℤ[Φ U], f_* G) = ε_* f_* G (U)`,
on one étale `X`-scheme. -/
noncomputable def directImageBaseChangeApp (G : AnSheaf x') (U : X.Etale) :
    AddCommGrpCat.of ((freeSectionsFunctor x').obj ((𝔅 f).obj U) ⟶ G) ⟶
      AddCommGrpCat.of ((freeSectionsFunctor x).obj U ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).obj G) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun φ => freeBaseChangeSections x x' f hf U ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map φ)
    (fun φ ψ => by
        rw [← Preadditive.comp_add]
        congr 1))

theorem directImageBaseChangeApp_bijective (G : AnSheaf x') (U : X.Etale) :
    Function.Bijective (directImageBaseChangeApp x x' f hf G U) :=
  freeBaseChangeSections_comp_bijective x x' f hf U G

/-- `ε'_* G ⟶ ... `: the comparison of the two direct images of an analytic sheaf on `X'(ℂ)` to
the small étale site of `X`. -/
noncomputable def directImageBaseChangeHom (G : AnSheaf x') :
    (smallEtalePushforwardAb f).obj ((analyticDirectImage x').obj G) ⟶
      (analyticDirectImage x).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).obj G) :=
  ObjectProperty.homMk
    { app U := directImageBaseChangeApp x x' f hf G U.unop
      naturality {U V} g := by
        ext φ
        change freeBaseChangeSections x x' f hf V.unop ≫ _ =
          (freeSectionsFunctor x).map g.unop ≫ freeBaseChangeSections x x' f hf U.unop ≫ _
        rw [← Category.assoc, freeBaseChangeSections_naturality, Category.assoc,
          ← Functor.map_comp]
        rfl }

instance isIso_directImageBaseChangeHom (G : AnSheaf x') :
    IsIso (directImageBaseChangeHom x x' f hf G) := by
  have : ∀ U, IsIso ((directImageBaseChangeHom x x' f hf G).hom.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (directImageBaseChangeApp_bijective x x' f hf G U.unop)
  have : IsIso ((sheafToPresheaf _ _).map (directImageBaseChangeHom x x' f hf G)) :=
    NatIso.isIso_of_isIso_app (directImageBaseChangeHom x x' f hf G).hom
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **The direct images commute with base change**: `f_* ∘ ε'_* ≅ ε_* ∘ f_an,*` as functors from
abelian sheaves on `X'(ℂ)` to abelian sheaves on the small étale site of `X`. -/
noncomputable def directImageBaseChangeIso :
    analyticDirectImage x' ⋙ smallEtalePushforwardAb f ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf) ⋙ analyticDirectImage x :=
  NatIso.ofComponents (fun G => asIso (directImageBaseChangeHom x x' f hf G)) (fun {G G'} ψ => by
    ext U φ
    change freeBaseChangeSections x x' f hf U.unop ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map (φ ≫ ψ) =
      (freeBaseChangeSections x x' f hf U.unop ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map φ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map ψ
    rw [Category.assoc, ← Functor.map_comp])

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- The direct image along `X'(ℂ) → X(ℂ)` is additive. -/
instance additive_pushforward_analyticMap :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).Additive where
  map_add := rfl

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- The direct image along `X'(ℂ) → X(ℂ)` is additive (in the spelling of `AnSheaf`). -/
instance additive_pushforward_analyticMap' :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf) :
      Sheaf (_root_.Opens.grothendieckTopology (TopCat.of (ULift.{1} (ComplexPoints x'))))
          AddCommGrpCat.{1} ⥤
        Sheaf (_root_.Opens.grothendieckTopology (TopCat.of (ULift.{1} (ComplexPoints x))))
          AddCommGrpCat.{1}).Additive where
  map_add := rfl

/-- The adjunction `f^* ⊣ f_*` for abelian sheaves on small étale sites. -/
noncomputable abbrev etaleInverseImageAdjunction :
    etaleAbelianInverseImage.{0, 0} f ⊣ smallEtalePushforwardAb f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (𝔅 f)
    AddCommGrpCat.{1} X.smallEtaleTopology X'.smallEtaleTopology

/-- **`ε` commutes with inverse images**: `ε'^* ∘ f^* ≅ f_an^* ∘ ε^*`, from the isomorphism of
right adjoints `directImageBaseChangeIso`. -/
noncomputable def inverseImageIso :
    etaleAbelianInverseImage.{0, 0} f ⋙ analyticInverseImage x' ≅
      analyticInverseImage x ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{1} (analyticMap x x' f hf) :=
  Adjunction.leftAdjointUniq ((etaleInverseImageAdjunction f).comp (analyticAdjunction x'))
    (((analyticAdjunction x).comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{1}
      (analyticMap x x' f hf))).ofNatIsoRight (directImageBaseChangeIso x x' f hf).symm)

/-- **The base change map** `ε^* f_* ⟶ f_an,* ε'^*`, the mate of `inverseImageIso`. -/
noncomputable def pushforwardBaseChange :
    smallEtalePushforwardAb f ⋙ analyticInverseImage x ⟶
      analyticInverseImage x' ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{1}
        (analyticMap x x' f hf) :=
  mateEquiv (etaleInverseImageAdjunction f) (TopCat.Sheaf.pullbackPushforwardAdjunction
    AddCommGrpCat.{1} (analyticMap x x' f hf)) (inverseImageIso x x' f hf).inv

end DirectImage

end BaseChangeSections

/-! ### The comparison predicate and its invariance under isomorphisms -/

section PC

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x']

/-- `c^ν(X, F)` is bijective for every `F` in `P` and every `ν`. -/
def ComparisonBijectiveOn (P : ObjectProperty (EtSheaf X)) : Prop :=
  ∀ F, P F → ∀ n, Function.Bijective (comparisonMap x F n)

/-- `PC(X)`: the comparison map is bijective on torsion sheaves in every degree. -/
abbrev PC : Prop :=
  ComparisonBijectiveOn x (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology)

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- Direct image along an isomorphism of schemes is an equivalence of étale sheaf categories. -/
theorem isEquivalence_smallEtalePushforwardAb (f : X' ⟶ X) [IsIso f] :
    (smallEtalePushforwardAb f).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (smallEtalePushforwardAb f) (smallEtalePushforwardAb (inv f))
    ((smallEtalePushforwardAbIdOf (f ≫ inv f) (by simp)).symm ≪≫
      (smallEtalePushforwardAbCompIso f (inv f)).symm)
    (smallEtalePushforwardAbCompIso (inv f) f ≪≫
      smallEtalePushforwardAbIdOf (inv f ≫ f) (by simp))).isEquivalence_functor

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- Inverse image along an isomorphism of schemes is an equivalence of étale sheaf categories. -/
theorem isEquivalence_etaleAbelianInverseImage (f : X' ⟶ X) [IsIso f] :
    (etaleAbelianInverseImage.{0, 0} f).IsEquivalence :=
  have := isEquivalence_smallEtalePushforwardAb f
  (etaleInverseImageAdjunction f).isEquivalence_left_of_isEquivalence_right

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
theorem analyticMap_analyticMap (f : X' ⟶ X) [IsIso f] (hf : f ≫ x = x')
    (p : analyticSpace x') :
    analyticMap x' x (inv f) (by rw [IsIso.inv_comp_eq, hf]) (analyticMap x x' f hf p) = p :=
  ULift.ext _ _ (ext (by
    change (p.down.hom ≫ f) ≫ inv f = p.down.hom
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]))

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
theorem analyticMap_analyticMap_inv (f : X' ⟶ X) [IsIso f] (hf : f ≫ x = x')
    (p : analyticSpace x) :
    analyticMap x x' f hf (analyticMap x' x (inv f) (by rw [IsIso.inv_comp_eq, hf]) p) = p :=
  ULift.ext _ _ (ext (by
    change (p.down.hom ≫ inv f) ≫ f = p.down.hom
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]))

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- Direct image along the homeomorphism of complex points induced by an isomorphism is an
equivalence. -/
theorem isEquivalence_pushforward_analyticMap (f : X' ⟶ X) [IsIso f] (hf : f ≫ x = x') :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).IsEquivalence := by
  have hinv : inv f ≫ x' = x := by rw [IsIso.inv_comp_eq, hf]
  let g := analyticMap x' x (inv f) hinv
  have : (TopologicalSpace.Opens.map (analyticMap x x' f hf)).IsContinuous
      (Opens.grothendieckTopology (analyticSpace x))
      (Opens.grothendieckTopology (analyticSpace x')) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  have : (TopologicalSpace.Opens.map g).IsContinuous
      (Opens.grothendieckTopology (analyticSpace x'))
      (Opens.grothendieckTopology (analyticSpace x)) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  have : (TopologicalSpace.Opens.map g ⋙
      TopologicalSpace.Opens.map (analyticMap x x' f hf)).IsContinuous
      (Opens.grothendieckTopology (analyticSpace x'))
      (Opens.grothendieckTopology (analyticSpace x')) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (analyticSpace x)) _
  have : (TopologicalSpace.Opens.map (analyticMap x x' f hf) ⋙
      TopologicalSpace.Opens.map g).IsContinuous
      (Opens.grothendieckTopology (analyticSpace x))
      (Opens.grothendieckTopology (analyticSpace x)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (analyticSpace x')) _
  have e₁ : TopologicalSpace.Opens.map g ⋙ TopologicalSpace.Opens.map (analyticMap x x' f hf) ≅
      𝟭 _ := NatIso.ofComponents (fun U => eqToIso (TopologicalSpace.Opens.ext (by
        ext p
        change g (analyticMap x x' f hf p) ∈ U ↔ p ∈ U
        rw [analyticMap_analyticMap]))) (fun _ => rfl)
  have e₂ : TopologicalSpace.Opens.map (analyticMap x x' f hf) ⋙ TopologicalSpace.Opens.map g ≅
      𝟭 _ := NatIso.ofComponents (fun U => eqToIso (TopologicalSpace.Opens.ext (by
        ext p
        change analyticMap x x' f hf (g p) ∈ U ↔ p ∈ U
        rw [analyticMap_analyticMap_inv]))) (fun _ => rfl)
  exact (CategoryTheory.Equivalence.mk
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf))
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} g)
    ((Functor.sheafPushforwardContinuousId' e₁ _ _).symm ≪≫
      (Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _).symm)
    (Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' e₂ _ _)).isEquivalence_functor

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- The inverse image of abelian sheaves along `X'(ℂ) → X(ℂ)`, in the spelling of `AnSheaf`. -/
noncomputable abbrev analyticPullback (f : X' ⟶ X) (hf : f ≫ x = x') :
    Sheaf (_root_.Opens.grothendieckTopology (TopCat.of (ULift.{1} (ComplexPoints x))))
        AddCommGrpCat.{1} ⥤
      Sheaf (_root_.Opens.grothendieckTopology (TopCat.of (ULift.{1} (ComplexPoints x'))))
        AddCommGrpCat.{1} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{1} (analyticMap x x' f hf)

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- Inverse image along the homeomorphism of complex points induced by an isomorphism is an
equivalence. -/
theorem isEquivalence_pullback_analyticMap (f : X' ⟶ X) [IsIso f] (hf : f ≫ x = x') :
    (analyticPullback x x' f hf).IsEquivalence :=
  have := isEquivalence_pushforward_analyticMap x x' f hf
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{1}
    (analyticMap x x' f hf)).isEquivalence_left_of_isEquivalence_right

/-- **Invariance of the comparison map under isomorphisms**: for an isomorphism `f : X' ⟶ X` over
`ℂ`, `c^n(X', f^* F)` is bijective if and only if `c^n(X, F)` is. -/
theorem comparisonMap_bijective_iff_of_isIso (f : X' ⟶ X) [IsIso f] (hf : f ≫ x = x')
    (F : EtSheaf X) (n : ℕ) :
    Function.Bijective (comparisonMap x' ((etaleAbelianInverseImage.{0, 0} f).obj F) n) ↔
      Function.Bijective (comparisonMap x F n) := by
  rw [comparisonMap, Functor.mapExtOfIso_bijective_iff, comparisonMap,
    Functor.mapExtOfIso_bijective_iff,
    Functor.mapExtAddHom_bijective_iff_of_iso (analyticInverseImage x')
      (((etaleAbelianInverseImageConstantIso.{0, 0} f).app (AddCommGrpCat.of (ULift ℤ))).symm)]
  exact Functor.mapExtAddHom_bijective_iff_of_natIso _ (isEquivalence_etaleAbelianInverseImage f)
    _ _ (analyticPullback x x' f hf) (isEquivalence_pullback_analyticMap x x' f hf)
    (inverseImageIso x x' f hf) _ F n

/-- **`PC` is invariant under isomorphisms of schemes over `ℂ`.** -/
theorem pc_iff_of_iso (e : X' ≅ X) (he : e.hom ≫ x = x') : PC x ↔ PC x' := by
  have hinv : e.inv ≫ x' = x := by rw [← he, Iso.inv_hom_id_assoc]
  constructor
  · intro h G hG n
    exact (comparisonMap_bijective_iff_of_isIso x' x e.inv hinv G n).1
      (h _ (torsionSheafProperty_etaleAbelianInverseImage.{0, 0} e.inv G hG) n)
  · intro h F hF n
    exact (comparisonMap_bijective_iff_of_isIso x x' e.hom he F n).1
      (h _ (torsionSheafProperty_etaleAbelianInverseImage.{0, 0} e.hom F hF) n)

end PC

end AlgebraicGeometry.Scheme.ComplexPoints
