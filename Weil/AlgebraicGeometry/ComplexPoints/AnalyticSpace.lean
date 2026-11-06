module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import Weil.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import Weil.Topology.Sheaves.Cohomology.UniverseLift

/-!
# The complex points in the next universe

Let `Y` be a scheme over `ℂ`. Its complex points `Y(ℂ)` with the analytic topology form a
topological space in `Type`, and the sheaf cohomology `H ^ ν (Y(ℂ), M)` of a constant sheaf is
computed with sheaves of abelian groups in `Type`. Comparison with étale cohomology, whose
sheaves take values in `Type 1`, is more convenient on the space `ULift Y(ℂ)` of `TopCat.{1}`,
with abelian groups in `Type 1`. This file shows that nothing is lost:

  `H ^ ν (Y(ℂ), M) ≃+ H ^ ν (ULift Y(ℂ), ULift M)`

naturally in `M`, and more generally that the functor raising the universe of the values and
transporting along the homeomorphism `ULift Y(ℂ) ≃ₜ Y(ℂ)` is exact and preserves sheaf
cohomology, naturally in the sheaf and compatibly with connecting maps.

The general statement is about a topological space `T : Type u`: the homeomorphism
`ULift T ≃ₜ T` induces an equivalence of the categories of open sets, which is an equivalence of
sites; restriction of sheaves along it is an equivalence of sheaf categories, and it preserves
cohomology by the Comparison Lemma.

## Main definitions

* `TopCat.opensULiftEquivalence`: the equivalence `Opens (ULift T) ≌ Opens T`.
* `TopCat.sheafULiftRestriction`: restriction of abelian sheaves from `T` to `ULift T`.
* `TopCat.sheafHULiftRestrictionAddEquiv`: `H ^ n (T, F) ≃+ H ^ n (ULift T, F|)`.
* `TopCat.constantSheafHULiftSpaceAddEquiv`: `H ^ n (T, M) ≃+ H ^ n (ULift T, M)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticSpace`: `ULift Y(ℂ)` in `TopCat.{1}`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticConstantAddEquiv`:
  `H ^ ν (Y(ℂ), M) ≃+ H ^ ν (ULift Y(ℂ), ULift M)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.liftToAnalytic`: the exact functor from abelian sheaves
  on `Y(ℂ)` to abelian sheaves in `Type 1` on `ULift Y(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.liftToAnalyticHAddEquiv`: it preserves cohomology.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.analyticConstantAddEquiv_naturality`: naturality of
  `analyticConstantAddEquiv` in the coefficients.
* `AlgebraicGeometry.Scheme.ComplexPoints.liftToAnalyticHAddEquiv_naturality` and
  `AlgebraicGeometry.Scheme.ComplexPoints.liftToAnalyticHAddEquiv_comp_extClass`: naturality in
  the sheaf and compatibility with the connecting maps.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 01FT](https://stacks.math.columbia.edu/tag/01FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

-- These instances leave the universe `w` of `AddCommGrpCat.{max v₁ w}` undetermined, and
-- unification against them gets stuck on `u + 1 =?= max (u + 1) ?w`.
attribute [-instance] Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction
  Stacks.Cohomology.DerivedLowerShriek.preservesColimits_abelianRestriction

universe a u

namespace TopCat

variable (T : Type u) [TopologicalSpace T]

/-- The equivalence of the categories of open sets of `ULift T` and `T` induced by the
homeomorphism `ULift T ≃ₜ T`. -/
def opensULiftEquivalence : Opens (TopCat.of (ULift.{u + 1} T)) ≌ Opens (TopCat.of T) :=
  (Homeomorph.ulift (X := T)).opensCongr.equivalence

instance isDenseSubsite_opensULiftEquivalence_functor :
    (opensULiftEquivalence T).functor.IsDenseSubsite
    (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
    (Opens.grothendieckTopology (TopCat.of T)) where
  functorPushforward_mem_iff {V S} := by
    simp only [Opens.mem_grothendieckTopology, Sieve.mem_functorPushforward_functor]
    constructor
    · intro H x hxV
      obtain ⟨W, f, hW, hxW⟩ := H x.down hxV
      exact ⟨_, _, hW, hxW⟩
    · intro H x hxV
      obtain ⟨W, f, hW, hxW⟩ := H ⟨x⟩ hxV
      refine ⟨_, (opensULiftEquivalence T).functor.map f, ?_, hxW⟩
      convert S.downward_closed hW ((opensULiftEquivalence T).unitInv.app W) using 1
      · rfl
      · exact Subsingleton.elim _ _

/-- Restriction of abelian sheaves on `T` (with groups in `Type (u + 1)`) to `ULift T`, along
the homeomorphism `ULift T ≃ₜ T`. It is an equivalence of categories. -/
abbrev sheafULiftRestriction :
    CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
        AddCommGrpCat.{u + 1} :=
  (opensULiftEquivalence T).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
    (Opens.grothendieckTopology (TopCat.of T))

instance : (sheafULiftRestriction T).IsEquivalence := by
  dsimp only [sheafULiftRestriction]
  infer_instance

instance : (sheafULiftRestriction T).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction to `ULift T` carries the constant sheaf to the constant sheaf, naturally in the
group of coefficients. -/
def constantSheafULiftRestrictionIso :
    constantSheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1} ⋙
        sheafULiftRestriction T ≅
      constantSheaf (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
        AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso _ _ _

section Cohomology

variable
  [HasExt.{a}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1})]
  [HasExt.{a} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
    AddCommGrpCat.{u + 1})]

/-- **Sheaf cohomology of `T` is sheaf cohomology of `ULift T`**: restriction along the
homeomorphism `ULift T ≃ₜ T` induces `H ^ n (T, F) ≃+ H ^ n (ULift T, F|)`. -/
def sheafHULiftRestrictionAddEquiv
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1})
    (n : ℕ) :
    Sheaf.H.{a} F n ≃+ Sheaf.H.{a} ((sheafULiftRestriction T).obj F) n :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv _ _ (opensULiftEquivalence T).functor F n

lemma sheafHULiftRestrictionAddEquiv_apply
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1})
    (n : ℕ)
    (x : Sheaf.H.{a} F n) :
    sheafHULiftRestrictionAddEquiv T F n x =
      (Ext.mk₀ (((constantSheafULiftRestrictionIso T).app
          (AddCommGrpCat.of (ULift ℤ))).inv)).comp
        (x.mapExactFunctor (sheafULiftRestriction T)) (zero_add n) :=
  rfl

/-- `TopCat.sheafHULiftRestrictionAddEquiv` is natural in the sheaf. -/
lemma sheafHULiftRestrictionAddEquiv_naturality
    {F F' : CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1}}
    (f : F ⟶ F')
    (n : ℕ) (x : Sheaf.H.{a} F n) :
    sheafHULiftRestrictionAddEquiv T F' n (Sheaf.H.map f n x) =
      Sheaf.H.map ((sheafULiftRestriction T).map f) n
        (sheafHULiftRestrictionAddEquiv T F n x) :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv_map _ _ _ f n x

/-- `TopCat.sheafHULiftRestrictionAddEquiv` is compatible with the connecting maps of short exact
sequences. -/
lemma sheafHULiftRestrictionAddEquiv_comp_extClass
    {S : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{a} S.X₃ n) :
    sheafHULiftRestrictionAddEquiv T S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (sheafHULiftRestrictionAddEquiv T S.X₃ n x).comp
        (hS.map_of_exact (sheafULiftRestriction T)).extClass rfl := by
  rw [sheafHULiftRestrictionAddEquiv_apply, sheafHULiftRestrictionAddEquiv_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc]
  omega

/-- **Constant coefficients**: `H ^ n (T, M) ≃+ H ^ n (ULift T, M)` for the constant sheaves
with values `M`. -/
def constantSheafHULiftSpaceAddEquiv (M : AddCommGrpCat.{u + 1}) (n : ℕ) :
    Sheaf.H.{a} ((constantSheaf (Opens.grothendieckTopology (TopCat.of T))
        AddCommGrpCat.{u + 1}).obj M) n ≃+
      Sheaf.H.{a} ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
        AddCommGrpCat.{u + 1}).obj M) n :=
  (sheafHULiftRestrictionAddEquiv T _ n).trans
    { toFun := Sheaf.H.map ((constantSheafULiftRestrictionIso T).hom.app M) n
      invFun := Sheaf.H.map ((constantSheafULiftRestrictionIso T).inv.app M) n
      left_inv := fun x ↦ by
        rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id_app, Sheaf.H.map_id_apply]
      right_inv := fun x ↦ by
        rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id_app, Sheaf.H.map_id_apply]
      map_add' := map_add _ }

/-- `TopCat.constantSheafHULiftSpaceAddEquiv` is natural in the group of coefficients. -/
lemma constantSheafHULiftSpaceAddEquiv_naturality {M N : AddCommGrpCat.{u + 1}} (g : M ⟶ N)
    (n : ℕ)
    (x : Sheaf.H.{a} ((constantSheaf (Opens.grothendieckTopology (TopCat.of T))
      AddCommGrpCat.{u + 1}).obj M) n) :
    constantSheafHULiftSpaceAddEquiv T N n
        (Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology (TopCat.of T))
          AddCommGrpCat.{u + 1}).map g) n x) =
      Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} T)))
          AddCommGrpCat.{u + 1}).map g) n
        (constantSheafHULiftSpaceAddEquiv T M n x) := by
  change Sheaf.H.map _ n (sheafHULiftRestrictionAddEquiv T _ n (Sheaf.H.map _ n x)) =
    Sheaf.H.map _ n (Sheaf.H.map _ n (sheafHULiftRestrictionAddEquiv T _ n x))
  rw [sheafHULiftRestrictionAddEquiv_naturality, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply]
  congr 2
  exact (constantSheafULiftRestrictionIso T).hom.naturality g

end Cohomology

end TopCat

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ))

/-- The complex points `Y(ℂ)` with the analytic topology, lifted to `TopCat.{1}`. -/
abbrev analyticSpace : TopCat.{1} := TopCat.of (ULift.{1} (ComplexPoints y))

/-- Abelian sheaves with groups in `Type 1` on the complex points, lifted to `TopCat.{1}`. -/
abbrev AnSheaf := Sheaf (Opens.grothendieckTopology (analyticSpace y)) AddCommGrpCat.{1}

/-- Abelian sheaves with groups in `Type 1` on the small étale site of `Y`. -/
abbrev EtSheaf (Y : Scheme.{0}) := Sheaf Y.smallEtaleTopology AddCommGrpCat.{1}

instance : HasExt.{1} (AnSheaf y) := IsGrothendieckAbelian.hasExt.{1} _

instance (Y : Scheme.{0}) : IsGrothendieckAbelian.{1} (EtSheaf Y) :=
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Y

instance (Y : Scheme.{0}) : HasExt.{1} (EtSheaf Y) := IsGrothendieckAbelian.hasExt.{1} _

/-- **The analytic cohomology of a constant sheaf, in the next universe**:
`H ^ ν (Y(ℂ), M) ≃+ H ^ ν (ULift Y(ℂ), ULift M)`, the right side computed with abelian sheaves in
`Type 1` on `analyticSpace y`. -/
def analyticConstantAddEquiv (M : AddCommGrpCat.{0}) (ν : ℕ) :
    analyticCohomologyConstant y M ν ≃+
      Sheaf.H.{1} ((constantSheaf (Opens.grothendieckTopology (analyticSpace y))
        AddCommGrpCat.{1}).obj (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  letI := IsGrothendieckAbelian.hasExt.{1}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{1})
  (TopCat.constantSheafHULiftAddEquiv.{0, 1, 1} (TopCat.of (ComplexPoints y)) M ν).trans
    (TopCat.constantSheafHULiftSpaceAddEquiv.{1} (ComplexPoints y) _ ν)

/-- `analyticConstantAddEquiv` is natural in the group of coefficients. -/
theorem analyticConstantAddEquiv_naturality {M N : AddCommGrpCat.{0}} (g : M ⟶ N) (ν : ℕ)
    (x : analyticCohomologyConstant y M ν) :
    analyticConstantAddEquiv y N ν (analyticCohomologyConstantMap y g ν x) =
      Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology (analyticSpace y))
        AddCommGrpCat.{1}).map (AddCommGrpCat.uliftFunctor.{1, 0}.map g)) ν
        (analyticConstantAddEquiv y M ν x) := by
  let := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  let := IsGrothendieckAbelian.hasExt.{1}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{1})
  exact (congrArg (TopCat.constantSheafHULiftSpaceAddEquiv.{1} (ComplexPoints y) _ ν)
    (TopCat.constantSheafHULiftAddEquiv_naturality.{0, 1, 1} (TopCat.of (ComplexPoints y)) g ν
      x)).trans
    (TopCat.constantSheafHULiftSpaceAddEquiv_naturality.{1} (ComplexPoints y)
      (AddCommGrpCat.uliftFunctor.{1, 0}.map g) ν _)

/-- The exact functor from abelian sheaves on `Y(ℂ)` to abelian sheaves with groups in `Type 1`
on `analyticSpace y`: raise the universe of the groups of sections, then restrict along the
homeomorphism `ULift Y(ℂ) ≃ₜ Y(ℂ)`. -/
abbrev liftToAnalytic :
    Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0} ⥤
      AnSheaf y :=
  Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{1, 0}
      (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) ⋙
    TopCat.sheafULiftRestriction (ComplexPoints y)

/-- The universe lift of abelian sheaves on `Y(ℂ)` preserves finite colimits. -/
instance : PreservesFiniteColimits (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{1, 0}
    (Opens.grothendieckTopology (TopCat.of (ComplexPoints y)))) :=
  TopCat.preservesFiniteColimits_uliftSheafFunctor_opens.{1, 0} _

instance : PreservesFiniteColimits (liftToAnalytic y) := comp_preservesFiniteColimits _ _

instance : PreservesFiniteLimits (liftToAnalytic y) := inferInstance

instance : (liftToAnalytic y).Additive := inferInstance

section Cohomology

variable [HasExt.{0}
  (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})]

/-- `liftToAnalytic y` preserves sheaf cohomology:
`H ^ n (Y(ℂ), F) ≃+ H ^ n (ULift Y(ℂ), (liftToAnalytic y).obj F)`. -/
def liftToAnalyticHAddEquiv
    (F : Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
    (n : ℕ) :
    Sheaf.H.{0} F n ≃+ Sheaf.H.{1} ((liftToAnalytic y).obj F) n :=
  letI := IsGrothendieckAbelian.hasExt.{1}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{1})
  (TopCat.sheafHULiftAddEquiv.{0, 1, 1} (TopCat.of (ComplexPoints y)) F n).trans
    (TopCat.sheafHULiftRestrictionAddEquiv.{1} (ComplexPoints y) _ n)

/-- `liftToAnalyticHAddEquiv` is natural in the sheaf. -/
theorem liftToAnalyticHAddEquiv_naturality
    {F G : Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0}}
    (f : F ⟶ G) (n : ℕ) (x : Sheaf.H.{0} F n) :
    liftToAnalyticHAddEquiv y G n (Sheaf.H.map f n x) =
      Sheaf.H.map ((liftToAnalytic y).map f) n (liftToAnalyticHAddEquiv y F n x) := by
  let := IsGrothendieckAbelian.hasExt.{1}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{1})
  exact (congrArg (TopCat.sheafHULiftRestrictionAddEquiv.{1} (ComplexPoints y) _ n)
    (TopCat.sheafHULiftAddEquiv_naturality.{0, 1, 1} (TopCat.of (ComplexPoints y)) f n x)).trans
    (TopCat.sheafHULiftRestrictionAddEquiv_naturality.{1} (ComplexPoints y) _ n _)

/-- `liftToAnalyticHAddEquiv` is compatible with the connecting maps of short exact
sequences. -/
theorem liftToAnalyticHAddEquiv_comp_extClass
    {S : ShortComplex
      (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})}
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n) :
    liftToAnalyticHAddEquiv y S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (liftToAnalyticHAddEquiv y S.X₃ n x).comp
        (hS.map_of_exact (liftToAnalytic y)).extClass rfl := by
  let := IsGrothendieckAbelian.hasExt.{1}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{1})
  have h1 := TopCat.sheafHULiftAddEquiv_comp_extClass.{0, 1, 1} (TopCat.of (ComplexPoints y)) hS n x
  have h2 := TopCat.sheafHULiftRestrictionAddEquiv_comp_extClass.{1} (ComplexPoints y)
    (hS.map_of_exact (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{1, 0}
      (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))))) n
    (TopCat.sheafHULiftAddEquiv.{0, 1, 1} (TopCat.of (ComplexPoints y)) S.X₃ n x)
  have key : (hS.map_of_exact (liftToAnalytic y)).extClass =
      ((hS.map_of_exact (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{1, 0}
      (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))))).map_of_exact
        (TopCat.sheafULiftRestriction (ComplexPoints y))).extClass := rfl
  rw [key]
  exact (congrArg (TopCat.sheafHULiftRestrictionAddEquiv.{1} (ComplexPoints y) _ (n + 1)) h1).trans
    h2

end Cohomology

end AlgebraicGeometry.Scheme.ComplexPoints
