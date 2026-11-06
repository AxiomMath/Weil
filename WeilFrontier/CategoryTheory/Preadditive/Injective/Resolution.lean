module

public import Weil.Attr
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.AB
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# Pointwise injective resolutions of diagrams

Let `A` be an abelian category with enough injectives and the products indexed by the objects
and the morphism sets of a category `I`. Every diagram `F : I ⥤ A` admits a resolution
`F ⟶ J⁰ ⟶ J¹ ⟶ ⋯` by diagrams `Jᵏ : I ⥤ A` and natural transformations such that, for every
object `ν` of `I`, every `Jᵏ(ν)` is injective in `A` and `0 ⟶ F(ν) ⟶ J⁰(ν) ⟶ J¹(ν) ⟶ ⋯` is
exact. This applies in particular to sheaves of `R`-modules on the small étale site of a
scheme.

The diagram `injectiveHull G` is the product over the objects `ν` of `I` of the right adjoint
of evaluation at `ν` applied to an injective object containing `G(ν)`; its value at `μ` is
`∏_ν ∏_{μ ⟶ ν} I(G(ν))`. It is injective in `I ⥤ A` and pointwise injective, and `G` embeds
into it. Hence `I ⥤ A` has enough injectives, and every injective object of `I ⥤ A` is a
retract of its injective hull, hence pointwise injective. An injective resolution of `F` in the
abelian category `I ⥤ A` therefore evaluates, at every `ν`, to an injective resolution of
`F(ν)`, evaluation being exact.

## Main definitions

* `CategoryTheory.Functor.injectiveHull`: a pointwise injective, injective diagram containing a
  given diagram.

## Main results

* `CategoryTheory.Functor.enoughInjectives`: `I ⥤ A` has enough injectives.
* `CategoryTheory.Functor.injective_obj_of_injective_functor`: an injective object of `I ⥤ A` is
  pointwise injective.
* `CategoryTheory.Functor.exists_injective_resolution_pointwise`: pointwise injective
  resolutions of diagrams in `A`.
* `AlgebraicGeometry.SmallEtale.exists_injective_resolution_pointwise`: the same for diagrams of
  sheaves of `R`-modules on the small étale site of a scheme.
* `Stacks.EtaleCohomology.exists_injective_resolution_pointwise`: the same on Mathlib's small
  étale site, for the category `Stacks.EtaleCohomology.EtaleModules`.

## Implementation notes

The resolution is an injective resolution in the functor category `I ⥤ A` rather than the
inductive construction through cokernels of the source: the two give the same kind of
resolution, and the functor category is abelian with kernels and cokernels computed pointwise.
The noetherian and separatedness hypotheses on the scheme are not needed, and the small étale
site is the one of all schemes étale over `S` in a big étale site.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v₁ u₁ r

namespace CategoryTheory.Functor

variable {I : Type u₁} [Category.{v₁} I] {A : Type u} [Category.{v} A] [Abelian A]
  [EnoughInjectives A] [HasProductsOfShape I A] [∀ a b : I, HasProductsOfShape (a ⟶ b) A]

/-- The injective hull of a diagram: the product over `ν` of the right adjoint to evaluation
at `ν` applied to a chosen injective object containing `G.obj ν`. -/
noncomputable abbrev injectiveHull (G : I ⥤ A) : I ⥤ A :=
  ∏ᶜ fun ν : I => (evaluationRightAdjoint A ν).obj (Injective.under (G.obj ν))

/-- The embedding of a diagram into its injective hull. -/
noncomputable def toInjectiveHull (G : I ⥤ A) : G ⟶ injectiveHull G :=
  Pi.lift fun ν => ((evaluationAdjunctionLeft A ν).homEquiv _ _) (Injective.ι (G.obj ν))

omit [Abelian A] in
/-- The component of `toInjectiveHull G` at `μ`, followed by the projection to the factor
indexed by `μ` and `𝟙 μ`, is the chosen embedding of `G.obj μ` into an injective object. -/
theorem toInjectiveHull_app_comp (G : I ⥤ A) (μ : I) :
    (toInjectiveHull G).app μ ≫ ((Pi.π (fun ν : I => (evaluationRightAdjoint A ν).obj
      (Injective.under (G.obj ν))) μ).app μ ≫ (evaluationAdjunctionLeft A μ).counit.app _) =
      Injective.ι (G.obj μ) := by
  have := ((evaluationAdjunctionLeft A μ).homEquiv _ _).symm_apply_apply (Injective.ι (G.obj μ))
  rw [← this, Adjunction.homEquiv_counit, ← Category.assoc, ← NatTrans.comp_app, toInjectiveHull,
    Pi.lift_π]
  rfl

instance (G : I ⥤ A) (μ : I) : Mono ((toInjectiveHull G).app μ) := by
  have h := toInjectiveHull_app_comp G μ
  have : Mono ((toInjectiveHull G).app μ ≫ ((Pi.π (fun ν : I => (evaluationRightAdjoint A ν).obj
      (Injective.under (G.obj ν))) μ).app μ ≫ (evaluationAdjunctionLeft A μ).counit.app _)) := by
    rw [h]; infer_instance
  exact mono_of_mono _ (((Pi.π (fun ν : I => (evaluationRightAdjoint A ν).obj
      (Injective.under (G.obj ν))) μ).app μ ≫ (evaluationAdjunctionLeft A μ).counit.app _))

instance (G : I ⥤ A) : Mono (toInjectiveHull G) := NatTrans.mono_of_mono_app _

instance (G : I ⥤ A) (μ : I) : Injective ((injectiveHull G).obj μ) := by
  have (ν : I) :
      Injective (((evaluationRightAdjoint A ν).obj (Injective.under (G.obj ν))).obj μ) := by
    exact inferInstanceAs (Injective (∏ᶜ fun _ : μ ⟶ ν => Injective.under (G.obj ν)))
  exact Injective.of_iso (piObjIso _ μ).symm inferInstance

instance (G : I ⥤ A) : Injective (injectiveHull G) := by
  have (ν : I) : Injective ((evaluationRightAdjoint A ν).obj (Injective.under (G.obj ν))) :=
    (evaluationAdjunctionLeft A ν).map_injective _ inferInstance
  unfold injectiveHull; infer_instance

/-- A diagram category with values in an abelian category with enough injectives and the
relevant products has enough injectives. -/
instance enoughInjectives : EnoughInjectives (I ⥤ A) where
  presentation G := ⟨{ J := injectiveHull G, f := toInjectiveHull G }⟩

omit [Abelian A] in
/-- An injective object of `I ⥤ A` is pointwise injective: it is a retract of its injective
hull. (Mathlib's `CategoryTheory.Functor.injective_obj_of_injective` is the different statement
that a functor preserving injective objects sends an injective object to one.) -/
theorem injective_obj_of_injective_functor (J : I ⥤ A) [Injective J] (ν : I) :
    Injective (J.obj ν) :=
  Retract.injective (Y := (injectiveHull J).obj ν)
    { i := (toInjectiveHull J).app ν
      r := (Injective.factorThru (𝟙 J) (toInjectiveHull J)).app ν
      retract := by rw [← NatTrans.comp_app, Injective.comp_factorThru]; rfl }

/-- Every diagram `F : I ⥤ A` has a resolution `F ⟶ J⁰ ⟶ J¹ ⟶ ⋯` by diagrams and natural
transformations which, at every object `ν` of `I`, is an injective resolution of `F.obj ν`. -/
theorem exists_injective_resolution_pointwise (F : I ⥤ A) :
    ∃ (J : CochainComplex (I ⥤ A) ℕ) (d : F ⟶ J.X 0) (hd : d ≫ J.d 0 1 = 0),
      ∀ ν : I, (∀ k, Injective ((J.X k).obj ν)) ∧ Mono (d.app ν) ∧
        (ShortComplex.mk (d.app ν) ((J.d 0 1).app ν)
          (by rw [← NatTrans.comp_app, hd]; rfl)).Exact ∧
        ∀ k, (ShortComplex.mk ((J.d k (k + 1)).app ν) ((J.d (k + 1) (k + 2)).app ν)
          (by rw [← NatTrans.comp_app, J.d_comp_d]; rfl)).Exact := by
  let R : InjectiveResolution F := injectiveResolution F
  refine ⟨R.cocomplex, R.ι.f 0, R.ι_f_zero_comp_complex_d, fun ν => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro k; exact injective_obj_of_injective_functor _ ν
  · exact ((evaluation I A).obj ν).map_mono (R.ι.f 0)
  · exact (ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (R.ι.f 0) (R.cocomplex.d 0 1) R.ι_f_zero_comp_complex_d)
      R.isLimitKernelFork).map ((evaluation I A).obj ν)
  · intro k; exact (R.exact_succ k).map ((evaluation I A).obj ν)

end CategoryTheory.Functor

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (R : Type u) [Ring R]

/-- For a small category `I` and a diagram `F` of sheaves of `R`-modules on the small étale site
of `S`, there are diagrams `Jᵏ` and natural transformations `F ⟶ J⁰ ⟶ J¹ ⟶ ⋯` such that for
every object `ν` of `I` each `Jᵏ(ν)` is an injective sheaf and
`0 ⟶ F(ν) ⟶ J⁰(ν) ⟶ J¹(ν) ⟶ ⋯` is exact. -/
@[weil "lem_fk104_direct_system_injective_resolution"]
theorem exists_injective_resolution_pointwise {I : Type u} [SmallCategory I]
    (F : I ⥤ Sheaf (topology B S hS) (ModuleCat.{u} R)) :
    ∃ (J : CochainComplex (I ⥤ Sheaf (topology B S hS) (ModuleCat.{u} R)) ℕ) (d : F ⟶ J.X 0)
      (hd : d ≫ J.d 0 1 = 0),
      ∀ ν : I, (∀ k, Injective ((J.X k).obj ν)) ∧ Mono (d.app ν) ∧
        (ShortComplex.mk (d.app ν) ((J.d 0 1).app ν)
          (by rw [← NatTrans.comp_app, hd]; rfl)).Exact ∧
        ∀ k, (ShortComplex.mk ((J.d k (k + 1)).app ν) ((J.d (k + 1) (k + 2)).app ν)
          (by rw [← NatTrans.comp_app, J.d_comp_d]; rfl)).Exact := by
  let : Abelian (Sheaf (topology B S hS) (ModuleCat.{u} R)) := sheafIsAbelian
  have : IsGrothendieckAbelian.{u} (Sheaf (topology B S hS) (ModuleCat.{u} R)) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact CategoryTheory.Functor.exists_injective_resolution_pointwise F

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : AlgebraicGeometry.Scheme.{u})

/-- Pointwise injective resolutions of diagrams of sheaves of `Λ`-modules on Mathlib's small
étale site of `X`. -/
theorem exists_injective_resolution_pointwise {I : Type (max (u + 1) r)} [SmallCategory I]
    (F : I ⥤ EtaleModules.{u, r} Λ X) :
    ∃ (J : CochainComplex (I ⥤ EtaleModules.{u, r} Λ X) ℕ) (d : F ⟶ J.X 0)
      (hd : d ≫ J.d 0 1 = 0),
      ∀ ν : I, (∀ k, Injective ((J.X k).obj ν)) ∧ Mono (d.app ν) ∧
        (ShortComplex.mk (d.app ν) ((J.d 0 1).app ν)
          (by rw [← NatTrans.comp_app, hd]; rfl)).Exact ∧
        ∀ k, (ShortComplex.mk ((J.d k (k + 1)).app ν) ((J.d (k + 1) (k + 2)).app ν)
          (by rw [← NatTrans.comp_app, J.d_comp_d]; rfl)).Exact :=
  CategoryTheory.Functor.exists_injective_resolution_pointwise F

end Stacks.EtaleCohomology

end
