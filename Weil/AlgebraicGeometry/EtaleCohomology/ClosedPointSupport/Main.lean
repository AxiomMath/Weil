module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Main
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk

/-!
# Kernel and cokernel of a map that is an isomorphism away from closed points are acyclic

Let `K` be a separably closed field, `X` a scheme of finite type over `K`, and
`φ : F ⟶ G` a morphism of abelian sheaves on the small étale site of `X`. Suppose `T` is a set
of closed points of `X` such that the stalk map `φ_s` is bijective at every geometric point `s`
of `X` lying outside `T`. Then the kernel and the cokernel of `φ` have vanishing cohomology in
every positive degree.

Indeed, stalks are exact, so the stalks of `ker φ` and `coker φ` vanish at every geometric point
outside `T`; their supports therefore consist of closed points, and Stacks Tag 0F1F applies.

## Main results

* `AlgebraicGeometry.isZero_etaleStalk_kernel_of_bijective`,
  `AlgebraicGeometry.isZero_etaleStalk_cokernel_of_bijective`: the stalk of the kernel
  (cokernel) of `φ` vanishes where the stalk map of `φ` is bijective.
* `AlgebraicGeometry.subsingleton_sheafH_kernel_and_cokernel_of_bijective_etaleStalk`: the
  acyclicity statement.

## Implementation notes

Geometric points are over algebraically closed fields, and the stalk at a geometric point `s`
is `etaleStalkPresheafFunctor` applied to the underlying presheaf. Coefficients are abelian
groups in universe `u + 1` and cohomology is `CategoryTheory.Sheaf.H` at the `Ext` universe
`u + 1`, the setting of
`AlgebraicGeometry.subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints`.
The finiteness of `T` is not needed: it suffices that every point of `T` is closed.

## References

* [FK] Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The stalk of the kernel of `φ` vanishes at a geometric point where `φ` is injective on
stalks. -/
theorem isZero_etaleStalk_kernel_of_injective {F G : SmallEtaleAbelianSheaf B X} (φ : F ⟶ G)
    (s : GeometricPoint X.obj)
    (hs : Function.Injective
      ((etaleStalkPresheafFunctor B X.obj X.property s AddCommGrpCat.{u + 1}).map φ.hom)) :
    IsZero (etaleStalk B X.obj X.property s (kernel φ).obj) := by
  have h₁ := (exact_iff_etaleStalk_exact.{u, u + 1} B X.obj X.property
    (ShortComplex.mk (0 : kernel φ ⟶ kernel φ) (kernel.ι φ) (by simp))).1
    ((ShortComplex.exact_iff_mono _ rfl).2 inferInstance) s
  have h₂ := (exact_iff_etaleStalk_exact.{u, u + 1} B X.obj X.property
    (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ))).1
    (ShortComplex.exact_kernel φ) s
  simp only at h₁ h₂
  have : (etaleStalkPresheafFunctor B X.obj X.property s AddCommGrpCat.{u + 1}).Additive :=
    inferInstanceAs
      (elementColimit (geometricPointFiber B X.obj X.property s) AddCommGrpCat.{u + 1}).Additive
  have hall : ∀ b : ↑((etaleStalkPresheafFunctor B X.obj X.property s
      AddCommGrpCat.{u + 1}).obj (kernel φ).obj), b = 0 := by
    intro b
    have hb := (h₂ _).2 ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := (h₁ b).1 (hs (hb.trans (map_zero _).symm))
    rw [← ha, Functor.map_zero]
    rfl
  have : Subsingleton ↑((etaleStalkPresheafFunctor B X.obj X.property s
      AddCommGrpCat.{u + 1}).obj (kernel φ).obj) :=
    ⟨fun a b => (hall a).trans (hall b).symm⟩
  rw [← etaleStalkPresheafFunctor_obj]
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The stalk of the cokernel of `φ` vanishes at a geometric point where `φ` is surjective on
stalks. -/
theorem isZero_etaleStalk_cokernel_of_surjective {F G : SmallEtaleAbelianSheaf B X} (φ : F ⟶ G)
    (s : GeometricPoint X.obj)
    (hs : Function.Surjective
      ((etaleStalkPresheafFunctor B X.obj X.property s AddCommGrpCat.{u + 1}).map φ.hom)) :
    IsZero (etaleStalk B X.obj X.property s (cokernel φ).obj) := by
  have h₁ := (exact_iff_etaleStalk_exact.{u, u + 1} B X.obj X.property
    (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ))).1
    (ShortComplex.exact_cokernel φ) s
  have h₂ := (exact_iff_etaleStalk_exact.{u, u + 1} B X.obj X.property
    (ShortComplex.mk (cokernel.π φ) (0 : cokernel φ ⟶ cokernel φ) (by simp))).1
    ((ShortComplex.exact_iff_epi _ rfl).2 (show Epi (cokernel.π φ) from inferInstance)) s
  simp only at h₁ h₂
  have : (etaleStalkPresheafFunctor B X.obj X.property s AddCommGrpCat.{u + 1}).Additive :=
    inferInstanceAs
      (elementColimit (geometricPointFiber B X.obj X.property s) AddCommGrpCat.{u + 1}).Additive
  have hall : ∀ c : ↑((etaleStalkPresheafFunctor B X.obj X.property s
      AddCommGrpCat.{u + 1}).obj (cokernel φ).obj), c = 0 := by
    intro c
    obtain ⟨g, rfl⟩ := (h₂ c).1 (by rw [Functor.map_zero]; rfl)
    obtain ⟨a, ha⟩ := hs g
    exact (h₁ g).2 ⟨a, ha⟩
  have : Subsingleton ↑((etaleStalkPresheafFunctor B X.obj X.property s
      AddCommGrpCat.{u + 1}).obj (cokernel φ).obj) :=
    ⟨fun a b => (hall a).trans (hall b).symm⟩
  rw [← etaleStalkPresheafFunctor_obj]
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Let `K` be a separably closed field, `X` a scheme of finite type over `K`, `φ : F ⟶ G` a
morphism of abelian sheaves on the small étale site of `X`, and `T` a set of closed points of
`X` such that `φ` is bijective on the stalk at every geometric point of `X` not lying over a
point of `T`. Then `H^q(X, ker φ) = 0` and `H^q(X, coker φ) = 0` for every `q > 0`. -/
@[weil "lem_fk105_iso_outside_finite_set_kernel_acyclic"]
theorem subsingleton_sheafH_kernel_and_cokernel_of_bijective_etaleStalk
    (K : Type u) [Field K] [IsSepClosed K] (f : X.obj ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f] {F G : SmallEtaleAbelianSheaf B X} (φ : F ⟶ G)
    (T : Set X.obj) (hT : ∀ x ∈ T, IsClosed ({x} : Set X.obj))
    (hφ : ∀ s : GeometricPoint X.obj, s.hom default ∉ T → Function.Bijective
      ((etaleStalkPresheafFunctor B X.obj X.property s AddCommGrpCat.{u + 1}).map φ.hom))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} (kernel φ) q) ∧
      Subsingleton (Sheaf.H.{u + 1, u + 1} (cokernel φ) q) := by
  constructor
  · refine (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K X f
      (kernel φ) ?_).1 q hq
    rintro x ⟨t, rfl, hnz⟩
    by_contra hx
    refine hnz ((isZero_etaleStalk_ulift_iff.{u, u + 1} B X.obj X.property _ t).2 ?_)
    exact (isZero_etaleStalk_kernel_of_injective B X φ t
      (hφ t fun ht => hx (hT _ ht)).1)
  · refine (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K X f
      (cokernel φ) ?_).1 q hq
    rintro x ⟨t, rfl, hnz⟩
    by_contra hx
    refine hnz ((isZero_etaleStalk_ulift_iff.{u, u + 1} B X.obj X.property _ t).2 ?_)
    exact (isZero_etaleStalk_cokernel_of_surjective B X φ t
      (hφ t fun ht => hx (hT _ ht)).2)

end AlgebraicGeometry

end

/-! ### Isomorphisms outside a finite set induce isomorphisms on cohomology -/

/-!
# A map that is an isomorphism away from closed points is a cohomology isomorphism in degree ≥ 2

Let `K` be a separably closed field, `X` a scheme of finite type over `K`, and `φ : F ⟶ G` a
morphism of abelian sheaves on the small étale site of `X`. Suppose that `T` is a set of closed
points of `X` such that the stalk map `φ_s` is an isomorphism at every geometric point `s` of `X`
lying outside `T`. Then `H^q(φ) : H^q(X, F) → H^q(X, G)` is bijective for every `q ≥ 2`.

Stalks are exact, so the kernel `𝒦` and the cokernel `𝒞` of `φ` have zero stalks outside `T`;
their supports consist of closed points, so they have no cohomology in positive degrees
[Stacks, Tag 0F1F]. Writing `φ` as `F ↠ ℐ ↪ G` through its image, the long exact `Ext`
sequences of `0 → 𝒦 → F → ℐ → 0` and `0 → ℐ → G → 𝒞 → 0` give `H^q(F) ≅ H^q(ℐ)` for `q ≥ 1`
and `H^q(ℐ) ≅ H^q(G)` for `q ≥ 2`.

## Main results

* `CategoryTheory.Abelian.Ext.bijective_postcomp_mk₀_of_subsingleton_kernel_cokernel`: in an
  abelian category, if the kernel and cokernel of `φ` have no `Ext` out of `X` in positive
  degrees, then postcomposition with `φ` is bijective on `Ext X - q` for `q ≥ 2`.
* `AlgebraicGeometry.isZero_sheafFiber_kernel_of_isIso`,
  `AlgebraicGeometry.isZero_sheafFiber_cokernel_of_isIso`: the stalks of the kernel and the
  cokernel vanish where the stalk map is an isomorphism.
* `AlgebraicGeometry.bijective_sheafH_map_of_isIso_sheafFiber_map_of_notMem`: the theorem.

## Implementation notes

Geometric points are over algebraically closed fields, and the stalk at a geometric point `s`
is the fibre functor of the point `AlgebraicGeometry.geometricPointSitePoint` (which is
`AlgebraicGeometry.etaleStalk` by `AlgebraicGeometry.etaleStalk_eq_presheafFiber`). Coefficients
are abelian groups in universe `u + 1` and cohomology is `CategoryTheory.Sheaf.H` at the `Ext`
universe `u + 1`, the setting of
`AlgebraicGeometry.subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints`.
The finiteness of `T` is not needed: it suffices that every point of `T` is closed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.5.
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' u' u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasExt.{w} C] (X : C)

/-- For a short exact sequence `0 → S₁ → S₂ → S₃ → 0` with `Ext^n(X, S₁) = Ext^{n+1}(X, S₁) = 0`,
postcomposition with `S₂ ⟶ S₃` is bijective on `Ext^n(X, -)`. -/
theorem bijective_postcomp_mk₀_g_of_subsingleton {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (h₀ : Subsingleton (Ext X S.X₁ n)) (h₁ : Subsingleton (Ext X S.X₁ (n + 1))) :
    Function.Bijective ((mk₀ S.g).postcomp X (add_zero n)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x₃ ↦ ?_⟩
  · obtain ⟨x₁, rfl⟩ := covariant_sequence_exact₂ X hS x hx
    rw [Subsingleton.elim x₁ 0, zero_comp]
  · obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ X hS x₃ rfl (Subsingleton.elim _ _)
    exact ⟨x₂, hx₂⟩

/-- For a short exact sequence `0 → S₁ → S₂ → S₃ → 0` with `Ext^n(X, S₃) = Ext^{n+1}(X, S₃) = 0`,
postcomposition with `S₁ ⟶ S₂` is bijective on `Ext^{n+1}(X, -)`. -/
theorem bijective_postcomp_mk₀_f_of_subsingleton {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (h₀ : Subsingleton (Ext X S.X₃ n)) (h₁ : Subsingleton (Ext X S.X₃ (n + 1))) :
    Function.Bijective ((mk₀ S.f).postcomp X (add_zero (n + 1))) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x₂ ↦ ?_⟩
  · obtain ⟨x₃, rfl⟩ := covariant_sequence_exact₁ X hS x hx rfl
    rw [Subsingleton.elim x₃ 0, zero_comp]
  · obtain ⟨x₁, hx₁⟩ := covariant_sequence_exact₂ X hS x₂ (Subsingleton.elim _ _)
    exact ⟨x₁, hx₁⟩

/-- In an abelian category, if the kernel and the cokernel of `φ : F ⟶ G` have vanishing
`Ext^q(X, -)` for every `q > 0`, then postcomposition with `φ` is a bijection
`Ext^q(X, F) → Ext^q(X, G)` for every `q ≥ 2`. -/
theorem bijective_postcomp_mk₀_of_subsingleton_kernel_cokernel {F G : C} (φ : F ⟶ G)
    (hK : ∀ q : ℕ, 0 < q → Subsingleton (Ext X (kernel φ) q))
    (hC : ∀ q : ℕ, 0 < q → Subsingleton (Ext X (cokernel φ) q)) (q : ℕ) (hq : 2 ≤ q) :
    Function.Bijective ((mk₀ φ).postcomp X (add_zero q)) := by
  have hzero : kernel.ι φ ≫ Abelian.factorThruImage φ = 0 := by
    rw [← cancel_mono (Abelian.image.ι φ), Category.assoc, Abelian.image.fac,
      kernel.condition, Limits.zero_comp]
  let S₁ := ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ) hzero
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (Abelian.image.ι φ) φ (kernelIsKernel φ) hzero (Abelian.image.fac φ))
      mono_f := inferInstanceAs (Mono (kernel.ι φ))
      epi_g := inferInstanceAs (Epi (Abelian.factorThruImage φ)) }
  let S₂ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (kernel.condition _)
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π φ))
      mono_f := inferInstanceAs (Mono (Abelian.image.ι φ))
      epi_g := inferInstanceAs (Epi (cokernel.π φ)) }
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have h₁ := bijective_postcomp_mk₀_g_of_subsingleton X hS₁ (n + 1)
    (hK _ (by omega)) (hK _ (by omega))
  have h₂ := bijective_postcomp_mk₀_f_of_subsingleton X hS₂ n
    (hC _ (by omega)) (hC _ (by omega))
  have heq : (mk₀ φ).postcomp X (add_zero (n + 1)) =
      ((mk₀ S₂.f).postcomp X (add_zero (n + 1))).comp
        ((mk₀ S₁.g).postcomp X (add_zero (n + 1))) := by
    ext x
    change x.comp (mk₀ φ) (add_zero _) =
      (x.comp (mk₀ S₁.g) (add_zero _)).comp (mk₀ S₂.f) (add_zero _)
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]
    exact congrArg (fun g ↦ x.comp (mk₀ g) (add_zero (n + 1))) (Abelian.image.fac φ).symm
  rw [heq, AddMonoidHom.coe_comp]
  exact h₂.comp h₁

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

section Stalks

variable {F G : SmallEtaleAbelianSheaf B X} (φ : F ⟶ G) (s : GeometricPoint X.obj)

/-- The stalk of the kernel of `φ` vanishes at a geometric point where the stalk map of `φ` is
an isomorphism. -/
theorem isZero_sheafFiber_kernel_of_isIso
    (hs : IsIso ((geometricPointSitePoint B X.obj X.property s).sheafFiber.map φ)) :
    IsZero ((geometricPointSitePoint B X.obj X.property s).sheafFiber.obj (kernel φ)) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ φ)

/-- The stalk of the cokernel of `φ` vanishes at a geometric point where the stalk map of `φ` is
an isomorphism. -/
theorem isZero_sheafFiber_cokernel_of_isIso
    (hs : IsIso ((geometricPointSitePoint B X.obj X.property s).sheafFiber.map φ)) :
    IsZero ((geometricPointSitePoint B X.obj X.property s).sheafFiber.obj (cokernel φ)) :=
  (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ φ)

end Stalks

/-- A sheaf whose stalks vanish at every geometric point lying outside a set `T` of closed points
has its support among the closed points. -/
theorem supportSheaf_subset_closedPoints_of_isZero_sheafFiber (H : SmallEtaleAbelianSheaf B X)
    (T : Set X.obj) (hT : ∀ x ∈ T, IsClosed ({x} : Set X.obj))
    (hH : ∀ s : GeometricPoint X.obj, (∀ x ∈ T, ¬ s.LiesOver x) →
      IsZero ((geometricPointSitePoint B X.obj X.property s).sheafFiber.obj H)) :
    supportSheaf B X.obj X.property H ⊆ {x : X.obj | IsClosed ({x} : Set X.obj)} := by
  rintro x ⟨t, htx, hnz⟩
  rw [isZero_etaleStalk_ulift_iff] at hnz
  by_cases hx : x ∈ T
  · exact hT x hx
  · refine absurd (hH t fun y hy hty ↦ hx ?_) hnz
    rw [← htx]
    exact hty ▸ hy

/-- **FK I.5.** Let `K` be a separably closed field, `X` a scheme of finite type over `K`,
`φ : F ⟶ G` a morphism of abelian sheaves on the small étale site of `X`, and `T` a set of
closed points of `X` such that the stalk map `φ_s` is an isomorphism at every geometric point `s`
of `X` lying outside `T`. Then `H^q(φ) : H^q(X, F) → H^q(X, G)` is bijective for every
`q ≥ 2`. -/
@[weil "lem_fk105_iso_outside_finite_set_cohomology_iso"]
theorem bijective_sheafH_map_of_isIso_sheafFiber_map_of_notMem
    (K : Type u) [Field K] [IsSepClosed K]
    (f : X.obj ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    {F G : SmallEtaleAbelianSheaf B X} (φ : F ⟶ G)
    (T : Set X.obj) (hT : ∀ x ∈ T, IsClosed ({x} : Set X.obj))
    (hφ : ∀ s : GeometricPoint X.obj, (∀ x ∈ T, ¬ s.LiesOver x) →
      IsIso ((geometricPointSitePoint B X.obj X.property s).sheafFiber.map φ))
    (q : ℕ) (hq : 2 ≤ q) :
    Function.Bijective (Sheaf.H.map.{u + 1, u + 1} φ q) :=
  Abelian.Ext.bijective_postcomp_mk₀_of_subsingleton_kernel_cokernel _ φ
    (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K X f _
      (supportSheaf_subset_closedPoints_of_isZero_sheafFiber B X _ T hT fun s hs ↦
        isZero_sheafFiber_kernel_of_isIso B X φ s (hφ s hs))).1
    (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K X f _
      (supportSheaf_subset_closedPoints_of_isZero_sheafFiber B X _ T hT fun s hs ↦
        isZero_sheafFiber_cokernel_of_isIso B X φ s (hφ s hs))).1 q hq

end AlgebraicGeometry

end

/-! ### Sheaves on a curve with zero generic stalk are acyclic -/

/-!
# Sheaves on a curve with zero generic stalk are acyclic

Let `k` be a separably closed field, `X` an integral scheme of finite type over `k` of dimension
at most one (for instance an integral curve over an algebraically closed field), `η̄` the generic
geometric point of `X`, and `F` an abelian sheaf on the small étale site of `X` with `F_η̄ = 0`.
Then `H^q(X, F) = 0` for every `q > 0`.

Indeed, every point of `X` other than the generic point is closed, so the vanishing of the
generic stalk says that the support of `F` consists of closed points, and the cohomology of
such a sheaf vanishes in positive degrees ([Stacks, Tag 0F1F]).

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one`: in an
  irreducible quasi-compact scheme of topological Krull dimension at most one, every point other
  than the generic point is closed.
* `AlgebraicGeometry.subsingleton_sheafH_of_isZero_etaleStalk_genericGeometricPoint`: the
  acyclicity statement.
* `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_isZero_etaleStalk_genericGeometricPoint`:
  the same for a curve over a separably closed field.

## Implementation notes

The source assumes `F` to be a torsion sheaf and reduces to constructible sheaves; the statement
holds for every abelian sheaf, because a sheaf whose support consists of closed points has
vanishing positive-degree cohomology without any torsion hypothesis, so the torsion hypothesis
is dropped. Likewise the base field only needs to be separably closed.

The point-set lemma
`AlgebraicGeometry.isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one` is the
variant of `Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint`
for dimension at most one (rather than exactly one), at the cost of quasi-compactness.

Coefficients are abelian groups in universe `u + 1` and cohomology is `CategoryTheory.Sheaf.H`
at the `Ext` universe `u + 1`, the setting of
`AlgebraicGeometry.subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints`.
Geometric points are over algebraically closed fields; the generic one is
`AlgebraicGeometry.Scheme.genericGeometricPoint`.

## References

* [FK] Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

/-- In an irreducible quasi-compact scheme of topological Krull dimension at most one, every
point other than the generic point is closed. -/
theorem isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [IrreducibleSpace X] [CompactSpace X] (hdim : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  by_contra hxc
  obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  let Z : TopologicalSpace.IrreducibleCloseds X := ⟨{y}, isIrreducible_singleton, hyc⟩
  let Y : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hZY : Z < Y := by
    refine lt_of_le_of_ne (Set.singleton_subset_iff.mpr hy) fun h ↦ hxc ?_
    have hxy : x ∈ ({y} : Set X) := by
      have : (Z : Set X) = Y := congrArg SetLike.coe h
      change x ∈ (Z : Set X)
      rw [this]
      exact subset_closure rfl
    rw [Set.mem_singleton_iff.mp hxy]
    exact hyc
  have hYT : Y < T := by
    refine lt_of_le_of_ne (Set.subset_univ _) fun h ↦ hx ?_
    have hgen : IsGenericPoint x (⊤ : Set X) := by
      rw [isGenericPoint_def]
      exact congrArg SetLike.coe h
    exact hgen.eq (genericPoint_spec X)
  rcases Order.krullDim_le_one_iff.mp hdim Y with hmin | hmax
  · exact hZY.not_isMin hmin |>.elim
  · exact hYT.not_isMax hmax |>.elim

variable (B : BigEtaleSite.{u})

/-- Let `k` be a separably closed field, `X` an integral scheme of finite type over `k` of
dimension at most one, and `F` an abelian sheaf on the small étale site of `X` whose stalk at
the generic geometric point vanishes. Then `H^q(X, F) = 0` for every `q > 0`. -/
@[weil "lem_fk105_torsion_sheaf_zero_generic_stalk_acyclic"]
theorem subsingleton_sheafH_of_isZero_etaleStalk_genericGeometricPoint
    (k : Type u) [Field k] [IsSepClosed k] (X : B.Scheme) [IsIntegral X.obj]
    (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X.obj ≤ 1) (F : SmallEtaleAbelianSheaf B X)
    (hF : IsZero (etaleStalk B X.obj X.property (Scheme.genericGeometricPoint X.obj) F.obj))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  refine (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B k X f F
    ?_).1 q hq
  intro x hx
  by_contra hxc
  have hxη : x = genericPoint X.obj := by
    by_contra h
    exact hxc (isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one X.obj hdim h)
  subst hxη
  rw [mem_supportSheaf_iff B X.obj X.property F (Scheme.genericGeometricPoint X.obj) _
    (Scheme.genericGeometricPoint_liesOver X.obj)] at hx
  exact hx ((isZero_etaleStalk_ulift_iff.{u, u + 1} B X.obj X.property F _).2 hF)

/-- Let `k` be a separably closed field (for instance an algebraically closed one), `X` a curve
over `k`, and `F` an abelian sheaf on the small étale site of `X` whose stalk at the generic
geometric point vanishes. Then `H^q(X, F) = 0` for every `q > 0`. -/
@[weil "lem_fk105_torsion_sheaf_zero_generic_stalk_acyclic"]
theorem IsCurve.subsingleton_sheafH_of_isZero_etaleStalk_genericGeometricPoint
    (k : Type u) [Field k] [IsSepClosed k] (X : B.Scheme) (f : X.obj ⟶ Spec (.of k))
    [IsCurve k f] (F : SmallEtaleAbelianSheaf B X)
    (hF : IsZero (etaleStalk B X.obj X.property (Scheme.genericGeometricPoint X.obj) F.obj))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) :=
  AlgebraicGeometry.subsingleton_sheafH_of_isZero_etaleStalk_genericGeometricPoint B k X f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le F hF q hq

end AlgebraicGeometry

end

/-! ### Acyclicity of étale sheaves supported on a finite closed subscheme -/

/-!
# Acyclicity of étale sheaves supported on a finite closed subscheme

Let `k` be a separably closed field, `X` a `k`-scheme locally of finite type, `i : S ⟶ X` a
closed immersion with `S` finite over `k`, `j : U ⟶ X` the open immersion of the complement of
`S`, and `F` an abelian sheaf on the small étale site of `X` whose restriction `j^* F` to `U`
vanishes. Then `H^q(X, F) = 0` for every `q > 0`.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_of_isZero_smallEtaleInverseImage`: the vanishing
  `H^q(X, F) = 0` for `q > 0`.
* `AlgebraicGeometry.supportSheaf_subset_compl_range_of_isZero_smallEtaleInverseImage`: an
  abelian sheaf whose inverse image along an open immersion vanishes has its support outside
  the image of that open immersion.

## Implementation notes

The source deduces the statement from the description of sheaves supported on a closed
subscheme as direct images and from the cohomology of finite direct images, reducing to the
spectrum of `k`. We argue instead that `j^* F = 0` forces every stalk of `F` at a geometric
point over `U` to vanish (stalks of inverse images are stalks), so that the support of `F` lies
in the image of `S`. That image is a finite set of closed points, since `S` is finite and
discrete over `k`, and the vanishing is then [Stacks, Tag 0F1F] in the form
`AlgebraicGeometry.subsingleton_sheafH_and_epi_counit_of_finite_support`.

The restriction of `F` to the open `U` is the inverse image along `j`. The open `U` is any
open immersion whose image contains the complement of the image of `S`; the source's `U`
is the case of equality. Finite type over `k` is weakened to locally of finite type.
The cohomology groups are `CategoryTheory.Sheaf.H` in any `Ext` universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X U : B.Scheme} (j : U ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

/-- A geometric point of `X` whose image lies in the image of an open immersion `j : U ⟶ X`
is the image of a geometric point of `U`. -/
theorem exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion
    (s : GeometricPoint X.obj) (hs : s.hom default ∈ Set.range (B.inclusion.map j).base) :
    ∃ t : GeometricPoint U.obj, t.map (B.inclusion.map j) = s := by
  have hr : Set.range s.hom.base ⊆ Set.range (B.inclusion.map j).base := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  refine ⟨⟨s.residueField, IsOpenImmersion.lift (B.inclusion.map j) s.hom hr⟩, ?_⟩
  cases s
  simp only [GeometricPoint.map, IsOpenImmersion.lift_fac]

/-- If the inverse image of an abelian sheaf `F` along an open immersion `j : U ⟶ X` vanishes,
then the support of `F` misses the image of `j`. -/
theorem supportSheaf_subset_compl_range_of_isZero_smallEtaleInverseImage
    (F : SmallEtaleAbelianSheaf B X)
    (hF : IsZero ((smallEtaleInverseImage B j AddCommGrpCat.{u + 1}).obj F)) :
    supportSheaf B X.obj X.property F ⊆ (Set.range (B.inclusion.map j).base)ᶜ := by
  rintro x ⟨p, hp, hnz⟩ hx
  obtain ⟨t, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion B j p
    (hp ▸ hx)
  apply hnz
  rw [isZero_etaleStalk_ulift_iff, etaleStalk_eq_presheafFiber]
  refine IsZero.of_iso ?_ ((smallEtaleInverseImageSheafFiberIso B j t _).app F)
  change IsZero ((geometricPointSitePoint B U.obj U.property t).sheafFiber.obj _)
  exact Functor.map_isZero _ hF

/-- The image of a closed immersion `i : S ⟶ X` with `S` finite over a field `k` is a finite set
of closed points of `X`. -/
theorem finite_range_and_isClosed_singleton_of_isFinite {k : Type u} [Field k] {S X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : S ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ f)] :
    (Set.range i.base).Finite ∧ ∀ x ∈ Set.range i.base, IsClosed ({x} : Set X) := by
  have hpre : (i ≫ f).base ⁻¹' {default} = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hfin : (Set.univ : Set S).Finite := hpre ▸ (i ≫ f).finite_preimage_singleton default
  have hdisc : _root_.IsDiscrete (Set.univ : Set S) :=
    hpre ▸ (i ≫ f).isDiscrete_preimage_singleton default
  refine ⟨?_, ?_⟩
  · simpa [Set.image_univ] using hfin.image i.base
  · rintro _ ⟨z, rfl⟩
    have : DiscreteTopology S := isDiscrete_univ_iff.mp hdisc
    simpa [Set.image_singleton] using
      i.isClosedEmbedding.isClosedMap _ (isClosed_discrete ({z} : Set S))

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ in
/-- **Sheaves supported on a finite closed subscheme are acyclic.** Let `k` be a separably closed
field, `X` a scheme locally of finite type over `k`, `i : S ⟶ X` a closed immersion with `S`
finite over `k`, `j : U ⟶ X` an open immersion whose image contains the complement of the image
of `S`, and `F` an abelian sheaf on the small étale site of `X` whose restriction `j^* F` to `U`
vanishes. Then `H^q(X, F) = 0` for every `q > 0`. -/
@[weil "lem_fk105_finite_support_sheaf_acyclic"]
theorem subsingleton_sheafH_of_isZero_smallEtaleInverseImage
    (k : Type u) [Field k] [IsSepClosed k] {S : B.Scheme}
    (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (i : S ⟶ X) [IsClosedImmersion (B.inclusion.map i)] [IsFinite (B.inclusion.map i ≫ f)]
    (hij : (Set.range (B.inclusion.map i).base)ᶜ ⊆ Set.range (B.inclusion.map j).base)
    [HasExt.{w} (SmallEtaleAbelianSheaf B X)] (F : SmallEtaleAbelianSheaf B X)
    (hF : IsZero ((smallEtaleInverseImage B j AddCommGrpCat.{u + 1}).obj F))
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H.{w} F q) := by
  obtain ⟨hfin, hcl⟩ := finite_range_and_isClosed_singleton_of_isFinite f (B.inclusion.map i)
  have hsupp : supportSheaf B X.obj X.property F ⊆ Set.range (B.inclusion.map i).base :=
    fun x hx ↦ by
      by_contra hxi
      exact supportSheaf_subset_compl_range_of_isZero_smallEtaleInverseImage B j F hF hx
        (hij hxi)
  have h := (subsingleton_sheafH_and_epi_counit_of_finite_support B k X f _ hfin hcl F
    hsupp).1 q hq
  exact (Abelian.Ext.chgUniv : Sheaf.H.{u + 1} F q ≃ Sheaf.H.{w} F q).symm.subsingleton

end AlgebraicGeometry
