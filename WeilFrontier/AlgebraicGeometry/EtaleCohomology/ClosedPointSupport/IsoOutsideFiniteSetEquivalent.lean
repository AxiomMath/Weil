module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Main
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import WeilFrontier.Defs.CategoryTheory.Sites.SheafCohomology.CohomologyBoundProperty
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedPartFiniteSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Cohomology bound properties along maps that are isomorphisms off a finite set

Let `K` be a separably closed field, `X` a scheme of finite type over `K`, `φ : F ⟶ G` a morphism
of constructible abelian sheaves on the small étale site of `X`, and `T` a finite set of closed
points of `X` such that the stalk map `φ_s` is an isomorphism at every geometric point `s` of `X`
lying outside `T`. Then for each cohomology bound property `P` (`fin`, or `van m` for `m ≥ 2`),
`P(X, F)` holds if and only if `P(X, G)` holds.

In degrees `q ≥ 2` the map `H^q(φ)` is bijective. In degrees `0` and `1` one uses the kernel
`𝒦`, image `ℐ` and cokernel `𝒞` of `φ`: these have no cohomology in positive degree, since their
supports consist of closed points, and `H⁰(X, 𝒦)`, `H⁰(X, 𝒞)` are finite, because a global section
of a sheaf is determined by its stalks at the geometric points over the points of `X`, those
stalks vanish outside `T`, and the stalks of a constructible sheaf are finite. The long exact
sequences of `0 → 𝒦 → F → ℐ → 0` and `0 → ℐ → G → 𝒞 → 0` then show that `H^q(X, F)` is finite
exactly when `H^q(X, G)` is, for `q = 0, 1`.

## Main results

* `AddMonoidHom.finite_of_exact`: the middle term of an exact sequence `A → M → N` of abelian
  groups with `A` and `N` finite is finite.
* `CategoryTheory.Abelian.Ext.finite_iff_of_kernel_cokernel`: in an abelian category, if the
  kernel and the cokernel of `φ : F ⟶ G` have finite `Ext⁰(X, -)` and vanishing `Ext^q(X, -)` for
  `q > 0`, then `Ext^q(X, F)` is finite if and only if `Ext^q(X, G)` is, in every degree.
* `AlgebraicGeometry.injective_globalSections_toPresheafFiber_smallEtale`: on the small étale
  site, global sections inject into the product of the stalks at the geometric points over the
  points of `X`.
* `AlgebraicGeometry.finite_sheafH_zero_of_isZero_sheafFiber_of_notMem`: `H⁰` of a sheaf whose
  stalks are finite at the points of a finite set `T` and zero elsewhere is finite.
* `AlgebraicGeometry.cohomologyBoundProperty_holds_iff_of_isIso_sheafFiber_map_of_notMem`: the
  theorem.

## Implementation notes

Geometric points are over algebraically closed fields, and the stalk at a geometric point `s` is
the fibre functor of `AlgebraicGeometry.geometricPointSitePoint`. Coefficients are abelian groups
in universe `u + 1` and cohomology is `CategoryTheory.Sheaf.H` at the `Ext` universe `u + 1`, the
setting of `AlgebraicGeometry.bijective_sheafH_map_of_isIso_sheafFiber_map_of_notMem`.
Constructibility is `AlgebraicGeometry.IsConstructibleAbelianSheaf` (Stacks, Tag 03RW).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.5.
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' u

/-- The middle term of an exact sequence `A → M → N` of abelian groups whose outer terms are
finite is finite. -/
theorem AddMonoidHom.finite_of_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M]
    [AddCommGroup N] [Finite A] [Finite N] (f : A →+ M) (g : M →+ N)
    (hfg : ∀ m, g m = 0 → ∃ a, f a = m) : Finite M := by
  have : Finite g.ker := by
    refine Finite.of_injective (fun m : g.ker => (⟨m.1, hfg m.1 m.2⟩ : Set.range f)) ?_
    intro m m' h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have : Finite (M ⧸ g.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange g).symm.toEquiv
  exact Finite.of_addSubgroup_quotient g.ker

namespace CategoryTheory.Abelian.Ext

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasExt.{w} C] (X : C)

/-- Postcomposition with a monomorphism is injective on `Ext⁰(X, -)`. -/
theorem injective_postcomp_mk₀_zero_of_mono {Y Z : C} (f : Y ⟶ Z) [Mono f] :
    Function.Injective ((mk₀ f).postcomp X (add_zero 0)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  change (mk₀ g).comp (mk₀ f) (add_zero 0) = 0 at hx
  rw [mk₀_comp_mk₀, mk₀_eq_zero_iff] at hx
  change mk₀ g = 0
  rw [mk₀_eq_zero_iff]
  exact (cancel_mono f).1 (by simpa using hx)

/-- In an abelian category, if the kernel and the cokernel of `φ : F ⟶ G` have finite
`Ext⁰(X, -)` and vanishing `Ext^q(X, -)` for every `q > 0`, then `Ext^q(X, F)` is finite if and
only if `Ext^q(X, G)` is, for every `q`. -/
theorem finite_iff_of_kernel_cokernel {F G : C} (φ : F ⟶ G)
    (hK₀ : Finite (Ext X (kernel φ) 0)) (hC₀ : Finite (Ext X (cokernel φ) 0))
    (hK : ∀ q : ℕ, 0 < q → Subsingleton (Ext X (kernel φ) q))
    (hC : ∀ q : ℕ, 0 < q → Subsingleton (Ext X (cokernel φ) q)) (q : ℕ) :
    Finite (Ext X F q) ↔ Finite (Ext X G q) := by
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
  rcases q with _ | _ | q
  · -- degree `0`
    have e₁ : Finite (Ext X F 0) ↔ Finite (Ext X (Abelian.image φ) 0) := by
      constructor
      · intro _
        refine Finite.of_surjective ((mk₀ S₁.g).postcomp X (add_zero 0)) fun x₃ => ?_
        obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ X hS₁ x₃ (zero_add 1)
          (by have := hK 1 one_pos; exact Subsingleton.elim _ _)
        exact ⟨x₂, hx₂⟩
      · intro _
        exact AddMonoidHom.finite_of_exact ((mk₀ S₁.f).postcomp X (add_zero 0))
          ((mk₀ S₁.g).postcomp X (add_zero 0))
          fun x hx => covariant_sequence_exact₂ X hS₁ x hx
    have e₂ : Finite (Ext X (Abelian.image φ) 0) ↔ Finite (Ext X G 0) := by
      constructor
      · intro _
        exact AddMonoidHom.finite_of_exact ((mk₀ S₂.f).postcomp X (add_zero 0))
          ((mk₀ S₂.g).postcomp X (add_zero 0))
          fun x hx => covariant_sequence_exact₂ X hS₂ x hx
      · intro _
        exact Finite.of_injective _
          (injective_postcomp_mk₀_zero_of_mono X (Abelian.image.ι φ))
    exact e₁.trans e₂
  · -- degree `1`
    have h₁ := bijective_postcomp_mk₀_g_of_subsingleton X hS₁ 1 (hK 1 one_pos) (hK 2 two_pos)
    have e₁ : Finite (Ext X F 1) ↔ Finite (Ext X (Abelian.image φ) 1) :=
      (Equiv.ofBijective _ h₁).finite_iff
    have e₂ : Finite (Ext X (Abelian.image φ) 1) ↔ Finite (Ext X G 1) := by
      constructor
      · intro _
        refine Finite.of_surjective ((mk₀ S₂.f).postcomp X (add_zero 1)) fun x₂ => ?_
        have := hC 1 one_pos
        obtain ⟨x₁, hx₁⟩ := covariant_sequence_exact₂ X hS₂ x₂ (Subsingleton.elim _ _)
        exact ⟨x₁, hx₁⟩
      · intro _
        refine AddMonoidHom.finite_of_exact (hS₂.extClass.postcomp X (zero_add 1))
          ((mk₀ S₂.f).postcomp X (add_zero 1)) fun x hx => ?_
        exact covariant_sequence_exact₁ X hS₂ x hx (zero_add 1)
    exact e₁.trans e₂
  · -- degrees `≥ 2`
    exact (Equiv.ofBijective _ (bijective_postcomp_mk₀_of_subsingleton_kernel_cokernel X φ
      hK hC (q + 2) (by omega))).finite_iff

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The geometric point of `X` at a point `x`, as a lift of itself to the final object of the
small étale site. -/
def geometricPointSitePointFinalElement (x : X.obj) :
    (geometricPointSitePoint B X.obj X.property (GeometricPoint.ofPoint X.obj x)).fiber.obj
      (SmallEtale.final B X.obj X.property) :=
  ⟨(GeometricPoint.ofPoint X.obj x).hom, by simp [SmallEtale.final]⟩

/-- **Global sections inject into the product of the geometric stalks.** On the small étale site
of `X`, a global section of an abelian sheaf is determined by its germs at the geometric points
over the points of `X`: two sections with the same germs agree on an étale neighbourhood of each
point, and these neighbourhoods cover `X`. -/
theorem injective_globalSections_toPresheafFiber_smallEtale (H : SmallEtaleAbelianSheaf B X) :
    Function.Injective (fun (a : ToType (H.obj.obj (op (SmallEtale.final B X.obj X.property))))
      (x : X.obj) => (geometricPointSitePoint B X.obj X.property
        (GeometricPoint.ofPoint X.obj x)).toPresheafFiber _
        (geometricPointSitePointFinalElement B X x) H.obj a) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  intro a b hab
  have h := fun x : X.obj =>
    (GrothendieckTopology.Point.toPresheafFiber_eq_iff' _ _ _ a b).1 (congrFun hab x)
  choose Y f y hy hf using h
  have hcov : Sieve.ofArrows Y f ∈ SmallEtale.topology B X.obj X.property
      (SmallEtale.final B X.obj X.property) := by
    refine SmallEtale.mem_topology_of_jointlySurjective fun x => ⟨Y x, f x,
      Sieve.ofArrows_mk _ _ x, (y x).1 default, ?_⟩
    have h1 : (y x).1 ≫ (SmallEtale.toScheme B X.obj X.property).map (f x) =
        (GeometricPoint.ofPoint X.obj x).hom := congrArg Subtype.val (hy x)
    change ((y x).1 ≫ (SmallEtale.toScheme B X.obj X.property).map (f x)) default = x
    rw [h1]
    exact GeometricPoint.ofPoint_liesOver X.obj x
  have hsh := ((sheafCompose (SmallEtale.topology B X.obj X.property)
    (forget AddCommGrpCat.{u + 1})).obj H).property
  rw [isSheaf_iff_isSheaf_of_type] at hsh
  refine (hsh _ hcov).isSeparatedFor.ext fun Z g hg => ?_
  obtain ⟨x, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  change H.obj.map (h ≫ f x).op a = H.obj.map (h ≫ f x).op b
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hf x]

/-- An abelian sheaf on the small étale site of `X` whose stalks at the geometric points over the
points of a finite set `T` are finite, and vanish over the points outside `T`, has finite
`H⁰`. -/
theorem finite_sheafH_zero_of_isZero_sheafFiber_of_notMem
    (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (T : Set X.obj) (hT : T.Finite)
    (hfin : ∀ x ∈ T, Finite ↑((geometricPointSitePoint B X.obj X.property
      (GeometricPoint.ofPoint X.obj x)).presheafFiber.obj H.obj))
    (hzero : ∀ x ∉ T, IsZero ((geometricPointSitePoint B X.obj X.property
      (GeometricPoint.ofPoint X.obj x)).sheafFiber.obj H)) :
    Finite (Sheaf.H.{u + 1, u + 1} H 0) := by
  have : Finite T := hT.to_subtype
  have : ∀ x : T, Finite ↑((geometricPointSitePoint B X.obj X.property
      (GeometricPoint.ofPoint X.obj x)).presheafFiber.obj H.obj) := fun x => hfin x x.2
  let germ := fun (a : ToType (H.obj.obj (op (SmallEtale.final B X.obj X.property))))
      (x : X.obj) => (geometricPointSitePoint B X.obj X.property
        (GeometricPoint.ofPoint X.obj x)).toPresheafFiber _
        (geometricPointSitePointFinalElement B X x) H.obj a
  have hinj : Function.Injective fun a (x : T) => germ a x := by
    intro a b hab
    refine injective_globalSections_toPresheafFiber_smallEtale B X H (funext fun x => ?_)
    by_cases hx : x ∈ T
    · exact congrFun hab ⟨x, hx⟩
    · have := AddCommGrpCat.isZero_iff_subsingleton.1 (hzero x hx)
      exact @Subsingleton.elim _ this _ _
  have : Finite (ToType (H.obj.obj (op (SmallEtale.final B X.obj X.property)))) :=
    Finite.of_injective _ hinj
  exact Finite.of_equiv _
    (Sheaf.H.equiv₀ H (SmallEtale.finalIsTerminal B X.obj X.property)).toEquiv.symm

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **FK I.5.** Let `K` be a separably closed field, `X` a scheme of finite type over `K`,
`φ : F ⟶ G` a morphism of constructible abelian sheaves on the small étale site of `X`, and `T` a
finite set of closed points of `X` such that the stalk map `φ_s` is an isomorphism at every
geometric point `s` of `X` lying outside `T`. Then for every cohomology bound property `P`,
`P(X, F)` holds if and only if `P(X, G)` holds. -/
@[weil "lem_fk105_iso_outside_finite_set_equivalent"]
theorem cohomologyBoundProperty_holds_iff_of_isIso_sheafFiber_map_of_notMem
    (K : Type u) [Field K] [IsSepClosed K]
    (f : X.obj ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    {F G : SmallEtaleAbelianSheaf B X} (φ : F ⟶ G)
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G)
    (T : Set X.obj) (hTfin : T.Finite) (hT : ∀ x ∈ T, IsClosed ({x} : Set X.obj))
    (hφ : ∀ s : GeometricPoint X.obj, (∀ x ∈ T, ¬ s.LiesOver x) →
      IsIso ((geometricPointSitePoint B X.obj X.property s).sheafFiber.map φ))
    (P : Sheaf.CohomologyBoundProperty) :
    P.Holds F ↔ P.Holds G := by
  obtain ⟨hKc, hCc, -⟩ := isConstructibleAbelianSheaf_kernel_cokernel_biprod B X φ hF hG
  have hK := (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K X f _
    (supportSheaf_subset_closedPoints_of_isZero_sheafFiber B X _ T hT fun s hs ↦
      isZero_sheafFiber_kernel_of_isIso B X φ s (hφ s hs))).1
  have hC := (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K X f _
    (supportSheaf_subset_closedPoints_of_isZero_sheafFiber B X _ T hT fun s hs ↦
      isZero_sheafFiber_cokernel_of_isIso B X φ s (hφ s hs))).1
  have hnot : ∀ x ∉ T, ∀ y ∈ T, ¬ (GeometricPoint.ofPoint X.obj x).LiesOver y := by
    intro x hx y hy h
    have hxy : x = y := (GeometricPoint.ofPoint_liesOver X.obj x).symm.trans h
    exact hx (hxy ▸ hy)
  have hK₀ : Finite (Sheaf.H.{u + 1, u + 1} (kernel φ) 0) :=
    finite_sheafH_zero_of_isZero_sheafFiber_of_notMem B X _ T hTfin
      (fun x _ => finite_etaleStalk_of_isConstructibleAbelianSheaf.{u, 0} B X _ hKc _)
      (fun x hx => isZero_sheafFiber_kernel_of_isIso B X φ _ (hφ _ (hnot x hx)))
  have hC₀ : Finite (Sheaf.H.{u + 1, u + 1} (cokernel φ) 0) :=
    finite_sheafH_zero_of_isZero_sheafFiber_of_notMem B X _ T hTfin
      (fun x _ => finite_etaleStalk_of_isConstructibleAbelianSheaf.{u, 0} B X _ hCc _)
      (fun x hx => isZero_sheafFiber_cokernel_of_isIso B X φ _ (hφ _ (hnot x hx)))
  cases P with
  | fin =>
    exact forall_congr' fun q =>
      Abelian.Ext.finite_iff_of_kernel_cokernel _ φ hK₀ hC₀ hK hC q
  | van m hm =>
    refine forall_congr' fun q => imp_congr_right fun hq => ?_
    have hb := bijective_sheafH_map_of_isIso_sheafFiber_map_of_notMem B X K f φ T hT hφ q
      (hm.trans hq)
    exact ⟨fun _ => hb.2.subsingleton, fun _ => hb.1.subsingleton⟩

end AlgebraicGeometry

end
