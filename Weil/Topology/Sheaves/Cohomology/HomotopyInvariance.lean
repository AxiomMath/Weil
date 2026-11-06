module

public import Weil.Topology.Sheaves.Cohomology.PullbackMap
public import Weil.Topology.Sheaves.Cohomology.UnitInterval
public import Weil.Topology.Sheaves.Cohomology.ProperBaseChangeAbelian
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.UnitOnSections
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible

/-!
# Homotopy invariance of sheaf cohomology with constant coefficients

Let `f : X ⟶ Y` be a continuous map and `G` an abelian sheaf on `X`. The **edge map**
`Hⁿ(Y, f_* G) → Hⁿ(X, G)` is the pullback `f^*` followed by the counit `f⁻¹ f_* G ⟶ G`. If `f` is
proper and separated and `G` has acyclic fibres (its restriction to every fibre `f⁻¹(y)` has no
cohomology in positive degrees), the edge map is bijective in every degree: in degree `0` it is
the adjunction `Hom(ℤ_Y, f_* G) ≃ Hom(f⁻¹ ℤ_Y, G)`, and the higher degrees follow by dimension
shifting along `0 → G → J → J/G → 0` with `J` injective, because proper base change identifies
the stalks of `f_* G` with the sections over the fibres, so that `f_*` keeps such sequences short
exact and `J/G` again has acyclic fibres.

If moreover the fibres are connected and the constant sheaf `M_X` has acyclic fibres, then
`M_Y ⟶ f_* M_X` is an isomorphism (on stalks it is `M → Γ(f⁻¹(y), M) = M`), and the pullback
`f^* : Hⁿ(Y, M) → Hⁿ(X, M)` factors as this isomorphism followed by the edge map: it is bijective
(a Vietoris–Begle theorem for proper maps).

The projection `p : [0, 1] × X → X` is proper and separated with fibres `[0, 1]`, whose
cohomology with constant coefficients vanishes in positive degrees. Hence `p^*` is bijective for
every topological space `X`, the inclusions `iₜ : X → [0, 1] × X` all induce `(p^*)⁻¹`, and
homotopic maps induce the same map on cohomology. A contractible space then has the cohomology of
a point; in particular nonempty convex and star-convex subsets of real topological vector spaces
are acyclic.

## Main definitions

* `TopCat.SheafCohomology.pushforwardCohomologyMap f G n : Hⁿ(Y, f_* G) →+ Hⁿ(X, G)`: the edge
  map.
* `TopCat.SheafCohomology.constantSheafToPushforward f M : M_Y ⟶ f_* M_X`.
* `TopCat.SheafCohomology.HasAcyclicFibers f G`: the restrictions of `G` to the fibres of `f` have
  vanishing positive-degree cohomology.
* `TopCat.SheafCohomology.cylinder X`, `cylinderProj X`, `cylinderIncl X t`: `[0, 1] × X`, the
  projection to `X` and the inclusion at level `t`.
* `TopCat.SheafCohomology.constantSheafHZeroAddEquivOfConnectedSpace`,
  `TopCat.SheafCohomology.constantSheafHZeroAddEquivOfContractibleSpace`,
  `TopCat.SheafCohomology.constantSheafHZeroAddEquivOfConvex`,
  `TopCat.SheafCohomology.constantSheafHZeroAddEquivOfStarConvex`: `H⁰(X, A) ≃+ A`.

## Main results

* `CategoryTheory.Abelian.Ext.bijective_of_dimension_shifting`: an abstract dimension-shifting
  criterion for a family of maps `Extⁿ(B, F G) → Extⁿ(A, G)` to be bijective.
* `TopCat.SheafCohomology.pushforwardCohomologyMap_bijective`: degenerate Leray, for a proper
  separated map and a sheaf with acyclic fibres, as bijectivity of the edge map.
* `TopCat.SheafCohomology.isIso_constantSheafToPushforward`: `M_Y ≅ f_* M_X` for a proper
  separated map with connected fibres.
* `TopCat.SheafCohomology.constantCohomologyPullback_bijective_of_isProperMap`: Vietoris–Begle
  for proper separated maps with connected acyclic fibres.
* `TopCat.SheafCohomology.constantCohomologyPullback_cylinderProj_bijective`: `p^*` is bijective
  for `p : [0, 1] × X → X`.
* `TopCat.SheafCohomology.constantCohomologyPullback_eq_of_homotopic`: homotopic maps induce
  equal maps on cohomology with constant coefficients.
* `TopCat.SheafCohomology.subsingleton_H_of_contractibleSpace`: contractible spaces are acyclic;
  `subsingleton_H_of_convex` and `subsingleton_H_of_starConvex` for nonempty convex and
  star-convex sets.

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ`, on the site
`Opens.grothendieckTopology X`, and the pullback with constant coefficients is
`TopCat.SheafCohomology.constantCohomologyPullback`. Degenerate Leray is proved for the edge map
itself rather than taken from the derived-functor isomorphism
`TopologicalSpace.ProperBaseChange.sheafHAddEquivPushforward`: that isomorphism is built from right
derived functors, and identifying it with the pullback would need the comparison of the two
constructions. Only the degree-zero proper base change (`stalkToFiberSections`) and the
acyclicity of injective sheaves on fibres are used from proper base change.

The cohomology of `[0, 1]` and of the point `[0, 0]` is known in coefficient universe `0`
(`unitInterval.subsingleton_H_constantSheaf`), so the statements from the cylinder on are for
spaces in `TopCat.{0}`; everything before it is universe polymorphic.

## References

* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* B. Iversen, *Cohomology of Sheaves*, Universitext, Springer, 1986
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian Opposite
open Stacks.Cohomology.AbelianColimit (sheafPullback)

universe u

namespace TopCat.SheafCohomology

set_option quotPrecheck false in
/-- Abelian sheaves on a topological space, at the site spelling. -/
local notation "Sh(" X ")" => CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
set_option quotPrecheck false in
/-- The constant sheaf functor on a topological space. -/
local notation "c(" X ")" => constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **The edge map** `Hⁿ(Y, f_* G) → Hⁿ(X, G)`: the pullback to `Hⁿ(X, f⁻¹ f_* G)` followed by
the counit `f⁻¹ f_* G ⟶ G`. -/
def pushforwardCohomologyMap (G : Sh(X)) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} ((sheafPushforward f).obj G) n →+ CategoryTheory.Sheaf.H.{u} G n :=
  (CategoryTheory.Sheaf.H.map ((pullbackAdjunction f).counit.app G) n).comp
    (cohomologyPullback f _ n)

/-- Unfolding of the edge map. -/
theorem pushforwardCohomologyMap_apply (G : Sh(X)) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} ((sheafPushforward f).obj G) n) :
    pushforwardCohomologyMap f G n x =
      CategoryTheory.Sheaf.H.map ((pullbackAdjunction f).counit.app G) n
        (cohomologyPullback f _ n x) := rfl

/-- The edge map is natural in the sheaf. -/
theorem pushforwardCohomologyMap_map {G G' : Sh(X)} (φ : G ⟶ G') (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} ((sheafPushforward f).obj G) n) :
    pushforwardCohomologyMap f G' n
        (CategoryTheory.Sheaf.H.map ((sheafPushforward f).map φ) n x) =
      CategoryTheory.Sheaf.H.map φ n (pushforwardCohomologyMap f G n x) := by
  rw [pushforwardCohomologyMap_apply, pushforwardCohomologyMap_apply, cohomologyPullback_map,
    ← CategoryTheory.Sheaf.H.map_comp_apply, ← CategoryTheory.Sheaf.H.map_comp_apply]
  congr 2
  exact (pullbackAdjunction f).counit.naturality φ

/-- The edge map commutes with connecting homomorphisms. -/
theorem pushforwardCohomologyMap_comp_extClass {S : ShortComplex Sh(X)} (hS : S.ShortExact)
    (hS' : (S.map (sheafPushforward f)).ShortExact) {n : ℕ}
    (x : CategoryTheory.Sheaf.H.{u} ((sheafPushforward f).obj S.X₃) n) :
    pushforwardCohomologyMap f S.X₁ (n + 1) (x.comp hS'.extClass rfl) =
      (pushforwardCohomologyMap f S.X₃ n x).comp hS.extClass rfl := by
  let φ : (S.map (sheafPushforward f)).map (sheafPullback f) ⟶ S :=
    { τ₁ := (pullbackAdjunction f).counit.app S.X₁
      τ₂ := (pullbackAdjunction f).counit.app S.X₂
      τ₃ := (pullbackAdjunction f).counit.app S.X₃
      comm₁₂ := ((pullbackAdjunction f).counit.naturality S.f).symm
      comm₂₃ := ((pullbackAdjunction f).counit.naturality S.g).symm }
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (hS'.map_of_exact (sheafPullback f)) hS φ
  rw [pushforwardCohomologyMap_apply, pushforwardCohomologyMap_apply, cohomologyPullback_apply,
    cohomologyPullback_apply, CategoryTheory.Sheaf.H.map_apply, CategoryTheory.Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, hnat, Ext.comp_assoc_of_second_deg_zero]
  exact (Ext.comp_assoc _ _ _ _ _ (by omega)).symm


/-- In degree zero the edge map is bijective: it is the adjunction bijection
`Hom(ℤ_Y, f_* G) ≃ Hom(f⁻¹ ℤ_Y, G)` followed by `ℤ_X ≅ f⁻¹ ℤ_Y`. -/
theorem pushforwardCohomologyMap_zero_bijective (G : Sh(X)) :
    Function.Bijective (pushforwardCohomologyMap f G 0) := by
  let e := (constantSheafIsoPullback f).app (AddCommGrpCat.of (ULift ℤ))
  have key : ∀ φ : c(Y).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafPushforward f).obj G,
      pushforwardCohomologyMap f G 0 (Ext.mk₀ φ) =
        Ext.mk₀ (e.hom ≫ ((pullbackAdjunction f).homEquiv _ _).symm φ) := by
    intro φ
    rw [pushforwardCohomologyMap_apply, cohomologyPullback_apply, Ext.mapExactFunctor_mk₀,
      Ext.mk₀_comp_mk₀, CategoryTheory.Sheaf.H.map_apply, Ext.mk₀_comp_mk₀,
      Adjunction.homEquiv_counit, Category.assoc]
    rfl
  have hpre : Function.Bijective (fun ψ : (sheafPullback f).obj
      (c(Y).obj (AddCommGrpCat.of (ULift ℤ))) ⟶ G => e.hom ≫ ψ) :=
    ⟨fun _ _ h => (cancel_epi e.hom).1 h, fun ψ => ⟨e.inv ≫ ψ, by simp⟩⟩
  have hcomp : (pushforwardCohomologyMap f G 0) ∘ Ext.mk₀ =
      Ext.mk₀ ∘ (fun ψ => e.hom ≫ ψ) ∘ ((pullbackAdjunction f).homEquiv _ _).symm := by
    funext φ; exact key φ
  have hb : Function.Bijective ((pushforwardCohomologyMap f G 0) ∘ Ext.mk₀) := by
    rw [hcomp]
    exact (Ext.mk₀_bijective _ _).comp (hpre.comp (Equiv.bijective _))
  exact (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _)).1 hb

/-- The comparison `M_Y ⟶ f_* M_X` of constant sheaves: the adjunct of `f⁻¹ M_Y ≅ M_X`. -/
def constantSheafToPushforward (M : AddCommGrpCat.{u}) :
    c(Y).obj M ⟶ (sheafPushforward f).obj (c(X).obj M) :=
  (pullbackAdjunction f).unit.app (c(Y).obj M) ≫
    (sheafPushforward f).map ((constantSheafIsoPullback f).inv.app M)

/-- **The pullback with constant coefficients factors through the edge map**:
`f^* = (Hⁿ(Y, f_* M_X) → Hⁿ(X, M_X)) ∘ (Hⁿ(Y, M_Y) → Hⁿ(Y, f_* M_X))`. -/
theorem constantCohomologyPullback_eq_pushforwardCohomologyMap (M : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} (c(Y).obj M) n) :
    constantCohomologyPullback f M n x =
      pushforwardCohomologyMap f _ n
        (CategoryTheory.Sheaf.H.map (constantSheafToPushforward f M) n x) := by
  rw [pushforwardCohomologyMap_apply, cohomologyPullback_map,
    ← CategoryTheory.Sheaf.H.map_comp_apply,
    constantCohomologyPullback_apply]
  congr 2
  rw [constantSheafToPushforward, Functor.map_comp, Category.assoc]
  erw [(pullbackAdjunction f).counit.naturality ((constantSheafIsoPullback f).inv.app M)]
  rw [← Category.assoc]
  erw [(pullbackAdjunction f).left_triangle_components]
  rw [Category.id_comp]
  rfl


/-- **Dimension shifting for edge maps.** Let `F : C ⥤ D` be a left exact functor between
abelian categories, `P` a class of objects of `C` containing the injectives, and
`E_G : Extⁿ(B, F G) → Extⁿ(A, G)` maps which are natural in `G`, commute with the connecting
maps of the short exact sequences that `F` keeps short exact, and are bijective in degree `0`.
If `F` preserves injectives and for every short exact `0 → G₁ → G₂ → G₃ → 0` with `G₁, G₂ ∈ P`
also `G₃ ∈ P` and `0 → F G₁ → F G₂ → F G₃ → 0` is short exact, then `E_G` is bijective in every
degree for every `G ∈ P`. -/
theorem _root_.CategoryTheory.Abelian.Ext.bijective_of_dimension_shifting
    {C D : Type*} [Category C] [Abelian C] [HasExt C] [EnoughInjectives C]
    [Category D] [Abelian D] [HasExt D] (F : C ⥤ D) [F.Additive] (P : C → Prop) (A : C) (B : D)
    (E : ∀ (G : C) (n : ℕ), Ext B (F.obj G) n →+ Ext A G n)
    (hnat : ∀ {G G' : C} (φ : G ⟶ G') (n : ℕ) (x : Ext B (F.obj G) n),
      E G' n (x.comp (Ext.mk₀ (F.map φ)) (add_zero n)) = (E G n x).comp (Ext.mk₀ φ) (add_zero n))
    (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (hS' : (S.map F).ShortExact) (n : ℕ)
      (x : Ext B (F.obj S.X₃) n),
      E S.X₁ (n + 1) (x.comp hS'.extClass rfl) = (E S.X₃ n x).comp hS.extClass rfl)
    (h0 : ∀ G, Function.Bijective (E G 0))
    (hinj : ∀ (J : C) [Injective J], P J) (hinjF : ∀ (J : C) [Injective J], Injective (F.obj J))
    (hP : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hF : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₁ → (S.map F).ShortExact) :
    ∀ (n : ℕ) (G : C), P G → Function.Bijective (E G n) := by
  intro n
  induction n with
  | zero => exact fun G _ => h0 G
  | succ n ih =>
    intro G hG
    let I : InjectivePresentation G := Classical.arbitrary _
    have : Mono I.f := I.mono
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective S.X₂ := I.injective
    have hJ : P S.X₂ := hinj S.X₂
    have hQ : P S.X₃ := hP hS hG hJ
    have hS' := hF hS hG
    have : Injective (S.map F).X₂ := hinjF S.X₂
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (E S.X₂ n) (E S.X₃ n) (E S.X₁ (n + 1))
      (AddMonoidHom.ext fun x => (hnat S.g n x).symm)
      (AddMonoidHom.ext fun x => (hδ hS hS' n x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B hS' n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
      (ih _ hJ).surjective (ih _ hQ)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS' x₁ (Ext.eq_zero_of_injective _) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS y₁ (Ext.eq_zero_of_injective _) rfl)

/-! ### Sheaves with acyclic fibres -/

/-- An abelian sheaf on `X` has **acyclic fibres** along `f` when its restriction to every fibre
of `f` has vanishing cohomology in positive degrees. -/
def HasAcyclicFibers
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ (y : Y) (q : ℕ), 0 < q →
    Subsingleton (CategoryTheory.Sheaf.H.{u} ((Stacks.Topology.restrictionFunctor X
      (TopologicalSpace.ProperBaseChange.fiber f y)).obj G) q)

section AcyclicFibers

attribute [local instance] HasDerivedCategory.standard

variable {f}

/-- An injective abelian sheaf has acyclic fibres along a separated map with quasi-compact
fibres: its restriction to a fibre is acyclic for global sections. -/
theorem hasAcyclicFibers_of_injective
    (hcompact : ∀ y, IsCompact (TopologicalSpace.ProperBaseChange.fiber f y))
    (hsep : IsSeparatedMap (f.hom : X → Y))
    (J : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective J] :
    HasAcyclicFibers f J := by
  intro y q hq
  have h := TopologicalSpace.ProperBaseChange.rightAcyclic_sections_restriction_of_injective y
    (hcompact y) hsep J
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at h
  exact AddCommGrpCat.subsingleton_of_isZero ((h q hq).of_iso
    (TopologicalSpace.ProperBaseChange.sheafHIsoRightDerivedSections.{u}
      (TopCat.of (TopologicalSpace.ProperBaseChange.fiber f y)) _ q))

end AcyclicFibers

section Leray

variable {f}

/-- In a short exact sequence whose first two terms have acyclic fibres, so does the third. -/
theorem hasAcyclicFibers_X₃ {S : ShortComplex Sh(X)} (hS : S.ShortExact)
    (h₁ : HasAcyclicFibers f S.X₁) (h₂ : HasAcyclicFibers f S.X₂) : HasAcyclicFibers f S.X₃ := by
  intro y q hq
  have hR := hS.map_of_exact
    (Stacks.Topology.restrictionFunctor X (TopologicalSpace.ProperBaseChange.fiber f y))
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ x : CategoryTheory.Sheaf.H.{u} ((Stacks.Topology.restrictionFunctor X
      (TopologicalSpace.ProperBaseChange.fiber f y)).obj S.X₃) q, x = 0 := by
    intro x
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hR x rfl
      (@Subsingleton.elim _ (h₁ y (q + 1) (by omega)) _ _)
    rw [← hx₂, @Subsingleton.elim _ (h₂ y q hq) x₂ 0, Ext.zero_comp]
  rw [h0 a, h0 b]

/-- Global sections over a fibre are surjective on the last map of a short exact sequence whose
first term has acyclic fibres. -/
theorem fiberSections_surjective {S : ShortComplex Sh(X)} (hS : S.ShortExact)
    (h₁ : HasAcyclicFibers f S.X₁) (y : Y) :
    Function.Surjective ((TopologicalSpace.ProperBaseChange.fiberSectionsFunctor f y).map S.g) := by
  have hR := hS.map_of_exact
    (Stacks.Topology.restrictionFunctor X (TopologicalSpace.ProperBaseChange.fiber f y))
  intro s
  let hT : IsTerminal (⊤ : Opens (TopCat.of (TopologicalSpace.ProperBaseChange.fiber f y))) :=
    isTerminalTop
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hR
    ((CategoryTheory.Sheaf.H.equiv₀ _ hT).symm s) rfl (@Subsingleton.elim _ (h₁ y 1 one_pos) _ _)
  refine ⟨CategoryTheory.Sheaf.H.equiv₀ _ hT x₂, ?_⟩
  have := CategoryTheory.Sheaf.H.equiv₀_naturality (hT := hT)
    (f := (Stacks.Topology.restrictionFunctor X
      (TopologicalSpace.ProperBaseChange.fiber f y)).map S.g) x₂
  refine this.trans ?_
  rw [CategoryTheory.Sheaf.H.map_apply]
  erw [hx₂]
  simp


/-- **Direct image of a short exact sequence.** For a closed separated map with quasi-compact
fibres, the direct image of a short exact sequence whose first term has acyclic fibres is short
exact: surjectivity on stalks is surjectivity on sections over the fibres. -/
theorem shortExact_map_pushforward (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : ∀ y, IsCompact (TopologicalSpace.ProperBaseChange.fiber f y))
    (hsep : IsSeparatedMap (f.hom : X → Y)) {S : ShortComplex Sh(X)} (hS : S.ShortExact)
    (h₁ : HasAcyclicFibers f S.X₁) : (S.map (sheafPushforward f)).ShortExact := by
  have hmono : Mono ((sheafPushforward f).map S.f) := by
    have := hS.mono_f
    infer_instance
  have hex : (S.map (sheafPushforward f)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
  have hepi : Epi ((sheafPushforward f).map S.g) := by
    refine (TopCat.Sheaf.isLocallySurjective_iff_epi (C := AddCommGrpCat.{u})
      ((sheafPushforward f).map S.g)).1 ?_
    refine (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2 fun y => ?_
    have hiso := TopologicalSpace.ProperBaseChange.isIso_stalkToFiberSections y hclosed
      (hcompact y) hsep
    have hnat := (TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).naturality S.g
    have h2 := ConcreteCategory.bijective_of_isIso
      ((TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).app S.X₂)
    have h3 := ConcreteCategory.bijective_of_isIso
      ((TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).app S.X₃)
    intro t
    obtain ⟨u, hu⟩ := fiberSections_surjective hS h₁ y
      ((TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).app S.X₃ t)
    obtain ⟨v, rfl⟩ := h2.2 u
    refine ⟨v, h3.1 ?_⟩
    have := ConcreteCategory.congr_hom hnat v
    simp only [ConcreteCategory.comp_apply] at this
    exact this.trans hu
  exact ShortComplex.ShortExact.mk' hex hmono hepi


/-- The edge maps are bijective in every degree on the sheaves with acyclic fibres. -/
theorem pushforwardCohomologyMap_bijective (hf : IsProperMap (f.hom : X → Y))
    (hsep : IsSeparatedMap (f.hom : X → Y)) (n : ℕ) (G : Sh(X)) (hG : HasAcyclicFibers f G) :
    Function.Bijective (pushforwardCohomologyMap f G n) := by
  have hcompact : ∀ y, IsCompact (TopologicalSpace.ProperBaseChange.fiber f y) :=
    fun _ => hf.isCompact_preimage isCompact_singleton
  exact CategoryTheory.Abelian.Ext.bijective_of_dimension_shifting (sheafPushforward f)
    (HasAcyclicFibers f) _ _ (pushforwardCohomologyMap f)
    (fun φ n x => pushforwardCohomologyMap_map f φ n x)
    (fun hS hS' n x => pushforwardCohomologyMap_comp_extClass f hS hS' x)
    (pushforwardCohomologyMap_zero_bijective f)
    (fun J _ => hasAcyclicFibers_of_injective hcompact hsep J)
    (fun J _ => Adjunction.map_injective (pullbackAdjunction f) J inferInstance)
    (fun hS h₁ h₂ => hasAcyclicFibers_X₃ hS h₁ h₂)
    (fun hS h₁ => shortExact_map_pushforward hf.isClosedMap hcompact hsep hS h₁) n G hG

end Leray

/-! ### Constant sections -/

/-- The unit of the constant sheaf adjunction sends `a` to the constant global section `a`. -/
theorem constantSheafAdjunction_unit_apply (Z : TopCat.{u}) (A : AddCommGrpCat.{u}) (a : A) :
    (constantSheafAdjunction Z).unit.app A a =
      Weil.ConstantSheafSections.constSection (X := Z) A ⊤ a := by
  rfl

/-- `M_Y ⟶ f_* M_X` sends the constant global section `a` to the constant global section `a`. -/
theorem constantSheafToPushforward_unit (M : AddCommGrpCat.{u}) (a : M) :
    (constantSheafToPushforward f M).hom.app (op ⊤) ((constantSheafAdjunction Y).unit.app M a) =
      (constantSheafAdjunction X).unit.app M a := by
  have h : ((constantSheafIsoPullback f).hom.app M).hom.app (op ⊤)
      ((constantSheafAdjunction X).unit.app M a) =
      ((pullbackAdjunction f).unit.app (c(Y).obj M)).hom.app (op ⊤)
        ((constantSheafAdjunction Y).unit.app M a) :=
    (ConcreteCategory.congr_hom (constantSheafIsoPullback_unit f M) a).trans
      (ConcreteCategory.comp_apply _ _ a)
  change ((constantSheafIsoPullback f).inv.app M).hom.app (op ⊤)
    (((pullbackAdjunction f).unit.app (c(Y).obj M)).hom.app (op ⊤)
      ((constantSheafAdjunction Y).unit.app M a)) = _
  rw [← h]
  have h4 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op ⊤))
    ((constantSheafIsoPullback f).hom_inv_id_app M)) ((constantSheafAdjunction X).unit.app M a)
  exact h4

/-- The section of `f⁻¹ M_Y` induced by the constant global section `a` of `M_Y` is the constant
section `a`, through `M_X ≅ f⁻¹ M_Y`. -/
theorem ambientSection_constantSheaf_unit (M : AddCommGrpCat.{u}) (a : M)
    (h : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤) :
    Stacks.Topology.ambientSection f (c(Y).obj M) h ((constantSheafAdjunction Y).unit.app M a) =
      ((constantSheafIsoPullback f).hom.app M).hom.app (op ⊤)
        ((constantSheafAdjunction X).unit.app M a) := by
  have h2 := ConcreteCategory.congr_hom (constantSheafIsoPullback_unit f M) a
  simp only [ConcreteCategory.comp_apply] at h2
  have h3 := ConcreteCategory.congr_hom (Stacks.Topology.ambientSection_eq_unit f
    (c(Y).obj M : TopCat.Sheaf AddCommGrpCat.{u} Y) ⊤) ((constantSheafAdjunction Y).unit.app M a)
  exact h3.trans ((ConcreteCategory.comp_apply _ _ a).symm.trans h2.symm)

variable {f} in
/-- **Direct image of a constant sheaf along a map with connected fibres.** For a closed separated
map `f` with quasi-compact connected fibres, the comparison `M_Y ⟶ f_* M_X` is an isomorphism:
on stalks it is `M → Γ(f⁻¹(y), M) = M`. -/
theorem isIso_constantSheafToPushforward (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : ∀ y, IsCompact (TopologicalSpace.ProperBaseChange.fiber f y))
    (hsep : IsSeparatedMap (f.hom : X → Y))
    (hconn : ∀ y, ConnectedSpace (TopologicalSpace.ProperBaseChange.fiber f y))
    (M : AddCommGrpCat.{u}) : IsIso (constantSheafToPushforward f M) := by
  have hstalk : ∀ y : Y, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (constantSheafToPushforward f M).hom) := by
    intro y
    have hiso := TopologicalSpace.ProperBaseChange.isIso_stalkToFiberSections y hclosed
      (hcompact y) hsep
    have hτ := ConcreteCategory.bijective_of_isIso
      ((TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).app (c(X).obj M))
    have hg := Weil.ConstantSheafSections.germ_constSection_top_bijective (X := Y) M y
    let i := Stacks.subsetInclusion X (TopologicalSpace.ProperBaseChange.fiber f y)
    have hfib : Function.Bijective (fun a : M =>
        ((constantSheafIsoPullback i).hom.app M).hom.app (op ⊤)
          (Weil.ConstantSheafSections.constSection
            (X := TopCat.of (TopologicalSpace.ProperBaseChange.fiber f y)) M ⊤ a)) := by
      have := hconn y
      refine (ConcreteCategory.bijective_of_isIso
        (((constantSheafIsoPullback i).hom.app M).hom.app (op ⊤))).comp ?_
      exact Weil.ConstantSheafSections.constSection_bijective M (by
        rw [Opens.coe_top]; exact isConnected_univ)
    have key : ∀ a : M,
        (TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).app (c(X).obj M)
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            (constantSheafToPushforward f M).hom
            ((Weil.ConstantSheafSections.constSheaf (X := Y) M).presheaf.germ ⊤ y
              (Opens.mem_top y)
              (Weil.ConstantSheafSections.constSection (X := Y) M ⊤ a))) =
        ((constantSheafIsoPullback i).hom.app M).hom.app (op ⊤)
          (Weil.ConstantSheafSections.constSection
            (X := TopCat.of (TopologicalSpace.ProperBaseChange.fiber f y)) M ⊤ a) := by
      intro a
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      erw [constantSheafToPushforward_unit f M a]
      erw [Stacks.Topology.fiberStalkSectionsMap_germ]
      exact ambientSection_constantSheaf_unit i M a _
    have hcomp : Function.Bijective
        (((TopologicalSpace.ProperBaseChange.stalkToFiberSections f y).app (c(X).obj M)) ∘
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            (constantSheafToPushforward f M).hom)) := by
      refine (Function.Bijective.of_comp_iff _ hg).1
        ⟨fun a b hab => hfib.1 ((key a).symm.trans (hab.trans (key b))), fun z => ?_⟩
      obtain ⟨a, ha⟩ := hfib.2 z
      exact ⟨a, (key a).trans ha⟩
    exact (Function.Bijective.of_comp_iff' hτ _).1 hcomp
  have : ∀ y : Y, IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (constantSheafToPushforward f M).hom) :=
    fun y => (ConcreteCategory.isIso_iff_bijective _).2 (hstalk y)
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    (F := (c(Y).obj M : TopCat.Sheaf AddCommGrpCat.{u} Y)) (constantSheafToPushforward f M)

/-- A morphism of sheaves which is an isomorphism induces a bijection on cohomology. -/
theorem sheafH_map_bijective {F G : Sh(X)} (φ : F ⟶ G) [IsIso φ] (n : ℕ) :
    Function.Bijective (CategoryTheory.Sheaf.H.map.{u} φ n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨CategoryTheory.Sheaf.H.map (inv φ) n, fun x => ?_,
    fun x => ?_⟩
  · rw [← CategoryTheory.Sheaf.H.map_comp_apply, IsIso.hom_inv_id,
      CategoryTheory.Sheaf.H.map_id_apply]
  · rw [← CategoryTheory.Sheaf.H.map_comp_apply, IsIso.inv_hom_id,
      CategoryTheory.Sheaf.H.map_id_apply]

variable {f} in
/-- **Proper maps with connected acyclic fibres induce isomorphisms on cohomology with constant
coefficients** (a Vietoris–Begle theorem). Let `f` be a proper separated map whose fibres are
connected, such that the constant sheaf `M_X` has vanishing positive-degree cohomology on every
fibre. Then `f^* : Hⁿ(Y, M) → Hⁿ(X, M)` is bijective for every `n`. -/
theorem constantCohomologyPullback_bijective_of_isProperMap (hf : IsProperMap (f.hom : X → Y))
    (hsep : IsSeparatedMap (f.hom : X → Y))
    (hconn : ∀ y, ConnectedSpace (TopologicalSpace.ProperBaseChange.fiber f y))
    (M : AddCommGrpCat.{u}) (hM : HasAcyclicFibers f (c(X).obj M)) (n : ℕ) :
    Function.Bijective (constantCohomologyPullback f M n) := by
  have hcompact : ∀ y, IsCompact (TopologicalSpace.ProperBaseChange.fiber f y) :=
    fun _ => hf.isCompact_preimage isCompact_singleton
  have := isIso_constantSheafToPushforward hf.isClosedMap hcompact hsep hconn M
  have e : constantCohomologyPullback f M n =
      (pushforwardCohomologyMap f _ n).comp
        (CategoryTheory.Sheaf.H.map (constantSheafToPushforward f M) n) :=
    AddMonoidHom.ext (constantCohomologyPullback_eq_pushforwardCohomologyMap f M n)
  rw [e]
  exact (pushforwardCohomologyMap_bijective hf hsep n _ hM).comp
    (sheafH_map_bijective _ n)

/-- A homeomorphism induces a bijection on cohomology with constant coefficients. -/
theorem constantCohomologyPullback_bijective_of_iso (φ : X ≅ Y) (M : AddCommGrpCat.{u})
    (n : ℕ) : Function.Bijective (constantCohomologyPullback φ.hom M n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨constantCohomologyPullback φ.inv M n,
    fun x => ?_, fun x => ?_⟩
  · rw [← constantCohomologyPullback_comp, φ.inv_hom_id, constantCohomologyPullback_id]
  · rw [← constantCohomologyPullback_comp, φ.hom_inv_id, constantCohomologyPullback_id]

end TopCat.SheafCohomology

namespace TopCat.SheafCohomology

open unitInterval

/-! ### Homotopy invariance -/

/-- The cylinder `[0, 1] × X` on a topological space. -/
abbrev cylinder (X : TopCat.{0}) : TopCat.{0} := TopCat.of (I × X)

/-- The projection `[0, 1] × X → X`. -/
def cylinderProj (X : TopCat.{0}) : cylinder X ⟶ X := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The inclusion `x ↦ (t, x)` of `X` into the cylinder at the level `t`. -/
def cylinderIncl (X : TopCat.{0}) (t : I) : X ⟶ cylinder X :=
  TopCat.ofHom ⟨fun x => (t, x), by fun_prop⟩

/-- The inclusions are sections of the projection. -/
@[reassoc (attr := simp)]
theorem cylinderIncl_proj (X : TopCat.{0}) (t : I) : cylinderIncl X t ≫ cylinderProj X = 𝟙 X :=
  rfl

/-- The projection of the cylinder is separated. -/
theorem isSeparatedMap_cylinderProj (X : TopCat.{0}) :
    IsSeparatedMap ((cylinderProj X).hom : cylinder X → X) := by
  rw [isSeparatedMap_iff_disjoint_nhds]
  rintro ⟨t, x⟩ ⟨s, x'⟩ (h : x = x') hne
  subst h
  have hts : t ≠ s := fun h => hne (by rw [h])
  rw [nhds_prod_eq, nhds_prod_eq]
  exact Filter.disjoint_prod.2 (Or.inl (disjoint_nhds_nhds.2 hts))

/-- The fibre of the cylinder over `x` is `[0, 1]`. -/
def cylinderFiberHomeomorph (X : TopCat.{0}) (x : X) :
    TopologicalSpace.ProperBaseChange.fiber (cylinderProj X) x ≃ₜ I where
  toFun z := z.1.1
  invFun t := ⟨(t, x), rfl⟩
  left_inv z := by
    obtain ⟨⟨t, y⟩, hy⟩ := z
    have : y = x := hy
    subst this
    rfl
  right_inv t := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The constant sheaf on the cylinder has acyclic fibres along the projection: the fibres are
copies of `[0, 1]`. -/
theorem hasAcyclicFibers_cylinderProj (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    HasAcyclicFibers (cylinderProj X)
      ((constantSheaf (Opens.grothendieckTopology (cylinder X)) AddCommGrpCat.{0}).obj A) := by
  intro x q hq
  let i := Stacks.subsetInclusion (cylinder X)
    (TopologicalSpace.ProperBaseChange.fiber (cylinderProj X) x)
  let φ : TopCat.of (TopologicalSpace.ProperBaseChange.fiber (cylinderProj X) x) ≅ TopCat.of I :=
    TopCat.isoOfHomeo (cylinderFiberHomeomorph X x)
  have h1 := unitInterval.subsingleton_H_constantSheaf A q hq
  have h2 := (constantCohomologyPullback_bijective_of_iso φ A q).2
  have h3 := (sheafH_map_bijective ((constantSheafIsoPullback i).hom.app A) q).2
  constructor
  intro a b
  obtain ⟨a', rfl⟩ := h3 a
  obtain ⟨b', rfl⟩ := h3 b
  obtain ⟨a'', rfl⟩ := h2 a'
  obtain ⟨b'', rfl⟩ := h2 b'
  rw [Subsingleton.elim a'' b'']

/-- **Homotopy invariance, the cylinder.** The projection `p : [0, 1] × X → X` induces a bijection
`p^* : Hⁿ(X, A) → Hⁿ([0, 1] × X, A)` on cohomology with constant coefficients. -/
theorem constantCohomologyPullback_cylinderProj_bijective (X : TopCat.{0})
    (A : AddCommGrpCat.{0}) (n : ℕ) :
    Function.Bijective (constantCohomologyPullback (cylinderProj X) A n) :=
  constantCohomologyPullback_bijective_of_isProperMap (isProperMap_snd_of_compactSpace)
    (isSeparatedMap_cylinderProj X)
    (fun x => (cylinderFiberHomeomorph X x).symm.surjective.connectedSpace
      (cylinderFiberHomeomorph X x).symm.continuous)
    A (hasAcyclicFibers_cylinderProj X A) n

/-- The inclusions of `X` into the cylinder at every level induce the same map on cohomology:
the inverse of `p^*`. -/
theorem constantCohomologyPullback_cylinderIncl_eq (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (n : ℕ) (s t : I) :
    constantCohomologyPullback (cylinderIncl X s) A n =
      constantCohomologyPullback (cylinderIncl X t) A n := by
  ext y
  obtain ⟨z, rfl⟩ := (constantCohomologyPullback_cylinderProj_bijective X A n).2 y
  rw [← constantCohomologyPullback_comp, ← constantCohomologyPullback_comp, cylinderIncl_proj,
    cylinderIncl_proj]

/-- **Homotopy invariance of sheaf cohomology with constant coefficients.** Homotopic maps
`f ≃ g : X → Y` induce the same map `Hⁿ(Y, A) → Hⁿ(X, A)`. -/
theorem constantCohomologyPullback_eq_of_homotopic {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (A : AddCommGrpCat.{0}) (n : ℕ) :
    constantCohomologyPullback f A n = constantCohomologyPullback g A n := by
  obtain ⟨F⟩ := h
  let H : cylinder X ⟶ Y := TopCat.ofHom F.toContinuousMap
  have hf : f = cylinderIncl X 0 ≫ H := by ext x; exact (F.apply_zero x).symm
  have hg : g = cylinderIncl X 1 ≫ H := by ext x; exact (F.apply_one x).symm
  ext y
  rw [hf, hg, constantCohomologyPullback_comp, constantCohomologyPullback_comp,
    constantCohomologyPullback_cylinderIncl_eq X A n 0 1]

/-! ### Contractible spaces -/

section Contractible

/-- The one-point space `[0, 0]`, on which the cohomology of a constant sheaf is known. -/
abbrev pointInterval : TopCat.{0} := TopCat.of (Set.Icc (0 : ℝ) 0)

instance : Subsingleton pointInterval :=
  ⟨fun a b => Subtype.ext ((le_antisymm a.2.2 a.2.1).trans (le_antisymm b.2.2 b.2.1).symm)⟩

/-- The map from a space to the point. -/
def toPointInterval (X : TopCat.{0}) : X ⟶ pointInterval :=
  TopCat.ofHom (ContinuousMap.const X ⟨0, le_rfl, le_rfl⟩)

/-- **`H⁰` of a connected space with constant coefficients is the coefficient group**: global
sections of the constant sheaf on a connected space are constant. -/
noncomputable def constantSheafHZeroAddEquivOfConnectedSpace (Z : TopCat.{u}) [ConnectedSpace Z]
    (M : AddCommGrpCat.{u}) :
    CategoryTheory.Sheaf.H.{u}
      ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj M) 0 ≃+ M :=
  (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).trans
    (AddEquiv.ofBijective ((Weil.ConstantSheafSections.toConst (X := Z) M).app (op ⊤)).hom
      (Weil.ConstantSheafSections.constSection_bijective M (U := ⊤) (by
        rw [Opens.coe_top]; exact isConnected_univ))).symm

variable (X : TopCat.{0}) [ContractibleSpace X] (A : AddCommGrpCat.{0})

/-- **A contractible space has the cohomology of a point**: the map `X → pt` induces a bijection
`Hⁿ(pt, A) → Hⁿ(X, A)` in every degree. -/
theorem constantCohomologyPullback_toPointInterval_bijective (n : ℕ) :
    Function.Bijective (constantCohomologyPullback (toPointInterval X) A n) := by
  obtain ⟨x₀, h⟩ := id_nullhomotopic X
  let s : pointInterval ⟶ X := TopCat.ofHom (ContinuousMap.const _ x₀)
  have hcs : ContinuousMap.Homotopic (TopCat.Hom.hom (𝟙 X))
      (TopCat.Hom.hom (toPointInterval X ≫ s)) := h
  have hsc : s ≫ toPointInterval X = 𝟙 pointInterval :=
    ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _
  refine Function.bijective_iff_has_inverse.2 ⟨constantCohomologyPullback s A n, fun y => ?_,
    fun x => ?_⟩
  · rw [← constantCohomologyPullback_comp, hsc, constantCohomologyPullback_id]
  · rw [← constantCohomologyPullback_comp, ← constantCohomologyPullback_eq_of_homotopic hcs,
      constantCohomologyPullback_id]

/-- **A contractible space is acyclic**: `Hⁿ(X, A) = 0` for `n ≥ 1`. -/
theorem subsingleton_H_of_contractibleSpace (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj A) n) := by
  have h := Set.Icc.subsingleton_H_constantSheaf (a := 0) (b := 0) A n hn
  constructor
  intro a b
  obtain ⟨a', rfl⟩ := (constantCohomologyPullback_toPointInterval_bijective X A n).2 a
  obtain ⟨b', rfl⟩ := (constantCohomologyPullback_toPointInterval_bijective X A n).2 b
  rw [Subsingleton.elim a' b']

/-- **`H⁰` of a contractible space with constant coefficients is the coefficient group.** -/
noncomputable def constantSheafHZeroAddEquivOfContractibleSpace :
    CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj A) 0 ≃+ A :=
  constantSheafHZeroAddEquivOfConnectedSpace X A

end Contractible

section Convex

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {s : Set E} (A : AddCommGrpCat.{0})

/-- **A nonempty star-convex subset of a real topological vector space is acyclic** for constant
coefficients: `Hⁿ(s, A) = 0` for `n ≥ 1`. -/
theorem subsingleton_H_of_starConvex {x : E} (hs : StarConvex ℝ x s) (hne : s.Nonempty) (n : ℕ)
    (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of s)) AddCommGrpCat.{0}).obj A) n) :=
  have : ContractibleSpace (TopCat.of s) := hs.contractibleSpace hne
  subsingleton_H_of_contractibleSpace (TopCat.of s) A n hn

/-- `H⁰(s, A) ≃ A` for a nonempty star-convex subset `s` of a real topological vector space. -/
noncomputable def constantSheafHZeroAddEquivOfStarConvex {x : E} (hs : StarConvex ℝ x s)
    (hne : s.Nonempty) :
    CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of s)) AddCommGrpCat.{0}).obj A) 0 ≃+
      A :=
  have : ContractibleSpace (TopCat.of s) := hs.contractibleSpace hne
  constantSheafHZeroAddEquivOfContractibleSpace (TopCat.of s) A

/-- **A nonempty convex subset of a real topological vector space is acyclic** for constant
coefficients: `Hⁿ(s, A) = 0` for `n ≥ 1`. -/
theorem subsingleton_H_of_convex (hs : Convex ℝ s) (hne : s.Nonempty) (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of s)) AddCommGrpCat.{0}).obj A) n) :=
  have : ContractibleSpace (TopCat.of s) := hs.contractibleSpace hne
  subsingleton_H_of_contractibleSpace (TopCat.of s) A n hn

/-- `H⁰(s, A) ≃ A` for a nonempty convex subset `s` of a real topological vector space. -/
noncomputable def constantSheafHZeroAddEquivOfConvex (hs : Convex ℝ s) (hne : s.Nonempty) :
    CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of s)) AddCommGrpCat.{0}).obj A) 0 ≃+
      A :=
  have : ContractibleSpace (TopCat.of s) := hs.contractibleSpace hne
  constantSheafHZeroAddEquivOfContractibleSpace (TopCat.of s) A

end Convex

end TopCat.SheafCohomology
