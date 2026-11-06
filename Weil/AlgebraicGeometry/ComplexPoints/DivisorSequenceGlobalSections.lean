/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.AlgebraicGeometry.ComplexPoints.DivisorSequenceComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDivisorSequence

/-!
# Global sections of the comparison of divisor sequences

Let `Y` be a smooth curve over `ℂ` and `τ : (0 → 𝐆_m → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0) ⟶
ε_* (0 → 𝒪^× → 𝓜^× → 𝒟iv → 0)` the comparison of the étale and the analytic divisor sequences
(`divisorSequenceComparison`). This file computes its components `τ₂` and `τ₃` on global
sections, that is over `Y` itself as an étale `Y`-scheme.

A section of `ε_* G` over `Y` is determined by its value on `Y(ℂ)`, `Y → Y` having exactly one
section over every open of `Y(ℂ)`. Restricting to an affine open `V ∋ x` of `Y` and a local
section of `V(ℂ) → Y(ℂ)` near `x`, where `τ₂` is the analytification along local sections, shows:

* `Γτ₂` sends the global section of `j_* 𝐆_{m,K}` given by `g ∈ K^×` to the meromorphic unit
  `g_an`; by GAGA for functions on a compact `Y(ℂ)` every global meromorphic unit is of this form.

For `τ₃`, a global section of `i_{q,*} ℤ` restricts to zero on `Y ∖ {q}`, so its divisor on `Y(ℂ)`
is supported at `q`; the divisor of `g ∈ K^×` is `x ↦ ord_x g` on both sides; and some `g` has
nonzero order at any given point. Since every global section of `⨁_x i_{x,*} ℤ` is a finite
combination of sections of the summands, this gives:

* `Γτ₃` is the identity on coefficients: read through `Γ(Y, ⨁_x i_{x,*} ℤ) ≃ (Y_0 →₀ ℤ)` and
  `Div(Y(ℂ)) ≃ (Y(ℂ) →₀ ℤ)`, it is `Finsupp.mapDomain` along `Y_0 ≃ Y(ℂ)`; in particular it is
  bijective when `Y(ℂ)` is compact.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.topSection`: the section of `Y(ℂ) → Y(ℂ)` over `W`.
* `AlgebraicGeometry.Scheme.ComplexPoints.globalDivisorComparison`: `Γτ₃` as a map to the
  global divisors of `Y(ℂ)`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.globalSectionsIso_hom_app_apply`: `Γ_et ∘ ε_* ≅ Γ_an`
  is the value along the section `Y(ℂ) → Y(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.evalSection_rationalComparison_etaleTop`,
  `globalSectionsIso_rationalComparison_etaleTop`: `Γτ₂(g) = g_an`.
* `AlgebraicGeometry.Scheme.ComplexPoints.surjective_rationalComparison_etaleTop`,
  `exists_globalSectionsIso_rationalComparison`: on a compact `Y(ℂ)`, `Γτ₂` hits every global
  meromorphic unit.
* `AlgebraicGeometry.Scheme.ComplexPoints.globalDivisorComparison_apply_eq`,
  `globalDivisorComparison_eq`, `divisorSection_globalSectionsIso_divisorComparison`,
  `globalSectionsIso_divisorComparison_etaleTop`: `Γτ₃` is `Finsupp.mapDomain closedPointsEquiv`.
* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_divisorComparison_etaleTop`,
  `bijective_globalSectionsIso_divisorComparison`: on a compact `Y(ℂ)`, `Γτ₃` is bijective.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Filter Manifold Opposite

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### Sections of `ε_* G` over `Y` itself -/

/-- `Y` itself, as an étale `Y`-scheme, is integral when `Y` is. -/
instance isIntegral_etaleTop_left {Y : Scheme.{0}} [IsIntegral Y] : IsIntegral (etaleTop Y).left :=
  inferInstanceAs (IsIntegral Y)

section TopSections

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

/-- The unique continuous section over `W` of `Y(ℂ) → Y(ℂ)`, for the étale `Y`-scheme `Y`. -/
noncomputable def topSection (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) :
    ((sectionsFunctor y).obj (etaleTop Y)).obj.obj W :=
  (default : (sectionsPresheaf y (etaleTop Y)).obj W)

instance subsingleton_sectionsFunctor_etaleTop (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) :
    Subsingleton (((sectionsFunctor y).obj (etaleTop Y)).obj.obj W) :=
  inferInstanceAs (Subsingleton ((sectionsPresheaf y (etaleTop Y)).obj W))

/-- The value of a section of `ε_* G` over `Y` on a section over `W` is the restriction to `W` of
its value on `Y(ℂ)`. -/
theorem evalSection_etaleTop {G : AnSheaf y}
    (t : ToType (((analyticDirectImage y).obj G).obj.obj (op (etaleTop Y))))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj (etaleTop Y)).obj.obj W) :
    evalSection y t σ =
      G.obj.map (homOfLE le_top : W.unop ⟶ ⊤).op (evalSection y t (topSection y (op ⊤))) := by
  have hσ : σ = ((sectionsFunctor y).obj (etaleTop Y)).obj.map (homOfLE le_top : W.unop ⟶ ⊤).op
      (topSection y (op ⊤)) := Subsingleton.elim _ _
  rw [hσ]
  have key := (directImageSectionsEquiv y G (etaleTop Y) t).hom.naturality
      (homOfLE le_top : W.unop ⟶ ⊤).op
  have h2 := ConcreteCategory.congr_hom key (topSection y (op ⊤))
  simp only [ConcreteCategory.comp_apply] at h2
  change ((directImageSectionsEquiv y G (etaleTop Y) t).hom.app _
    (((sectionsFunctor y).obj (etaleTop Y)).obj.map _ (topSection y (op ⊤)))) = _
  rw [h2]
  rfl

/-- The value along a section over `W` of the restriction to an étale `U` of a section of
`ε_* G` over `Y` is the restriction to `W` of its value on `Y(ℂ)`. -/
theorem evalSection_map_etaleTop {G : AnSheaf y} {U : Y.Etale} (φ : U ⟶ etaleTop Y)
    (t : ToType (((analyticDirectImage y).obj G).obj.obj (op (etaleTop Y))))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (((analyticDirectImage y).obj G).obj.map φ.op t) σ =
      G.obj.map (homOfLE le_top : W.unop ⟶ ⊤).op (evalSection y t (topSection y (op ⊤))) := by
  rw [evalSection_map]
  exact evalSection_etaleTop y t _

/-- A section of `ε_* G` over `Y` is determined by its value on `Y(ℂ)`. -/
theorem eq_of_evalSection_topSection {G : AnSheaf y}
    {t t' : ToType (((analyticDirectImage y).obj G).obj.obj (op (etaleTop Y)))}
    (h : evalSection y t (topSection y (op ⊤)) = evalSection y t' (topSection y (op ⊤))) :
    t = t' :=
  evalSection_injective y fun W σ => by
    rw [evalSection_etaleTop y t σ, evalSection_etaleTop y t' σ, h]

set_option hygiene false in
local notation "𝔍" => _root_.Opens.grothendieckTopology 𝔛

omit [LocallyOfFiniteType y] in
/-- Under `ℤ[Φ Y] ≅ ℤ`, the generator of the constant sheaf over `Y(ℂ)` is the section
`Y(ℂ) → Y(ℂ)`. -/
theorem freeSectionsEtaleTopIso_inv_toSheafify :
    (freeSectionsEtaleTopIso y).inv.hom.app (op ⊤)
        ((toSheafify (𝔍) ((Functor.const _).obj (AddCommGrpCat.free.obj PUnit.{2}))).app (op ⊤)
          (FreeAbelianGroup.of PUnit.unit)) =
      (toSheafify (𝔍) (sectionsPresheaf y (etaleTop Y) ⋙ AddCommGrpCat.free)).app (op ⊤)
        (FreeAbelianGroup.of (topSection y (op ⊤))) := by
  let β := Functor.isoWhiskerRight (sectionsPresheafEtaleTopIso y) AddCommGrpCat.free ≪≫
    Functor.constComp _ _ _
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (𝔍) β.inv) (op ⊤))
    (FreeAbelianGroup.of PUnit.unit)).symm

/-- **`Γ_et ∘ ε_* ≅ Γ_an` is the value on `Y(ℂ)`**: the isomorphism `globalSectionsIso` sends a
section of `ε_* G` over `Y` to its value along the section `Y(ℂ) → Y(ℂ)`. -/
theorem globalSectionsIso_hom_app_apply (G : AnSheaf y)
    (t : ToType (((analyticDirectImage y).obj G).obj.obj (op (etaleTop Y)))) :
    (globalSectionsIso y).hom.app G t = evalSection y t (topSection y (op ⊤)) := by
  have hL : (globalSectionsIso y).hom.app G t =
      (show (freeSectionsFunctor y).obj (etaleTop Y) ⟶ G from t).hom.app (op ⊤)
        ((freeSectionsEtaleTopIso y).inv.hom.app (op ⊤)
          ((toSheafify (𝔍) ((Functor.const _).obj (AddCommGrpCat.free.obj PUnit.{2}))).app (op ⊤)
            (FreeAbelianGroup.of PUnit.unit))) := rfl
  have hR : evalSection y t (topSection y (op ⊤)) =
      (show (freeSectionsFunctor y).obj (etaleTop Y) ⟶ G from t).hom.app (op ⊤)
        ((toSheafify (𝔍) (sectionsPresheaf y (etaleTop Y) ⋙ AddCommGrpCat.free)).app (op ⊤)
          (FreeAbelianGroup.of (topSection y (op ⊤)))) := rfl
  rw [hL, hR, freeSectionsEtaleTopIso_inv_toSheafify]

end TopSections

/-! ### Local sections through a point -/

section LocalSections

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

/-- Through every complex point `q` of an étale `U` passes a continuous section of
`U(ℂ) → Y(ℂ)` over an open neighbourhood of the image of `q`. -/
theorem exists_sectionsPresheaf_through (U : Y.Etale) (q : ComplexPoints (U.hom ≫ y)) :
    ∃ (W : TopologicalSpace.Opens 𝔛) (hW : ULift.up (etaleMap y U q) ∈ W)
      (σ : (sectionsPresheaf y U).obj (op W)), (σ.1 ⟨_, hW⟩).down = q := by
  obtain ⟨W, τ, hW, hpW, hτp, hτW, hτ⟩ := exists_local_lift_of_isLocalHomeomorph
    (V := 𝔛) (isLocalHomeomorph_etaleMap y U) continuous_uliftDown
    (v := ULift.up (etaleMap y U q)) (e := q) rfl
  refine ⟨⟨W, hW⟩, hpW, ⟨fun w => ULift.up (τ w.1), continuous_uliftUp.comp
    (hτW.comp_continuous continuous_subtype_val fun w => w.2), fun w => hτ w.1 w.2⟩, hτp⟩

/-- An open subscheme of `Y`, as an étale `Y`-scheme. -/
noncomputable abbrev etaleOpen (V : Y.Opens) : Y.Etale := Scheme.Etale.mk V.ι

/-- The inclusion of an open subscheme, as a morphism to the final étale `Y`-scheme. -/
noncomputable def etaleOpenToTop (V : Y.Opens) : etaleOpen V ⟶ etaleTop Y :=
  MorphismProperty.Over.homMk V.ι (Category.comp_id _) trivial

omit [LocallyOfFiniteType y] in
/-- Every complex point of an open subscheme `V` comes from a complex point of `V`. -/
theorem exists_etaleMap_etaleOpen_eq {V : Y.Opens} {x : ComplexPoints y} (hx : x.Mem V) :
    ∃ q : ComplexPoints ((etaleOpen V).hom ≫ y), etaleMap y (etaleOpen V) q = x := by
  have h := range_map_of_isOpenImmersion V.ι (y := V.ι ≫ y) (y' := y) rfl
  have hx' : x ∈ Set.range (map V.ι (y := V.ι ≫ y) (y' := y) rfl) := by
    rw [h]
    change x.Mem V.ι.opensRange
    rwa [Scheme.Opens.opensRange_ι]
  exact hx'

end LocalSections

/-! ### The comparison of rational functions on global sections -/

section RationalTop

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one
  smooth_of_smoothOfRelativeDimension_one

/-- The analytification of a nonzero rational function is a meromorphic unit on every subset. -/
theorem isMeromorphicUnitOn_analytifyRat [IsLocallyNoetherian Y] {g : Y.functionField}
    (hg : g ≠ 0) (S : Set (ComplexPoints y)) :
    RiemannSurface.IsMeromorphicUnitOn (analytifyRat (y := y) g) S :=
  ⟨fun x _ => meromorphicAt_analytifyRat g x, fun x _ => orderAt_analytifyRat_ne_top hg x⟩

/-- The global section `g_an` of `𝓜^×` for a nonzero rational function `g`. -/
noncomputable def analytifyRatSection {g : Y.functionField} (hg : g ≠ 0) :
    ToType ((analyticMeromorphicUnitsSheaf y).obj.obj (op ⊤)) :=
  haveI := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
  ULift.up (Additive.ofMul (RiemannSurface.meromorphicUnitsMk
    (isMeromorphicUnitOn_analytifyRat y hg _)))

/-- **The comparison of rational functions on global sections**: the global section of
`j_* 𝐆_{m,K}` given by an invertible rational function `g` goes to the meromorphic unit `g_an`
on `Y(ℂ)`. -/
theorem evalSection_rationalComparison_etaleTop
    (a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y)))) :
    evalSection y ((rationalComparisonToDirectImage y).hom.app (op (etaleTop Y)) a)
        (topSection y (op ⊤)) =
      analytifyRatSection y (generic_ne_zero y (etaleTop Y) a) := by
  have : IsLocallyNoetherian Y := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
  set t := (rationalComparisonToDirectImage y).hom.app (op (etaleTop Y)) a
  set g := generic y (etaleTop Y) a
  obtain ⟨f, hf, hfe⟩ := RiemannSurface.exists_eq_meromorphicUnitsMk
    (Additive.toMul (evalSection y t (topSection y (op ⊤))).down)
  have ht : evalSection y t (topSection y (op ⊤)) = ULift.up (Additive.ofMul
      (RiemannSurface.meromorphicUnitsMk hf)) := by
    rw [← hfe]
    rfl
  rw [ht]
  refine ULift.ext _ _ (congrArg Additive.ofMul ((RiemannSurface.meromorphicUnitsMk_eq_iff _ _).2
    (RiemannSurface.eventuallyEq_codiscreteWithin_of_nhdsNE fun x _ => ?_)))
  -- an affine open neighbourhood of `x` and a local section through it
  obtain ⟨V, hV, hxV, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
    (show x.toPoint ∈ (⊤ : Y.Opens) from trivial)
  have hxV' : x.Mem V := mem_iff_toPoint_mem.2 hxV
  obtain ⟨q, hq⟩ := exists_etaleMap_etaleOpen_eq y hxV'
  obtain ⟨W, hW, σ, hσ⟩ := exists_sectionsPresheaf_through y (etaleOpen V) q
  rw [hq] at hW
  have : Nonempty V := ⟨⟨x.toPoint, hxV⟩⟩
  have : IsAffine (etaleOpen V).left := hV
  have : IsIntegral (etaleOpen V).left := inferInstanceAs (IsIntegral V)
  let φ := etaleOpenToTop (Y := Y) V
  set b := (etaleRationalUnits y).obj.map φ.op a
  have h1 := evalSection_map_etaleTop y φ t (W := op W) σ
  have h2 : ((analyticDirectImage y).obj (analyticMeromorphicUnitsSheaf y)).obj.map φ.op t =
      (rationalComparisonToDirectImage y).hom.app (op (etaleOpen V)) b :=
    (ConcreteCategory.congr_hom ((rationalComparisonToDirectImage y).hom.naturality φ.op) a).symm
  rw [h2, evalSection_rationalComparisonToDirectImage y (etaleOpen V) b
    (σ := (σ : ((sectionsFunctor y).obj (etaleOpen V)).obj.obj (op W))), ht] at h1
  have hWsub : {x : ComplexPoints y | ULift.up x ∈ W} ⊆
      ((downOpens (⊤ : TopologicalSpace.Opens 𝔛) : TopologicalSpace.Opens (ComplexPoints y)) :
        Set (ComplexPoints y)) := fun _ _ => trivial
  have h3 : RiemannSurface.meromorphicUnitsMk
      (isMeromorphicUnitOn_alongSection (y := y) σ (generic_ne_zero y (etaleOpen V) b)) =
      RiemannSurface.meromorphicUnitsMk (hf.mono hWsub) :=
    congrArg (fun z => Additive.toMul z.down) h1
  rw [RiemannSurface.meromorphicUnitsMk_eq_iff] at h3
  let ι : (etaleOpen V).left ⟶ Y := Scheme.Opens.ι (V : Y.Opens)
  have : Etale ι := inferInstanceAs (Etale (Scheme.Opens.ι (V : Y.Opens)))
  have := isDominant_of_flat ι
  have h4 : generic y (etaleOpen V) b = dominantFunctionFieldMap ι g := generic_map y φ a
  have hd : ι ≫ y = (etaleOpen V).hom ≫ y := rfl
  have h5 := analytifyRat_dominantFunctionFieldMap_eventuallyEq (d := y) ι hd
    (isLocalHomeomorph_map_of_etale ι hd) g
  rw [← h4] at h5
  have h6 : alongSection σ (analytifyRat (y := y) g ∘ map ι hd) =ᶠ[codiscreteWithin
      {x : ComplexPoints y | ULift.up x ∈ W}] analytifyRat (y := y) g :=
    RiemannSurface.eventuallyEq_codiscreteWithin_of_eqOn fun z hz => by
      rw [alongSection_of_mem σ _ hz, Function.comp_apply]
      congr 1
      exact σ.2.2 ⟨ULift.up z, hz⟩
  exact RiemannSurface.eventuallyEq_nhdsNE_of_codiscreteWithin
    (h3.symm.trans ((alongSection_eventuallyEq σ h5).trans h6)) (isOpen_downOpens W) hW

/-- `Γτ₂(g) = g_an`, read through `Γ_et ∘ ε_* ≅ Γ_an`. -/
theorem globalSectionsIso_rationalComparison_etaleTop
    (a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y)))) :
    (globalSectionsIso y).hom.app (analyticMeromorphicUnitsSheaf y)
        ((rationalComparisonToDirectImage y).hom.app (op (etaleTop Y)) a) =
      analytifyRatSection y (generic_ne_zero y (etaleTop Y) a) := by
  rw [globalSectionsIso_hom_app_apply]
  exact evalSection_rationalComparison_etaleTop y a

omit [IsCurve ℂ y] in
theorem orderAt_eq_top_of_eventuallyEq_zero {f : ComplexPoints y → ℂ} {x : ComplexPoints y}
    (h : f =ᶠ[𝓝[≠] x] 0) : RiemannSurface.orderAt f x = ⊤ := by
  rw [RiemannSurface.orderAt_congr h, RiemannSurface.orderAt]
  exact meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ => rfl)

/-- **Every global meromorphic unit comes from a rational function** (GAGA for functions): on a
compact `Y(ℂ)`, the comparison `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^×` is surjective on global sections. -/
theorem surjective_rationalComparison_etaleTop [CompactSpace (ComplexPoints y)] :
    Function.Surjective ((rationalComparisonToDirectImage y).hom.app (op (etaleTop Y))) := by
  have : IsLocallyNoetherian Y := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
  intro t
  obtain ⟨f, hf, hfe⟩ := RiemannSurface.exists_eq_meromorphicUnitsMk
    (Additive.toMul (evalSection y t (topSection y (op ⊤))).down)
  have ht : evalSection y t (topSection y (op ⊤)) = ULift.up (Additive.ofMul
      (RiemannSurface.meromorphicUnitsMk hf)) := by
    rw [← hfe]
    rfl
  obtain ⟨g, hg, hfg⟩ : ∃ g : Y.functionField, g ≠ 0 ∧
      f =ᶠ[codiscrete (ComplexPoints y)] analytifyRat (y := y) g := by
    by_cases hX : Nonempty (ComplexPoints y)
    · obtain ⟨g, hfg⟩ := exists_eq_analytifyRat (y := y) (f := f) fun x _ => hf.1 x trivial
      refine ⟨g, fun hg0 => ?_, hfg⟩
      obtain ⟨x⟩ := hX
      rw [hg0, analytifyRat_zero] at hfg
      exact hf.2 x trivial (orderAt_eq_top_of_eventuallyEq_zero y
        ((eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hfg) x))
    · refine ⟨1, one_ne_zero, Eventually.of_forall fun x => (hX ⟨x⟩).elim⟩
  obtain ⟨u, hu⟩ := Stacks.EtaleCohomology.surjective_units_map_genericFibreToFunctionField
    (X := Y) (U := Y) (𝟙 Y) (Units.mk0 g hg)
  let a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y))) := ULift.up (Additive.ofMul u)
  refine ⟨a, eq_of_evalSection_topSection y ?_⟩
  rw [evalSection_rationalComparison_etaleTop y a, ht]
  have hgen : generic y (etaleTop Y) a = g := congrArg Units.val hu
  refine ULift.ext _ _ (congrArg Additive.ofMul ((RiemannSurface.meromorphicUnitsMk_eq_iff _ _).2
    (RiemannSurface.eventuallyEq_codiscreteWithin_of_nhdsNE fun x _ => ?_)))
  rw [hgen]
  exact ((eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hfg) x).symm

/-- **Every global meromorphic unit of `Y(ℂ)` is the image of a global section of
`j_* 𝐆_{m,K}`**, read through `Γ_et ∘ ε_* ≅ Γ_an`. -/
theorem exists_globalSectionsIso_rationalComparison [CompactSpace (ComplexPoints y)]
    (m : ToType ((analyticMeromorphicUnitsSheaf y).obj.obj (op ⊤))) :
    ∃ a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y))),
      (globalSectionsIso y).hom.app (analyticMeromorphicUnitsSheaf y)
        ((rationalComparisonToDirectImage y).hom.app (op (etaleTop Y)) a) = m := by
  let e := (globalSectionsIso y).app (analyticMeromorphicUnitsSheaf y)
  obtain ⟨a, ha⟩ := surjective_rationalComparison_etaleTop y (e.inv m)
  refine ⟨a, ?_⟩
  have h : e.hom (e.inv m) = m := ConcreteCategory.congr_hom e.inv_hom_id m
  change e.hom _ = m
  rw [ha]
  exact h

end RationalTop

/-! ### The comparison of divisors on global sections -/

section DivisorTop

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one
  smooth_of_smoothOfRelativeDimension_one

attribute [local instance 10000] Stacks.EtaleCohomology.hasCoproduct_closedPointSkyscraper

omit [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] in
theorem evalSection_zero [LocallyOfFiniteType y] {G : AnSheaf y} {U : Y.Etale}
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (0 : ToType (((analyticDirectImage y).obj G).obj.obj (op U))) σ = 0 := by
  have h := evalSection_add y (0 : ToType (((analyticDirectImage y).obj G).obj.obj (op U))) 0 σ
  rw [add_zero] at h
  have := congrArg (· - evalSection y (0 : ToType
    (((analyticDirectImage y).obj G).obj.obj (op U))) σ) h
  simpa using this.symm

/-- **The comparison of divisors on global sections**: a global section of `⨁_x i_{x,*} ℤ` goes
to a divisor on `Y(ℂ)`. -/
noncomputable def globalDivisorComparison :
    ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj (op (etaleTop Y))) →+
      (RiemannSurface.divisorSheaf (ComplexPoints y)).obj.obj (op ⊤) where
  toFun s := (evalSection y ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y)) s)
    (topSection y (op ⊤))).down
  map_zero' := by
    rw [map_zero, evalSection_zero]
    rfl
  map_add' s s' := by
    rw [map_add, evalSection_add]
    rfl

theorem globalDivisorComparison_apply
    (s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y)))) :
    globalDivisorComparison y s = (evalSection y ((divisorComparisonToDirectImage y).hom.app
      (op (etaleTop Y)) s) (topSection y (op ⊤))).down := rfl

omit [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] in
/-- Over an open of `Y` missing the closed point `q`, the skyscraper `i_{q,*} ℤ` has no nonzero
sections. -/
theorem subsingleton_closedPointSkyscraper_etaleOpen (q : closedPoints Y) {V : Y.Opens}
    (hq : q.1 ∉ V) :
    Subsingleton (ToType ((Stacks.EtaleCohomology.closedPointSkyscraper.{0, 1} Y q).obj.obj
      (op (etaleOpen V)))) := by
  have hE : IsEmpty ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (Y.fromSpecResidueField q.1)).obj (etaleOpen V)).left := ⟨fun z => hq (by
    have := Stacks.EtaleCohomology.hom_base_pullback_fst_fromSpecResidueField q.1 (etaleOpen V) z
    rw [← this]
    exact ((Limits.pullback.fst (etaleOpen V).hom (Y.fromSpecResidueField q.1)) z).2)⟩
  let e := (Stacks.EtaleCohomology.integerSkyscraperSectionsIsoLocallyConstantMaps.{0, 1} Y q.1
    (etaleOpen V)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b => e.injective (LocallyConstant.ext fun z => isEmptyElim z)⟩

/-- The divisor on `Y(ℂ)` of a global section of the summand `i_{q,*} ℤ` vanishes at every point
other than `q`. -/
theorem globalDivisorComparison_ι_apply_eq_zero (q : closedPoints Y)
    (w : ToType ((Stacks.EtaleCohomology.closedPointSkyscraper.{0, 1} Y q).obj.obj
      (op (etaleTop Y))))
    {x : ComplexPoints y} (hx : x.toPoint ≠ q.1) :
    RiemannSurface.divisorSection (globalDivisorComparison y
      ((Stacks.EtaleCohomology.closedPointDivisorSheaf.ι.{0, 1} Y q).hom.app (op (etaleTop Y)) w))
        x = 0 := by
  let V : Y.Opens := ⟨{q.1}ᶜ, q.2.isOpen_compl⟩
  have hxV : x.Mem V := mem_iff_toPoint_mem.2 hx
  obtain ⟨q', hq'⟩ := exists_etaleMap_etaleOpen_eq y hxV
  obtain ⟨W, hW, σ, -⟩ := exists_sectionsPresheaf_through y (etaleOpen V) q'
  rw [hq'] at hW
  let φ := etaleOpenToTop (Y := Y) V
  set s := (Stacks.EtaleCohomology.closedPointDivisorSheaf.ι.{0, 1} Y q).hom.app (op (etaleTop Y)) w
  have h1 := evalSection_map_etaleTop y φ ((divisorComparisonToDirectImage y).hom.app
    (op (etaleTop Y)) s) (W := op W) σ
  have h2 : ((analyticDirectImage y).obj (analyticDivisorSheaf y)).obj.map φ.op
      ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y)) s) =
      (divisorComparisonToDirectImage y).hom.app (op (etaleOpen V))
        ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.map φ.op s) :=
    (ConcreteCategory.congr_hom ((divisorComparisonToDirectImage y).hom.naturality φ.op) s).symm
  have h3 : (Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.map φ.op s =
      (Stacks.EtaleCohomology.closedPointDivisorSheaf.ι.{0, 1} Y q).hom.app (op (etaleOpen V))
        ((Stacks.EtaleCohomology.closedPointSkyscraper.{0, 1} Y q).obj.map φ.op w) :=
    (ConcreteCategory.congr_hom
      ((Stacks.EtaleCohomology.closedPointDivisorSheaf.ι.{0, 1} Y q).hom.naturality φ.op) w).symm
  have : Subsingleton (ToType ((Stacks.EtaleCohomology.closedPointSkyscraper.{0, 1} Y q).obj.obj
      (op (etaleOpen V)))) :=
    subsingleton_closedPointSkyscraper_etaleOpen q (V := V) fun h => h rfl
  have h4 : (Stacks.EtaleCohomology.closedPointSkyscraper.{0, 1} Y q).obj.map φ.op w = 0 :=
    Subsingleton.elim _ _
  rw [h2, h3, h4, map_zero, map_zero, evalSection_zero y
    (σ := (σ : ((sectionsFunctor y).obj (etaleOpen V)).obj.obj (op W)))] at h1
  have h5 := congrArg (fun D : ToType ((analyticDivisorSheaf y).obj.obj (op W)) =>
    RiemannSurface.divisorSection D.down x) h1
  change 0 = RiemannSurface.divisorSection ((RiemannSurface.divisorPresheaf (ComplexPoints y)).map
    ((TopCat.opensULiftEquivalence (ComplexPoints y)).functor.op.map
      (homOfLE le_top : W ⟶ ⊤).op) (globalDivisorComparison y s)) x at h5
  have h6 := RiemannSurface.divisorPresheaf_map_apply
    ((TopCat.opensULiftEquivalence (ComplexPoints y)).functor.op.map
      (homOfLE le_top : W ⟶ ⊤).op) (globalDivisorComparison y s) x
  have hW' : x ∈ ((unop ((TopCat.opensULiftEquivalence (ComplexPoints y)).functor.op.obj
      (op W)) : TopologicalSpace.Opens (ComplexPoints y)) : Set (ComplexPoints y)) := hW
  rw [ite_eq_left hW'] at h6
  exact (h5.trans h6).symm

/-- **The divisor of a global invertible rational function**: the comparison of divisors sends
the étale divisor of a global section `a` of `j_* 𝐆_{m,K}` to the divisor on `Y(ℂ)` whose value at
`x` is the order of vanishing of the rational function of `a` at the point under `x`. -/
theorem globalDivisorComparison_secondMap_apply
    (a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y)))) (x : ComplexPoints y) :
    haveI : IsLocallyNoetherian Y := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
    RiemannSurface.divisorSection (globalDivisorComparison y
      ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app
        (op (etaleTop Y)) a)) x = Y.ord (generic y (etaleTop Y) a) x.toPoint := by
  have : IsLocallyNoetherian Y := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
  have h := congrArg (fun φ => evalSection y (φ.hom.app (op (etaleTop Y)) a)
    (topSection y (op ⊤))) (divisorSequenceSecondMapOfCurve_comp_divisorComparison y)
  have h' := h.trans (evalSection_analyticDirectImage_map y _ _ (topSection y (op ⊤)))
  have hg := generic_ne_zero y (etaleTop Y) a
  have key : evalSection y ((divisorComparisonToDirectImage y).hom.app
      (op (etaleTop Y)) ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app
        (op (etaleTop Y)) a)) (topSection y (op ⊤)) =
      ((liftToAnalytic y).map (RiemannSurface.meromorphicUnitsToDivisor
        (ComplexPoints y))).hom.app (op ⊤) (analytifyRatSection y hg) :=
    h'.trans (congrArg _ (evalSection_rationalComparison_etaleTop y a))
  rw [globalDivisorComparison_apply, key]
  change RiemannSurface.divisorSection ((RiemannSurface.meromorphicUnitsToDivisor
    (ComplexPoints y)).hom.app _ (Additive.ofMul (RiemannSurface.meromorphicUnitsMk
      (isMeromorphicUnitOn_analytifyRat y hg _)))) x = _
  rw [RiemannSurface.meromorphicUnitsToDivisor_app_ofMul_mk,
    RiemannSurface.divisorOn_apply (isMeromorphicUnitOn_analytifyRat y hg
      (((⊤ : TopologicalSpace.Opens (ComplexPoints y))) : Set (ComplexPoints y))).1
      (show x ∈ (((⊤ : TopologicalSpace.Opens (ComplexPoints y))) : Set (ComplexPoints y))
        from trivial)]
  have ho : RiemannSurface.orderAt (analytifyRat (y := y) (generic y (etaleTop Y) a)) x =
      Y.ord (generic y (etaleTop Y) a) x.toPoint :=
    orderAt_analytifyRat (C := Y) (y := y) (g := generic y (etaleTop Y) a) hg x
  rw [ho]
  rfl

/-- At every complex point some rational function has nonzero order: the image of a uniformizer of
the local ring. -/
theorem exists_ord_ne_zero (p : ComplexPoints y) :
    haveI : IsLocallyNoetherian Y := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
    ∃ g : Y.functionField, g ≠ 0 ∧ Y.ord g p.toPoint ≠ 0 := by
  have : IsLocallyNoetherian Y := Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve y
  have := isDiscreteValuationRing_stalk_toPoint (y := y) p
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk p.toPoint)
  set g := algebraMap (Y.presheaf.stalk p.toPoint) Y.functionField ϖ
  have hg : g ≠ 0 := fun h => hϖ.ne_zero ((IsFractionRing.injective
    (Y.presheaf.stalk p.toPoint) Y.functionField) (h.trans (map_zero _).symm))
  have h1 := IsRegularAt.one_le_orderAt (isRegularAt_algebraMap (y := y) ϖ)
    ((analytifyRat_algebraMap_eq_zero_iff (y := y) ϖ).2
      ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit))
  rw [orderAt_analytifyRat hg] at h1
  refine ⟨g, hg, fun h0 => ?_⟩
  rw [h0] at h1
  exact absurd h1 (by decide)

section Stacks

variable [IsNormal Y] [IsLocallyNoetherian Y] [NoetherianSpace Y] [QuasiSeparatedSpace Y]

/-- The étale divisor of a global section `a` of `j_* 𝐆_{m,K}`, read as a finitely supported
function on the closed points, is the family of orders of vanishing of its rational function. -/
theorem closedPointDivisorSheafTopAddEquiv_secondMap_apply
    (a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y)))) (p : closedPoints Y) :
    Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y
      ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app
        (op (etaleTop Y)) a) p = Y.ord (generic y (etaleTop Y) a) p.1 := by
  have h :=
    Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv_divisorSequenceSecondMap.{0, 1} Y a
  exact (DFunLike.congr_fun h p).trans
    (Stacks.EtaleCohomology.closedPointDivisorOfUnit_apply Y _ p)

/-- The value at `x` of the divisor on `Y(ℂ)` of a global section of `⨁_x i_{x,*} ℤ`, as an
additive map. -/
noncomputable def globalDivisorComparisonEval (x : ComplexPoints y) :
    ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj (op (etaleTop Y))) →+
      ℤ where
  toFun s := RiemannSurface.divisorSection (globalDivisorComparison y s) x
  map_zero' := by
    rw [map_zero]
    rfl
  map_add' s s' := by
    rw [map_add]
    rfl

/-- **The comparison of divisors on global sections is the identity on coefficients**: the divisor
on `Y(ℂ)` of a global section `s` of `⨁_x i_{x,*} ℤ` has at `x` the coefficient of `s` at the closed
point under `x`. -/
theorem globalDivisorComparison_apply_eq
    (s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y)))) (x : ComplexPoints y) :
    RiemannSurface.divisorSection (globalDivisorComparison y s) x =
      Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y s
        ((closedPointsEquiv (y := y)).symm x) := by
  classical
  set e := Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y
  set p := (closedPointsEquiv (y := y)).symm x
  set Ψ := globalDivisorComparisonEval y x
  change Ψ s = e s p
  let δ : closedPoints Y → ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y))) := fun q =>
    (Stacks.EtaleCohomology.closedPointDivisorSheaf.ι.{0, 1} Y q).hom.app (op (etaleTop Y))
      ((Stacks.EtaleCohomology.integerSkyscraperTopAddEquiv.{0, 1} Y q.1).symm 1)
  have heδ : ∀ q, e (δ q) = Finsupp.single q 1 := fun q => by
    refine (Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv_ι Y q _).trans ?_
    rw [AddEquiv.apply_symm_apply]
  have hΨδ : ∀ q, q ≠ p → Ψ (δ q) = 0 := fun q hq =>
    globalDivisorComparison_ι_apply_eq_zero y q _ fun h => hq (Subtype.ext (by
      rw [coe_closedPointsEquiv_symm]; exact h.symm))
  -- every global section is a finite combination of the `δ q`
  have hdec : ∀ t, t = (e t).sum fun q c => c • δ q := fun t => e.injective (by
    rw [map_finsuppSum]
    simp_rw [map_zsmul, heδ, Finsupp.smul_single_one]
    exact (Finsupp.sum_single (e t)).symm)
  have hΨ : ∀ t, Ψ t = e t p * Ψ (δ p) := fun t => by
    conv_lhs => rw [hdec t]
    rw [map_finsuppSum, Finsupp.sum_eq_single p (fun q _ hq => by rw [map_zsmul, hΨδ q hq,
      smul_zero]) (fun _ => by rw [zero_smul, map_zero]), map_zsmul, smul_eq_mul]
  -- a rational function with nonzero order at `p` normalises the coefficient
  obtain ⟨g, hg, hgp⟩ := exists_ord_ne_zero y x
  obtain ⟨u, hu⟩ := Stacks.EtaleCohomology.surjective_units_map_genericFibreToFunctionField
    (X := Y) (U := Y) (𝟙 Y) (Units.mk0 g hg)
  let a : ToType ((etaleRationalUnits y).obj.obj (op (etaleTop Y))) := ULift.up (Additive.ofMul u)
  have hgen : generic y (etaleTop Y) a = g := congrArg Units.val hu
  have h1 := globalDivisorComparison_secondMap_apply y a x
  have h2 := closedPointDivisorSheafTopAddEquiv_secondMap_apply y a p
  rw [hgen] at h1 h2
  have h3 := hΨ ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app
    (op (etaleTop Y)) a)
  have h1' : Ψ ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app
      (op (etaleTop Y)) a) = Y.ord g x.toPoint := h1
  have h2' : e ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app
      (op (etaleTop Y)) a) p = Y.ord g x.toPoint := h2
  rw [h1', h2'] at h3
  have hκ : Ψ (δ p) = 1 := by
    have h4 : Y.ord g x.toPoint * (Ψ (δ p) - 1) = 0 := by rw [mul_sub, ← h3, mul_one, sub_self]
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hgp
    · exact sub_eq_zero.1 h
  rw [hΨ s, hκ, mul_one]

/-- `Γτ₃` is the identity on coefficients, read through `Γ_et ∘ ε_* ≅ Γ_an`. -/
theorem divisorSection_globalSectionsIso_divisorComparison
    (s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y)))) (x : ComplexPoints y) :
    RiemannSurface.divisorSection ((globalSectionsIso y).hom.app (analyticDivisorSheaf y)
        ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y)) s)).down x =
      Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y s
        ((closedPointsEquiv (y := y)).symm x) := by
  rw [globalSectionsIso_hom_app_apply]
  exact globalDivisorComparison_apply_eq y s x

section Compact

variable [T2Space (ComplexPoints y)] [CompactSpace (ComplexPoints y)]

/-- **The comparison of divisors on global sections is `Finsupp.mapDomain closedPointsEquiv`**: on a
compact `Y(ℂ)`, read through `Γ(Y, ⨁_x i_{x,*} ℤ) ≃ (Y_0 →₀ ℤ)` and `Div(Y(ℂ)) ≃ (Y(ℂ) →₀ ℤ)`, the
comparison of divisors transports a divisor along the bijection of the closed points of `Y` with
the complex points. -/
theorem globalDivisorComparison_eq
    (s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y)))) :
    globalDivisorComparison y s = RiemannSurface.globalDivisorEquiv (ComplexPoints y)
      (Finsupp.mapDomain (closedPointsEquiv (y := y))
        (Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y s)) := by
  apply RiemannSurface.divisorSection_injective
  ext x
  rw [globalDivisorComparison_apply_eq, RiemannSurface.globalDivisorEquiv_apply,
    ← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]

/-- `Γτ₃` is `Finsupp.mapDomain closedPointsEquiv`, read through `Γ_et ∘ ε_* ≅ Γ_an`. -/
theorem globalSectionsIso_divisorComparison_etaleTop
    (s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y)))) :
    ((globalSectionsIso y).hom.app (analyticDivisorSheaf y)
        ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y)) s)).down =
      RiemannSurface.globalDivisorEquiv (ComplexPoints y)
        (Finsupp.mapDomain (closedPointsEquiv (y := y))
          (Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y s)) := by
  rw [globalSectionsIso_hom_app_apply]
  exact globalDivisorComparison_eq y s

/-- On a compact `Y(ℂ)`, the comparison of divisors is bijective on global sections. -/
theorem bijective_globalDivisorComparison : Function.Bijective (globalDivisorComparison y) := by
  have h : ⇑(globalDivisorComparison y) =
      ⇑(((Stacks.EtaleCohomology.closedPointDivisorSheafTopAddEquiv.{0, 1} Y).trans
        (Finsupp.domCongr (closedPointsEquiv (y := y)))).trans
          (RiemannSurface.globalDivisorEquiv (ComplexPoints y))) := by
    funext s
    rw [globalDivisorComparison_eq]
    simp only [AddEquiv.trans_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [h]
  exact AddEquiv.bijective _

/-- **`Γτ₃` is bijective**: on a compact `Y(ℂ)`, the comparison `⨁_x i_{x,*} ℤ ⟶ ε_* 𝒟iv` is
bijective on global sections. -/
theorem bijective_divisorComparison_etaleTop :
    Function.Bijective ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y))) := by
  refine ⟨fun s s' h => (bijective_globalDivisorComparison y).1 (by
    rw [globalDivisorComparison_apply, globalDivisorComparison_apply, h]), fun t => ?_⟩
  obtain ⟨s, hs⟩ := (bijective_globalDivisorComparison y).2
    (evalSection y t (topSection y (op ⊤))).down
  exact ⟨s, eq_of_evalSection_topSection y (ULift.ext _ _ hs)⟩

/-- **`Γτ₃` is bijective**, read through `Γ_et ∘ ε_* ≅ Γ_an`: on a compact `Y(ℂ)`, global
sections of `⨁_x i_{x,*} ℤ` correspond bijectively to global sections of `𝒟iv` on `Y(ℂ)`. -/
theorem bijective_globalSectionsIso_divisorComparison :
    Function.Bijective fun s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1}
        Y).obj.obj (op (etaleTop Y))) =>
      (globalSectionsIso y).hom.app (analyticDivisorSheaf y)
        ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y)) s) := by
  let e := (globalSectionsIso y).app (analyticDivisorSheaf y)
  have he : Function.Bijective e.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom)
  exact he.comp (bijective_divisorComparison_etaleTop y)

end Compact

end Stacks

end DivisorTop

end AlgebraicGeometry.Scheme.ComplexPoints
