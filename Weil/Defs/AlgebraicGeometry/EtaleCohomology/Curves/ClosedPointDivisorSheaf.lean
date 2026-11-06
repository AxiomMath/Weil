module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorClass
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison

/-!
# The sheaf of divisors on the small étale site

Let `X` be a scheme. The sheaf of divisors `𝒟_X` on the small étale site of `X` is the coproduct
`⨁_{x} i_{x,*} ℤ` of the skyscraper sheaves at the closed points of `X`
(`Stacks.EtaleCohomology.closedPointDivisorSheaf`). On a smooth curve over a field it is the
third term of the divisor sequence `0 → 𝔾_m → j_* 𝔾_{m,η} → 𝒟_X → 0`.

This file identifies its sections with divisors in the classical sense. For an étale `X`-scheme
`U` which is quasi-compact and quasi-separated, and `X` a Jacobson scheme (for instance a scheme
locally of finite type over a field), the sections of `𝒟_X` over `U` are the finitely supported
`ℤ`-valued functions on the closed points of `U`, i.e. the free abelian group on the closed points
of `U`; and restriction along a morphism `ψ : V ⟶ U` of étale `X`-schemes is `D ↦ D ∘ ψ`, the
pull-back of divisors (all multiplicities `1`, `ψ` being unramified).

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheaf`: the sheaf of divisors on the
  étale site `Et(S)`, the restriction of `Stacks.EtaleCohomology.closedPointDivisorSheaf`.
* `AlgebraicGeometry.Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv`: the sections of
  `⨁_x i_{x,*} ℤ` over `U` are `closedPoints U →₀ ℤ`; on `Et(S)` this is
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheafSectionsAddEquiv`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mem_closedPoints_iff_of_locallyQuasiFinite`: for a locally
  quasi-finite morphism locally of finite type to a Jacobson scheme, a point is closed if and only
  if its image is.
* `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton_of_isClosed`: the fibre of a locally
  quasi-finite morphism from a quasi-compact scheme over a closed point is finite.
* `AlgebraicGeometry.Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv_map`: restriction of
  divisors along a morphism `ψ` of étale `X`-schemes is composition with `ψ`; on `Et(S)` this is
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheafSectionsAddEquiv_map`.

## Implementation notes

The sheaf is taken from the Stacks project formalization rather than built from the functions
`D : |U| → ℤ`: as a coproduct of skyscrapers its sheaf property and its description as a sum of
skyscraper sheaves hold by construction, and the description by functions is the theorem
`closedPointDivisorSheafSectionsAddEquiv`. No curve hypothesis is needed for either.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology Stacks.EtaleCohomology

universe u v

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A locally quasi-finite morphism locally of finite type to a Jacobson scheme maps exactly the
closed points to closed points**: a point is closed if and only if its image is. -/
theorem mem_closedPoints_iff_of_locallyQuasiFinite [JacobsonSpace Y] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] {x : X} : x ∈ closedPoints X ↔ f x ∈ closedPoints Y := by
  refine ⟨fun hx ↦ f.closePoints_subset_preimage_closedPoints hx, fun hx ↦ ?_⟩
  rw [mem_closedPoints_iff] at hx ⊢
  have hF : IsClosed (f ⁻¹' {f x}) := hx.preimage f.continuous
  have : DiscreteTopology (f ⁻¹' {f x}) := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h : IsClosed (((↑) : f ⁻¹' {f x} → X) '' {⟨x, rfl⟩}) :=
    hF.isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_discrete ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})))
  rwa [Set.image_singleton] at h

/-- **The fibre of a locally quasi-finite morphism from a quasi-compact scheme over a closed point
is finite**: it is closed, hence compact, and discrete. -/
theorem finite_preimage_singleton_of_isClosed [CompactSpace X] [LocallyQuasiFinite f] {y : Y}
    (hy : IsClosed {y}) : (f ⁻¹' {y}).Finite :=
  ((hy.preimage f.continuous).isCompact).finite (f.isDiscrete_preimage_singleton y)

/-- The fibre of a locally quasi-finite morphism is discrete. -/
instance discreteTopology_fiber_of_locallyQuasiFinite [LocallyQuasiFinite f] (y : Y) :
    DiscreteTopology (f.fiber y) :=
  have : DiscreteTopology (f ⁻¹' {y}) := (f.isDiscrete_preimage_singleton y).to_subtype
  (f.fiberHomeo y).isEmbedding.discreteTopology

end Scheme.Hom

namespace Scheme.Etale

variable {X : Scheme.{u}}

/-- **A point of an étale `X`-scheme is closed if and only if its image in `X` is**, for `X` a
Jacobson scheme. -/
theorem mem_closedPoints_iff [JacobsonSpace X] (U : X.Etale) {y : U.left} :
    y ∈ closedPoints U.left ↔ U.hom y ∈ closedPoints X :=
  haveI : JacobsonSpace ((Functor.fromPUnit X).obj U.right) := inferInstanceAs (JacobsonSpace X)
  U.hom.mem_closedPoints_iff_of_locallyQuasiFinite

/-- Locally constant `ℤ`-valued functions on the fibre of an étale `X`-scheme over a point are
the `ℤ`-valued functions on the set-theoretic fibre, the fibre being discrete. -/
def locallyConstantFiberAddEquiv (U : X.Etale) (x : X) :
    LocallyConstant (U.hom.fiber x) (ULift.{max (u + 1) v} ℤ) ≃+ (U.hom ⁻¹' {x} → ℤ) where
  toFun g p := (g ((U.hom.fiberHomeo x).symm p)).down
  invFun h := ⟨fun q ↦ ⟨h (U.hom.fiberHomeo x q)⟩, IsLocallyConstant.of_discrete _⟩
  left_inv g := LocallyConstant.ext fun q ↦ by simp
  right_inv h := funext fun p ↦ by simp
  map_add' _ _ := rfl

/-- **The sections of the skyscraper `i_{x,*} ℤ` over an étale `X`-scheme `U`** are the
`ℤ`-valued functions on the points of `U` over `x`. -/
def integerSkyscraperSectionsAddEquiv (U : X.Etale) (x : X) :
    (integerSkyscraper.{u, v} X x).obj.obj (op U) ≃+ (U.hom ⁻¹' {x} → ℤ) :=
  (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).addCommGroupIsoToAddEquiv.trans
    (locallyConstantFiberAddEquiv.{u, v} U x)

/-- A morphism of étale `X`-schemes maps points over `x` to points over `x`. -/
theorem hom_left_mem_preimage_singleton {V U : X.Etale} (ψ : V ⟶ U) {x : X}
    (p : V.hom ⁻¹' {x}) : ψ.left p.1 ∈ U.hom ⁻¹' {x} := by
  have h : U.hom (ψ.left p.1) = V.hom p.1 := by
    rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w ψ]
  exact h.trans p.2

/-- The morphism of fibres over `x` induced by a morphism `ψ : V ⟶ U` of étale `X`-schemes: the
base change of `ψ` along `Spec κ(x) ⟶ X`. -/
def fiberMap {V U : X.Etale} (ψ : V ⟶ U) (x : X) : V.hom.fiber x ⟶ U.hom.fiber x :=
  ((Stacks.EtaleCohomology.smallEtaleBaseChange (X.fromSpecResidueField x)).map ψ).left

/-- The morphism of fibres induced by `ψ` lies over `ψ`. -/
@[reassoc (attr := simp)]
theorem fiberMap_fiberι {V U : X.Etale} (ψ : V ⟶ U) (x : X) :
    fiberMap ψ x ≫ U.hom.fiberι x = V.hom.fiberι x ≫ ψ.left := by
  simp only [fiberMap, Stacks.EtaleCohomology.smallEtaleBaseChange, Scheme.Hom.fiberι]
  exact pullback.lift_fst _ _ _

/-- On points, the morphism of fibres induced by `ψ` is `ψ`. -/
theorem fiberMap_fiberHomeo_symm {V U : X.Etale} (ψ : V ⟶ U) (x : X) (p : V.hom ⁻¹' {x}) :
    fiberMap ψ x ((V.hom.fiberHomeo x).symm p) =
      (U.hom.fiberHomeo x).symm ⟨ψ.left p.1, hom_left_mem_preimage_singleton ψ p⟩ := by
  apply (U.hom.fiberHomeo x).injective
  apply Subtype.ext
  rw [Homeomorph.apply_symm_apply, Scheme.Hom.fiberHomeo_apply, ← Scheme.Hom.comp_apply,
    fiberMap_fiberι, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm]

/-- **Restriction of sections of `i_{x,*} ℤ` is composition**: along a morphism `ψ : V ⟶ U` of
étale `X`-schemes, the function on the points of `V` over `x` attached to the restriction of a
section is the function on the points of `U` over `x` composed with `ψ`. -/
theorem integerSkyscraperSectionsAddEquiv_map {V U : X.Etale} (ψ : V ⟶ U) (x : X)
    (t : (integerSkyscraper.{u, v} X x).obj.obj (op U)) (p : V.hom ⁻¹' {x}) :
    integerSkyscraperSectionsAddEquiv.{u, v} V x ((integerSkyscraper.{u, v} X x).obj.map ψ.op t) p =
      integerSkyscraperSectionsAddEquiv.{u, v} U x t
        ⟨ψ.left p.1, hom_left_mem_preimage_singleton ψ p⟩ := by
  change ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x V).hom
    ((integerSkyscraper.{u, v} X x).obj.map ψ.op t) ((V.hom.fiberHomeo x).symm p)).down = _
  let L := smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} (Spec (X.residueField x))
    (ULift.{max (u + 1) v} ℤ)
  let g := (Stacks.EtaleCohomology.smallEtaleBaseChange (X.fromSpecResidueField x)).map ψ
  have h := NatTrans.naturality_apply L.hom g.op t
  change ((show LocallyConstant (V.hom.fiber x) (ULift.{max (u + 1) v} ℤ) from
    L.hom.app _ (((constantSheaf (Spec (X.residueField x)).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ))).obj.map g.op t))
        ((V.hom.fiberHomeo x).symm p)).down = _
  rw [h]
  change ((show LocallyConstant (U.hom.fiber x) (ULift.{max (u + 1) v} ℤ) from L.hom.app _ t)
    (fiberMap ψ x ((V.hom.fiberHomeo x).symm p))).down = _
  rw [fiberMap_fiberHomeo_symm]
  rfl

/-- The points of an étale `X`-scheme `U` over closed points of `X`, grouped by their image, are
the closed points of `U`, when `X` is Jacobson. -/
def sigmaFiberClosedPointsEquiv [JacobsonSpace X] (U : X.Etale) :
    (Σ x : closedPoints X, ↥(U.hom ⁻¹' {x.1})) ≃ closedPoints U.left where
  toFun p := ⟨p.2.1, (mem_closedPoints_iff U).2 <| by
    have h : U.hom p.2.1 = p.1.1 := p.2.2
    rw [h]
    exact p.1.2⟩
  invFun y := ⟨⟨U.hom y.1, (mem_closedPoints_iff U).1 y.2⟩, ⟨y.1, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain rfl : U.hom y = x := hy
    rfl
  right_inv _ := rfl

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **The sections over an étale `X`-scheme `U` of the sheaf of divisors `⨁_x i_{x,*} ℤ` are the
divisors on `U`**: the finitely supported `ℤ`-valued functions on the closed points of `U`, i.e.
the free abelian group on the closed points of `U`. Here `U` is quasi-compact and
quasi-separated and `X` is a Jacobson scheme. -/
@[weil "def_fk105_sheaf_divisors"]
def closedPointDivisorSheafSectionsAddEquiv [JacobsonSpace X] (U : X.Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] :
    (closedPointDivisorSheaf.{u, v} X).obj.obj (op U) ≃+ (closedPoints U.left →₀ ℤ) :=
  haveI : CompactSpace ((𝟭 Scheme).obj U.left) := inferInstanceAs (CompactSpace U.left)
  haveI : ∀ x : closedPoints X, Finite ↥(U.hom ⁻¹' {x.1}) := fun x ↦
    (U.hom.finite_preimage_singleton_of_isClosed ((_root_.mem_closedPoints_iff).1 x.2)).to_subtype
  (closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X U).symm.trans <|
    (DFinsupp.mapRange.addEquiv fun x : closedPoints X ↦
      (integerSkyscraperSectionsAddEquiv.{u, v} U x.1).trans
        Finsupp.addEquivFunOnFinite.symm).trans <|
    sigmaFinsuppAddEquivDFinsupp.symm.trans (Finsupp.domCongr (sigmaFiberClosedPointsEquiv U))

/-- The value of a divisor at a closed point `y` of `U` is read off the component of the section
at the closed point `x = U.hom y` of `X`. -/
theorem closedPointDivisorSheafSectionsAddEquiv_apply [JacobsonSpace X] (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (s : (closedPointDivisorSheaf.{u, v} X).obj.obj (op U)) (y : closedPoints U.left)
    (x : closedPoints X) (hy : U.hom y.1 = x.1) :
    closedPointDivisorSheafSectionsAddEquiv.{u, v} U s y =
      integerSkyscraperSectionsAddEquiv.{u, v} U x.1
        ((closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X U).symm s x) ⟨y.1, hy⟩ := by
  obtain ⟨x, hx⟩ := x
  obtain rfl : U.hom y.1 = x := hy
  rfl

/-- A morphism of étale `X`-schemes maps closed points to closed points, for `X` Jacobson. -/
theorem hom_left_mem_closedPoints [JacobsonSpace X] {V U : X.Etale} (ψ : V ⟶ U)
    (y : closedPoints V.left) : ψ.left y.1 ∈ closedPoints U.left := by
  have h : U.hom (ψ.left y.1) = V.hom y.1 := by
    rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w ψ]
  exact (mem_closedPoints_iff U).2 (h ▸ (mem_closedPoints_iff V).1 y.2)

/-- **Restriction of divisors is pull-back**: along a morphism `ψ : V ⟶ U` of quasi-compact
quasi-separated étale `X`-schemes, the divisor attached to the restriction of a section of
`⨁_x i_{x,*} ℤ` is `D ∘ ψ`, where `D` is the divisor attached to the section. -/
@[weil "def_fk105_sheaf_divisors"]
theorem closedPointDivisorSheafSectionsAddEquiv_map [JacobsonSpace X] {V U : X.Etale} (ψ : V ⟶ U)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] (s : (closedPointDivisorSheaf.{u, v} X).obj.obj (op U))
    (y : closedPoints V.left) :
    closedPointDivisorSheafSectionsAddEquiv.{u, v} V
        ((closedPointDivisorSheaf.{u, v} X).obj.map ψ.op s) y =
      closedPointDivisorSheafSectionsAddEquiv.{u, v} U s
        ⟨ψ.left y.1, hom_left_mem_closedPoints ψ y⟩ := by
  have hU : U.hom (ψ.left y.1) = V.hom y.1 := by
    rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w ψ]
  let x : closedPoints X := ⟨V.hom y.1, (mem_closedPoints_iff V).1 y.2⟩
  rw [closedPointDivisorSheafSectionsAddEquiv_apply.{u, v} V _ y x rfl,
    closedPointDivisorSheafSectionsAddEquiv_apply.{u, v} U s _ x hU]
  obtain ⟨f, rfl⟩ := (closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X U).surjective s
  have hm := DFunLike.congr_fun
    (closedPointDivisorSheaf.map_comp_sheafSectionOfDirectSum.{u, v} X ψ) f
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at hm
  change integerSkyscraperSectionsAddEquiv.{u, v} V x.1
      ((closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X V).symm
        ((closedPointDivisorSheaf.{u, v} X).obj.map ψ.op
          (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U f)) x) _ =
    integerSkyscraperSectionsAddEquiv.{u, v} U x.1
      ((closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X U).symm
        (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U f) x) _
  rw [hm, closedPointDivisorSheaf.sectionsAddEquivDirectSum_symm_apply,
    closedPointDivisorSheaf.sectionsAddEquivDirectSum_symm_apply, DirectSum.map_apply]
  exact integerSkyscraperSectionsAddEquiv_map.{u, v} ψ x.1 (f x) ⟨y.1, rfl⟩

end Scheme.Etale

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]

/-- **The sheaf of divisors `𝒟_S` on the étale site `Et(S)`** of a locally noetherian scheme: the
restriction to `Et(S)` of the sheaf `⨁_x i_{x,*} ℤ` over the closed points of `S`. For `S`
Jacobson its sections over `U` are the divisors on `U`, the finitely supported `ℤ`-valued
functions on the closed points of `U` (`divisorSheafSectionsAddEquiv`), and its restriction maps
are pull-back of divisors (`divisorSheafSectionsAddEquiv_map`). -/
@[weil "def_fk105_sheaf_divisors"]
def divisorSheaf : Sheaf (topology B S hS) AddCommGrpCat.{max (u + 1) v} :=
  (sheafEquivEtale B S hS AddCommGrpCat.{max (u + 1) v}).inverse.obj
    (closedPointDivisorSheaf.{u, v} S)

variable {B S hS}

/-- The sections of the sheaf of divisors on `Et(S)` over `U` are the divisors on `U`: the
finitely supported `ℤ`-valued functions on the closed points of `U`. -/
def divisorSheafSectionsAddEquiv [JacobsonSpace S] (U : SmallNoetherianSeparatedEtale B S hS) :
    (divisorSheaf.{u, v} B S hS).obj.obj (op U) ≃+ (closedPoints ((toScheme B S hS).obj U) →₀ ℤ) :=
  haveI : CompactSpace ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj U)).left :=
    inferInstanceAs (CompactSpace ((toScheme B S hS).obj U))
  haveI : QuasiSeparatedSpace
      ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj U)).left :=
    inferInstanceAs (QuasiSeparatedSpace ((toScheme B S hS).obj U))
  Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv.{u, v}
    ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj U))

/-- **Restriction of divisors on `Et(S)` is pull-back**: along `ψ : V ⟶ U` the divisor of the
restricted section is `D ∘ ψ`. -/
theorem divisorSheafSectionsAddEquiv_map [JacobsonSpace S]
    {V U : SmallNoetherianSeparatedEtale B S hS} (ψ : V ⟶ U)
    (s : (divisorSheaf.{u, v} B S hS).obj.obj (op U)) (y : closedPoints ((toScheme B S hS).obj V)) :
    divisorSheafSectionsAddEquiv.{u, v} V ((divisorSheaf.{u, v} B S hS).obj.map ψ.op s) y =
      divisorSheafSectionsAddEquiv.{u, v} U s
        ⟨(toScheme B S hS).map ψ y.1, Scheme.Etale.hom_left_mem_closedPoints
          ((SmallEtale.toEtaleSite B S hS).map ((inclusion B S hS).map ψ)) y⟩ := by
  have : CompactSpace ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj U)).left :=
    inferInstanceAs (CompactSpace ((toScheme B S hS).obj U))
  have : QuasiSeparatedSpace
      ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj U)).left :=
    inferInstanceAs (QuasiSeparatedSpace ((toScheme B S hS).obj U))
  have : CompactSpace ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj V)).left :=
    inferInstanceAs (CompactSpace ((toScheme B S hS).obj V))
  have : QuasiSeparatedSpace
      ((SmallEtale.toEtaleSite B S hS).obj ((inclusion B S hS).obj V)).left :=
    inferInstanceAs (QuasiSeparatedSpace ((toScheme B S hS).obj V))
  exact Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv_map.{u, v}
    ((SmallEtale.toEtaleSite B S hS).map ((inclusion B S hS).map ψ)) s y

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
