module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.RestrictionOnSections
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering

/-!
# Global sections over a henselian local ring and over the closed fibre

Let `A` be a henselian local ring, `f : X ⟶ Spec A` a proper morphism and
`j : X₀ ⟶ X` the inclusion of the closed fibre `X₀ = X ×_{Spec A} Spec κ(A)`. For every abelian
sheaf `F` on the small étale site of `X`, the restriction map
`j^* : H⁰(X, F) ⟶ H⁰(X₀, j^* F)` is bijective. In particular this holds for the constant sheaf
`(ℤ/n)_X`, whose inverse image `j^*(ℤ/n)_X` is the constant sheaf `(ℤ/n)_{X₀}`.

In degree `0` the restriction map is `a ↦ j^* a` on morphisms `ℤ_X ⟶ F`, so the statement is
that `j^*` is bijective on morphisms out of the constant sheaf `ℤ_X`. This is [Stacks, Tag 0A3S]
(global sections of étale sheaves over a proper scheme over a henselian local ring are those over
the closed fibre). Here it is deduced from its form on Mathlib's small étale site
(`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_closedFibre_zero`): the
equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` between sheaves on the size-bounded small
étale sites of a big étale site and on Mathlib's small étale sites commute with inverse images
(`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`) and with constant sheaves
(`CategoryTheory.equivCommuteConstant`), and bijectivity of a functor on a set of morphisms is
invariant under such conjugation (`CategoryTheory.Functor.bijective_map_of_comp_equivalence_iso`).

## Main definitions

* `AlgebraicGeometry.closedFibreObj`, `AlgebraicGeometry.closedFibreHom`: the closed fibre of
  `f : X ⟶ Spec A` and its inclusion into `X`, as an object and a morphism of the big étale site.

## Main results

* `AlgebraicGeometry.bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero`: the
  restriction `H⁰(X, F) ⟶ H⁰(X₀, j^* F)` is bijective for every abelian sheaf `F`.
* `AlgebraicGeometry.bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero_zmod`: the
  case `F = (ℤ/n)_X`.
* `CategoryTheory.Functor.bijective_map_of_comp_equivalence_iso`: bijectivity of a functor on
  morphisms transports along equivalences of categories.
* `CategoryTheory.Abelian.Ext.bijective_iff_of_apply_mk₀`: a map of `Ext⁰`-groups is bijective
  if and only if the map of morphisms it induces is.

## Implementation notes

The source assumes `A` noetherian, `n ≥ 1` invertible on `A` and `dim X₀ ≤ 1`; none of these is
needed in degree `0`, and the result holds for every abelian sheaf, not only `(ℤ/n)_X`. The
closed fibre is taken as an object of the big étale site under the hypothesis that it lies below
the size cutoff of the site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
-/

/- FK's
hypotheses (A noetherian, dim X_s ≤ 1, n invertible) are dropped (not used in degree 0), and the
statement is proved for every abelian sheaf. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe w u

namespace CategoryTheory

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']

/-- **Bijectivity on morphisms transports along equivalences.** Let `E₁ : C ≌ C'`,
`E₂ : D ≌ D'`, and let `L : C ⥤ D`, `L' : C' ⥤ D'` be functors with `E₁ ⋙ L' ≅ L ⋙ E₂`. If `L'`
is bijective on morphisms `a' ⟶ E₁ b` for an object `a' ≅ E₁ a`, then `L` is bijective on
morphisms `a ⟶ b`. -/
theorem Functor.bijective_map_of_comp_equivalence_iso (E₁ : C ≌ C') (E₂ : D ≌ D')
    (L : C ⥤ D) (L' : C' ⥤ D') (α : E₁.functor ⋙ L' ≅ L ⋙ E₂.functor) {a b : C} {a' : C'}
    (β : E₁.functor.obj a ≅ a')
    (h : Function.Bijective (fun g : a' ⟶ E₁.functor.obj b ↦ L'.map g)) :
    Function.Bijective (fun g : a ⟶ b ↦ L.map g) := by
  have h₁ : Function.Bijective (fun k : E₁.functor.obj a ⟶ E₁.functor.obj b ↦ L'.map k) := by
    have e : (fun k : E₁.functor.obj a ⟶ E₁.functor.obj b ↦ L'.map k) =
        (fun m ↦ L'.map β.hom ≫ m) ∘ (fun g : a' ⟶ E₁.functor.obj b ↦ L'.map g) ∘
          (fun k ↦ β.inv ≫ k) := by
      funext k
      simp [← Functor.map_comp]
    rw [e]
    refine Function.Bijective.comp ?_ (h.comp ?_)
    · refine Function.bijective_iff_has_inverse.2
        ⟨fun m ↦ L'.map β.inv ≫ m, fun m ↦ ?_, fun m ↦ ?_⟩ <;> simp [← Functor.map_comp_assoc]
    · exact Function.bijective_iff_has_inverse.2
        ⟨fun m ↦ β.hom ≫ m, fun m ↦ by simp, fun m ↦ by simp⟩
  have h₂ : Function.Bijective
      (fun g : a ⟶ b ↦ E₂.functor.map (L.map g)) := by
    have e : (fun g : a ⟶ b ↦ E₂.functor.map (L.map g)) =
        (fun m ↦ α.inv.app a ≫ m ≫ α.hom.app b) ∘
          (fun k : E₁.functor.obj a ⟶ E₁.functor.obj b ↦ L'.map k) ∘
          (fun g ↦ E₁.functor.map g) := by
      funext g
      have := α.hom.naturality g
      simp only [Functor.comp_map] at this
      simp [this]
    rw [e]
    refine Function.Bijective.comp ?_ (h₁.comp (E₁.fullyFaithfulFunctor.map_bijective a b))
    refine Function.bijective_iff_has_inverse.2
      ⟨fun m ↦ α.hom.app a ≫ m ≫ α.inv.app b, fun m ↦ ?_, fun m ↦ ?_⟩ <;> simp
  exact (Function.Bijective.of_comp_iff' (E₂.fullyFaithfulFunctor.map_bijective _ _)
    (fun g : a ⟶ b ↦ L.map g)).1 h₂

namespace Abelian.Ext

variable [Abelian C] [Abelian D] [HasExt.{w} C] [HasExt.{w} D]

/-- A map `R : Ext⁰(X, Y) ⟶ Ext⁰(X', Y')` carrying `mk₀ a` to `mk₀ (g a)` is bijective if and
only if `g : (X ⟶ Y) → (X' ⟶ Y')` is. -/
theorem bijective_iff_of_apply_mk₀ {X Y : C} {X' Y' : D} (R : Ext X Y 0 → Ext X' Y' 0)
    (g : (X ⟶ Y) → (X' ⟶ Y')) (h : ∀ a, R (Ext.mk₀ a) = Ext.mk₀ (g a)) :
    Function.Bijective R ↔ Function.Bijective g := by
  have e : R = homEquiv₀.symm ∘ g ∘ homEquiv₀ := by
    funext x
    rw [← mk₀_homEquiv₀_apply x, h]
    simp
  rw [e]
  simp

end Abelian.Ext

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [HenselianLocalRing A] (X : B.Scheme)
  (f : X.obj ⟶ Spec (.of A)) (hZ : B.Contains (closedFibre A f))

/-- The closed fibre `X ×_{Spec A} Spec κ(A)` of `f : X ⟶ Spec A`, as an object of the big étale
site `B`, when it lies below the size cutoff of `B`. -/
abbrev closedFibreObj : B.Scheme := B.obj (closedFibre A f) hZ

/-- The inclusion of the closed fibre, as a morphism of the big étale site `B`. -/
abbrev closedFibreHom : closedFibreObj B A X f hZ ⟶ X :=
  ObjectProperty.homMk (closedFibreInclusion A f)

@[simp]
theorem inclusion_map_closedFibreHom :
    B.inclusion.map (closedFibreHom B A X f hZ) = closedFibreInclusion A f := rfl

/-- **Restriction to the closed fibre is bijective on `H⁰`.** Let `A` be a henselian local ring,
`f : X ⟶ Spec A` a proper morphism and `j : X₀ ⟶ X` the inclusion of the closed fibre. For every
abelian sheaf `F` on the small étale site of `X`, the restriction map
`j^* : H⁰(X, F) ⟶ H⁰(X₀, j^* F)` is bijective. -/
@[weil "lem_fk106_dim_le_1_h0_bijective"]
theorem bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero
    [IsProper f]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (closedFibre A f) hZ) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Function.Bijective
      (smallEtaleCohomologyRestrictionMap B (closedFibreHom B A X f hZ) F 0) := by
  let j := closedFibreHom B A X f hZ
  let LS := smallEtaleInverseImage B j AddCommGrpCat.{u + 1}
  let ZS := (constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  rw [Ext.bijective_iff_of_apply_mk₀ _
    (fun a ↦ (smallEtaleInverseImageConstantSheafIso B j AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift ℤ))).inv ≫ LS.map a)
    (fun a ↦ by
      rw [smallEtaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀])]
  refine Function.Bijective.comp ?_ (?_ : Function.Bijective (fun a : ZS ⟶ F ↦ LS.map a))
  · refine Function.bijective_iff_has_inverse.2 ⟨fun m ↦
      (smallEtaleInverseImageConstantSheafIso B j AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift ℤ))).hom ≫ m, fun m ↦ by simp, fun m ↦ by simp⟩
  -- the Mathlib-site statement
  let LM := etaleAbelianInverseImage.{u, 0} (closedFibreInclusion A f)
  let ZM := (constantSheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  have hM (F' : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Function.Bijective (fun a : ZM ⟶ F' ↦ LM.map a) := by
    let _ := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X.obj
    let _ := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (closedFibre A f)
    have h := bijective_etaleCohomologyRestrictionMap_closedFibre_zero A f F'
    rw [Ext.bijective_iff_of_apply_mk₀ _
      (fun a ↦ ((etaleAbelianInverseImageConstantIso.{u, 0} (closedFibreInclusion A f)).app
        (AddCommGrpCat.of (ULift ℤ))).inv ≫ LM.map a)
      (fun a ↦ by
        rw [etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀])] at h
    refine (Function.Bijective.of_comp_iff' ?_ (fun a : ZM ⟶ F' ↦ LM.map a)).1 h
    exact Function.bijective_iff_has_inverse.2 ⟨fun m ↦
      ((etaleAbelianInverseImageConstantIso.{u, 0} (closedFibreInclusion A f)).app
        (AddCommGrpCat.of (ULift ℤ))).hom ≫ m, fun m ↦ by simp, fun m ↦ by simp⟩
  have : ∀ U : (X.obj.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow U (SmallEtale.toEtaleSite B X.obj X.property).op) AddCommGrpCat.{u + 1} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  let β := (equivCommuteConstant (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
    X.obj.smallEtaleTopology (SmallEtale.toEtaleSite B X.obj X.property)
    (SmallEtale.finalIsTerminal B X.obj X.property)
    (MorphismProperty.Over.mkIdTerminal _ _)).app (AddCommGrpCat.of (ULift ℤ))
  let α := SmallEtale.sheafEquivPullbackBaseChangeIso B j AddCommGrpCat.{u + 1}
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Stacks.EtaleCohomology.smallEtaleBaseChange (closedFibreInclusion A f)) _ _ _)
    (smallEtaleInverseImageAdjunction B j AddCommGrpCat.{u + 1})
  exact Functor.bijective_map_of_comp_equivalence_iso
    (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1})
    (SmallEtale.sheafEquiv B (closedFibre A f) hZ AddCommGrpCat.{u + 1}) LS LM α β (hM _)

/-- **Restriction of `H⁰(X, ℤ/n)` to the closed fibre is bijective.** Let `A` be a henselian
local ring, `f : X ⟶ Spec A` a proper morphism, `j : X₀ ⟶ X` the inclusion of the closed fibre
and `n` a natural number. The restriction map
`j^* : H⁰(X, (ℤ/n)_X) ⟶ H⁰(X₀, j^*(ℤ/n)_X)` is bijective. -/
@[weil "lem_fk106_dim_le_1_h0_bijective"]
theorem bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero_zmod
    [IsProper f]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (closedFibre A f) hZ) AddCommGrpCat.{u + 1})]
    (n : ℕ) :
    Function.Bijective
      (smallEtaleCohomologyRestrictionMap B (closedFibreHom B A X f hZ)
        ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift (ZMod n)))) 0) :=
  bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero B A X f hZ _

end AlgebraicGeometry

end

/-! ### Injectivity of restriction to the closed fibre in degree zero -/

/-!
# Injectivity of restriction to the closed fibre in degree zero

Let `A` be a local ring with residue field `k`, `f : X → Spec A` a universally closed morphism,
`i : X_s → X` the inclusion of the closed fibre `X_s = X ×_{Spec A} Spec k`, and `F` an abelian
sheaf on the small étale site of `X`. Then the restriction map
`i^* : H⁰(X, F) → H⁰(X_s, i^* F)` is injective.

The proof is the classical support argument. In degree zero the restriction map on the
`Ext`-groups out of the constant sheaf `ℤ` is injective as soon as the restriction of global
sections `F(X) → (i^* F)(X_s)` (the unit of `i^* ⊣ i_*` at the final object) is injective. Let
`s` be a global section with `i^* s = 0`. For a point `y` of `X_s`, the germ of `s` at a
geometric point over `i(y)` corresponds, under the canonical isomorphism of stalks
`F_{i(ȳ)} ≅ (i^* F)_ȳ`, to the germ of `i^* s`, hence vanishes; so `s` vanishes on an étale
neighbourhood of `i(y)`. The union `W` of the images of the étale `X`-schemes on which `s` vanishes
is open and contains `X_s`; its complement is closed, misses the closed fibre, and hence is empty,
since its image in `Spec A` is closed and every nonempty closed subset of `Spec A` contains the
closed point. Thus the étale `X`-schemes on which `s` vanishes cover `X`, and `s = 0`.

## Main results

* `AlgebraicGeometry.injective_smallEtaleCohomologyRestrictionMap_zero_of_isPullback`:
  restriction `H⁰(X, F) → H⁰(X_s, i^* F)` to the closed fibre of a universally closed scheme over
  a local ring is injective.
* `AlgebraicGeometry.injective_smallEtaleCohomologyRestrictionMap_zero_of_injective`: the
  degree-zero restriction map is injective when restriction of global sections is.
* `AlgebraicGeometry.injective_smallEtaleRestrictionOnSections_final_of_closed`: restriction of
  global sections along `h : Y → X` is injective when every nonempty closed subset of `X` meets
  the image of `h`.

## Implementation notes

The source states the result in its strictly Henselian setting: `A` a noetherian strictly
Henselian local ring, `n` invertible in `A`, `f` projective, `dim X_s ≤ 1` and `F` a sheaf of
`ℤ/nℤ`-modules, and deduces it from an embedding of constructible sheaves into sheaves with
bijective restriction on `H⁰`. The support argument needs none of these hypotheses: `A` is any
local ring, `f` any universally closed morphism (projective morphisms are proper), and `F` any
abelian sheaf. The closed fibre is given by a pullback square, so that `X_s` may be any object of
the big étale site representing it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (h : Y ⟶ X)

/-- Restriction of global sections along `h : Y ⟶ X` is injective as soon as every nonempty
closed subset of `X` meets the image of `h`: a global section killed by restriction vanishes on
an étale neighbourhood of every point in the image of `h`, by the comparison of stalks
`F_{h(ȳ)} ≅ (h^* F)_ȳ`, and the étale neighbourhoods on which it vanishes then cover `X`. -/
theorem injective_smallEtaleRestrictionOnSections_final_of_closed
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hZ : ∀ Z : Set X.obj, IsClosed Z → Disjoint Z (Set.range (B.inclusion.map h)) → Z = ∅) :
    Function.Injective (smallEtaleRestrictionOnSections B h AddCommGrpCat.{u + 1} F
      (SmallEtale.final B X.obj X.property)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  let T := SmallEtale.final B X.obj X.property
  let R : Sieve T :=
    { arrows := fun U g => F.obj.map g.op s = 0
      downward_closed := by
        intro U V g hg k
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        change F.obj.map k.op (F.obj.map g.op s) = 0
        rw [hg, map_zero] }
  -- the images of the étale neighbourhoods on which `s` vanishes cover `X`
  have hcov : ∀ x : (SmallEtale.toScheme B X.obj X.property).obj T,
      ∃ (U : SmallEtale B X.obj X.property) (g : U ⟶ T), R g ∧
        x ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map g) := by
    -- every point in the image of `h` lies in the image of such a neighbourhood
    have himage : ∀ y : Y.obj, ∃ (U : SmallEtale B X.obj X.property) (g : U ⟶ T), R g ∧
        B.inclusion.map h y ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map g) := by
      intro y
      let w : GeometricPoint Y.obj :=
        { residueField := AlgebraicClosure (Y.obj.residueField y)
          hom := Spec.map (CommRingCat.ofHom (algebraMap (Y.obj.residueField y)
            (AlgebraicClosure (Y.obj.residueField y)))) ≫ Y.obj.fromSpecResidueField y }
      let U : (geometricPointFiber B Y.obj Y.property w).Elements :=
        ⟨SmallEtale.final B Y.obj Y.property, ⟨w.hom, by simp [SmallEtale.final]⟩⟩
      let V : (geometricPointFiber B X.obj X.property (w.map (B.inclusion.map h))).Elements :=
        ⟨T, ⟨w.hom ≫ B.inclusion.map h, by simp [T, SmallEtale.final]⟩⟩
      let a := (smallEtaleBaseChange_finalIsTerminal B h).from (SmallEtale.final B Y.obj Y.property)
      have ha : U.2.1 ≫ (SmallEtale.toScheme B Y.obj Y.property).map a ≫
          B.inclusion.map (pullback.fst V.1.obj.hom h) = V.2.1 := by
        have hk : a.hom.left ≫ pullback.snd T.obj.hom h = 𝟙 _ := Over.w a.hom
        have ha' : a.hom.left ≫ pullback.fst T.obj.hom h = h := by
          have hc : pullback.fst T.obj.hom h ≫ T.obj.hom = pullback.snd T.obj.hom h ≫ h :=
            pullback.condition
          have hc' : pullback.fst T.obj.hom h = pullback.snd T.obj.hom h ≫ h := by
            refine Eq.trans ?_ hc
            exact (Category.comp_id _).symm
          rw [hc']
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) hk).trans (Category.id_comp h))
        change w.hom ≫ B.inclusion.map a.hom.left ≫ B.inclusion.map (pullback.fst T.obj.hom h) =
          w.hom ≫ B.inclusion.map h
        exact congrArg (w.hom ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
          (congrArg B.inclusion.map ha'))
      have hgerm := congrArg (fun φ => AddCommGrpCat.Hom.hom φ s)
        (smallEtaleInverseImageSheafFiberIso_germ B h w AddCommGrpCat.{u + 1} F U V a ha)
      let ιV := colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.obj X.property
          (w.map (B.inclusion.map h)))).op ⋙ F.obj) (op V)
      let ιU := colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.obj Y.property w)).op ⋙
          ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F).obj) (op U)
      have key : ((smallEtaleInverseImageSheafFiberIso B h w AddCommGrpCat.{u + 1}).hom.app F)
          (ιV s) = ιU (((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F).obj.map a.op
            (smallEtaleRestrictionOnSections B h AddCommGrpCat.{u + 1} F T s)) := hgerm
      rw [hs, map_zero, map_zero] at key
      have h0 : ιV s = ιV 0 := by
        rw [map_zero]
        exact (injective_iff_map_eq_zero _).1
          (ConcreteCategory.bijective_of_isIso
            ((smallEtaleInverseImageSheafFiberIso B h w AddCommGrpCat.{u + 1}).hom.app F)).1 _ key
      have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
      obtain ⟨U', g', y', hy', hg'⟩ :=
        ((geometricPointSitePoint B X.obj X.property
          (w.map (B.inclusion.map h))).toPresheafFiber_eq_iff' V.1 V.2 s 0).1 h0
      have hy1 : y'.1 ≫ (SmallEtale.toScheme B X.obj X.property).map g' =
          w.hom ≫ B.inclusion.map h := congrArg Subtype.val hy'
      refine ⟨U', g', ?_, y'.1 default, ?_⟩
      · change F.obj.map g'.op s = 0
        rw [hg', map_zero]
      · rw [← Scheme.Hom.comp_apply, hy1]
        change (B.inclusion.map h) ((Y.obj.fromSpecResidueField y) _) = _
        rw [Scheme.fromSpecResidueField_apply]
    let W : Set X.obj := {z | ∃ (U : SmallEtale B X.obj X.property) (g : U ⟶ T), R g ∧
      z ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map g)}
    have hW : IsOpen W := by
      rw [isOpen_iff_forall_mem_open]
      rintro z ⟨U, g, hg, hz⟩
      exact ⟨_, fun z' hz' => ⟨U, g, hg, hz'⟩,
        ((SmallEtale.toScheme B X.obj X.property).map g).isOpenMap.isOpen_range, hz⟩
    have hWc := hZ Wᶜ hW.isClosed_compl (Set.disjoint_left.2 fun z hz ⟨y, hy⟩ => hz (by
      obtain ⟨U, g, hg, hy'⟩ := himage y
      exact ⟨U, g, hg, hy ▸ hy'⟩))
    intro x
    by_contra hx
    have hxW : (x : X.obj) ∈ Wᶜ := by
      rintro ⟨U, g, hg, hxg⟩
      exact hx ⟨U, g, hg, hxg⟩
    rw [hWc] at hxW
    exact hxW
  have hR : R ∈ SmallEtale.topology B X.obj X.property T :=
    SmallEtale.mem_topology_of_jointlySurjective hcov
  exact F.isSeparated T R hR s 0 (fun U g hg => by rw [hg, map_zero])

variable [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]

/-- The restriction map `H⁰(X, F) → H⁰(Y, h^* F)` is injective as soon as restriction of global
sections `F(X) → (h^* F)(Y ×_X X)` is: a degree-zero class is a morphism `ℤ_X ⟶ F`, its
restriction corresponds under the adjunction `h^* ⊣ h_*` to its composite with the unit
`F ⟶ h_* h^* F`, and morphisms out of `ℤ_X` are global sections. -/
theorem injective_smallEtaleCohomologyRestrictionMap_zero_of_injective
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Function.Injective (smallEtaleRestrictionOnSections B h AddCommGrpCat.{u + 1} F
      (SmallEtale.final B X.obj X.property))) :
    Function.Injective (smallEtaleCohomologyRestrictionMap.{w} B h F 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  simp only [smallEtaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀] at hxy
  have h1 := (Ext.mk₀_bijective _ _).1 hxy
  rw [cancel_epi] at h1
  have h2 := congrArg ((smallEtaleInverseImageAdjunction B h AddCommGrpCat.{u + 1}).homEquiv _ _) h1
  simp only [Adjunction.homEquiv_unit, Adjunction.unit_naturality] at h2
  let cadj := constantSheafAdj (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
    (SmallEtale.finalIsTerminal B X.obj X.property)
  have h3 := congrArg (cadj.homEquiv _ _) h2
  simp only [Adjunction.homEquiv_naturality_right] at h3
  have hmono : Mono (((sheafSections _ _).obj (op (SmallEtale.final B X.obj X.property))).map
      ((smallEtaleInverseImageAdjunction B h AddCommGrpCat.{u + 1}).unit.app F)) :=
    (AddCommGrpCat.mono_iff_injective _).2 hF
  rw [cancel_mono] at h3
  rw [(cadj.homEquiv _ _).injective h3]

/-- **Restriction to the closed fibre is injective in degree zero.** Let `A` be a local ring,
`f : X ⟶ Spec A` universally closed and `h : Y ⟶ X` the inclusion of the closed fibre, given as
a pullback of `Spec k ⟶ Spec A` along `f` for the residue field `k` of `A`. For every abelian
sheaf `F` on the small étale site of `X`, the restriction map `H⁰(X, F) → H⁰(Y, h^* F)` is
injective. -/
@[weil "lem_fk106_h0_restriction_injective"]
theorem injective_smallEtaleCohomologyRestrictionMap_zero_of_isPullback
    {A : Type u} [CommRing A] [IsLocalRing A] (f : X.obj ⟶ Spec (.of A)) [UniversallyClosed f]
    (g : Y.obj ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (hP : IsPullback (B.inclusion.map h) g f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Function.Injective (smallEtaleCohomologyRestrictionMap.{w} B h F 0) := by
  refine injective_smallEtaleCohomologyRestrictionMap_zero_of_injective B h F
    (injective_smallEtaleRestrictionOnSections_final_of_closed B h F fun Z hZ hdisj => ?_)
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨z', hz', hz'f⟩ := (IsLocalRing.specializes_closedPoint (f z)).mem_closed
    (f.isClosedMap Z hZ) ⟨z, hz, rfl⟩
  have hr : z' ∈ Set.range (pullback.fst f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint _, ?_⟩
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) :=
      inferInstanceAs (IsLocalHom (IsLocalRing.residue A))
    rw [Spec_closedPoint]
    exact hz'f.symm
  obtain ⟨p, rfl⟩ := hr
  refine Set.disjoint_left.1 hdisj hz' ⟨hP.isoPullback.inv p, ?_⟩
  have e : hP.isoPullback.inv ≫ B.inclusion.map h = pullback.fst _ _ :=
    (Iso.inv_comp_eq _).2 hP.isoPullback_hom_fst.symm
  rw [← e]
  rfl

end AlgebraicGeometry

end
