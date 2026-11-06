module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.AffineEtale
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import Weil.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Restriction of an étale presheaf on `Spec A` to the étale category of `A`

Let `X = Spec A` and let `F` be a presheaf on the étale category `Et(X)` of noetherian separated
étale `X`-schemes. For an object `B` of the étale category `Et(A)` of étale `A`-algebras, let
`F₀(B)` be the set (group, ...) of families `(s_{V,φ})`, indexed by the pairs of an object `V` of
`Et(X)` and a morphism `φ : V ⟶ Spec B` of `Spec A`-schemes, with `s_{V,φ} ∈ F(V)` and
`h^* s_{V,φ} = s_{V',φ ∘ h}` for every morphism `h : V' ⟶ V` of `Et(X)`. A homomorphism `B → C`
of `Et(A)`, with `π : Spec C ⟶ Spec B`, induces `F₀(B) → F₀(C)`,
`(s_{V,φ}) ↦ (s_{V,π ∘ ψ})_{(V,ψ)}`. This defines a covariant functor `F₀` on `Et(A)`.

The pairs `(V, φ)` are the objects of the category of structured arrows from `Spec B` to the
functor `Et(X)ᵒᵖ ⥤ (X-schemes)ᵒᵖ`, and `F₀(B)` is the limit of `F` over it: `F₀` is the
pointwise right Kan extension of `F` along `Et(X)ᵒᵖ ⥤ (X-schemes)ᵒᵖ`, evaluated on the affine
étale `X`-schemes `Spec B`.

## Main definitions

* `AlgebraicGeometry.EtaleCategory.toOver A`: the functor `Et(A) ⥤ (Spec A-schemes)ᵒᵖ`,
  `B ↦ Spec B`.
* `AlgebraicGeometry.affineRestrictionIndex B hS X`: the category of pairs `(V, φ)`, with
  `AlgebraicGeometry.affineRestrictionIndex.mk` building one from `V` and `φ`.
* `AlgebraicGeometry.affineRestriction B hS F`: the functor `F₀ : Et(A) ⥤ C`.
* `AlgebraicGeometry.affineRestriction.π F X j`: the component `s ↦ s_{V,φ}` at `j = (V, φ)`.
* `AlgebraicGeometry.affineRestrictionFunctor B hS C`: the functor `F ↦ F₀`.
* `AlgebraicGeometry.affineRestriction.sectionsEquiv F X`: for a presheaf of sets, `F₀(B)` is
  the set of compatible families `(s_{V,φ})`.

## Main results

* `AlgebraicGeometry.affineRestriction.π_mk_map`: the families are compatible,
  `h^* s_{V,φ} = s_{V',φ ∘ h}`.
* `AlgebraicGeometry.affineRestriction.map_π_mk`: the map `F₀(B) → F₀(C)` induced by
  `Spec C ⟶ Spec B` sends `(s_{V,φ})` to `(s_{V,π ∘ ψ})`.

## Implementation notes

The values of `F` are taken in any category `C` with limits indexed by `u`-small categories
(sets and abelian groups of universe at least `u` among them); the index category of pairs
`(V, φ)` is essentially small because `Et(X)` is. `Et(A)` is
`AlgebraicGeometry.EtaleCategory A`, the opposite of Mathlib's affine étale site of `Spec A`;
its object `B` gives the scheme `Spec B` together with the étale morphism `Spec B ⟶ Spec A`.
No noetherian hypothesis on `A` is needed for the definition.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {A : CommRingCat.{u}} (B : BigEtaleSite.{u}) (hS : B.Contains (Spec A))

namespace EtaleCategory

variable (A) in
/-- The functor `Et(A) ⥤ (Spec A-schemes)ᵒᵖ` sending an étale `A`-algebra `B` to the
`Spec A`-scheme `Spec B`. -/
def toOver : EtaleCategory A ⥤ (Over (Spec A))ᵒᵖ :=
  (Scheme.AffineEtale.Spec (Spec A) ⋙ MorphismProperty.Over.forget _ _ _).op

@[simp]
lemma toOver_obj_unop_left (X : EtaleCategory A) :
    ((toOver A).obj X).unop.left = Spec X.unop.left.unop := rfl

@[simp]
lemma toOver_obj_unop_hom (X : EtaleCategory A) :
    ((toOver A).obj X).unop.hom = X.unop.hom := rfl

@[simp]
lemma toOver_map_unop_left {X Y : EtaleCategory A} (g : X ⟶ Y) :
    ((toOver A).map g).unop.left = Spec.map g.unop.left.unop := rfl

end EtaleCategory

/-- The category of pairs `(V, φ)` of an object `V` of `Et(Spec A)` and a morphism
`φ : V ⟶ Spec B` of `Spec A`-schemes, for `B` in `Et(A)`; a morphism `(V, φ) ⟶ (V', φ')` is a
morphism `h : V' ⟶ V` of `Et(Spec A)` with `φ ∘ h = φ'`. -/
abbrev affineRestrictionIndex (X : EtaleCategory A) :=
  StructuredArrow ((EtaleCategory.toOver A).obj X)
    (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).op

variable {B hS}

/-- The pair `(V, φ)` given by an object `V` of `Et(Spec A)` and a morphism `φ : V ⟶ Spec B` over
`Spec A`. -/
def affineRestrictionIndex.mk (X : EtaleCategory A)
    (V : SmallNoetherianSeparatedEtale B (Spec A) hS)
    (φ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec X.unop.left.unop)
    (hφ : φ ≫ X.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V) :
    affineRestrictionIndex B hS X :=
  StructuredArrow.mk (Y := op V)
    (Over.homMk (U := (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).obj V)
      (V := ((EtaleCategory.toOver A).obj X).unop) φ hφ).op

variable {C : Type v} [Category.{w} C] [HasLimitsOfSize.{u, u} C]

/-- The limits defining `F₀` exist: the category of pairs `(V, φ)` is essentially small. -/
instance (Y : (Over (Spec A))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow Y (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).op) C :=
  hasLimitsOfShape_of_essentiallySmall _ _

variable (B hS) in
/-- **The restriction `F₀` of a presheaf on `Et(Spec A)` to `Et(A)`.** For `B` in `Et(A)`,
`F₀(B)` is the limit of `F(V)` over the pairs `(V, φ : V ⟶ Spec B)`, i.e. the object of
compatible families `(s_{V,φ})`; a morphism `B ⟶ C` of `Et(A)` acts by
`(s_{V,φ}) ↦ (s_{V,π ∘ ψ})_{(V,ψ)}` with `π : Spec C ⟶ Spec B`. -/
@[weil "def_fk102_affine_sheaf_restriction"]
def affineRestriction (F : EtalePresheaf B (Spec A) hS C) : EtaleCategory A ⥤ C :=
  EtaleCategory.toOver A ⋙
    (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).op.pointwiseRightKanExtension F

namespace affineRestriction

variable (F : EtalePresheaf B (Spec A) hS C)

/-- The component `s ↦ s_{V,φ}`. -/
def π (X : EtaleCategory A) (j : affineRestrictionIndex B hS X) :
    (affineRestriction B hS F).obj X ⟶ F.obj j.right :=
  limit.π (StructuredArrow.proj _ _ ⋙ F) j

/-- Morphisms into `F₀(X)` are determined by their components. -/
@[ext]
lemma hom_ext {Z : C} {X : EtaleCategory A} {f g : Z ⟶ (affineRestriction B hS F).obj X}
    (h : ∀ j, f ≫ π F X j = g ≫ π F X j) : f = g :=
  limit.hom_ext h

/-- The map induced by `g : X ⟶ Y` composed with the component at `j` over `Y` is the component
at the image of `j` over `X`. -/
@[reassoc]
lemma map_π {X Y : EtaleCategory A} (g : X ⟶ Y) (j : affineRestrictionIndex B hS Y) :
    (affineRestriction B hS F).map g ≫ π F Y j =
      π F X ((StructuredArrow.map ((EtaleCategory.toOver A).map g)).obj j) := by
  exact limit.lift_π _ _

/-- The components of an element of `F₀(X)` are compatible along morphisms of pairs. -/
@[reassoc]
lemma π_map {X : EtaleCategory A} {j k : affineRestrictionIndex B hS X} (h : j ⟶ k) :
    π F X j ≫ F.map h.right = π F X k :=
  limit.w (StructuredArrow.proj _ _ ⋙ F) h

/-- For `g : B ⟶ C` in `Et(A)` and `ψ : V ⟶ Spec C` over `Spec A`, the composite
`V ⟶ Spec C ⟶ Spec B` is again a morphism over `Spec A`. -/
lemma mk_comp_spec_map_comp_hom {X Y : EtaleCategory A} (g : X ⟶ Y)
    (V : SmallNoetherianSeparatedEtale B (Spec A) hS)
    (ψ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec Y.unop.left.unop)
    (hψ : ψ ≫ Y.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V) :
    (ψ ≫ Spec.map g.unop.left.unop) ≫ X.unop.hom =
      SmallNoetherianSeparatedEtale.structureMorphism V := by
  rw [Category.assoc, ← hψ]
  congr 1
  simpa using g.unop.w

/-- **The families are compatible**: `h^* s_{V,φ} = s_{V',φ ∘ h}` for `h : V' ⟶ V`. -/
@[reassoc]
lemma π_mk_map {X : EtaleCategory A} {V V' : SmallNoetherianSeparatedEtale B (Spec A) hS}
    (h : V' ⟶ V)
    (φ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec X.unop.left.unop)
    (hφ : φ ≫ X.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V) :
    π F X (affineRestrictionIndex.mk X V φ hφ) ≫ F.map h.op =
      π F X (affineRestrictionIndex.mk X V'
        ((SmallNoetherianSeparatedEtale.toScheme B _ hS).map h ≫ φ)
        (by rw [Category.assoc, hφ]
            exact SmallNoetherianSeparatedEtale.toScheme_map_comp_structureMorphism h)) := by
  refine π_map F (StructuredArrow.homMk (f := affineRestrictionIndex.mk X V φ hφ)
    (f' := affineRestrictionIndex.mk X V' _ _) h.op ?_)
  apply Quiver.Hom.unop_inj
  ext
  simp [affineRestrictionIndex.mk]
  rfl

/-- The pair `(V, ψ)` over `Spec C` becomes `(V, π ∘ ψ)` over `Spec B`. -/
lemma map_obj_mk {X Y : EtaleCategory A} (g : X ⟶ Y)
    (V : SmallNoetherianSeparatedEtale B (Spec A) hS)
    (ψ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec Y.unop.left.unop)
    (hψ : ψ ≫ Y.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V) :
    (StructuredArrow.map ((EtaleCategory.toOver A).map g)).obj
        (affineRestrictionIndex.mk Y V ψ hψ) =
      affineRestrictionIndex.mk X V (ψ ≫ Spec.map g.unop.left.unop)
        (mk_comp_spec_map_comp_hom g V ψ hψ) := by
  simp only [affineRestrictionIndex.mk, StructuredArrow.map_mk]
  congr 1

/-- **The transition maps**: `F₀(B) → F₀(C)` sends `(s_{V,φ})` to `(s_{V,π ∘ ψ})_{(V,ψ)}`. -/
@[weil "def_fk102_affine_sheaf_restriction", reassoc]
lemma map_π_mk {X Y : EtaleCategory A} (g : X ⟶ Y)
    (V : SmallNoetherianSeparatedEtale B (Spec A) hS)
    (ψ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec Y.unop.left.unop)
    (hψ : ψ ≫ Y.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V) :
    (affineRestriction B hS F).map g ≫ π F Y (affineRestrictionIndex.mk Y V ψ hψ) =
      π F X (affineRestrictionIndex.mk X V (ψ ≫ Spec.map g.unop.left.unop)
        (mk_comp_spec_map_comp_hom g V ψ hψ)) := by
  exact map_π F g _

end affineRestriction

namespace affineRestriction

/-- The components of the limit map induced by a morphism of presheaves. -/
@[reassoc]
lemma limMap_whiskerLeft_π {F G : EtalePresheaf B (Spec A) hS C} (α : F ⟶ G)
    (X : EtaleCategory A) (j : affineRestrictionIndex B hS X) :
    limMap (Functor.whiskerLeft (StructuredArrow.proj ((EtaleCategory.toOver A).obj X)
      (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).op) α) ≫ π G X j =
      π F X j ≫ α.app j.right :=
  limMap_π _ _

/-- A morphism of presheaves `α : F ⟶ G` induces `F₀ ⟶ G₀`, `(s_{V,φ}) ↦ (α s_{V,φ})`. -/
def map {F G : EtalePresheaf B (Spec A) hS C} (α : F ⟶ G) :
    affineRestriction B hS F ⟶ affineRestriction B hS G where
  app X := limMap (Functor.whiskerLeft (StructuredArrow.proj _ _) α)
  naturality X Y g := by
    refine hom_ext G fun j ↦ ?_
    erw [Category.assoc, Category.assoc, limMap_whiskerLeft_π, map_π_assoc, map_π,
      limMap_whiskerLeft_π]
    rfl

/-- The components of `α₀ : F₀ ⟶ G₀` are those of `α`. -/
@[reassoc (attr := simp)]
lemma map_app_π {F G : EtalePresheaf B (Spec A) hS C} (α : F ⟶ G)
    (X : EtaleCategory A) (j : affineRestrictionIndex B hS X) :
    (map α).app X ≫ π G X j = π F X j ≫ α.app j.right :=
  limMap_whiskerLeft_π α X j

end affineRestriction

variable (B hS C) in
/-- The functor `F ↦ F₀` from presheaves on `Et(Spec A)` to presheaves on `Et(A)`. -/
def affineRestrictionFunctor : EtalePresheaf B (Spec A) hS C ⥤ (EtaleCategory A ⥤ C) where
  obj F := affineRestriction B hS F
  map α := affineRestriction.map α
  map_id F := by
    ext X : 2
    exact affineRestriction.hom_ext F fun j ↦ by simp
  map_comp α β := by
    ext X : 2
    exact affineRestriction.hom_ext _ fun j ↦ by simp

@[simp]
lemma affineRestrictionFunctor_obj (F : EtalePresheaf B (Spec A) hS C) :
    (affineRestrictionFunctor B hS C).obj F = affineRestriction B hS F :=
  rfl

@[simp]
lemma affineRestrictionFunctor_map {F G : EtalePresheaf B (Spec A) hS C} (α : F ⟶ G) :
    (affineRestrictionFunctor B hS C).map α = affineRestriction.map α :=
  rfl

namespace affineRestriction

section Types

variable [HasLimitsOfSize.{u, u} (Type v)] (F : EtalePresheaf B (Spec A) hS (Type v))

/-- **`F₀(B)` is the set of families**: for a presheaf of sets, an element of `F₀(B)` is the
same as a family `(s_{V,φ})` with `h^* s_{V,φ} = s_{V',φ ∘ h}`. -/
@[weil "def_fk102_affine_sheaf_restriction"]
def sectionsEquiv (X : EtaleCategory A) :
    (affineRestriction B hS F).obj X ≃ (StructuredArrow.proj ((EtaleCategory.toOver A).obj X)
      (SmallNoetherianSeparatedEtale.toOver B (Spec A) hS).op ⋙ F).sections :=
  Types.limitEquivSections _

/-- The family attached to `x` has components `π F X j x`. -/
@[simp]
lemma sectionsEquiv_apply (X : EtaleCategory A) (x : (affineRestriction B hS F).obj X)
    (j : affineRestrictionIndex B hS X) :
    (sectionsEquiv F X x).1 j = π F X j x :=
  rfl

/-- Elements of `F₀(X)` are determined by their components. -/
@[ext]
lemma ext {X : EtaleCategory A} {x y : (affineRestriction B hS F).obj X}
    (h : ∀ j, π F X j x = π F X j y) : x = y :=
  Types.limit_ext _ x y h

/-- `h^* s_{V,φ} = s_{V',φ ∘ h}`, elementwise. -/
lemma π_mk_map_apply {X : EtaleCategory A} {V V' : SmallNoetherianSeparatedEtale B (Spec A) hS}
    (h : V' ⟶ V)
    (φ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec X.unop.left.unop)
    (hφ : φ ≫ X.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V)
    (x : (affineRestriction B hS F).obj X) :
    F.map h.op (π F X (affineRestrictionIndex.mk X V φ hφ) x) =
      π F X (affineRestrictionIndex.mk X V'
        ((SmallNoetherianSeparatedEtale.toScheme B _ hS).map h ≫ φ)
        (by rw [Category.assoc, hφ]
            exact SmallNoetherianSeparatedEtale.toScheme_map_comp_structureMorphism h)) x :=
  by rw [← π_mk_map F h φ hφ]; rfl

/-- The transition map `F₀(B) → F₀(C)`, elementwise. -/
lemma π_mk_affineRestriction_map_apply {X Y : EtaleCategory A} (g : X ⟶ Y)
    (V : SmallNoetherianSeparatedEtale B (Spec A) hS)
    (ψ : (SmallNoetherianSeparatedEtale.toScheme B (Spec A) hS).obj V ⟶ Spec Y.unop.left.unop)
    (hψ : ψ ≫ Y.unop.hom = SmallNoetherianSeparatedEtale.structureMorphism V)
    (x : (affineRestriction B hS F).obj X) :
    π F Y (affineRestrictionIndex.mk Y V ψ hψ) ((affineRestriction B hS F).map g x) =
      π F X (affineRestrictionIndex.mk X V (ψ ≫ Spec.map g.unop.left.unop)
        (mk_comp_spec_map_comp_hom g V ψ hψ)) x :=
  by rw [← map_π_mk F g V ψ hψ]; rfl

end Types

end affineRestriction

end AlgebraicGeometry

end
