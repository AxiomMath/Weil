module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringSectionsMap
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtalePresheafFk101
public import WeilFrontier.Defs.CategoryTheory.Sites.Plus

/-!
# Plus presheaves on the étale category

Let `A` be a commutative ring and `F` a presheaf on the étale category `Et(A)`. A plus presheaf
of `F` is a presheaf `P` whose value at every object `B` is the plus construction `F̃(B)`, and
whose restriction maps are given on classes by morphisms of coverings: for every morphism
`f : B ⟶ B'`, coverings `𝔅` of `B` and `𝔅'` of `B'`, every morphism `φ : 𝔅 ⟶ 𝔅'` over `f` and
every `s ∈ F(𝔅)`,
`P(f)([𝔅, s]) = [𝔅', φ_* s]`.

For a presheaf of sets `P(B)` is the set `F̃(B)`; for a presheaf of abelian groups it is the
abelian group `F̃(B)` and `P(f)` is a homomorphism.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf F`: a plus presheaf of a presheaf of sets `F`,
  given by its restriction maps `F̃(B) → F̃(B')`.
- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.toPresheaf`: the underlying presheaf
  `B ↦ F̃(B)`.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf F`: a plus presheaf of a presheaf of abelian
  groups `F`.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.toPresheaf`: the underlying presheaf of
  abelian groups `B ↦ F̃(B)`.

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.toPresheaf_map_mk`,
  `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.toPresheaf_map_mk`:
  `P(f)([𝔅, s]) = [𝔅', φ_* s]` for the underlying presheaf.

## Implementation notes

A plus presheaf is bundled as its family of restriction maps between the plus constructions,
so that the value of the underlying presheaf at `B` is `F̃(B)` by definition rather than up to
an equality of types. The plus construction is the colimit over the category of coverings of
`B` indexed in a universe `w`, which is a parameter.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

open Covering

/-- A plus presheaf of a presheaf of sets `F` on `Et(A)`: restriction maps
`P(f) : F̃(B) → F̃(B')` for the morphisms `f : B ⟶ B'` of `Et(A)`, functorial in `f`, such that
`P(f)([𝔅, s]) = [𝔅', φ_* s]` for every covering `𝔅` of `B`, every covering `𝔅'` of `B'`, every
morphism `φ : 𝔅 ⟶ 𝔅'` over `f` and every `s ∈ F(𝔅)`. -/
@[weil "def_fk101_plus_presheaf", ext]
structure PlusPresheaf (F : Presheaf A (Type v)) where
  /-- The restriction map `P(f) : F̃(B) → F̃(B')`. -/
  map : ∀ {B B' : EtaleCategory A}, (B ⟶ B') →
    plusConstruction.{w} F B → plusConstruction.{w} F B'
  /-- Restriction along the identity is the identity. -/
  map_id : ∀ (B : EtaleCategory A) (t : plusConstruction.{w} F B), map (𝟙 B) t = t
  /-- Restriction is functorial. -/
  map_comp : ∀ {B B' B'' : EtaleCategory A} (f : B ⟶ B') (g : B' ⟶ B'')
    (t : plusConstruction.{w} F B), map (f ≫ g) t = map g (map f t)
  /-- `P(f)([𝔅, s]) = [𝔅', φ_* s]` for every morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`. -/
  map_mk : ∀ {B B' : EtaleCategory A} (f : B ⟶ B') (𝔅 : Covering.{w} B) (𝔅' : Covering.{w} B')
    (φ : HomOver f 𝔅 𝔅') (s : coveringSections F 𝔅.map),
    map f (plusConstruction.mk 𝔅 s) = plusConstruction.mk 𝔅' (φ.sectionsMap F s)

namespace PlusPresheaf

variable {F : Presheaf A (Type v)} (P : PlusPresheaf.{w} F)

/-- The presheaf `B ↦ F̃(B)` underlying a plus presheaf. -/
@[weil "def_fk101_plus_presheaf", simps obj]
def toPresheaf : Presheaf A (Type (max (u + 1) (w + 1) v)) where
  obj B := plusConstruction.{w} F B
  map f := ↾(P.map f)
  map_id B := ConcreteCategory.hom_ext _ _ (P.map_id B)
  map_comp f g := ConcreteCategory.hom_ext _ _ (P.map_comp f g)

@[simp]
lemma toPresheaf_map_apply {B B' : EtaleCategory A} (f : B ⟶ B')
    (t : plusConstruction.{w} F B) : P.toPresheaf.map f t = P.map f t :=
  rfl

/-- `P(f)([𝔅, s]) = [𝔅', φ_* s]` for the underlying presheaf of a plus presheaf. -/
lemma toPresheaf_map_mk {B B' : EtaleCategory A} (f : B ⟶ B') (𝔅 : Covering.{w} B)
    (𝔅' : Covering.{w} B') (φ : HomOver f 𝔅 𝔅') (s : coveringSections F 𝔅.map) :
    P.toPresheaf.map f (plusConstruction.mk 𝔅 s) =
      plusConstruction.mk 𝔅' (φ.sectionsMap F s) :=
  P.map_mk f 𝔅 𝔅' φ s

end PlusPresheaf

/-- A plus presheaf of a presheaf of abelian groups `F` on `Et(A)`: homomorphisms
`P(f) : F̃(B) ⟶ F̃(B')` for the morphisms `f : B ⟶ B'` of `Et(A)`, functorial in `f`, such that
`P(f)([𝔅, s]) = [𝔅', φ_* s]` for every covering `𝔅` of `B`, every covering `𝔅'` of `B'`, every
morphism `φ : 𝔅 ⟶ 𝔅'` over `f` and every `s ∈ F(𝔅)`. -/
@[weil "def_fk101_plus_presheaf", ext]
structure AddPlusPresheaf (F : Presheaf A AddCommGrpCat.{v}) where
  /-- The restriction homomorphism `P(f) : F̃(B) ⟶ F̃(B')`. -/
  map : ∀ {B B' : EtaleCategory A}, (B ⟶ B') →
    (addPlusConstruction.{w} F B ⟶ addPlusConstruction.{w} F B')
  /-- Restriction along the identity is the identity. -/
  map_id : ∀ B : EtaleCategory A, map (𝟙 B) = 𝟙 _
  /-- Restriction is functorial. -/
  map_comp : ∀ {B B' B'' : EtaleCategory A} (f : B ⟶ B') (g : B' ⟶ B''),
    map (f ≫ g) = map f ≫ map g
  /-- `P(f)([𝔅, s]) = [𝔅', φ_* s]` for every morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`. -/
  map_mk : ∀ {B B' : EtaleCategory A} (f : B ⟶ B') (𝔅 : Covering.{w} B) (𝔅' : Covering.{w} B')
    (φ : HomOver f 𝔅 𝔅') (s : coveringSectionsAddSubgroup F 𝔅.map),
    map f (addPlusConstruction.mk 𝔅 s) =
      addPlusConstruction.mk 𝔅' (HomOver.sectionsAddMonoidHom F φ s)

namespace AddPlusPresheaf

variable {F : Presheaf A AddCommGrpCat.{v}} (P : AddPlusPresheaf.{w} F)

/-- The presheaf of abelian groups `B ↦ F̃(B)` underlying a plus presheaf. -/
@[weil "def_fk101_plus_presheaf", simps obj map]
def toPresheaf : Presheaf A AddCommGrpCat where
  obj B := addPlusConstruction.{w} F B
  map f := P.map f
  map_id B := P.map_id B
  map_comp f g := P.map_comp f g

/-- `P(f)([𝔅, s]) = [𝔅', φ_* s]` for the underlying presheaf of a plus presheaf. -/
lemma toPresheaf_map_mk {B B' : EtaleCategory A} (f : B ⟶ B') (𝔅 : Covering.{w} B)
    (𝔅' : Covering.{w} B') (φ : HomOver f 𝔅 𝔅') (s : coveringSectionsAddSubgroup F 𝔅.map) :
    P.toPresheaf.map f (addPlusConstruction.mk 𝔅 s) =
      addPlusConstruction.mk 𝔅' (HomOver.sectionsAddMonoidHom F φ s) :=
  P.map_mk f 𝔅 𝔅' φ s

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
