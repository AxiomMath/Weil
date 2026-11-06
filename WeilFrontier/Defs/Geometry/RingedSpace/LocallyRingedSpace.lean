module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Basic.Complex.Basic

/-!
# Locally `ℂ`-ringed spaces

A *locally `ℂ`-ringed space* is a topological space `Z` with a sheaf `𝒪_Z` of `ℂ`-algebras all of
whose stalks are local rings; a morphism `(Z, 𝒪_Z) ⟶ (Y, 𝒪_Y)` is a morphism of locally ringed
spaces `(f, f^#)` whose sheaf map `f^# : 𝒪_Y ⟶ f_* 𝒪_Z` is a map of sheaves of `ℂ`-algebras.

We model this category as the over category of locally ringed spaces over `Spec ℂ`. By the
`Γ ⊣ Spec` adjunction a morphism of locally ringed spaces `Z ⟶ Spec ℂ` is the same as a ring map
`ℂ ⟶ Γ(Z, 𝒪_Z)`, which in turn makes every ring of sections and every stalk of `𝒪_Z` a
`ℂ`-algebra, compatibly with restrictions and germs; and a morphism of locally ringed spaces
commutes with the structure maps to `Spec ℂ` exactly when its sheaf map is `ℂ`-linear
(`AlgebraicGeometry.LocallyCRingedSpace.comp_hom_eq_hom_iff`).

A scheme over `ℂ` is a locally `ℂ`-ringed space through the fully faithful functor
`AlgebraicGeometry.LocallyCRingedSpace.ofScheme`, so that morphisms of `ℂ`-schemes are exactly the
morphisms of the associated locally `ℂ`-ringed spaces.

## Main definitions

- `AlgebraicGeometry.LocallyCRingedSpace`: the category `LRS_ℂ` of locally `ℂ`-ringed spaces.
- `AlgebraicGeometry.LocallyCRingedSpace.toΓ`: the structure map `ℂ ⟶ Γ(Z, 𝒪_Z)`; it induces the
  `ℂ`-algebra structures on the rings of sections and on the stalks.
- `AlgebraicGeometry.LocallyCRingedSpace.ofScheme`: a scheme over `Spec ℂ` as a locally
  `ℂ`-ringed space.
- `AlgebraicGeometry.LocallyCRingedSpace.restrict`: the open subspace `(W, 𝒪_Z|_W)` on an open
  subset `W ⊆ Z`, with its inclusion `AlgebraicGeometry.LocallyCRingedSpace.ofRestrict`.

## Main results

- `AlgebraicGeometry.LocallyCRingedSpace.comp_hom_eq_hom_iff`: a morphism of locally ringed spaces
  is a morphism over `Spec ℂ` if and only if its sheaf map is `ℂ`-linear on all sections.
- `AlgebraicGeometry.LocallyCRingedSpace.fullyFaithfulOfScheme`: `ofScheme` is fully faithful.

## Implementation notes

The structure sheaf of a locally ringed space in Mathlib is valued in commutative rings; the
`ℂ`-algebra structure is the extra datum of the structure morphism to `Spec ℂ`, rather than a
sheaf valued in `ℂ`-algebras. The two descriptions agree by `comp_hom_eq_hom_iff`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, §I.11.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The category `LRS_ℂ` of *locally `ℂ`-ringed spaces*: locally ringed spaces together with a
morphism to `Spec ℂ`, i.e. with a sheaf of `ℂ`-algebras whose stalks are local rings. Morphisms
are morphisms of locally ringed spaces over `Spec ℂ`, i.e. those whose sheaf maps are
`ℂ`-algebra maps. -/
@[weil "def_fk111_locally_c_ringed_space"]
abbrev LocallyCRingedSpace : Type 1 :=
  Over (Spec.toLocallyRingedSpace.obj (op (CommRingCat.of ℂ)))

namespace LocallyCRingedSpace

variable (Z : LocallyCRingedSpace)

/-- The structure map `ℂ ⟶ Γ(Z, 𝒪_Z)` of a locally `ℂ`-ringed space. -/
def toΓ : CommRingCat.of ℂ ⟶ Z.left.presheaf.obj (op ⊤) :=
  toSpecΓ _ ≫ LocallyRingedSpace.Γ.map Z.hom.op

theorem toΓ_def : Z.toΓ = toSpecΓ _ ≫ LocallyRingedSpace.Γ.map Z.hom.op :=
  rfl

/-- The structure map `ℂ ⟶ 𝒪_Z(U)` on an open subset `U`. -/
def toSections (U : Opens Z.left) : CommRingCat.of ℂ ⟶ Z.left.presheaf.obj (op U) :=
  Z.toΓ ≫ Z.left.presheaf.map (homOfLE le_top).op

/-- The structure map `ℂ ⟶ 𝒪_{Z,z}` on the stalk at a point `z`. -/
def toStalk (z : Z.left) : CommRingCat.of ℂ ⟶ Z.left.presheaf.stalk z :=
  Z.toΓ ≫ Z.left.presheaf.germ ⊤ z trivial

instance (U : Opens Z.left) : Algebra ℂ (Z.left.presheaf.obj (op U)) :=
  (Z.toSections U).hom.toAlgebra

instance (z : Z.left) : Algebra ℂ (Z.left.presheaf.stalk z) :=
  (Z.toStalk z).hom.toAlgebra

theorem algebraMap_sections (U : Opens Z.left) :
    algebraMap ℂ (Z.left.presheaf.obj (op U)) = (Z.toSections U).hom :=
  rfl

theorem algebraMap_stalk (z : Z.left) :
    algebraMap ℂ (Z.left.presheaf.stalk z) = (Z.toStalk z).hom :=
  rfl

@[simp]
theorem toSections_top : Z.toSections ⊤ = Z.toΓ := by
  rw [toSections, show homOfLE (le_top : (⊤ : Opens Z.left) ≤ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem toSections_comp_map {U V : Opens Z.left} (i : U ⟶ V) :
    Z.toSections V ≫ Z.left.presheaf.map i.op = Z.toSections U := by
  rw [toSections, toSections, Category.assoc, ← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem toSections_comp_germ (U : Opens Z.left) (z : Z.left) (hz : z ∈ U) :
    Z.toSections U ≫ Z.left.presheaf.germ U z hz = Z.toStalk z := by
  rw [toSections, toStalk, Category.assoc, TopCat.Presheaf.germ_res]

variable {Z} {Y : LocallyCRingedSpace}

/-- The structure maps to the global sections are compatible with a morphism of locally
`ℂ`-ringed spaces. -/
@[reassoc (attr := simp)]
theorem toΓ_comp_c_app (f : Z ⟶ Y) :
    Y.toΓ ≫ f.left.c.app (op ⊤) = Z.toΓ := by
  have h : LocallyRingedSpace.Γ.map Z.hom.op =
      LocallyRingedSpace.Γ.map Y.hom.op ≫ LocallyRingedSpace.Γ.map f.left.op := by
    rw [← Functor.map_comp, ← op_comp, Over.w f]
  rw [toΓ_def, toΓ_def, h, ← LocallyRingedSpace.Γ_map_op f.left]
  rfl

/-- The sheaf map of a morphism of locally `ℂ`-ringed spaces is `ℂ`-linear. -/
@[reassoc (attr := simp)]
theorem toSections_comp_c_app (f : Z ⟶ Y) (U : Opens Y.left) :
    Y.toSections U ≫ f.left.c.app (op U) =
      Z.toSections ((Opens.map f.left.base).obj U) := by
  have := f.left.c.naturality (homOfLE (le_top : U ≤ ⊤)).op
  rw [toSections, toSections, Category.assoc]
  erw [this]
  rw [← Category.assoc, toΓ_comp_c_app]
  rfl

/-- The stalk maps of a morphism of locally `ℂ`-ringed spaces are `ℂ`-linear. -/
@[reassoc (attr := simp)]
theorem toStalk_comp_stalkMap (f : Z ⟶ Y) (z : Z.left) :
    Y.toStalk (f.left.base z) ≫ f.left.stalkMap z = Z.toStalk z := by
  rw [← Y.toSections_comp_germ ⊤ _ trivial, Category.assoc]
  erw [LocallyRingedSpace.stalkMap_germ]
  rw [toSections_comp_c_app_assoc]
  exact Z.toSections_comp_germ ((Opens.map f.left.base).obj ⊤) z trivial

/-- The structure map `ℂ ⟶ Γ(Z, 𝒪_Z)` is the adjoint transpose of the structure morphism
`Z ⟶ Spec ℂ`. -/
theorem toΓ_eq_homEquiv_symm (Z : LocallyCRingedSpace) :
    Z.toΓ = ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv Z.left _).symm Z.hom).unop := by
  rw [Adjunction.homEquiv_counit]
  simp [toΓ]
  rfl

/-- A morphism of locally ringed spaces `g` between locally `ℂ`-ringed spaces is a morphism over
`Spec ℂ` if and only if its sheaf map `g^#` is `ℂ`-linear on the sections over every open
subset. -/
@[weil "def_fk111_locally_c_ringed_space"]
theorem comp_hom_eq_hom_iff (g : Z.left ⟶ Y.left) :
    g ≫ Y.hom = Z.hom ↔ ∀ U : Opens Y.left,
      Y.toSections U ≫ g.c.app (op U) = Z.toSections ((Opens.map g.base).obj U) := by
  constructor
  · intro h U
    exact toSections_comp_c_app (Over.homMk g h : Z ⟶ Y) U
  · intro h
    apply (ΓSpec.locallyRingedSpaceAdjunction.homEquiv Z.left _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_naturality_left_symm, unop_comp, ← toΓ_eq_homEquiv_symm,
      ← toΓ_eq_homEquiv_symm]
    have h' := h ⊤
    rw [toSections_top] at h'
    exact h'.trans (toSections_top Z)

/-- A scheme over `Spec ℂ` regarded as a locally `ℂ`-ringed space. -/
def ofScheme : Over (Spec (CommRingCat.of ℂ)) ⥤ LocallyCRingedSpace :=
  Over.post Scheme.forgetToLocallyRingedSpace

/-- Morphisms of `ℂ`-schemes are exactly the morphisms of the associated locally `ℂ`-ringed
spaces. -/
@[weil "def_fk111_locally_c_ringed_space"]
def fullyFaithfulOfScheme : ofScheme.FullyFaithful :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.over _

instance : ofScheme.Full := fullyFaithfulOfScheme.full

instance : ofScheme.Faithful := fullyFaithfulOfScheme.faithful

@[simp]
theorem ofScheme_obj_left (X : Over (Spec (CommRingCat.of ℂ))) :
    (ofScheme.obj X).left = X.left.toLocallyRingedSpace :=
  rfl

@[simp]
theorem ofScheme_map_left {X X' : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ X') :
    (ofScheme.map f).left = f.left.toLRSHom :=
  rfl

variable (Z) in
/-- The open subspace `(W, 𝒪_Z|_W)` of a locally `ℂ`-ringed space on an open subset `W`. -/
@[weil "def_fk111_locally_c_ringed_space"]
def restrict (W : Opens Z.left) : LocallyCRingedSpace :=
  Over.mk (Z.left.ofRestrict W.isOpenEmbedding ≫ Z.hom)

variable (Z) in
/-- The inclusion of the open subspace on `W`. -/
def ofRestrict (W : Opens Z.left) : Z.restrict W ⟶ Z :=
  Over.homMk (Z.left.ofRestrict W.isOpenEmbedding)

@[simp]
theorem restrict_left (W : Opens Z.left) :
    (Z.restrict W).left = Z.left.restrict W.isOpenEmbedding :=
  rfl

@[simp]
theorem ofRestrict_left (W : Opens Z.left) :
    (Z.ofRestrict W).left = Z.left.ofRestrict W.isOpenEmbedding :=
  rfl

end LocallyCRingedSpace

end AlgebraicGeometry

