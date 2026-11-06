module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.IsSheafFor
public import Weil.Defs.CategoryTheory.Sites.Plus

/-!
# The unit of the plus construction on the étale category

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)` and `B` an object of
`Et(A)`. The one-member family `(id_B)` is a covering of `B`, and the sections of `F` over it are
`F((id_B)) = F(B)`: the compatibility condition is vacuous, since `u ∘ id_B = v ∘ id_B` forces
`u = v`. The map `ι_{F,B} : F(B) → F̃(B)` into the plus construction is `s ↦ [(id_B), s]`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.Covering.self B`: the covering `(id_B)` of `B`.
- `AlgebraicGeometry.EtaleCategory.coveringSectionsSelfEquiv F B`: the identification
  `F((id_B)) ≃ F(B)` for a presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.coveringSectionsAddSubgroupSelfEquiv F B`: the same
  identification, as an isomorphism of abelian groups, for a presheaf of abelian groups.
- `AlgebraicGeometry.EtaleCategory.toPlusConstruction F B`: the map `ι_{F,B} : F(B) → F̃(B)`,
  `s ↦ [(id_B), s]`, for a presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.toAddPlusConstruction F B`: the homomorphism
  `ι_{F,B} : F(B) → F̃(B)` for a presheaf of abelian groups.

## Main results

- `AlgebraicGeometry.EtaleCategory.toPlusConstruction_apply`,
  `AlgebraicGeometry.EtaleCategory.toAddPlusConstruction_apply`: `ι_{F,B}(s) = [(id_B), s]`.

## Implementation notes

The map `ι_{F,B}` is the analogue, for the colimit over the coverings of `B`, of the component
at `B` of Mathlib's `GrothendieckTopology.toPlus`, which sends a section to its class over the
maximal covering sieve.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

namespace Covering

/-- The one-member covering `(id_B)` of an object `B` of `Et(A)`. -/
@[weil "def_fk101_plus_unit"]
def self (B : EtaleCategory A) : Covering.{w} B where
  ι := PUnit
  obj _ := B
  map _ := 𝟙 B
  isCovering :=
    { finite := inferInstance
      exists_comap_eq p := ⟨PUnit.unit, p, by ext; rfl⟩ }

@[simp]
lemma self_obj (B : EtaleCategory A) (i : (self.{w} B).ι) : (self.{w} B).obj i = B := rfl

@[simp]
lemma self_map (B : EtaleCategory A) (i : (self.{w} B).ι) : (self.{w} B).map i = 𝟙 B := rfl

end Covering

open Covering

variable (F : EtaleCategory A ⥤ Type v) (B : EtaleCategory A)

/-- Every constant family `(s)` is a section of `F` over the covering `(id_B)`: the condition
`F(u)(s) = F(v)(s)` for `u ∘ id_B = v ∘ id_B` holds since then `u = v`. -/
lemma const_mem_coveringSections_self (s : F.obj B) :
    (fun _ ↦ s : ∀ i, F.obj ((self.{w} B).obj i)) ∈ coveringSections F (self.{w} B).map := by
  refine (mem_coveringSections_iff F (self.{w} B).map _).2 fun i j D u v huv ↦ ?_
  obtain ⟨⟩ := i
  obtain ⟨⟩ := j
  have huv' : u = v := (Category.id_comp u).symm.trans (huv.trans (Category.id_comp v))
  rw [huv']

/-- The sections of `F` over the covering `(id_B)` are `F((id_B)) = F(B)`. -/
@[weil "def_fk101_plus_unit"]
def coveringSectionsSelfEquiv : coveringSections F (self.{w} B).map ≃ F.obj B where
  toFun s := s.1 PUnit.unit
  invFun s := ⟨fun _ ↦ s, const_mem_coveringSections_self F B s⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma coveringSectionsSelfEquiv_apply (s : coveringSections F (self.{w} B).map) :
    coveringSectionsSelfEquiv F B s = s.1 PUnit.unit :=
  rfl

@[simp]
lemma coveringSectionsSelfEquiv_symm_apply_coe (s : F.obj B) (i : (self.{w} B).ι) :
    ((coveringSectionsSelfEquiv.{w} F B).symm s).1 i = s :=
  rfl

/-- The map `ι_{F,B} : F(B) → F̃(B)`, `s ↦ [(id_B), s]`, from the sections of a presheaf of sets
`F` over `B` to its plus construction at `B`. -/
@[weil "def_fk101_plus_unit"]
def toPlusConstruction : F.obj B → plusConstruction.{w} F B :=
  fun s ↦ plusConstruction.mk (self.{w} B) ((coveringSectionsSelfEquiv.{w} F B).symm s)

lemma toPlusConstruction_apply (s : F.obj B) :
    toPlusConstruction.{w} F B s =
      plusConstruction.mk (self.{w} B) ((coveringSectionsSelfEquiv.{w} F B).symm s) :=
  rfl

section AddCommGrp

variable (F : EtaleCategory A ⥤ AddCommGrpCat.{v}) (B : EtaleCategory A)

/-- The sections of a presheaf of abelian groups `F` over the covering `(id_B)` are
`F((id_B)) = F(B)`, as abelian groups. -/
@[weil "def_fk101_plus_unit"]
def coveringSectionsAddSubgroupSelfEquiv :
    coveringSectionsAddSubgroup F (self.{w} B).map ≃+ F.obj B where
  toFun s := s.1 PUnit.unit
  invFun s := ⟨fun _ ↦ s, const_mem_coveringSections_self (F ⋙ forget AddCommGrpCat) B s⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
lemma coveringSectionsAddSubgroupSelfEquiv_apply
    (s : coveringSectionsAddSubgroup F (self.{w} B).map) :
    coveringSectionsAddSubgroupSelfEquiv F B s = s.1 PUnit.unit :=
  rfl

@[simp]
lemma coveringSectionsAddSubgroupSelfEquiv_symm_apply_coe (s : F.obj B) (i : (self.{w} B).ι) :
    ((coveringSectionsAddSubgroupSelfEquiv.{w} F B).symm s).1 i = s :=
  rfl

/-- The homomorphism `ι_{F,B} : F(B) → F̃(B)`, `s ↦ [(id_B), s]`, from the sections of a presheaf
of abelian groups `F` over `B` to its plus construction at `B`. -/
@[weil "def_fk101_plus_unit"]
def toAddPlusConstruction : F.obj B →+ addPlusConstruction.{w} F B :=
  (addPlusConstruction.mk (self.{w} B)).comp
    (coveringSectionsAddSubgroupSelfEquiv.{w} F B).symm.toAddMonoidHom

lemma toAddPlusConstruction_apply (s : F.obj B) :
    toAddPlusConstruction.{w} F B s =
      addPlusConstruction.mk (self.{w} B) ((coveringSectionsAddSubgroupSelfEquiv.{w} F B).symm s) :=
  rfl

end AddCommGrp

end EtaleCategory

end AlgebraicGeometry
