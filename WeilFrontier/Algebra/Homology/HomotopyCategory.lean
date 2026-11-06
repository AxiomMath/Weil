module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Weil.Attr

/-!
# The homotopy category is additive

For a preadditive category `A` and a complex shape `c` (the case of `K(A)` is
`c = ComplexShape.up ℤ`), the morphisms `X ⟶ Y` of complexes that are homotopic to zero
form an additive subgroup `HomotopyCategory.nullHomotopic X Y`, stable under composition
on either side with arbitrary morphisms of complexes. Two morphisms have the same class in
the homotopy category exactly when their difference lies in this subgroup. The quotient
functor `HomotopyCategory.quotient A c` is additive and the identity on objects; the image
of the zero complex is a zero object, and the image of the degreewise biproduct of two
complexes is a biproduct in the homotopy category. In particular the homotopy category of
an additive category is additive.

## Main definitions

* `HomotopyCategory.nullHomotopic X Y`: the subgroup of morphisms homotopic to zero.

## Main results

* `HomotopyCategory.mem_nullHomotopic_iff`, `HomotopyCategory.comp_mem_nullHomotopic_left`,
  `HomotopyCategory.comp_mem_nullHomotopic_right`,
  `HomotopyCategory.quotient_map_eq_iff_sub_mem_nullHomotopic`.
* `HomotopyCategory.quotient_additive`: the quotient functor is additive.
* `HomotopyCategory.isZero_quotient_obj_zero`: the zero complex is a zero object.
* `HomotopyCategory.isBilimit_quotient_mapBinaryBicone`: the degreewise direct sum is a
  biproduct in the homotopy category; `HomotopyCategory.hasBinaryBiproducts`.

## Implementation notes

The preadditive structure on `HomotopyCategory A c` is Mathlib's
`HomotopyCategory.instPreadditive`, induced from the quotient by the homotopy relation; the
objects of the homotopy category are `HomotopyCategory.quotient A c` applied to complexes,
with `(HomotopyCategory.quotient A c).obj X).as = X` (`HomotopyCategory.quotient_obj_as`).
The statements hold for an arbitrary complex shape.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

namespace HomotopyCategory

variable {ι : Type*} {A : Type*} [Category A] [Preadditive A] {c : ComplexShape ι}

/-- The subgroup of morphisms of complexes `X ⟶ Y` that are homotopic to zero: the kernel of
the quotient map to the homotopy category. -/
@[weil "lem_fka2_homotopy_category_additive"]
def nullHomotopic (X Y : HomologicalComplex A c) : AddSubgroup (X ⟶ Y) :=
  ((quotient A c).mapAddHom (X := X) (Y := Y)).ker

@[weil "lem_fka2_homotopy_category_additive"]
theorem mem_nullHomotopic_iff {X Y : HomologicalComplex A c} (f : X ⟶ Y) :
    f ∈ nullHomotopic X Y ↔ Nonempty (Homotopy f 0) := by
  rw [nullHomotopic, AddMonoidHom.mem_ker, Functor.mapAddHom_apply,
    quotient_map_eq_zero_iff]

theorem sub_mem_nullHomotopic_iff {X Y : HomologicalComplex A c} (f g : X ⟶ Y) :
    f - g ∈ nullHomotopic X Y ↔ Nonempty (Homotopy f g) := by
  rw [mem_nullHomotopic_iff]
  exact ⟨fun ⟨h⟩ => ⟨Homotopy.equivSubZero.symm h⟩, fun ⟨h⟩ => ⟨Homotopy.equivSubZero h⟩⟩

@[weil "lem_fka2_homotopy_category_additive"]
theorem quotient_map_eq_iff_sub_mem_nullHomotopic {X Y : HomologicalComplex A c}
    (f g : X ⟶ Y) : (quotient A c).map f = (quotient A c).map g ↔ f - g ∈ nullHomotopic X Y := by
  rw [sub_mem_nullHomotopic_iff]
  exact ⟨fun h => ⟨homotopyOfEq f g h⟩, fun ⟨h⟩ => eq_of_homotopy f g h⟩

@[weil "lem_fka2_homotopy_category_additive"]
theorem comp_mem_nullHomotopic_left {W X Y : HomologicalComplex A c} (a : W ⟶ X)
    {f : X ⟶ Y} (hf : f ∈ nullHomotopic X Y) : a ≫ f ∈ nullHomotopic W Y := by
  obtain ⟨h⟩ := (mem_nullHomotopic_iff f).1 hf
  exact (mem_nullHomotopic_iff _).2 ⟨(h.compLeft a).trans (Homotopy.ofEq (by simp))⟩

@[weil "lem_fka2_homotopy_category_additive"]
theorem comp_mem_nullHomotopic_right {X Y Z : HomologicalComplex A c} {f : X ⟶ Y}
    (hf : f ∈ nullHomotopic X Y) (b : Y ⟶ Z) : f ≫ b ∈ nullHomotopic X Z := by
  obtain ⟨h⟩ := (mem_nullHomotopic_iff f).1 hf
  exact (mem_nullHomotopic_iff _).2 ⟨(h.compRight b).trans (Homotopy.ofEq (by simp))⟩

/-- The quotient functor `C(A) ⥤ K(A)` is additive. -/
@[weil "lem_fka2_homotopy_category_additive"]
theorem quotient_additive : (quotient A c).Additive := inferInstance

/-- The zero complex is a zero object of the homotopy category. -/
@[weil "lem_fka2_homotopy_category_additive"]
theorem isZero_quotient_obj_zero [HasZeroObject A] : IsZero ((quotient A c).obj 0) :=
  (quotient A c).map_isZero (isZero_zero _)

/-- The image in the homotopy category of the degreewise biproduct bicone of two complexes is a
biproduct bicone. -/
@[weil "lem_fka2_homotopy_category_additive"]
theorem isBilimit_quotient_mapBinaryBicone (X Y : HomologicalComplex A c)
    [∀ i, HasBinaryBiproduct (X.X i) (Y.X i)] :
    Nonempty ((quotient A c).mapBinaryBicone (BinaryBiproduct.bicone X Y)).IsBilimit :=
  ⟨isBinaryBilimitOfTotal _ (by
    have h := ((quotient A c).congr_map (biprod.total (X := X) (Y := Y))).trans
      ((quotient A c).map_id _)
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp] at h
    exact h)⟩

/-- The homotopy category of complexes in a category with binary biproducts has binary
biproducts. -/
@[weil "lem_fka2_homotopy_category_additive"]
instance hasBinaryBiproducts [HasBinaryBiproducts A] :
    HasBinaryBiproducts (HomotopyCategory A c) where
  has_binary_biproduct K L := by
    obtain ⟨h⟩ := isBilimit_quotient_mapBinaryBicone K.as L.as
    exact HasBinaryBiproduct.mk ⟨_, h⟩

end HomotopyCategory
