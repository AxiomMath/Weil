module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ShiftMorphismSheaves
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ShiftedSystem
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Weil.Attr

/-!
# The system of universal images of a projective system

Let `F = (F_n)_{n ∈ ℤ}` be a projective system in an abelian category `C`, that is a functor
`ℤᵒᵖ ⥤ C`, and for `t ≥ 0` let `ε_{t,n} : F_{n+t} ⟶ F_n` be its map along `n ≤ n + t`. The
*universal image* of `F` in degree `n` is the subobject
`F̄_n = ⋂_{t ≥ 0} im(ε_{t,n})` of `F_n`. The transition map `F_{n+1} ⟶ F_n` carries
`im(F_{n+1+t} ⟶ F_{n+1})` into `im(F_{n+1+t} ⟶ F_n) ⊆ im(F_{n+t} ⟶ F_n)`, hence `F̄_{n+1}` into
`F̄_n`, and the subobjects `F̄_n` with the restricted transition maps form a subsystem `F̄` of
`F`, the *system of universal images*.

The construction applies to the two cases of the source: projective systems of `l`-power
torsion `Λ`-modules (`CategoryTheory.ProjectiveSystem`) and the category `P_S` of projective
systems of `l`-torsion sheaves on the small étale site of a scheme `S`
(`AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem`). In both cases `F̄` is again an object
of the category, since a subobject of an `l`-torsion object is `l`-torsion and a subobject of
zero is zero.

## Main definitions

* `CategoryTheory.Functor.universalImage F n`: the subobject `⋂_{t ≥ 0} im(ε_{t,n})` of `F_n`.
* `CategoryTheory.Functor.universalImageSystem F`: the system `n ↦ F̄_n` with the restricted
  transition maps, and `CategoryTheory.Functor.universalImageι F : F̄ ⟶ F`, its inclusion.
* `CategoryTheory.ProjectiveSystem.universalImageSystem`: the system of universal images of a
  projective system of `l`-power torsion modules.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.universalImageSystem`: the system of
  universal images of a projective system of `l`-torsion sheaves.

## Main results

* `CategoryTheory.Functor.factors_universalImage_iff`,
  `CategoryTheory.Functor.le_universalImage_iff`: a morphism factors through `F̄_n` (a
  subobject lies in `F̄_n`) if and only if it does through every `im(ε_{t,n})`.
* `CategoryTheory.Functor.isGLB_universalImage`: `F̄_n` is the greatest lower bound of the
  images `im(ε_{t,n})`.
* `CategoryTheory.Functor.universalImageι_app_arrow`: the inclusion `F̄ ⟶ F` is the inclusion
  of the subobjects `F̄_n ⊆ F_n`; it is a monomorphism.
* `CategoryTheory.ProjectiveSystem.subobjectModule_universalImage`: for modules, `F̄_n` is the
  submodule `⨅ t, range(ε_{t,n})` of `F_n`.

## Implementation notes

The intersection `⋂_t im(ε_{t,n})` is constructed as the kernel of
`F_n ⟶ ∏_t coker(ε_{t,n})`; in an abelian category the image of a morphism is the kernel of its
cokernel, so this kernel is the greatest lower bound of the images
(`CategoryTheory.Functor.isGLB_universalImage`). This needs only countable products, while the
complete lattice structure on subobjects needs limits of the size of the category, which the
category of sheaves on the (large) small étale site does not have. For sheaves of abelian groups
limits are computed sectionwise, so this is the sectionwise intersection of the source.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u v v₁ u₁

namespace CategoryTheory

section Image

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- In an abelian category a morphism `g` factors through the image of `f` if and only if
`g` composed with the cokernel of `f` vanishes. -/
theorem imageSubobject_factors_iff_comp_cokernel_π {X Y W : C} (f : X ⟶ Y) (g : W ⟶ Y) :
    (imageSubobject f).Factors g ↔ g ≫ cokernel.π f = 0 := by
  have h := (ShortComplex.exact_iff_image_eq_kernel _).mp (ShortComplex.exact_cokernel f)
  simp only at h
  rw [h, kernelSubobject_factors_iff]

end Image

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProductsOfShape ℕ C] (F : ℤᵒᵖ ⥤ C)

/-- The map `ε_{t,n} : F_{n+t} ⟶ F_n` of a projective system `F : ℤᵒᵖ ⥤ C` along
`n ≤ n + t`. -/
abbrev mapAddNat (n : ℤ) (t : ℕ) : F.obj (op (n + t)) ⟶ F.obj (op n) :=
  F.map (homOfLE (by omega : n ≤ n + t)).op

/-- **The universal image** `F̄_n = ⋂_{t ≥ 0} im(ε_{t,n} : F_{n+t} ⟶ F_n)` of a projective
system `F : ℤᵒᵖ ⥤ C` in degree `n`, as a subobject of `F_n`. It is the greatest lower bound of
the images of the maps `ε_{t,n}` (`Functor.isGLB_universalImage`). -/
@[weil "def_fk112_universal_image_system"]
def universalImage (n : ℤ) : Subobject (F.obj (op n)) :=
  kernelSubobject (Pi.lift fun t : ℕ ↦ cokernel.π (F.mapAddNat n t))

/-- A morphism factors through the universal image `F̄_n` if and only if it factors through
the image of every `ε_{t,n}`. -/
theorem factors_universalImage_iff {n : ℤ} {W : C} (g : W ⟶ F.obj (op n)) :
    (F.universalImage n).Factors g ↔ ∀ t : ℕ, (imageSubobject (F.mapAddNat n t)).Factors g := by
  simp only [universalImage, kernelSubobject_factors_iff,
    imageSubobject_factors_iff_comp_cokernel_π]
  constructor
  · intro h t
    simpa using h =≫ Pi.π _ t
  · intro h
    exact Pi.hom_ext _ _ fun t ↦ by simpa using h t

/-- The universal image `F̄_n` lies in the image of every `ε_{t,n}`. -/
theorem universalImage_le_imageSubobject (n : ℤ) (t : ℕ) :
    F.universalImage n ≤ imageSubobject (F.mapAddNat n t) :=
  Subobject.le_of_factors ((F.factors_universalImage_iff _).mp (Subobject.factors_self _) t)

/-- A subobject lies in the universal image `F̄_n` if and only if it lies in the image of
every `ε_{t,n}`. -/
theorem le_universalImage_iff {n : ℤ} (P : Subobject (F.obj (op n))) :
    P ≤ F.universalImage n ↔ ∀ t : ℕ, P ≤ imageSubobject (F.mapAddNat n t) :=
  ⟨fun h t ↦ h.trans (F.universalImage_le_imageSubobject n t), fun h ↦
    Subobject.le_of_factors ((F.factors_universalImage_iff P.arrow).mpr fun t ↦
      Subobject.factors_of_le _ (h t) (Subobject.factors_self P))⟩

/-- The universal image `F̄_n` is the greatest lower bound of the images of the maps
`ε_{t,n}`, `t ≥ 0`. -/
theorem isGLB_universalImage (n : ℤ) :
    IsGLB (Set.range fun t : ℕ ↦ imageSubobject (F.mapAddNat n t)) (F.universalImage n) := by
  refine ⟨?_, fun P hP ↦ (F.le_universalImage_iff P).mpr fun t ↦ hP ⟨t, rfl⟩⟩
  rintro _ ⟨t, rfl⟩
  exact F.universalImage_le_imageSubobject n t

/-- For `m ≤ n`, the map `F_n ⟶ F_m` carries the universal image `F̄_n` into `F̄_m`. -/
theorem factors_universalImage_arrow_comp_map {m n : ℤ} (h : m ≤ n) :
    (F.universalImage m).Factors ((F.universalImage n).arrow ≫ F.map (homOfLE h).op) := by
  rw [factors_universalImage_iff]
  intro t
  rw [imageSubobject_factors_iff_comp_cokernel_π]
  have hle := F.universalImage_le_imageSubobject n t
  have e : F.mapAddNat n t ≫ F.map (homOfLE h).op =
      F.map (homOfLE (by omega : m + t ≤ n + t)).op ≫ F.mapAddNat m t := by
    simp only [← F.map_comp]
    rfl
  have h0 : (imageSubobject (F.mapAddNat n t)).arrow ≫ F.map (homOfLE h).op ≫
      cokernel.π (F.mapAddNat m t) = 0 := by
    rw [← cancel_epi (factorThruImageSubobject (F.mapAddNat n t)), comp_zero,
      imageSubobject_arrow_comp_assoc, reassoc_of% e, cokernel.condition, comp_zero]
  rw [← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc, h0, comp_zero]

/-- The transition map `F̄_n ⟶ F̄_m` of the system of universal images, for `m ≤ n`: the
restriction of `F_n ⟶ F_m`. -/
def universalImageMap {m n : ℤ} (h : m ≤ n) :
    (F.universalImage n : C) ⟶ (F.universalImage m : C) :=
  (F.universalImage m).factorThru _ (F.factors_universalImage_arrow_comp_map h)

@[reassoc (attr := simp)]
theorem universalImageMap_arrow {m n : ℤ} (h : m ≤ n) :
    F.universalImageMap h ≫ (F.universalImage m).arrow =
      (F.universalImage n).arrow ≫ F.map (homOfLE h).op :=
  Subobject.factorThru_arrow _ _ _

/-- **The system of universal images** `F̄ = (F̄_n)_{n ∈ ℤ}` of a projective system
`F : ℤᵒᵖ ⥤ C`: the subsystem with `F̄_n = ⋂_{t ≥ 0} im(ε_{t,n})`, whose transition maps are the
restrictions of those of `F` (`Functor.universalImageMap_arrow`). -/
@[weil "def_fk112_universal_image_system"]
def universalImageSystem : ℤᵒᵖ ⥤ C where
  obj n := (F.universalImage n.unop : C)
  map φ := F.universalImageMap (leOfHom φ.unop)
  map_id n := by
    rw [← cancel_mono (F.universalImage n.unop).arrow, universalImageMap_arrow]
    erw [Category.id_comp]
    rw [show (homOfLE (leOfHom (𝟙 n).unop)).op = 𝟙 n from rfl, F.map_id, Category.comp_id]
  map_comp {a b c} φ ψ := by
    rw [← cancel_mono (F.universalImage c.unop).arrow, Category.assoc, universalImageMap_arrow,
      universalImageMap_arrow, universalImageMap_arrow_assoc, ← F.map_comp]
    rfl

@[simp]
theorem universalImageSystem_obj (n : ℤ) :
    F.universalImageSystem.obj (op n) = (F.universalImage n : C) :=
  rfl

/-- The inclusion `F̄ ⟶ F` of the system of universal images. -/
@[weil "def_fk112_universal_image_system"]
def universalImageι : F.universalImageSystem ⟶ F where
  app n := (F.universalImage n.unop).arrow
  naturality _ _ φ := F.universalImageMap_arrow (leOfHom φ.unop)

@[simp]
theorem universalImageι_app_arrow (n : ℤ) :
    F.universalImageι.app (op n) = (F.universalImage n).arrow :=
  rfl

instance (n : ℤᵒᵖ) : Mono (F.universalImageι.app n) :=
  Subobject.arrow_mono (F.universalImage n.unop)

instance : Mono F.universalImageι := NatTrans.mono_of_mono_app _

end Functor

end CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R]

theorem subobjectModule_apply (M : ModuleCat.{v} R) (P : Subobject M) :
    subobjectModule M P = LinearMap.range P.arrow.hom :=
  rfl

/-- The submodule corresponding to the image of a linear map is its range. -/
theorem subobjectModule_imageSubobject {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    subobjectModule N (imageSubobject f) = LinearMap.range f.hom := by
  rw [subobjectModule_apply]
  conv_rhs => rw [← imageSubobject_arrow_comp f, hom_comp]
  rw [LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end ModuleCat

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The system of universal images of a projective system of `l`-power torsion modules is
again such a system: a submodule of an `l`-power torsion module is `l`-power torsion, and a
submodule of zero is zero. -/
theorem isTorsionBounded_universalImageSystem (F : ProjectiveSystem.{v} Λ l) :
    isTorsionBounded.{v} Λ l F.obj.universalImageSystem := by
  have hinj : ∀ n : ℤ, Function.Injective (F.obj.universalImageι.app (op n)) := fun n ↦
    (ModuleCat.mono_iff_injective _).mp inferInstance
  refine ⟨fun n x ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := F.isTorsion' n (x := F.obj.universalImageι.app (op n) x)
    refine ⟨a, hinj n ?_⟩
    rw [Submonoid.smul_def] at ha ⊢
    rw [map_smul, ha, map_zero]
  · obtain ⟨n₀, hn₀⟩ := F.exists_isZero
    exact ⟨n₀, fun n hn ↦ IsZero.of_mono (F.obj.universalImageι.app (op n)) (hn₀ n hn)⟩

/-- **The system of universal images** `F̄` of a projective system `F` of `l`-power torsion
`Λ`-modules: `F̄_n = ⋂_{t ≥ 0} im(F_{n+t} ⟶ F_n)`, with the restricted transition maps. -/
@[weil "def_fk112_universal_image_system"]
def universalImageSystem (F : ProjectiveSystem.{v} Λ l) : ProjectiveSystem.{v} Λ l :=
  ⟨F.obj.universalImageSystem, F.isTorsionBounded_universalImageSystem⟩

/-- The inclusion `F̄ ⟶ F` of the system of universal images. -/
@[weil "def_fk112_universal_image_system"]
def universalImageι (F : ProjectiveSystem.{v} Λ l) : F.universalImageSystem ⟶ F :=
  ObjectProperty.homMk F.obj.universalImageι

theorem universalImageSystem_term (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    F.universalImageSystem.term n = (F.obj.universalImage n : ModuleCat.{v} Λ) :=
  rfl

@[simp]
theorem app_universalImageι (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app F.universalImageι n = (F.obj.universalImage n).arrow :=
  rfl

/-- The submodule of `F_n` corresponding to the universal image `F̄_n` is the intersection of
the ranges of the maps `ε_{t,n} : F_{n+t} ⟶ F_n`, `t ≥ 0`. -/
theorem subobjectModule_universalImage (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    ModuleCat.subobjectModule _ (F.obj.universalImage n) =
      ⨅ t : ℕ, LinearMap.range (F.obj.mapAddNat n t).hom := by
  set e := ModuleCat.subobjectModule (F.term n)
  have he : ∀ t : ℕ, e (imageSubobject (F.obj.mapAddNat n t)) =
      LinearMap.range (F.obj.mapAddNat n t).hom := fun t ↦
    ModuleCat.subobjectModule_imageSubobject _
  refine le_antisymm (le_iInf fun t ↦ ?_) ?_
  · rw [← he t]
    exact e.monotone (F.obj.universalImage_le_imageSubobject n t)
  · rw [← e.symm_apply_le, Functor.le_universalImage_iff]
    intro t
    rw [e.symm_apply_le, he t]
    exact iInf_le _ t

/-- An element of `F_n` lies in the universal image `F̄_n` if and only if it lies in the
range of every map `ε_{t,n} : F_{n+t} ⟶ F_n`. -/
theorem mem_range_universalImage_arrow_iff (F : ProjectiveSystem.{v} Λ l) {n : ℤ}
    (x : F.term n) :
    x ∈ LinearMap.range (F.obj.universalImage n).arrow.hom ↔
      ∀ t : ℕ, x ∈ LinearMap.range (F.obj.mapAddNat n t).hom := by
  rw [← Submodule.mem_iInf, ← subobjectModule_universalImage]
  rfl

instance (F : ProjectiveSystem.{v} Λ l) : Mono F.universalImageι :=
  (isTorsionBounded.{v} Λ l).ι.mono_of_mono_map (by
    change Mono F.obj.universalImageι
    infer_instance)

end ProjectiveSystem

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

/-- The system of universal images of a projective system of `l`-torsion sheaves is again such
a system: a subsheaf of an `l`-torsion sheaf is `l`-torsion, and a subsheaf of zero is zero. -/
theorem isLTorsionProjectiveSystem_universalImageSystem
    (F : LTorsionProjectiveSystem.{u} B S hS l) :
    IsLTorsionProjectiveSystem.{u} B S hS l F.obj.universalImageSystem := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · exact (IsLTorsionSheaf.{u} B S hS l).prop_of_mono (F.obj.universalImageι.app (op n))
      (F.isLTorsionSheaf_obj n)
  · obtain ⟨n₀, hn₀⟩ := F.exists_isZero_obj
    exact ⟨n₀, fun n hn ↦ IsZero.of_mono (F.obj.universalImageι.app (op n)) (hn₀ n hn)⟩

/-- **The system of universal images** `F̄` of a projective system `F ∈ P_S` of `l`-torsion
sheaves: `F̄_n = ⋂_{t ≥ 0} im(F_{n+t} ⟶ F_n)` (intersection of subsheaves), with the restricted
transition maps. -/
@[weil "def_fk112_universal_image_system"]
def universalImageSystem (F : LTorsionProjectiveSystem.{u} B S hS l) :
    LTorsionProjectiveSystem.{u} B S hS l :=
  ⟨F.obj.universalImageSystem, F.isLTorsionProjectiveSystem_universalImageSystem⟩

/-- The inclusion `F̄ ⟶ F` of the system of universal images. -/
@[weil "def_fk112_universal_image_system"]
def universalImageι (F : LTorsionProjectiveSystem.{u} B S hS l) : F.universalImageSystem ⟶ F :=
  ObjectProperty.homMk F.obj.universalImageι

@[simp]
theorem universalImageι_hom_app (F : LTorsionProjectiveSystem.{u} B S hS l) (n : ℤ) :
    F.universalImageι.hom.app (op n) = (F.obj.universalImage n).arrow :=
  rfl

instance (F : LTorsionProjectiveSystem.{u} B S hS l) : Mono F.universalImageι :=
  (IsLTorsionProjectiveSystem.{u} B S hS l).ι.mono_of_mono_map (by
    change Mono F.obj.universalImageι
    infer_instance)

end AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem
