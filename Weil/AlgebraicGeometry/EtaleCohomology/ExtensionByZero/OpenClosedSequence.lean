module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# Restricting an extension by zero to the open

Let `j : U ⟶ X` be an étale monomorphism of schemes (for instance an open immersion) and `F` an
abelian sheaf on the small étale site of `U`. The unit `η_F : F ⟶ (j_! F)|_U` of the adjunction
`j_! ⊣ j^{-1}` between extension by zero and restriction is an isomorphism; consequently the
inverse image of `j_! F` along `j` is isomorphic to `F`, naturally in `F`. The same holds for
sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.isIso_extensionByZeroAdj_unit_app`: `η_F : F ⟶ (j_! F)|_U` is an
  isomorphism.
* `AlgebraicGeometry.etaleAbelianExtensionByZeroInverseImageIso`: `j^* (j_! F) ≅ F`, naturally
  in `F`.
* `AlgebraicGeometry.isIso_etaleModuleExtensionByZeroAdj_unit_app`,
  `AlgebraicGeometry.etaleModuleExtensionByZeroInverseImageIsoOfMono`: the same for sheaves of
  `Λ`-modules.

## Implementation notes

The unit is invertible because, in the adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`, the counit of
`j^{-1} ⊣ j_*` is invertible: `j_*` is the right Kan extension along composition with `j`, a
fully faithful functor of small étale sites since `j` is a monomorphism. This replaces the
stalkwise computation through the direct-sum presheaf. The inverse image along base change is
identified with restriction since both are left adjoint to the direct image.

All statements are on the small étale site `X.Etale` with the topology `X.smallEtaleTopology`,
where extension by zero is defined.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 84.
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe r v u

namespace AlgebraicGeometry

section Abelian

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [Mono j]

/-- For an étale monomorphism `j : U ⟶ X` and an abelian sheaf `F` on `U_ét`, the unit
`η_F : F ⟶ (j_! F)|_U` of extension by zero is an isomorphism. -/
@[weil "lem_fk108_open_extension_by_zero_restrict_open"]
theorem isIso_extensionByZeroAdj_unit_app
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((extensionByZeroAdj.{u, v} j).unit.app F) :=
  inferInstance

/-- For an étale monomorphism `j : U ⟶ X`, the inverse image of an extension by zero is the
original sheaf: `j^* (j_! F) ≅ F`, naturally in the abelian sheaf `F`. -/
@[weil "lem_fk108_open_extension_by_zero_restrict_open"]
def etaleAbelianExtensionByZeroInverseImageIso :
    extensionByZero.{u, v} j ⋙ etaleAbelianInverseImage.{u, v} j ≅
      𝟭 (Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  Functor.isoWhiskerLeft _ (etaleAbelianInverseImageRestrictionIso.{u, v} j) ≪≫
    (asIso (extensionByZeroAdj.{u, v} j).unit).symm

/-- The isomorphism `j^* (j_! F) ≅ F` is the inverse of the unit `η_F`, transported along the
identification of the inverse image with restriction. -/
theorem etaleAbelianExtensionByZeroInverseImageIso_inv_app
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianExtensionByZeroInverseImageIso j).inv.app F =
      (extensionByZeroAdj.{u, v} j).unit.app F ≫
        (etaleAbelianInverseImageRestrictionIso.{u, v} j).inv.app
          ((extensionByZero.{u, v} j).obj F) :=
  rfl

end Abelian

section Modules

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [Mono j]

/-- For an étale monomorphism `j : U ⟶ X` and a sheaf `F` of `Λ`-modules on `U_ét`, the unit
`η_F : F ⟶ (j_! F)|_U` of extension by zero is an isomorphism. -/
theorem isIso_etaleModuleExtensionByZeroAdj_unit_app (F : EtaleModules.{u, r} Λ U) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F) :=
  inferInstance

/-- For an étale monomorphism `j : U ⟶ X`, `j^* (j_! F) ≅ F`, naturally in the sheaf `F` of
`Λ`-modules. -/
def etaleModuleExtensionByZeroInverseImageIsoOfMono :
    etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleInverseImage.{u, r} Λ j ≅
      𝟭 (EtaleModules.{u, r} Λ U) :=
  Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, r} Λ j) ≪≫
    (asIso (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit).symm

end Modules

end AlgebraicGeometry

end

/-! ### The extension by zero restricted to the closed complement -/

/-!
# The extension by zero restricted to the closed complement

Let `X` be a scheme, `j : U ⟶ X` an étale morphism and `i : Z ⟶ X` a morphism whose image is the
complement of the image of `j` (for instance an open immersion and the inclusion of a closed
complement). For every abelian sheaf `F` on the small étale site of `U`, the inverse image along
`i` of the extension by zero `j_! F` vanishes:
```
  i^* (j_! F) = 0.
```

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_smallEtaleInverseImage_extensionByZero`: `i^* (j_! F) = 0`
  on the small étale sites `SmallEtale` of a big étale site.

## Implementation notes

Extension by zero is `Stacks.EtaleCohomology.extensionByZero`, on Mathlib's small étale site; on
the small étale sites of a big étale site it is that functor transported along the equivalences of
sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv`. The vanishing on Mathlib's site is the
Stacks Project's `Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_extensionByZero`, proved
by adjunction (`i^*` is left adjoint to `i_*`, `j_!` to `j^{-1}`, and `j^{-1} i_*` vanishes). It is
transported to the small étale sites of `B` through the compatibility of inverse images with the
equivalences of sheaf categories, `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`.
The stalkwise argument of [FK] is not needed.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.SmallEtale

/-- The small étale site of a scheme of `B` is essentially small in every universe above `u`. -/
lemma essentiallySmall_max (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EssentiallySmall.{max (u + 1) v} (SmallEtale B S hS) := by
  have h := (essentiallySmall_iff.{u} (SmallEtale B S hS)).1 inferInstance
  have := h.1
  exact (essentiallySmall_iff _).2 ⟨small_lift.{_, u, max (u + 1) v} _, inferInstance⟩

/-- Abelian sheafification on the small étale site of a scheme of `B`, with coefficients
`AddCommGrpCat.{max (u + 1) v}`. -/
local instance hasSheafify_max (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v} :=
  haveI := essentiallySmall_max.{v} B S hS
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _

variable (B : BigEtaleSite.{u}) {Z U X : B.Scheme} (i : Z ⟶ X) (j : U ⟶ X)
  [Etale (B.inclusion.map j)]

/-- **The extension by zero vanishes on the complement** (FK I.8). Let `j : U ⟶ X` be étale and
`i : Z ⟶ X` a morphism whose image is the complement of the image of `j`. For every abelian sheaf
`F` on the small étale site of `U`, the inverse image `i^* (j_! F)` of its extension by zero is
zero. Here `j_! F` is the extension by zero on Mathlib's small étale site, transported along the
equivalences `sheafEquiv` of sheaf categories. -/
@[weil "lem_fk108_open_extension_by_zero_restrict_complement"]
theorem isZero_smallEtaleInverseImage_extensionByZero
    (hij : Set.range (B.inclusion.map j).base = (Set.range (B.inclusion.map i).base)ᶜ)
    (F : Sheaf (SmallEtale.topology B U.obj U.property) AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((smallEtaleInverseImage B i AddCommGrpCat.{max (u + 1) v}).obj
      ((sheafEquiv B X.obj X.property AddCommGrpCat.{max (u + 1) v}).inverse.obj
        ((Stacks.EtaleCohomology.extensionByZero.{u, v} (B.inclusion.map j)).obj
          ((sheafEquiv B U.obj U.property AddCommGrpCat.{max (u + 1) v}).functor.obj F)))) := by
  set A := AddCommGrpCat.{max (u + 1) v}
  set EX := sheafEquiv B X.obj X.property A
  set EZ := sheafEquiv B Z.obj Z.property A
  set H := (Stacks.EtaleCohomology.extensionByZero.{u, v} (B.inclusion.map j)).obj
    ((sheafEquiv B U.obj U.property A).functor.obj F)
  have e := sheafEquivPullbackBaseChangeIso B i A
    (Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, v} (B.inclusion.map i))
    (smallEtaleInverseImageAdjunction B i A)
  have h0 : IsZero ((Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, v}
      (B.inclusion.map i)).obj H) :=
    Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_extensionByZero _ _ hij _
  have h1 : IsZero (EZ.functor.obj
      ((smallEtaleInverseImage B i A).obj (EX.inverse.obj H))) :=
    h0.of_iso ((e.app (EX.inverse.obj H)).symm ≪≫
      (Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, v}
        (B.inclusion.map i)).mapIso (EX.counitIso.app H))
  exact (EZ.inverse.map_isZero h1).of_iso (EZ.unitIso.app _)

end AlgebraicGeometry.SmallEtale

end

/-! ### The open-closed sequence for an extension by zero to a compactification -/

/-!
# The open-closed sequence for an extension by zero to a compactification

Let `φ : X ⟶ X̄` be an open immersion (for instance the open immersion of a compactification of a
morphism `X ⟶ S`), let `j : U ⟶ X` be an open immersion and `i : A ⟶ X` a closed immersion with
complementary images, and let `i_B : B ⟶ X̄` be a closed immersion whose image together with the
image of `φ` covers `X̄`, such that the square
```
A --φ_A--> B
|i         |i_B
X ---φ---> X̄
```
is cartesian. Then `φ_A` is an open immersion, and for every abelian sheaf `F` on the small étale
site of `X` there is a short exact sequence, natural in `F`,
```
0 → (φ ∘ j)_! (j^* F) → φ_! F → i_{B,*} φ_{A,!} (i^* F) → 0.
```

The sequence is the open-closed sequence `0 → ψ_! ψ^{-1} G → G → i_{B,*} i_B^{-1} G → 0` on `X̄`
(Stacks Project, Tag 095L) for `G = φ_! F`, the open immersion `ψ = φ ∘ j` and the closed
immersion `i_B`, whose images are complementary; its outer terms are identified using
`ψ^{-1} φ_! F ≅ j^{-1} φ^{-1} φ_! F ≅ j^* F` and the base change isomorphism
`i_B^* φ_! ≅ φ_{A,!} i^*` of extension by zero along the cartesian square.

## Main definitions

* `AlgebraicGeometry.extensionByZeroOpenClosedι`: the natural map
  `(φ ∘ j)_! (j^* F) ⟶ φ_! F`, induced by the counit of `(φ ∘ j)_! ⊣ (φ ∘ j)^{-1}`.
* `AlgebraicGeometry.extensionByZeroOpenClosedπ`: the natural map
  `φ_! F ⟶ i_{B,*} φ_{A,!} (i^* F)`, the unit of `i_B^* ⊣ i_{B,*}` followed by the base change
  isomorphism.
* `AlgebraicGeometry.etaleAbelianInverseImageExtensionByZeroIso`: the base change isomorphism
  `φ_{A,!} ∘ i^* ≅ i_B^* ∘ φ_!` for an arbitrary cartesian square with `φ` étale.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_isPullback_of_isOpenImmersion`: `φ_A` is an open immersion.
* `AlgebraicGeometry.range_comp_base_eq_compl_range_of_isPullback`: the image of `φ ∘ j` is
  the complement of `B`.
* `AlgebraicGeometry.extensionByZeroOpenClosedι_comp_π`: the composite of the two maps is zero.
* `AlgebraicGeometry.shortExact_extensionByZeroOpenClosed`: the sequence is short exact.

## Implementation notes

Sheaves live on Mathlib's small étale site `X.Etale` with the topology `X.smallEtaleTopology`,
where the Stacks Project's extension by zero `Stacks.EtaleCohomology.extensionByZero`, inverse
image `Stacks.EtaleCohomology.etaleAbelianInverseImage` and direct image
`Stacks.EtaleCohomology.etaleAbelianDirectImage` are defined, with coefficients in
`AddCommGrpCat.{max (u + 1) v}`.

The statement is made for an arbitrary open immersion `φ`; the compactification enters only
through its open immersion. The condition that `B ×_{X̄} X` is `A` as a subscheme of `X` is the
cartesian square `IsPullback i φ_A φ i_B`, and naturality in `F` is expressed by the two maps
being natural transformations of functors. Exactness is deduced from Tag 095L rather than
checked on stalks.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology
open AlgebraicGeometry.Scheme.Etale

universe v u

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

namespace AlgebraicGeometry

section

variable {Xbar X A B : Scheme.{u}} {φ : X ⟶ Xbar} {i : A ⟶ X} {iB : B ⟶ Xbar} {φA : A ⟶ B}

/-- The base change of an open immersion is an open immersion: in a cartesian square
`IsPullback i φ_A φ i_B` with `φ` an open immersion, `φ_A` is an open immersion. -/
@[weil "lem_fk108_open_closed_extension_short_exact"]
theorem isOpenImmersion_of_isPullback_of_isOpenImmersion (sq : IsPullback i φA φ iB)
    [IsOpenImmersion φ] :
    IsOpenImmersion φA :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) sq
    inferInstance

/-- Extension by zero commutes with inverse image along an arbitrary cartesian square
`IsPullback i φ_A φ i_B` with `φ` étale: `φ_{A,!} ∘ i^* ≅ i_B^* ∘ φ_!` on abelian sheaves. Both
sides are left adjoints, of `i_* ∘ φ_A^{-1}` and of `φ^{-1} ∘ i_{B,*}`, and those agree. -/
def etaleAbelianInverseImageExtensionByZeroIso (sq : IsPullback i φA φ iB) [Etale φ]
    [Etale φA] :
    etaleAbelianInverseImage.{u, v} i ⋙ extensionByZero.{u, v} φA ≅
      extensionByZero.{u, v} φ ⋙ etaleAbelianInverseImage.{u, v} iB :=
  Adjunction.leftAdjointUniq
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).comp (extensionByZeroAdj.{u, v} φA))
    (((extensionByZeroAdj.{u, v} φ).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} iB)).ofNatIsoRight
        (etaleAbelianRestrictionPushforwardIsoOfIsPullback sq).symm)

end

section

variable {Xbar X U : Scheme.{u}} (φ : X ⟶ Xbar) (j : U ⟶ X) [Etale φ] [Mono φ] [Etale j]

/-- Restriction along an étale morphism `j ≫ φ` is restriction along `φ` followed by restriction
along `j`. -/
def etaleRestrictionCompIso :
    etaleRestriction.{u, v} (j ≫ φ) ≅ etaleRestriction.{u, v} φ ⋙ etaleRestriction.{u, v} j :=
  (Functor.sheafPushforwardContinuousComp' (smallEtaleComposeCompIso j φ).symm
    AddCommGrpCat.{max (u + 1) v} U.smallEtaleTopology X.smallEtaleTopology
      Xbar.smallEtaleTopology).symm

/-- For an étale monomorphism `φ : X ⟶ Xbar` and an étale `j : U ⟶ X`, restricting `φ_! F` along
`φ ∘ j` gives `j^* F`, naturally in the abelian sheaf `F`. -/
def extensionByZeroCompEtaleRestrictionIso :
    extensionByZero.{u, v} φ ⋙ etaleRestriction.{u, v} (j ≫ φ) ≅
      etaleAbelianInverseImage.{u, v} j :=
  Functor.isoWhiskerLeft _ (etaleRestrictionCompIso.{v} φ j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (extensionByZeroAdj.{u, v} φ).unit).symm _ ≪≫
    Functor.leftUnitor _ ≪≫ (etaleAbelianInverseImageRestrictionIso.{u, v} j).symm

/-- The natural map `(φ ∘ j)_! (j^* F) ⟶ φ_! F`: the identification `j^* F ≅ (φ ∘ j)^{-1} φ_! F`
followed by the counit of `(φ ∘ j)_! ⊣ (φ ∘ j)^{-1}` at `φ_! F`. -/
def extensionByZeroOpenClosedι :
    etaleAbelianInverseImage.{u, v} j ⋙ extensionByZero.{u, v} (j ≫ φ) ⟶
      extensionByZero.{u, v} φ :=
  Functor.whiskerRight (extensionByZeroCompEtaleRestrictionIso.{v} φ j).inv _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (extensionByZeroAdj.{u, v} (j ≫ φ)).counit ≫
    (Functor.rightUnitor _).hom

lemma extensionByZeroOpenClosedι_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (extensionByZeroOpenClosedι.{v} φ j).app F =
      (extensionByZero.{u, v} (j ≫ φ)).map
          ((extensionByZeroCompEtaleRestrictionIso.{v} φ j).inv.app F) ≫
        (extensionByZeroAdj.{u, v} (j ≫ φ)).counit.app ((extensionByZero.{u, v} φ).obj F) := by
  simp [extensionByZeroOpenClosedι]

end

section

variable {Xbar X A B : Scheme.{u}} (φ : X ⟶ Xbar) (i : A ⟶ X) (iB : B ⟶ Xbar) (φA : A ⟶ B)
  (sq : IsPullback i φA φ iB) [Etale φ] [Etale φA]

/-- The natural map `φ_! F ⟶ i_{B,*} φ_{A,!} (i^* F)`: the unit of `i_B^* ⊣ i_{B,*}` at `φ_! F`
followed by `i_{B,*}` of the base change isomorphism `i_B^* φ_! F ≅ φ_{A,!} i^* F`. -/
def extensionByZeroOpenClosedπ :
    extensionByZero.{u, v} φ ⟶
      etaleAbelianInverseImage.{u, v} i ⋙ extensionByZero.{u, v} φA ⋙
        etaleAbelianDirectImage.{u, v} iB :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (etaleAbelianInverseImageDirectImageAdj.{u, v} iB).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleAbelianInverseImageExtensionByZeroIso.{v} sq).inv _ ≫
    (Functor.associator _ _ _).hom

lemma extensionByZeroOpenClosedπ_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (extensionByZeroOpenClosedπ.{v} φ i iB φA sq).app F =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} iB).unit.app
          ((extensionByZero.{u, v} φ).obj F) ≫
        (etaleAbelianDirectImage.{u, v} iB).map
          ((etaleAbelianInverseImageExtensionByZeroIso.{v} sq).inv.app F) := by
  simp [extensionByZeroOpenClosedπ]

end

section

variable {Xbar X U A B : Scheme.{u}} {φ : X ⟶ Xbar} {j : U ⟶ X} {i : A ⟶ X} {iB : B ⟶ Xbar}
  {φA : A ⟶ B}

/-- In the situation of the open-closed sequence, the image of `φ ∘ j` is the complement of the
image of `i_B`: a point of `X̄` outside `B` lies in `φ(X)`, outside `φ(A)`, hence in `φ(j(U))`;
a point of `φ(j(U))` in `B` would lift to `A`, as `B ×_{X̄} X = A`. -/
theorem range_comp_base_eq_compl_range_of_isPullback (sq : IsPullback i φA φ iB)
    [IsOpenImmersion φ] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hcov : Set.range φ.base ∪ Set.range iB.base = Set.univ) :
    Set.range (j ≫ φ).base = (Set.range iB.base)ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Scheme.Hom.comp_base, TopCat.comp_app]
  constructor
  · rintro ⟨y, rfl⟩ ⟨b, hb⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hb.symm
    have hji : j.base y ∈ Set.range i.base :=
      ⟨sq.isoPullback.inv.base z, by
        rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]⟩
    have hy : j.base y ∈ Set.range j.base := ⟨y, rfl⟩
    rw [hij] at hy
    exact hy hji
  · intro hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range φ.base := by
      have : x ∈ Set.range φ.base ∪ Set.range iB.base := hcov ▸ Set.mem_univ x
      exact this.resolve_right fun h ↦ hx (by simpa using h)
    have hy : y ∈ Set.range j.base := by
      rw [hij]
      rintro ⟨a, rfl⟩
      refine hx ⟨φA.base a, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]
    obtain ⟨u, rfl⟩ := hy
    exact ⟨u, rfl⟩

end

section

variable {Xbar X U A B : Scheme.{u}} (φ : X ⟶ Xbar) [IsOpenImmersion φ] (j : U ⟶ X)
  [IsOpenImmersion j] (i : A ⟶ X) (iB : B ⟶ Xbar) [IsClosedImmersion iB] (φA : A ⟶ B)
  [IsOpenImmersion φA] (sq : IsPullback i φA φ iB)
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (hcov : Set.range φ.base ∪ Set.range iB.base = Set.univ)

include hij hcov

omit [IsClosedImmersion iB] in
/-- The composite `(φ ∘ j)_! (j^* F) ⟶ φ_! F ⟶ i_{B,*} φ_{A,!} (i^* F)` is zero. -/
theorem extensionByZeroOpenClosedι_comp_π :
    extensionByZeroOpenClosedι.{v} φ j ≫ extensionByZeroOpenClosedπ.{v} φ i iB φA sq = 0 := by
  refine NatTrans.ext (funext fun F ↦ ?_)
  rw [NatTrans.comp_app, extensionByZeroOpenClosedι_app, extensionByZeroOpenClosedπ_app,
    Category.assoc, ← Category.assoc ((extensionByZeroAdj.{u, v} (j ≫ φ)).counit.app _),
    extensionByZero_counit_comp_inverseImage_unit iB (j ≫ φ)
      (range_comp_base_eq_compl_range_of_isPullback sq hij hcov), zero_comp, comp_zero]
  rfl

/-- **The open-closed sequence for extension by zero to a compactification** ([FK], I.8). Let
`φ : X ⟶ X̄` be an open immersion, `j : U ⟶ X` an open immersion and `i : A ⟶ X` a morphism with
complementary images, `i_B : B ⟶ X̄` a closed immersion with `φ(X) ∪ B = X̄`, and `φ_A : A ⟶ B`
such that `B ×_{X̄} X = A` (the square `IsPullback i φ_A φ i_B`). For every abelian sheaf `F` on
the small étale site of `X` the natural maps form a short exact sequence
`0 → (φ ∘ j)_! (j^* F) → φ_! F → i_{B,*} φ_{A,!} (i^* F) → 0`. -/
@[weil "lem_fk108_open_closed_extension_short_exact"]
theorem shortExact_extensionByZeroOpenClosed
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (ShortComplex.mk ((extensionByZeroOpenClosedι.{v} φ j).app F)
      ((extensionByZeroOpenClosedπ.{v} φ i iB φA sq).app F)
      (by rw [← NatTrans.comp_app, extensionByZeroOpenClosedι_comp_π φ j i iB φA sq hij hcov,
        NatTrans.app_zero])).ShortExact := by
  obtain ⟨w, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} iB (j ≫ φ)
    (range_comp_base_eq_compl_range_of_isPullback sq hij hcov) ((extensionByZero.{u, v} φ).obj F)
  refine ShortComplex.shortExact_of_iso ?_ hS
  refine ShortComplex.isoMk
    ((extensionByZero.{u, v} (j ≫ φ)).mapIso
      ((extensionByZeroCompEtaleRestrictionIso.{v} φ j).app F))
    (Iso.refl _)
    ((etaleAbelianDirectImage.{u, v} iB).mapIso
      ((etaleAbelianInverseImageExtensionByZeroIso.{v} sq).app F).symm) ?_ ?_
  · simp [extensionByZeroOpenClosedι_app, ← Functor.map_comp_assoc]
  · simp [extensionByZeroOpenClosedπ_app]

end

end AlgebraicGeometry

end
