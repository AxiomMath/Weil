module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbOfSets
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImage
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer

/-!
# Base change morphisms for direct images of étale sheaves

Consider a commuting square `g' ≫ f = f' ≫ g` of schemes of a big étale site
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
(for instance `X' = X ×_Y Y'` with its two projections) and a sheaf of sets `𝒢` on the small
étale site of `X`. Let `η^g` and `η^{g'}` be the units of the inverse-image/direct-image
adjunctions of `g` and `g'`, and `σ : f_* g'_* ⟶ g_* f'_*` the canonical identification of the
two composite direct images around the square. A morphism `b : g⁻¹ f_* 𝒢 ⟶ f'_* g'⁻¹ 𝒢` is a
*base change morphism* if `f_* η^{g'}_𝒢 ≫ σ_{g'⁻¹ 𝒢} = η^g_{f_* 𝒢} ≫ g_* b` as morphisms
`f_* 𝒢 ⟶ g_* f'_* g'⁻¹ 𝒢`.

By adjunction there is exactly one such morphism, namely the mate of `σ`, which is
`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`.

## Main definitions

* `CategoryTheory.Adjunction.IsUnitCompatible`: for adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a 2-cell
  `α : R₁ ⋙ G ⟶ H ⋙ R₂`, the unit equation characterising the components of the mate of `α`.
* `AlgebraicGeometry.IsBaseChangeMorphism`: the defining unit equation of a base change morphism.

## Main results

* `AlgebraicGeometry.isBaseChangeMorphism_smallEtaleBaseChangeNatTransUniv`: the canonical
  comparison `g⁻¹ f_* 𝒢 ⟶ f'_* g'⁻¹ 𝒢` is a base change morphism.
* `AlgebraicGeometry.isBaseChangeMorphism_iff`: a morphism is a base change morphism if and only
  if it is the canonical comparison.
* `AlgebraicGeometry.existsUnique_isBaseChangeMorphism`: there is exactly one base change
  morphism.

## Implementation notes

The square is only required to commute; cartesianness is not needed to state the definition.
The source and target of a base change morphism are written as objects of the composite functors
`f_* ⋙ g⁻¹` and `g'⁻¹ ⋙ f'_*`, which is how the components of
`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv` are typed; they are definitionally
`g⁻¹ (f_* 𝒢)` and `f'_* (g'⁻¹ 𝒢)`. The definition is the specialisation of
`CategoryTheory.Adjunction.IsUnitCompatible` to the inverse-image/direct-image adjunctions, with
the functors given explicitly.
Sheaves take values in `Type (max (u + 1) v)`, the coefficient universe of
`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][freitag-kiehl]
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u v

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- Given adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a 2-cell `α : R₁ ⋙ G ⟶ H ⋙ R₂`, a morphism
`b : L₂ (G c) ⟶ H (L₁ c)` is *unit-compatible* with `α` at `c` if `G` of the unit of `L₁ ⊣ R₁` at
`c` followed by `α` equals the unit of `L₂ ⊣ R₂` at `G c` followed by `R₂ b`. -/
def IsUnitCompatible (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂) {c : C}
    (b : (G ⋙ L₂).obj c ⟶ (L₁ ⋙ H).obj c) : Prop :=
  G.map (adj₁.unit.app c) ≫ α.app (L₁.obj c) = adj₂.unit.app (G.obj c) ≫ R₂.map b

variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂)

/-- Unfolded form of `CategoryTheory.Adjunction.IsUnitCompatible`. -/
theorem isUnitCompatible_iff_comp_eq {c : C} (b : (G ⋙ L₂).obj c ⟶ (L₁ ⋙ H).obj c) :
    IsUnitCompatible adj₁ adj₂ α b ↔
      G.map (adj₁.unit.app c) ≫ α.app (L₁.obj c) = adj₂.unit.app (G.obj c) ≫ R₂.map b :=
  Iff.rfl

/-- The component of the mate of `α` is unit-compatible with `α`. -/
theorem isUnitCompatible_mateEquiv_symm_app (c : C) :
    IsUnitCompatible adj₁ adj₂ α (((mateEquiv adj₁ adj₂).symm α).app c) :=
  unit_mateEquiv_symm adj₁ adj₂ α c

/-- A morphism is unit-compatible with `α` if and only if it is the component of the mate
of `α`. -/
theorem isUnitCompatible_iff {c : C} (b : (G ⋙ L₂).obj c ⟶ (L₁ ⋙ H).obj c) :
    IsUnitCompatible adj₁ adj₂ α b ↔ b = ((mateEquiv adj₁ adj₂).symm α).app c := by
  constructor
  · intro hb
    apply (adj₂.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact hb.symm.trans (isUnitCompatible_mateEquiv_symm_app adj₁ adj₂ α c)
  · rintro rfl
    exact isUnitCompatible_mateEquiv_symm_app adj₁ adj₂ α c

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y) (h : g' ≫ f = f' ≫ g)

/-- A morphism `b : g⁻¹ f_* 𝒢 ⟶ f'_* g'⁻¹ 𝒢` is a *base change morphism* for the commuting square
`g' ≫ f = f' ≫ g` if `f_*` of the unit of `g'` at `𝒢`, followed by the identification
`f_* g'_* ⟶ g_* f'_*` of the composite direct images, equals the unit of `g` at `f_* 𝒢` followed
by `g_* b`. -/
@[weil "def_fk103_base_change_morphism_degree_zero"]
def IsBaseChangeMorphism
    {𝒢 : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))}
    (b : (B.smallPushforward f (Type (max (u + 1) v)) ⋙
        B.smallInverseImage g (Type (max (u + 1) v))).obj 𝒢 ⟶
      (B.smallInverseImage g' (Type (max (u + 1) v)) ⋙
        B.smallPushforward f' (Type (max (u + 1) v))).obj 𝒢) : Prop :=
  @Adjunction.IsUnitCompatible _ _ _ _ _ _ _ _
    (B.smallPushforward f (Type (max (u + 1) v))) (B.smallPushforward f' (Type (max (u + 1) v)))
    (B.smallInverseImage g' (Type (max (u + 1) v))) (B.smallPushforward g' (Type (max (u + 1) v)))
    (B.smallInverseImage g (Type (max (u + 1) v))) (B.smallPushforward g (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g (Type (max (u + 1) v)))
    (smallEtaleBaseChangeMateUniv.{u, v} B g' f' f g h) 𝒢 b

/-- The canonical comparison is the mate of the identification of the two composite direct
images, with the universes of the coefficients fixed. -/
private theorem smallEtaleBaseChangeNatTransUniv_eq_mateEquiv_symm :
    smallEtaleBaseChangeNatTransUniv.{u, v} B g' f' f g h =
      (mateEquiv (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
        (B.smallPullbackAdjunction g (Type (max (u + 1) v)))).symm
        (smallEtaleBaseChangeMateUniv.{u, v} B g' f' f g h) :=
  rfl

/-- The canonical comparison `g⁻¹ f_* 𝒢 ⟶ f'_* g'⁻¹ 𝒢` is a base change morphism. -/
theorem isBaseChangeMorphism_smallEtaleBaseChangeNatTransUniv
    (𝒢 : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    IsBaseChangeMorphism B g' f' f g h
      ((smallEtaleBaseChangeNatTransUniv.{u, v} B g' f' f g h).app 𝒢) := by
  rw [smallEtaleBaseChangeNatTransUniv_eq_mateEquiv_symm]
  exact @Adjunction.isUnitCompatible_mateEquiv_symm_app _ _ _ _ _ _ _ _
    (B.smallPushforward f (Type (max (u + 1) v))) (B.smallPushforward f' (Type (max (u + 1) v)))
    (B.smallInverseImage g' (Type (max (u + 1) v))) (B.smallPushforward g' (Type (max (u + 1) v)))
    (B.smallInverseImage g (Type (max (u + 1) v))) (B.smallPushforward g (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g (Type (max (u + 1) v)))
    (smallEtaleBaseChangeMateUniv.{u, v} B g' f' f g h) 𝒢

/-- A morphism `g⁻¹ f_* 𝒢 ⟶ f'_* g'⁻¹ 𝒢` is a base change morphism if and only if it is the
canonical comparison `AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`. -/
theorem isBaseChangeMorphism_iff
    {𝒢 : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))}
    (b : (B.smallPushforward f (Type (max (u + 1) v)) ⋙
        B.smallInverseImage g (Type (max (u + 1) v))).obj 𝒢 ⟶
      (B.smallInverseImage g' (Type (max (u + 1) v)) ⋙
        B.smallPushforward f' (Type (max (u + 1) v))).obj 𝒢) :
    IsBaseChangeMorphism B g' f' f g h b ↔
      b = (smallEtaleBaseChangeNatTransUniv.{u, v} B g' f' f g h).app 𝒢 := by
  rw [smallEtaleBaseChangeNatTransUniv_eq_mateEquiv_symm]
  exact @Adjunction.isUnitCompatible_iff _ _ _ _ _ _ _ _
    (B.smallPushforward f (Type (max (u + 1) v))) (B.smallPushforward f' (Type (max (u + 1) v)))
    (B.smallInverseImage g' (Type (max (u + 1) v))) (B.smallPushforward g' (Type (max (u + 1) v)))
    (B.smallInverseImage g (Type (max (u + 1) v))) (B.smallPushforward g (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g (Type (max (u + 1) v)))
    (smallEtaleBaseChangeMateUniv.{u, v} B g' f' f g h) 𝒢 b

/-- There is exactly one base change morphism `g⁻¹ f_* 𝒢 ⟶ f'_* g'⁻¹ 𝒢`. -/
@[weil "lem_fk103_base_change_morphism_exists_unique"]
theorem existsUnique_isBaseChangeMorphism
    (𝒢 : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    ∃! b : (B.smallPushforward f (Type (max (u + 1) v)) ⋙
        B.smallInverseImage g (Type (max (u + 1) v))).obj 𝒢 ⟶
      (B.smallInverseImage g' (Type (max (u + 1) v)) ⋙
        B.smallPushforward f' (Type (max (u + 1) v))).obj 𝒢,
      IsBaseChangeMorphism B g' f' f g h b :=
  ⟨_, isBaseChangeMorphism_smallEtaleBaseChangeNatTransUniv B g' f' f g h 𝒢,
    fun b hb => (isBaseChangeMorphism_iff B g' f' f g h b).mp hb⟩

end AlgebraicGeometry

end

/-! ### Base change of higher direct images along a finite morphism -/

/-!
# Base change of higher direct images along a finite morphism

Consider a cartesian square of schemes of a big étale site
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with `f` finite, and an abelian sheaf `𝒢` on the small étale site of `X`. Then for every `ν ≥ 0`
the sheaves `g^*(R^ν f_* 𝒢)` and `R^ν f'_*(g'^* 𝒢)` on the small étale site of `Y'` are
isomorphic, and for `ν = 0` an isomorphism is given by the base change morphism
`g^* f_* 𝒢 ⟶ f'_* g'^* 𝒢`.

For `ν = 0` this is the finite base change theorem for abelian sheaves: the base change morphism
of abelian sheaves is the mate, along the inverse-image/direct-image adjunctions of `g` and `g'`,
of the identification `g'_* f_* ≅ f'_* g_*` of the two composite direct images around the square,
and it is invertible because the base change morphism of the underlying sheaves of sets is
([Stacks, Tag 0959]). For `ν > 0` both sheaves vanish: `R^ν f_* 𝒢 = 0` since `f` is finite, `g^*`
preserves zero objects, and `f'` is finite as a base change of `f`.

## Main definitions

* `AlgebraicGeometry.smallEtaleAbBaseChange`: the base change morphism
  `g^* f_* 𝒢 ⟶ f'_* g'^* 𝒢` of abelian sheaves on the small étale sites, for a commutative
  square.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleAbBaseChange`: for a cartesian square with `f` finite, the
  base change morphism of abelian sheaves is an isomorphism.
* `AlgebraicGeometry.nonempty_smallEtaleInverseImage_higherDirectImage_iso`: for a cartesian
  square with `f` finite, `g^*(R^ν f_* 𝒢) ≅ R^ν f'_*(g'^* 𝒢)` for every `ν`.

## Implementation notes

The coefficients are `AddCommGrpCat.{u + 1}`, for `u` the universe of the schemes of the big
étale site: these are the coefficients at which the inverse image
`AlgebraicGeometry.smallEtaleInverseImage` of abelian sheaves is compared with the inverse image
of the underlying sheaves of sets.

The passage from sheaves of sets to abelian sheaves is
`Stacks.EtaleCohomology.isIso_mateEquiv_symm_compositeDirectImageCell_of_sheafCompose`, stated
for an arbitrary square of continuous functors of sites; it is applied here to the base change
functors of the small étale sites, with the inverse images given by Kan extension and
sheafification, and transported to the chosen inverse images
`AlgebraicGeometry.smallEtaleInverseImage` by uniqueness of left adjoints.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.3
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y)

/-- The identification `g'_* f_* ≅ f'_* g_*` of the two composite direct images around a
commutative square `g' ≫ f = f' ≫ g` of a big étale site, with coefficients in `A`, as a
2-square, through the direct images along the two equal composites. -/
abbrev smallEtaleCompositeDirectImageCell (h : g' ≫ f = f' ≫ g) (A : Type*) [Category* A] :=
  Stacks.EtaleCohomology.compositeDirectImageCell (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Y'.1 Y'.property)
    (SmallEtale.topology B X'.1 X'.property) (smallEtaleBaseChange B f)
    (smallEtaleBaseChange B g) (smallEtaleBaseChange B g') (smallEtaleBaseChange B f')
    (fun k : X' ⟶ Y => smallEtaleBaseChange B k) (smallEtaleBaseChange_compIso B X' X Y g' f).val
    (smallEtaleBaseChange_compIso B X' Y' Y f' g).val h A

/-- **The base change morphism of abelian sheaves** `g^* f_* 𝒢 ⟶ f'_* g'^* 𝒢` for a commutative
square `g' ≫ f = f' ≫ g` of a big étale site: the mate, along the inverse-image/direct-image
adjunctions of `g'` and `g`, of the identification of the two composite direct images. -/
def smallEtaleAbBaseChange (h : g' ≫ f = f' ≫ g) :
    TwoSquare (B.smallPushforward f AddCommGrpCat.{u + 1})
      (smallEtaleInverseImage B g' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImage B g AddCommGrpCat.{u + 1})
      (B.smallPushforward f' AddCommGrpCat.{u + 1}) :=
  (mateEquiv (smallEtaleInverseImageAdjunction B g' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1})).symm
    (smallEtaleCompositeDirectImageCell B g' f' f g h AddCommGrpCat.{u + 1})

/-- The base change morphism of sheaves of sets is the mate of the identification of the two
composite direct images. -/
theorem smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm_compositeDirectImageCell
    (h : g' ≫ f = f' ≫ g) :
    smallEtaleBaseChangeNatTrans B g' f' f g h =
      ((mateEquiv (smallEtaleInverseImageAdjunction B g' (Type (u + 1)))
        (smallEtaleInverseImageAdjunction B g (Type (u + 1)))).symm
        (smallEtaleCompositeDirectImageCell B g' f' f g h (Type (u + 1)))).natTrans :=
  rfl

/-- **Finite base change for abelian sheaves.** For a cartesian square of a big étale site with
`f` finite, the base change morphism `g^* f_* 𝒢 ⟶ f'_* g'^* 𝒢` of abelian sheaves is an
isomorphism. -/
@[weil "lem_fk103_finite_base_change_higher_direct_images"]
theorem isIso_smallEtaleAbBaseChange
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g) :
    IsIso (smallEtaleAbBaseChange B g' f' f g h).natTrans := by
  have hset : IsIso ((mateEquiv (smallEtaleInverseImageAdjunction B g' (Type (u + 1)))
      (smallEtaleInverseImageAdjunction B g (Type (u + 1)))).symm
      (smallEtaleCompositeDirectImageCell B g' f' f g h (Type (u + 1)))).natTrans := by
    rw [← smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm_compositeDirectImageCell,
      NatTrans.isIso_iff_isIso_app]
    exact isIso_smallEtaleBaseChangeNatTrans B g' f' f g sq h
  have hset' := Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ (Type (u + 1)) _ _)
    (smallEtaleInverseImageAdjunction B g' (Type (u + 1)))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ (Type (u + 1)) _ _)
    (smallEtaleInverseImageAdjunction B g (Type (u + 1))) _ hset
  have hab := Stacks.EtaleCohomology.isIso_mateEquiv_symm_compositeDirectImageCell_of_sheafCompose
    (Φ := forget AddCommGrpCat.{u + 1}) _ _ _ _ _ _ _ _ _ _ _ _ hset'
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq
    (smallEtaleInverseImageAdjunction B g' AddCommGrpCat.{u + 1})
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)
    (smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1})
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _) _ hab

/-- **Base change of higher direct images along a finite morphism.** For a cartesian square of
a big étale site with `f` finite and an abelian sheaf `𝒢` on the small étale site of `X`, the
sheaves `g^*(R^ν f_* 𝒢)` and `R^ν f'_*(g'^* 𝒢)` are isomorphic for every `ν`. For `ν = 0` the
isomorphism constructed is the base change morphism `smallEtaleAbBaseChange`, through
`R^0 f_* ≅ f_*` and `R^0 f'_* ≅ f'_*`. -/
@[weil "lem_fk103_finite_base_change_higher_direct_images"]
theorem nonempty_smallEtaleInverseImage_higherDirectImage_iso
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Nonempty ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj
        ((BigEtaleSite.higherDirectImage.{u + 1} B f ν).obj G) ≅
      (BigEtaleSite.higherDirectImage.{u + 1} B f' ν).obj
        ((smallEtaleInverseImage B g' AddCommGrpCat.{u + 1}).obj G)) := by
  have h : g' ≫ f = f' ≫ g :=
    B.inclusion.map_injective (by rw [B.inclusion.map_comp, B.inclusion.map_comp]; exact sq.w)
  have hf' : IsFinite (B.inclusion.map f') := MorphismProperty.of_isPullback sq inferInstance
  have : (smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    (smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).isLeftAdjoint
  have : (smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  rcases ν with _ | ν
  · have := isIso_smallEtaleAbBaseChange B g' f' f g sq h
    exact ⟨(smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).mapIso
        ((BigEtaleSite.higherDirectImageZeroIso.{u + 1} B f).app G) ≪≫
      asIso ((smallEtaleAbBaseChange B g' f' f g h).natTrans.app G) ≪≫
      ((BigEtaleSite.higherDirectImageZeroIso.{u + 1} B f').app _).symm⟩
  · exact ⟨IsZero.iso (Functor.map_isZero _
      (BigEtaleSite.isZero_higherDirectImage_obj_of_isFinite.{u + 1} B f G (Nat.succ_pos ν)))
      (BigEtaleSite.isZero_higherDirectImage_obj_of_isFinite.{u + 1} B f' _ (Nat.succ_pos ν))⟩

end AlgebraicGeometry
