module

public import Weil.Attr
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionTwoSquare
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition

/-!
# Cohomology of a finite direct image and restriction

Let `p : X' ⟶ X` be a finite morphism of schemes of a big étale site, `h : Y ⟶ X` a morphism and
`Y' = X' ×_X Y`, with projections `p' : Y' ⟶ Y` and `h' : Y' ⟶ X'`. For an abelian sheaf `G` on
the small étale site of `X'` and `ν ≥ 0` there are isomorphisms
`a : Hᵛ(X, p_* G) ≃+ Hᵛ(X', G)` and `b : Hᵛ(Y, h^* p_* G) ≃+ Hᵛ(Y', h'^* G)` that intertwine the
restriction maps: `b ∘ h^* = h'^* ∘ a`.

Cohomology is `Ext` out of the constant sheaf `ℤ`. The isomorphism `a` is the adjunction
`p^* ⊣ p_*` on `Ext`, `Ext^ν(ℤ_X, p_* G) ≅ Ext^ν(p^* ℤ_X, G)`, which is bijective because both
`p^*` and `p_*` are exact (`p` is finite), followed by `p^* ℤ_X ≅ ℤ_{X'}`. The isomorphism `b`
first applies the base change isomorphism `h^* p_* G ≅ p'_* h'^* G` of a finite morphism, then the
adjunction of the finite morphism `p'`, then an identification `ℤ_{Y'} ≅ p'^* ℤ_Y`. The square
commutes because the base change morphism is the mate of the comparison
`p'^* h^* ≅ h'^* p^*` of the composite inverse images.

## Main definitions

* `AlgebraicGeometry.smallEtaleCohomologyDirectImageAddEquiv`: the isomorphism
  `Hᵛ(X, p_* G) ≃+ Hᵛ(X', G)` for finite `p`.
* `AlgebraicGeometry.smallEtaleCohomologyBaseChangeDirectImageAddEquiv`: the isomorphism
  `Hᵛ(Y, h^* p_* G) ≃+ Hᵛ(Y', h'^* G)` for a cartesian square with `p` finite.
* `AlgebraicGeometry.smallEtaleAbBaseChangeInverseImageComparison`: the comparison
  `p'^* h^* ⟶ h'^* p^*` whose mate is the base change morphism; it is invertible
  (`AlgebraicGeometry.isIso_smallEtaleAbBaseChangeInverseImageComparison`).
* `CategoryTheory.Adjunction.extMapOfIsoAddEquiv`, `CategoryTheory.TwoSquare.extBaseChangeAddEquiv`:
  the same isomorphisms for an arbitrary square of exact adjoint functors between abelian
  categories.

## Main results

* `AlgebraicGeometry.exists_addEquiv_comp_smallEtaleCohomologyRestrictionMap_directImage`: the
  isomorphisms `a` and `b` exist and satisfy `b ∘ h^* = h'^* ∘ a`.
* `CategoryTheory.TwoSquare.extBaseChangeAddEquiv_comp_mapExtAddHom`: the commutation in the
  abstract setting.

## Implementation notes

The source computes `a` and `b` on injective resolutions, through the identifications
`(p_* I)(X) = I(X')`. Here cohomology is `CategoryTheory.Sheaf.H`, the `Ext` groups out of `ℤ`,
and `a`, `b` are maps of `Ext` groups; the restriction maps are
`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`. The isomorphism `ℤ_{Y'} ≅ p'^* ℤ_Y`
used in `b` is the composite of the constant-sheaf comparisons for `h'`, `p` and `h` with the
inverse of the comparison of composite inverse images. The commutation is proved for an
arbitrary square of exact adjoint functors and then instantiated: stated directly on the small
étale sites, the kernel check does not finish within the default budget.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian

universe w u

namespace CategoryTheory

section ExtSquare

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁} {Lf' : C₃ ⥤ C₄} {Rf' : C₄ ⥤ C₃}
  {Lg : C₁ ⥤ C₃} {Lg' : C₂ ⥤ C₄}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (θ : TwoSquare Lg Lf Lf' Lg') [IsIso θ.natTrans]

/-- For a 2-square `θ : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` that is invertible, and identifications
`Lf Z₁ ≅ Z₂`, `Lg Z₁ ≅ Z₃`, `Lg' Z₂ ≅ Z₄`, the resulting identification `Z₄ ≅ Lf' Z₃`. -/
def TwoSquare.objIsoOfIsIso {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄} (ιf : Lf.obj Z₁ ≅ Z₂)
    (ιg : Lg.obj Z₁ ≅ Z₃) (ιg' : Lg'.obj Z₂ ≅ Z₄) : Z₄ ≅ Lf'.obj Z₃ :=
  ιg'.symm ≪≫ Lg'.mapIso ιf.symm ≪≫ (asIso (θ.natTrans.app Z₁)).symm ≪≫ Lf'.mapIso ιg

omit [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄] in
private theorem TwoSquare.objIsoOfIsIso_hom_comp {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄}
    (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃) (ιg' : Lg'.obj Z₂ ≅ Z₄) :
    (θ.objIsoOfIsIso ιf ιg ιg').hom ≫ Lf'.map ιg.inv ≫ θ.natTrans.app Z₁ =
      ιg'.inv ≫ Lg'.map ιf.inv := by
  simp only [objIsoOfIsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
    Category.assoc]
  rw [← Lf'.map_comp_assoc, Iso.hom_inv_id, Lf'.map_id, Category.id_comp, IsIso.inv_hom_id,
    Category.comp_id]

/-- The map `Ext^n(L A, M)` attached to an adjunction is natural in the first argument:
precomposing with `mk₀ φ` before is precomposing with `mk₀ (L.map φ)` after. -/
private theorem Adjunction.extMap_mk₀_comp {C D : Type*} [Category C] [Abelian C]
    [Category D] [Abelian D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [HasExt.{w} C] [HasExt.{w} D]
    {A A' : C} (φ : A' ⟶ A) (M : D) (n : ℕ) (e : Ext.{w} A (R.obj M) n) :
    Stacks.ExtAdjunction.extMap adj A' M n ((Ext.mk₀ φ).comp e (zero_add n)) =
      (Ext.mk₀ (L.map φ)).comp (Stacks.ExtAdjunction.extMap adj A M n e) (zero_add n) := by
  rw [Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The map `Ext^n(Z₁, R G) →+ Ext^n(Z₂, G)` of an adjunction `L ⊣ R` with `L` exact, through an
identification `L Z₁ ≅ Z₂`: the adjunction map `Stacks.ExtAdjunction.extMap` followed by
precomposition with `Z₂ ≅ L Z₁`. -/
def Adjunction.extMapOfIso {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [HasExt.{w} C] [HasExt.{w} D] {Z₁ : C} {Z₂ : D}
    (ι : L.obj Z₁ ≅ Z₂) (G : D) (n : ℕ) : Ext.{w} Z₁ (R.obj G) n →+ Ext.{w} Z₂ G n :=
  ((Ext.mk₀ ι.inv).precomp G (zero_add n)).comp (Stacks.ExtAdjunction.extMap adj Z₁ G n)

theorem Adjunction.bijective_extMapOfIso {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [EnoughInjectives D] [HasExt.{w} C] [HasExt.{w} D] {Z₁ : C}
    {Z₂ : D} (ι : L.obj Z₁ ≅ Z₂) (G : D) (n : ℕ) :
    Function.Bijective (adj.extMapOfIso.{w} ι G n) :=
  (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ n).comp
    (Stacks.ExtAdjunction.extMap_bijective _ _ _ n)

/-- The map `Ext^n(Z₃, Lg Rf G) →+ Ext^n(Z₄, Lg' G)` of a square of adjunctions with invertible
comparison `θ`: the base change map `Lg Rf G ⟶ Rf' Lg' G` (the mate of `θ`), then the adjunction
map of `Lf' ⊣ Rf'`, then precomposition with `Z₄ ≅ Lf' Z₃`
(`CategoryTheory.TwoSquare.objIsoOfIsIso`). -/
def TwoSquare.extBaseChangeHom [Lf'.Additive] [PreservesFiniteLimits Lf']
    [PreservesFiniteColimits Lf'] [HasExt.{w} C₃] [HasExt.{w} C₄] {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃}
    {Z₄ : C₄} (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃) (ιg' : Lg'.obj Z₂ ≅ Z₄) (G : C₂)
    (n : ℕ) : Ext.{w} Z₃ (Lg.obj (Rf.obj G)) n →+ Ext.{w} Z₄ (Lg'.obj G) n :=
  ((Ext.mk₀ (θ.objIsoOfIsIso ιf ιg ιg').hom).precomp _ (zero_add n)).comp
    ((Stacks.ExtAdjunction.extMap adjf' Z₃ (Lg'.obj G) n).comp
      ((Ext.mk₀ ((mateEquiv adjf adjf' θ).natTrans.app G)).postcomp _ (add_zero n)))

omit [Abelian C₁] [Abelian C₂] in
theorem TwoSquare.bijective_extBaseChangeHom [Lf'.Additive] [PreservesFiniteLimits Lf']
    [PreservesFiniteColimits Lf'] [Rf'.Additive] [PreservesFiniteLimits Rf']
    [PreservesFiniteColimits Rf'] [EnoughInjectives C₄] [HasExt.{w} C₃] [HasExt.{w} C₄]
    {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄} (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃)
    (ιg' : Lg'.obj Z₂ ≅ Z₄) (G : C₂) [IsIso ((mateEquiv adjf adjf' θ).natTrans.app G)]
    (n : ℕ) : Function.Bijective (θ.extBaseChangeHom.{w} adjf adjf' ιf ιg ιg' G n) :=
  (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ n).comp
    ((Stacks.ExtAdjunction.extMap_bijective _ _ _ n).comp
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso _ n))

/-- `CategoryTheory.Adjunction.extMapOfIso` as an additive equivalence, when `R` is exact and the
target has enough injectives. -/
def Adjunction.extMapOfIsoAddEquiv {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [EnoughInjectives D] [HasExt.{w} C] [HasExt.{w} D] {Z₁ : C}
    {Z₂ : D} (ι : L.obj Z₁ ≅ Z₂) (G : D) (n : ℕ) : Ext.{w} Z₁ (R.obj G) n ≃+ Ext.{w} Z₂ G n :=
  AddEquiv.ofBijective _ (adj.bijective_extMapOfIso ι G n)

/-- `CategoryTheory.TwoSquare.extBaseChangeHom` as an additive equivalence, when `Rf'` is exact,
`C₄` has enough injectives and the base change map at `G` is invertible. -/
def TwoSquare.extBaseChangeAddEquiv [Lf'.Additive] [PreservesFiniteLimits Lf']
    [PreservesFiniteColimits Lf'] [Rf'.Additive] [PreservesFiniteLimits Rf']
    [PreservesFiniteColimits Rf'] [EnoughInjectives C₄] [HasExt.{w} C₃] [HasExt.{w} C₄]
    {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄} (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃)
    (ιg' : Lg'.obj Z₂ ≅ Z₄) (G : C₂) [IsIso ((mateEquiv adjf adjf' θ).natTrans.app G)]
    (n : ℕ) : Ext.{w} Z₃ (Lg.obj (Rf.obj G)) n ≃+ Ext.{w} Z₄ (Lg'.obj G) n :=
  AddEquiv.ofBijective _ (θ.bijective_extBaseChangeHom adjf adjf' ιf ιg ιg' G n)

variable [Lf.Additive] [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf]
  [Lf'.Additive] [PreservesFiniteLimits Lf'] [PreservesFiniteColimits Lf']
  [Lg.Additive] [PreservesFiniteLimits Lg] [PreservesFiniteColimits Lg]
  [Lg'.Additive] [PreservesFiniteLimits Lg'] [PreservesFiniteColimits Lg']
  [HasExt.{w} C₁] [HasExt.{w} C₂] [HasExt.{w} C₃] [HasExt.{w} C₄] [EnoughInjectives C₁]

/-- **Restriction and adjunction on `Ext` commute.** Consider a square of exact functors with
`Lf ⊣ Rf`, `Lf' ⊣ Rf'` and an invertible comparison `θ : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'`, whose mate is
the base change map `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`. Let `a` be the map
`Ext^n(Z₁, Rf G) → Ext^n(Lf Z₁, G) ≅ Ext^n(Z₂, G)` and `b` the map
`Ext^n(Z₃, Lg Rf G) → Ext^n(Z₃, Rf' Lg' G) → Ext^n(Lf' Z₃, Lg' G) ≅ Ext^n(Z₄, Lg' G)`.
Then `b ∘ Lg = Lg' ∘ a`, where `Lg` and `Lg'` act on `Ext` through the identifications
`Lg Z₁ ≅ Z₃` and `Lg' Z₂ ≅ Z₄`. -/
private theorem TwoSquare.extMap_comp_mapExactFunctor_eq {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄}
    (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃) (ιg' : Lg'.obj Z₂ ≅ Z₄) (G : C₂) (n : ℕ)
    (x : Ext.{w} Z₁ (Rf.obj G) n) :
    (Ext.mk₀ (θ.objIsoOfIsIso ιf ιg ιg').hom).comp
        (Stacks.ExtAdjunction.extMap adjf' Z₃ (Lg'.obj G) n
          (((Ext.mk₀ ιg.inv).comp (x.mapExactFunctor Lg) (zero_add n)).comp
            (Ext.mk₀ ((mateEquiv adjf adjf' θ).app G)) (add_zero n))) (zero_add n) =
      (Ext.mk₀ ιg'.inv).comp
        (((Ext.mk₀ ιf.inv).comp (Stacks.ExtAdjunction.extMap adjf Z₁ G n x)
          (zero_add n)).mapExactFunctor Lg') (zero_add n) := by
  have hcomm := Stacks.ExtAdjunction.extMap_mapExactFunctor_comm adjf adjf'
    (asIso θ.natTrans) (Iso.refl _) Z₁ G n x
  have hmap : Stacks.CategoryTheory.BaseChange.map adjf adjf' (asIso θ.natTrans) (Iso.refl _) G =
      (mateEquiv adjf adjf' θ).app G := by
    have : Stacks.CategoryTheory.BaseChange.pullbackComparison (asIso θ.natTrans)
        (Iso.refl (Lf ⋙ Lg')) = θ := by
      simp [Stacks.CategoryTheory.BaseChange.pullbackComparison]
    rw [Stacks.CategoryTheory.BaseChange.map, Stacks.CategoryTheory.BaseChange.twoSquare, this]
  rw [hmap] at hcomm
  rw [Ext.comp_assoc_of_third_deg_zero, Adjunction.extMap_mk₀_comp, ← hcomm,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc]
  congr 2
  simpa [Stacks.ExtAdjunction.composite] using θ.objIsoOfIsIso_hom_comp ιf ιg ιg'


/-- `CategoryTheory.TwoSquare.extMap_comp_mapExactFunctor_eq` as an equality of additive maps:
`b ∘ Lg = Lg' ∘ a`, with `Lg` and `Lg'` acting on `Ext` through `Lg Z₁ ≅ Z₃` and
`Lg' Z₂ ≅ Z₄`. -/
private theorem TwoSquare.extBaseChangeHom_comp_mapExtAddHom {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄}
    (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃) (ιg' : Lg'.obj Z₂ ≅ Z₄) (G : C₂) (n : ℕ) :
    (θ.extBaseChangeHom.{w} adjf adjf' ιf ιg ιg' G n).comp
        (((Ext.mk₀ ιg.inv).precomp (Lg.obj (Rf.obj G)) (Nat.zero_add n)).comp
          (Lg.mapExtAddHom Z₁ (Rf.obj G) n)) =
      (((Ext.mk₀ ιg'.inv).precomp (Lg'.obj G) (Nat.zero_add n)).comp
          (Lg'.mapExtAddHom Z₂ G n)).comp (adjf.extMapOfIso.{w} ιf G n) := by
  ext x
  exact θ.extMap_comp_mapExactFunctor_eq adjf adjf' ιf ιg ιg' G n x

/-- `CategoryTheory.TwoSquare.extBaseChangeHom_comp_mapExtAddHom` for the additive equivalences
`CategoryTheory.TwoSquare.extBaseChangeAddEquiv` and
`CategoryTheory.Adjunction.extMapOfIsoAddEquiv`. -/
theorem TwoSquare.extBaseChangeAddEquiv_comp_mapExtAddHom [Rf.Additive]
    [PreservesFiniteLimits Rf] [PreservesFiniteColimits Rf] [EnoughInjectives C₂]
    [Rf'.Additive] [PreservesFiniteLimits Rf'] [PreservesFiniteColimits Rf']
    [EnoughInjectives C₄] {Z₁ : C₁} {Z₂ : C₂} {Z₃ : C₃} {Z₄ : C₄}
    (ιf : Lf.obj Z₁ ≅ Z₂) (ιg : Lg.obj Z₁ ≅ Z₃) (ιg' : Lg'.obj Z₂ ≅ Z₄) (G : C₂)
    [IsIso ((mateEquiv adjf adjf' θ).natTrans.app G)] (n : ℕ) :
    (θ.extBaseChangeAddEquiv.{w} adjf adjf' ιf ιg ιg' G n).toAddMonoidHom.comp
        (((Ext.mk₀ ιg.inv).precomp (Lg.obj (Rf.obj G)) (Nat.zero_add n)).comp
          (Lg.mapExtAddHom Z₁ (Rf.obj G) n)) =
      (((Ext.mk₀ ιg'.inv).precomp (Lg'.obj G) (Nat.zero_add n)).comp
          (Lg'.mapExtAddHom Z₂ G n)).comp (adjf.extMapOfIsoAddEquiv.{w} ιf G n).toAddMonoidHom :=
  θ.extBaseChangeHom_comp_mapExtAddHom adjf adjf' ιf ιg ιg' G n

end ExtSquare

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme} (p : X' ⟶ X) (h : Y ⟶ X)
  (p' : Y' ⟶ Y) (h' : Y' ⟶ X')

/-- The comparison `p'^* h^* ⟶ h'^* p^*` of the two composite inverse images around a
commutative square `h' ≫ p = p' ≫ h`, as the mate of the base change morphism. -/
def smallEtaleAbBaseChangeInverseImageComparison (w : h' ≫ p = p' ≫ h) :
    TwoSquare (smallEtaleInverseImage B h AddCommGrpCat.{u + 1})
      (smallEtaleInverseImage B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImage B p' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImage B h' AddCommGrpCat.{u + 1}) :=
  (mateEquiv (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})).symm
    (smallEtaleAbBaseChange B h' p' p h w)

theorem isIso_smallEtaleAbBaseChangeInverseImageComparison (w : h' ≫ p = p' ≫ h) :
    IsIso (smallEtaleAbBaseChangeInverseImageComparison B p h p' h' w).natTrans := by
  have key := iterated_mateEquiv_conjugateEquiv
    (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
    (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
    (smallEtaleInverseImageAdjunction B h AddCommGrpCat.{u + 1})
    (smallEtaleInverseImageAdjunction B h' AddCommGrpCat.{u + 1})
    (smallEtaleAbBaseChangeInverseImageComparison B p h p' h' w)
  simp only [smallEtaleAbBaseChangeInverseImageComparison, Equiv.apply_symm_apply,
    smallEtaleAbBaseChange] at key
  have :
      IsIso (smallEtaleCompositeDirectImageCell B h' p' p h w AddCommGrpCat.{u + 1}).natTrans := by
    dsimp only [smallEtaleCompositeDirectImageCell, Stacks.EtaleCohomology.compositeDirectImageCell,
      TwoSquare.mk]
    infer_instance
  rw [key] at this
  change IsIso ((conjugateEquiv _ _)
    (smallEtaleAbBaseChangeInverseImageComparison B p h p' h' w).natTrans) at this
  exact conjugateEquiv_of_iso
    ((smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1}).comp
      (smallEtaleInverseImageAdjunction B h' AddCommGrpCat.{u + 1}))
    ((smallEtaleInverseImageAdjunction B h AddCommGrpCat.{u + 1}).comp
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})) _

/-- The mate of `smallEtaleAbBaseChangeInverseImageComparison` is the base change morphism. -/
private theorem mateEquiv_smallEtaleAbBaseChangeInverseImageComparison (w : h' ≫ p = p' ≫ h) :
    mateEquiv (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
        (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
        (smallEtaleAbBaseChangeInverseImageComparison B p h p' h' w) =
      smallEtaleAbBaseChange B h' p' p h w :=
  Equiv.apply_symm_apply _ _


/-- The constant-sheaf comparison `f^* ℤ_S ≅ ℤ_T`. -/
abbrev smallEtaleInverseImageConstantZIso {S T : B.Scheme} (f : T ⟶ S) :
    (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj
        ((constantSheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  smallEtaleInverseImageConstantSheafIso B f AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift ℤ))

theorem preservesFiniteLimits_smallPushforward_of_isFinite {S T : B.Scheme} (f : T ⟶ S)
    [IsFinite (B.inclusion.map f)] :
    PreservesFiniteLimits (B.smallPushforward f AddCommGrpCat.{u + 1}) :=
  ((exactFunctor_iff _).mp (BigEtaleSite.smallPushforward_exact_of_isFinite f)).1

theorem preservesFiniteColimits_smallPushforward_of_isFinite {S T : B.Scheme} (f : T ⟶ S)
    [IsFinite (B.inclusion.map f)] :
    PreservesFiniteColimits (B.smallPushforward f AddCommGrpCat.{u + 1}) :=
  ((exactFunctor_iff _).mp (BigEtaleSite.smallPushforward_exact_of_isFinite f)).2

variable {B p h p' h'} in
theorem comm_of_isPullback_inclusion
    (sq : IsPullback (B.inclusion.map h') (B.inclusion.map p') (B.inclusion.map p)
      (B.inclusion.map h)) : h' ≫ p = p' ≫ h :=
  B.inclusion.map_injective (by rw [B.inclusion.map_comp, B.inclusion.map_comp]; exact sq.w)

variable {B p h p' h'} in
private theorem isIso_mateEquiv_smallEtaleAbBaseChangeInverseImageComparison_app
    (sq : IsPullback (B.inclusion.map h') (B.inclusion.map p') (B.inclusion.map p)
      (B.inclusion.map h)) [IsFinite (B.inclusion.map p)]
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) :
    IsIso ((mateEquiv (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
      (smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
        (comm_of_isPullback_inclusion sq))).natTrans.app G) := by
  have := isIso_smallEtaleAbBaseChange B h' p' p h sq (comm_of_isPullback_inclusion sq)
  rw [mateEquiv_smallEtaleAbBaseChangeInverseImageComparison]
  infer_instance

section Cohomology

variable [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1})]

/-- **The isomorphism `Hᵛ(X, p_* G) ≃+ Hᵛ(X', G)`** for a finite morphism `p : X' ⟶ X`: the
adjunction `p^* ⊣ p_*` on `Ext` out of `ℤ_X`, through `p^* ℤ_X ≅ ℤ_{X'}`. -/
def smallEtaleCohomologyDirectImageAddEquiv [IsFinite (B.inclusion.map p)]
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Sheaf.H.{w} ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj G) ν ≃+ Sheaf.H.{w} G ν :=
  have := preservesFiniteLimits_smallPushforward_of_isFinite B p
  have := preservesFiniteColimits_smallPushforward_of_isFinite B p
  (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1}).extMapOfIsoAddEquiv.{w}
    (smallEtaleInverseImageConstantZIso B p) G ν

omit [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})] in
theorem bijective_extBaseChangeHom_smallEtaleAbBaseChangeInverseImageComparison
    (sq : IsPullback (B.inclusion.map h') (B.inclusion.map p') (B.inclusion.map p)
      (B.inclusion.map h)) [IsFinite (B.inclusion.map p)]
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    have := isIso_smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
      (comm_of_isPullback_inclusion sq)
    Function.Bijective ((smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
      (comm_of_isPullback_inclusion sq)).extBaseChangeHom.{w}
      (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageConstantZIso B p) (smallEtaleInverseImageConstantZIso B h)
      (smallEtaleInverseImageConstantZIso B h') G ν) := by
  intro _
  have : IsFinite (B.inclusion.map p') := MorphismProperty.of_isPullback sq inferInstance
  have := preservesFiniteLimits_smallPushforward_of_isFinite B p'
  have := preservesFiniteColimits_smallPushforward_of_isFinite B p'
  have := isIso_mateEquiv_smallEtaleAbBaseChangeInverseImageComparison_app sq G
  exact (smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
      (comm_of_isPullback_inclusion sq)).bijective_extBaseChangeHom.{w}
      (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageConstantZIso B p) (smallEtaleInverseImageConstantZIso B h)
      (smallEtaleInverseImageConstantZIso B h') G ν

omit [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})] in
/-- **The isomorphism `Hᵛ(Y, h^* p_* G) ≃+ Hᵛ(Y', h'^* G)`** for a cartesian square with `p`
finite: the base change isomorphism `h^* p_* G ≅ p'_* h'^* G`, the adjunction `p'^* ⊣ p'_*` on
`Ext` out of `ℤ_Y`, and the identification `ℤ_{Y'} ≅ p'^* ℤ_Y`. -/
def smallEtaleCohomologyBaseChangeDirectImageAddEquiv
    (sq : IsPullback (B.inclusion.map h') (B.inclusion.map p') (B.inclusion.map p)
      (B.inclusion.map h)) [IsFinite (B.inclusion.map p)]
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Sheaf.H.{w} ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj
        ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj G)) ν ≃+
      Sheaf.H.{w} ((smallEtaleInverseImage B h' AddCommGrpCat.{u + 1}).obj G) ν :=
  have := isIso_smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
    (comm_of_isPullback_inclusion sq)
  AddEquiv.ofBijective ((smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
      (comm_of_isPullback_inclusion sq)).extBaseChangeHom.{w}
      (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageConstantZIso B p) (smallEtaleInverseImageConstantZIso B h)
      (smallEtaleInverseImageConstantZIso B h') G ν)
    (bijective_extBaseChangeHom_smallEtaleAbBaseChangeInverseImageComparison.{w} B p h p' h'
      sq G ν)

/-- **Freitag–Kiehl, I.6: restriction and finite direct image.** Let `p : X' ⟶ X` be finite,
`h : Y ⟶ X` a morphism and `Y' = X' ×_X Y` with projections `p' : Y' ⟶ Y`, `h' : Y' ⟶ X'`. For an
abelian sheaf `G` on the small étale site of `X'` and `ν ≥ 0` there are isomorphisms
`a : Hᵛ(X, p_* G) ≃+ Hᵛ(X', G)` and `b : Hᵛ(Y, h^* p_* G) ≃+ Hᵛ(Y', h'^* G)` with
`b ∘ h^* = h'^* ∘ a`, where `h^*` and `h'^*` are the restriction maps on cohomology. -/
@[weil "lem_fk106_finite_pushforward_restriction_square"]
theorem exists_addEquiv_comp_smallEtaleCohomologyRestrictionMap_directImage
    (sq : IsPullback (B.inclusion.map h') (B.inclusion.map p') (B.inclusion.map p)
      (B.inclusion.map h)) [IsFinite (B.inclusion.map p)]
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) (ν : ℕ) :
    ∃ (a : Sheaf.H.{w} ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj G) ν ≃+
        Sheaf.H.{w} G ν)
      (b : Sheaf.H.{w} ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj
        ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj G)) ν ≃+
          Sheaf.H.{w} ((smallEtaleInverseImage B h' AddCommGrpCat.{u + 1}).obj G) ν),
      b.toAddMonoidHom.comp (smallEtaleCohomologyRestrictionMap B h _ ν) =
        (smallEtaleCohomologyRestrictionMap B h' G ν).comp a.toAddMonoidHom := by
  have := preservesFiniteLimits_smallPushforward_of_isFinite B p
  have := preservesFiniteColimits_smallPushforward_of_isFinite B p
  have : IsFinite (B.inclusion.map p') := MorphismProperty.of_isPullback sq inferInstance
  have := preservesFiniteLimits_smallPushforward_of_isFinite B p'
  have := preservesFiniteColimits_smallPushforward_of_isFinite B p'
  have := isIso_smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
    (comm_of_isPullback_inclusion sq)
  have := isIso_mateEquiv_smallEtaleAbBaseChangeInverseImageComparison_app sq G
  exact ⟨_, _, (smallEtaleAbBaseChangeInverseImageComparison B p h p' h'
      (comm_of_isPullback_inclusion sq)).extBaseChangeAddEquiv_comp_mapExtAddHom.{w}
      (smallEtaleInverseImageAdjunction B p AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageAdjunction B p' AddCommGrpCat.{u + 1})
      (smallEtaleInverseImageConstantZIso B p) (smallEtaleInverseImageConstantZIso B h)
      (smallEtaleInverseImageConstantZIso B h') G ν⟩

end Cohomology

end AlgebraicGeometry
