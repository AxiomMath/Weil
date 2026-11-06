module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyLevels
public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleHomExt

/-!
# Étale cohomology of constant sheaves along isomorphisms of schemes

An isomorphism of schemes `e : Z ≅ Z'` induces, by post-composition, an equivalence between the
small étale sites of `Z` and `Z'`, hence between their categories of abelian sheaves. This
equivalence carries the constant sheaf on an abelian group `M` to the constant sheaf on `M`, so
it identifies the étale cohomology groups `H^ν_et(Z, M)` and `H^ν_et(Z', M)`, naturally in `M`.

The file also records two identifications between spellings of the same objects: the
cohomology of the constant sheaf `ULift (ℤ/n)` as `Sheaf.H` and as
`AlgebraicGeometry.Scheme.etaleCohomologyConstant`, compatibly with the reductions
`ℤ/n' ⟶ ℤ/n`, and the base change `Stacks.Frobenius.fieldBaseChange` of a scheme over a field
as a fibre product.

## Main definitions

* `AlgebraicGeometry.Scheme.etalePostcomp`: post-composition with an étale morphism, between
  small étale sites.
* `AlgebraicGeometry.Scheme.etaleEquivalenceOfIso`: the equivalence of small étale sites
  induced by an isomorphism of schemes.
* `AlgebraicGeometry.Scheme.etaleSheafEquivalenceOfIso`: the induced equivalence of sheaf
  categories.
* `AlgebraicGeometry.Scheme.constantSheafCompEtaleSheafEquivalenceOfIso`: this equivalence
  carries constant sheaves to constant sheaves.
* `AlgebraicGeometry.Scheme.etaleCohomologyConstantAddEquivOfIso`:
  `H^ν_et(Z, M) ≃+ H^ν_et(Z', M)` for an isomorphism `Z ≅ Z'`.
* `AlgebraicGeometry.Scheme.sheafHConstantZModAddEquiv`: `Sheaf.H` of the constant sheaf
  `ULift (ℤ/n)` is `etaleCohomologyConstant Z (ℤ/n)`.

## Main results

* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists`: a sieve of the small
  étale site is covering if and only if its arrows are jointly surjective.
* `AlgebraicGeometry.Scheme.etaleCohomologyConstantAddEquivOfIso_map`: the isomorphism
  `H^ν_et(Z, M) ≃+ H^ν_et(Z', M)` is natural in `M`.
* `AlgebraicGeometry.Scheme.sheafHConstantZModAddEquiv_comp_mk₀`,
  `AlgebraicGeometry.Scheme.sheafHConstantZModAddEquiv_uliftZModPowReduction`: compatibility
  with the reductions `ℤ/n' ⟶ ℤ/n`.
* `AlgebraicGeometry.Scheme.fieldBaseChange_mk_eq_pullback`: `X_K = X ×_{Spec k} Spec K`.

## Implementation notes

Post-composition with an étale morphism is cocontinuous, because a covering of an object
`W ⟶ U` over `Z'` is also a covering over `Z` once its members are viewed over `Z` through
`U`; for an isomorphism both post-compositions are cocontinuous, so the equivalence of sites is
a dense subsite equivalence and induces an equivalence of sheaf categories. The constant sheaf
functor is left adjoint to sections over the final object, and an equivalence preserves final
objects, which gives the comparison of constant sheaves by uniqueness of adjoints. On `Ext`,
the equivalence is exact, fully faithful and preserves injective objects, so it induces
bijections (`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

namespace AlgebraicGeometry.Scheme

section Site

variable {Z Z' : Scheme.{u}}

/-- A sieve on an object `U` of the small étale site of `Z` is a covering sieve if and only if
the underlying morphisms of its arrows are jointly surjective onto `U`. -/
theorem mem_smallEtaleTopology_iff_forall_exists {U : Z.Etale} (R : Sieve U) :
    R ∈ Z.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (V : Z.Etale) (g : V ⟶ U), R g ∧ x ∈ Set.range g.left := by
  have hR : R = Sieve.ofArrows (fun p : {p : Σ V : Z.Etale, V ⟶ U // R p.2} => p.1.1)
      (fun p => p.1.2) := by
    ext W g
    rw [Sieve.mem_ofArrows_iff]
    constructor
    · intro hg
      exact ⟨⟨⟨W, g⟩, hg⟩, 𝟙 _, by simp⟩
    · rintro ⟨i, h, rfl⟩
      exact R.downward_closed i.2 h
  conv_lhs => rw [hR]
  rw [ofArrows_mem_smallEtaleTopology_iff]
  constructor
  · intro h x
    have hx : x ∈ ⋃ i : {p : Σ V : Z.Etale, V ⟶ U // R p.2}, Set.range i.1.2.left := by
      rw [h]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨i.1.1, i.1.2, i.2, hi⟩
  · intro h
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨V, g, hg, hx⟩ := h x
    exact Set.mem_iUnion.2 ⟨⟨⟨V, g⟩, hg⟩, hx⟩

/-- Post-composition with an étale morphism `f : Z ⟶ Z'`, from the small étale site of `Z` to
the small étale site of `Z'`. -/
abbrev etalePostcomp (f : Z ⟶ Z') [Etale f] : Z.Etale ⥤ Z'.Etale :=
  MorphismProperty.Over.map ⊤ (P := @Etale) (f := f) inferInstance

/-- Post-composition with an étale morphism is cocontinuous for the small étale topologies. -/
instance (f : Z ⟶ Z') [Etale f] :
    (etalePostcomp f).IsCocontinuous Z.smallEtaleTopology Z'.smallEtaleTopology where
  cover_lift {U S} hS := by
    rw [mem_smallEtaleTopology_iff_forall_exists] at hS ⊢
    intro x
    obtain ⟨W, h, hh, y, rfl⟩ := hS x
    have hw : h.left ≫ U.hom ≫ f = W.hom := MorphismProperty.Over.w h
    have hl : Etale (h.left : W.left ⟶ U.left) := inferInstance
    let V : Z.Etale := MorphismProperty.Over.mk ⊤ (h.left ≫ U.hom)
      (MorphismProperty.comp_mem _ _ _ hl U.prop)
    let g : V ⟶ U := MorphismProperty.Over.homMk h.left rfl
    refine ⟨V, g, ?_, y, rfl⟩
    let i : (etalePostcomp f).obj V ≅ W :=
      MorphismProperty.Over.isoMk (Iso.refl W.left) (by
        change 𝟙 _ ≫ W.hom = (h.left ≫ U.hom) ≫ f
        rw [Category.id_comp]
        exact hw.symm.trans (Category.assoc _ _ _).symm)
    have : (etalePostcomp f).map g = i.hom ≫ h := by
      ext
      change h.left = 𝟙 _ ≫ h.left
      rw [Category.id_comp]
    change S.arrows ((etalePostcomp f).map g)
    rw [this]
    exact S.downward_closed hh _

/-- An isomorphism of schemes `Z ≅ Z'` induces an equivalence of small étale sites, by
post-composition. -/
def etaleEquivalenceOfIso (e : Z ≅ Z') : Z.Etale ≌ Z'.Etale where
  functor := etalePostcomp e.hom
  inverse := etalePostcomp e.inv
  unitIso := NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (Iso.refl _)
    (by change 𝟙 _ ≫ (U.hom ≫ e.hom) ≫ e.inv = U.hom; simp))
  counitIso := NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (Iso.refl _)
    (by change 𝟙 _ ≫ U.hom = (U.hom ≫ e.inv) ≫ e.hom; simp))

instance (e : Z ≅ Z') : (etaleEquivalenceOfIso e).inverse.IsDenseSubsite
    Z'.smallEtaleTopology Z.smallEtaleTopology := by
  have : (etaleEquivalenceOfIso e).functor.IsCocontinuous
      Z.smallEtaleTopology Z'.smallEtaleTopology :=
    inferInstanceAs ((etalePostcomp e.hom).IsCocontinuous _ _)
  have : (etaleEquivalenceOfIso e).inverse.IsCocontinuous
      Z'.smallEtaleTopology Z.smallEtaleTopology :=
    inferInstanceAs ((etalePostcomp e.inv).IsCocontinuous _ _)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- An isomorphism of schemes `Z ≅ Z'` induces an equivalence between the categories of sheaves
on their small étale sites. -/
abbrev etaleSheafEquivalenceOfIso (e : Z ≅ Z') (A : Type*) [Category* A] :
    Sheaf Z.smallEtaleTopology A ≌ Sheaf Z'.smallEtaleTopology A :=
  (etaleEquivalenceOfIso e).sheafCongr Z.smallEtaleTopology Z'.smallEtaleTopology A

/-- The final object `Z ⟶ Z` of the small étale site of `Z`. -/
abbrev smallEtaleFinal (Z : Scheme.{u}) : Z.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Z) inferInstance

/-- The final object of the small étale site is terminal. -/
def isTerminalSmallEtaleFinal (Z : Scheme.{u}) : IsTerminal Z.smallEtaleFinal :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- The equivalence of sheaf categories induced by an isomorphism of schemes carries constant
sheaves to constant sheaves. -/
def constantSheafCompEtaleSheafEquivalenceOfIso (e : Z ≅ Z') (A : Type*) [Category* A]
    [HasWeakSheafify Z.smallEtaleTopology A] [HasWeakSheafify Z'.smallEtaleTopology A] :
    constantSheaf Z.smallEtaleTopology A ⋙ (etaleSheafEquivalenceOfIso e A).functor ≅
      constantSheaf Z'.smallEtaleTopology A :=
  ((constantSheafAdj Z.smallEtaleTopology A (isTerminalSmallEtaleFinal Z)).comp
    (etaleSheafEquivalenceOfIso e A).toAdjunction).leftAdjointUniq
    (constantSheafAdj Z'.smallEtaleTopology A
      ((isTerminalSmallEtaleFinal Z).isTerminalObj (etaleEquivalenceOfIso e).functor))

end Site

section Cohomology

/-- Composition with isomorphisms in both variables, on `Ext`. -/
def extAddEquivOfIso {C : Type*} [Category* C] [Abelian C] [HasExt.{u} C]
    {A A' M M' : C} (a : A ≅ A') (m : M ≅ M') (n : ℕ) :
    Ext.{u} A M n ≃+ Ext.{u} A' M' n where
  toFun x := (Ext.mk₀ a.inv).comp (x.comp (Ext.mk₀ m.hom) (add_zero n)) (zero_add n)
  invFun y := (Ext.mk₀ a.hom).comp (y.comp (Ext.mk₀ m.inv) (add_zero n)) (zero_add n)
  left_inv x := by
    simp only [Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_mk₀_id]
  right_inv y := by
    simp only [Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_mk₀_id]
  map_add' x y := by
    simp only [Ext.add_comp, Ext.comp_add]

/-- `extAddEquivOfIso` intertwines composition with `g` after an exact functor with
composition with `r`, when `F.map g ≫ m₂ = m₁ ≫ r`. -/
theorem extAddEquivOfIso_mapExactFunctor_comp_mk₀ {C D : Type*} [Category* C] [Abelian C]
    [Category* D] [Abelian D] [HasExt.{u} C] [HasExt.{u} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {A M₁ M₂ : C} {A' M₁' M₂' : D}
    (a : F.obj A ≅ A') (m₁ : F.obj M₁ ≅ M₁') (m₂ : F.obj M₂ ≅ M₂') (g : M₁ ⟶ M₂)
    (r : M₁' ⟶ M₂') (h : F.map g ≫ m₂.hom = m₁.hom ≫ r) {n : ℕ} (x : Ext.{u} A M₁ n) :
    extAddEquivOfIso a m₂ n ((x.comp (Ext.mk₀ g) (add_zero n)).mapExactFunctor F) =
      (extAddEquivOfIso a m₁ n (x.mapExactFunctor F)).comp (Ext.mk₀ r) (add_zero n) := by
  change (Ext.mk₀ a.inv).comp
      (((x.comp (Ext.mk₀ g) (add_zero n)).mapExactFunctor F).comp (Ext.mk₀ m₂.hom) (add_zero n))
      (zero_add n) =
    ((Ext.mk₀ a.inv).comp ((x.mapExactFunctor F).comp (Ext.mk₀ m₁.hom) (add_zero n))
      (zero_add n)).comp (Ext.mk₀ r) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, h]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

variable {Z Z' : Scheme.{0}}

/-- **Étale cohomology of a constant sheaf along an isomorphism of schemes**: an isomorphism
`e : Z ≅ Z'` induces `H^ν_et(Z, M) ≃+ H^ν_et(Z', M)`. -/
def etaleCohomologyConstantAddEquivOfIso (e : Z ≅ Z') (M : AddCommGrpCat.{0}) (ν : ℕ) :
    etaleCohomologyConstant Z M ν ≃+ etaleCohomologyConstant Z' M ν :=
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z'
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{1})
  let E := etaleSheafEquivalenceOfIso e AddCommGrpCat.{1}
  let c := constantSheafCompEtaleSheafEquivalenceOfIso e AddCommGrpCat.{1}
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  (AddEquiv.ofBijective (E.functor.mapExtAddHom _ _ ν)
    (E.functor.mapExt_bijective_of_preservesInjectiveObjects _ _ ν)).trans
    (extAddEquivOfIso (c.app _) (c.app _) ν)

/-- `etaleCohomologyConstantAddEquivOfIso` is natural in the coefficients. -/
theorem etaleCohomologyConstantAddEquivOfIso_map (e : Z ≅ Z') {M N : AddCommGrpCat.{0}}
    (g : M ⟶ N) (ν : ℕ) (x : etaleCohomologyConstant Z M ν) :
    etaleCohomologyConstantAddEquivOfIso e N ν (etaleCohomologyConstantMap Z g ν x) =
      etaleCohomologyConstantMap Z' g ν (etaleCohomologyConstantAddEquivOfIso e M ν x) := by
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z'
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{1})
  have : (etaleSheafEquivalenceOfIso e AddCommGrpCat.{1}).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have key := extAddEquivOfIso_mapExactFunctor_comp_mk₀
    (etaleSheafEquivalenceOfIso e AddCommGrpCat.{1}).functor
    ((constantSheafCompEtaleSheafEquivalenceOfIso e AddCommGrpCat.{1}).app
      (AddCommGrpCat.of (ULift.{1} ℤ)))
    ((constantSheafCompEtaleSheafEquivalenceOfIso e AddCommGrpCat.{1}).app
      (AddCommGrpCat.uliftFunctor.{1, 0}.obj M))
    ((constantSheafCompEtaleSheafEquivalenceOfIso e AddCommGrpCat.{1}).app
      (AddCommGrpCat.uliftFunctor.{1, 0}.obj N))
    ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).map
      (AddCommGrpCat.uliftFunctor.{1, 0}.map g))
    ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{1}).map
      (AddCommGrpCat.uliftFunctor.{1, 0}.map g))
    ((constantSheafCompEtaleSheafEquivalenceOfIso e AddCommGrpCat.{1}).hom.naturality
      (AddCommGrpCat.uliftFunctor.{1, 0}.map g)) x
  exact key

/-- **The level spelling of `ℤ/n`-cohomology**: `Sheaf.H` of the constant sheaf
`ULift (ℤ/n)` on `Z_et` is `etaleCohomologyConstant Z (ℤ/n)`. -/
def sheafHConstantZModAddEquiv (Z : Scheme.{0}) (n ν : ℕ) :
    letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
    letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
    Sheaf.H.{1} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.of (ULift.{1} (ZMod n)))) ν ≃+
      etaleCohomologyConstant Z (AddCommGrpCat.of (ZMod n)) ν :=
  AddEquiv.refl _

/-- The reduction `ℤ/n' ⟶ ℤ/n` for `n ∣ n'`, as a morphism of abelian groups. -/
def zmodReduction {n n' : ℕ} (h : n ∣ n') :
    AddCommGrpCat.of (ZMod n') ⟶ AddCommGrpCat.of (ZMod n) :=
  AddCommGrpCat.ofHom (ZMod.castHom h (ZMod n)).toAddMonoidHom

/-- `sheafHConstantZModAddEquiv` turns the map induced by the lifted reduction
`ULift (ℤ/n') ⟶ ULift (ℤ/n)` into `etaleCohomologyConstantMap` of the reduction. -/
theorem sheafHConstantZModAddEquiv_comp_mk₀ (Z : Scheme.{0}) {n n' : ℕ} (h : n ∣ n') (ν : ℕ)
    (x : letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
      letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
      Sheaf.H.{1} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).obj
        (AddCommGrpCat.of (ULift.{1} (ZMod n')))) ν) :
    letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
    letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
    sheafHConstantZModAddEquiv Z n ν (x.comp (Ext.mk₀
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).map
          (AddCommGrpCat.uliftFunctor.{1, 0}.map (zmodReduction h)))) (add_zero ν)) =
      etaleCohomologyConstantMap Z (zmodReduction h) ν (sheafHConstantZModAddEquiv Z n' ν x) :=
  rfl

/-- Lvl's reduction `ULift (ℤ/ℓⁿ⁺²) ⟶ ULift (ℤ/ℓⁿ⁺¹)` is the lift of `zmodReduction`. -/
theorem uliftZModPowReduction_eq (ℓ n : ℕ) :
    Weil.uliftZModPowReduction.{0} ℓ n = AddCommGrpCat.uliftFunctor.{1, 0}.map
      (zmodReduction (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))) :=
  rfl

/-- **Compatibility with lvl's transition maps**: `sheafHConstantZModAddEquiv` turns the map
induced by `Weil.uliftZModPowReduction` (the transition of `Weil.uliftZModSystem`) into
`etaleCohomologyConstantMap` of the reduction `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`. -/
theorem sheafHConstantZModAddEquiv_uliftZModPowReduction (Z : Scheme.{0}) (ℓ n ν : ℕ)
    (x : letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
      letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
      Sheaf.H.{1} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).obj
        (AddCommGrpCat.of (ULift.{1} (ZMod (ℓ ^ (n + 1 + 1)))))) ν) :
    letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Z
    letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{1})
    sheafHConstantZModAddEquiv Z (ℓ ^ (n + 1)) ν (x.comp (Ext.mk₀
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).map
          (Weil.uliftZModPowReduction.{0} ℓ n))) (add_zero ν)) =
      etaleCohomologyConstantMap Z (zmodReduction (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))) ν
        (sheafHConstantZModAddEquiv Z (ℓ ^ (n + 1 + 1)) ν x) :=
  rfl

end Cohomology

section FieldBaseChange

/-- **The geometric fibre is the pullback**: for `s₀ : S₀ ⟶ Spec κ` and a field extension
`K` of `κ`, `Stacks.Frobenius.fieldBaseChange (Over.mk s₀) K` is, by definition, the fibre
product `S₀ ×_{Spec κ} Spec K`. -/
theorem fieldBaseChange_mk_eq_pullback {κ : Type u} [Field κ] {S₀ : Scheme.{u}}
    (s₀ : S₀ ⟶ Spec (.of κ)) (K : Type u) [Field K] [Algebra κ K] :
    Stacks.Frobenius.fieldBaseChange (Over.mk s₀) K =
      pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap κ K))) :=
  rfl

/-- The identification `fieldBaseChange_mk_eq_pullback`, as an isomorphism of schemes. -/
def fieldBaseChangeMkIsoPullback {κ : Type u} [Field κ] {S₀ : Scheme.{u}}
    (s₀ : S₀ ⟶ Spec (.of κ)) (K : Type u) [Field K] [Algebra κ K] :
    Stacks.Frobenius.fieldBaseChange (Over.mk s₀) K ≅
      pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap κ K))) :=
  Iso.refl _

end FieldBaseChange

end AlgebraicGeometry.Scheme
