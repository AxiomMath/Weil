module

public import WeilFrontier.AlgebraicGeometry.Etale.RefinedTorsionStalk
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.IsoOutsideFiniteSetEquivalent
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentationPushforwardModules
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImageConstructibleFk105
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PurelyInseparableCohomologyIso
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PurelyInseparableFieldExtensionCohomologyIso
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageCohomology
public import WeilFrontier.AlgebraicGeometry.Scheme.Reduction
public import WeilFrontier.CategoryTheory.Sites.Pullback
public import WeilFrontier.Defs.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NormalizationReduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPointsSize
public import Weil.Attr

/-!
# Reduction of cohomology bound properties on curves to smooth curves over an algebraically
closed field

Let `k` be a separably closed field, `X` a scheme of finite type over `k` of dimension at most
one, and `F` a constructible abelian sheaf on the small étale site of `X` whose torsion is prime
to the characteristic exponent `p` of `k`. Then there are an algebraically closed field `k'` of the
characteristic of `k`, a smooth scheme `Y` of finite type over `k'` of dimension at most one,
affine when `X` is, and a constructible abelian sheaf `G` on `Y` with torsion prime to `p`, such
that every cohomology bound property (`fin`, or `van m` for `m ≥ 2`) holds for `F` exactly when
it holds for `G`.

The proof passes through three inverse images, each of which preserves constructibility and
torsion prime to `p` (stalks of an inverse image are stalks of the original sheaf):

1. the base change `X₁ = X ⊗_k k'` to an algebraic closure `k'` of `k`, a purely inseparable
   extension, along which étale cohomology does not change;
2. the reduction `X₂ = (X₁)_red`, along which étale cohomology does not change either;
3. the normalization `ν : Y ⟶ X₂`, which is finite, with `Y` normal of dimension at most one,
   hence smooth over the perfect field `k'`. It is an isomorphism over a dense open `V ⊆ X₂`,
   whose complement is a finite set of closed points. The unit `F₂ ⟶ ν_* ν^* F₂` is an
   isomorphism on stalks at the geometric points over `V`, so the cohomology bound properties
   of `F₂` and `ν_* ν^* F₂` agree, and `ν_*` does not change cohomology since `ν` is finite.

## Main results

* `AlgebraicGeometry.exists_smooth_cohomologyBoundProperty_holds_iff`: the reduction.

## Implementation notes

Schemes are objects of a big étale site `B`; the three schemes constructed are shown to lie
below its size cutoff. "Sections of order prime to `char k`" is
`Stacks.Torsion.IsPrimeToCharacteristicTorsion` at the characteristic exponent `ringExpChar k`:
every local section is locally killed by an integer prime to it. For constructible, hence
torsion, sheaves this is the condition on the orders of the sections over quasi-compact étale
`X`-schemes (`AlgebraicGeometry.SmallEtale.coprime_addOrderOf_of_forall_etaleStalk`). "Finite
type" is `LocallyOfFiniteType` with `QuasiCompact`; smoothness of `Y` over `k'` (`Smooth`)
includes local finite presentation.

The stalk isomorphism of the unit at a geometric point `s` over `V` is obtained without computing
the unit: the triangle identity makes its stalk a split monomorphism, the finite base change
along `V ⟶ X₂` gives an abstract isomorphism between the two stalks, and these are finite since
the sheaves are constructible.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.5, proof
  of Theorem 5.3, "Reduction to smooth curves", p. 57.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- Torsion prime to `p` is preserved by inverse image along a morphism of a big étale site:
the stalks of the inverse image are stalks of the original sheaf. -/
private theorem isPrimeToCharacteristicTorsion_smallEtaleInverseImage {S T : B.Scheme}
    (f : T ⟶ S) (p : ℕ) (F : SmallEtaleAbelianSheaf B S)
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion (SmallEtale.topology B S.obj S.property)
      p F) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion (SmallEtale.topology B T.obj T.property) p
      ((smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj F) := by
  rw [SmallEtale.isPrimeToCharacteristicTorsion_iff_forall_etaleStalk.{u, 0}] at hF ⊢
  intro t g
  let e := (smallEtaleInverseImageSheafFiberIso B f t AddCommGrpCat.{u + 1}).app F
  obtain ⟨n, hn, hnp, hng⟩ := hF (t.map (B.inclusion.map f)) (e.inv g)
  refine ⟨n, hn, hnp, ?_⟩
  have key : ∀ {A A' : AddCommGrpCat.{u + 1}} (e : A ≅ A') (g : A'), n • e.inv g = 0 →
      n • g = 0 := fun e g h => by
    have := congrArg e.hom h
    rwa [map_nsmul, map_zero, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply] at this
  exact key e g hng


private theorem geometricPoint_map_map {X Y Z : Scheme.{u}} (s : GeometricPoint X) (a : X ⟶ Y)
    (b : Y ⟶ Z) : (s.map a).map b = s.map (a ≫ b) := by
  cases s
  simp only [GeometricPoint.map, Category.assoc]

private theorem geometricPoint_mk_eq {S : Scheme.{u}} (s : GeometricPoint S)
    {h : Spec (.of s.residueField) ⟶ S} (hh : h = s.hom) :
    (⟨s.residueField, h⟩ : GeometricPoint S) = s := by
  subst hh
  rfl

/-- The stalk at the image of a geometric point of the unit `F ⟶ f_* f^* F` is a split
monomorphism. -/
private theorem exists_sheafFiber_map_unit_comp_eq_id {S T : B.Scheme} (f : T ⟶ S)
    (F : SmallEtaleAbelianSheaf B S) (t : GeometricPoint T.obj) :
    ∃ r, (geometricPointSitePoint B S.obj S.property (t.map (B.inclusion.map f))).sheafFiber.map
      ((smallEtaleInverseImageUnit B f AddCommGrpCat.{u + 1}).app F) ≫ r = 𝟙 _ := by
  let adj := smallEtaleInverseImageAdjunction B f AddCommGrpCat.{u + 1}
  let e := smallEtaleInverseImageSheafFiberIso B f t AddCommGrpCat.{u + 1}
  refine ⟨e.hom.app _ ≫ (geometricPointSitePoint B T.obj T.property t).sheafFiber.map
    (adj.counit.app ((smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj F)) ≫ e.inv.app F, ?_⟩
  rw [← Category.assoc, ← Category.assoc, e.hom.naturality]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp_assoc]
  erw [adj.left_triangle_components]
  simp

/-- An abelian group map with a left inverse between finite groups of the same cardinality is
an isomorphism. -/
private theorem isIso_of_comp_eq_id_of_finite {A A' : AddCommGrpCat.{u + 1}} (φ : A ⟶ A')
    (r : A' ⟶ A) (hr : φ ≫ r = 𝟙 _) [Finite A] (e : A ≃ A') : IsIso φ := by
  have : Finite A' := Finite.of_equiv _ e
  have hinj : Function.Injective φ := fun a b h => by
    have := congrArg r h
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hr,
      ConcreteCategory.id_apply, ConcreteCategory.id_apply] at this
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hinj.bijective_of_nat_card_le (Nat.card_congr e).ge


/-- For a cartesian square `g' ≫ f = f' ≫ g` of a big étale site with `f` finite and `f'` an
isomorphism, the stalk of `f_* H` at the image of a geometric point `t₀` of `X'` is isomorphic to
the stalk of `H` at its image in `X`. -/
private theorem nonempty_sheafFiber_smallPushforward_iso {X' X Y' Y : B.Scheme} (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] [IsIso (B.inclusion.map f')]
    (H : SmallEtaleAbelianSheaf B X) (t₀ : GeometricPoint X'.obj) :
    Nonempty ((geometricPointSitePoint B Y.obj Y.property
        ((t₀.map (B.inclusion.map f')).map (B.inclusion.map g))).sheafFiber.obj
          ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj H) ≅
      (geometricPointSitePoint B X.obj X.property
        (t₀.map (B.inclusion.map g'))).sheafFiber.obj H) := by
  have h : g' ≫ f = f' ≫ g :=
    B.inclusion.map_injective (by rw [B.inclusion.map_comp, B.inclusion.map_comp]; exact sq.w)
  have hbc := isIso_smallEtaleAbBaseChange B g' f' f g sq h
  have := universalHomeomorphism_of_isIso (B.inclusion.map f')
  have := isEquivalence_smallPushforward_of_universalHomeomorphism B f' AddCommGrpCat.{u + 1}
  let adj := smallEtaleInverseImageAdjunction B f' AddCommGrpCat.{u + 1}
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  let K := (smallEtaleInverseImage B g' AddCommGrpCat.{u + 1}).obj H
  exact ⟨((smallEtaleInverseImageSheafFiberIso B g (t₀.map (B.inclusion.map f'))
      AddCommGrpCat.{u + 1}).app _) ≪≫
    (geometricPointSitePoint B Y'.obj Y'.property (t₀.map (B.inclusion.map f'))).sheafFiber.mapIso
      (asIso ((smallEtaleAbBaseChange B g' f' f g h).natTrans.app H)) ≪≫
    ((smallEtaleInverseImageSheafFiberIso B f' t₀ AddCommGrpCat.{u + 1}).app _) ≪≫
    (geometricPointSitePoint B X'.obj X'.property t₀).sheafFiber.mapIso
      (asIso (adj.counit.app K)) ≪≫
    ((smallEtaleInverseImageSheafFiberIso B g' t₀ AddCommGrpCat.{u + 1}).app H).symm⟩

/-- The size of the base change of a scheme over a field `k` to an algebraic closure of `k` is
below the cutoff of a big étale site containing the scheme. -/
private theorem contains_pullback_algebraicClosure {X : Scheme.{u}} (hX : B.Contains X)
    (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) :
    B.Contains (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := by
  rcases isEmpty_or_nonempty X with hE | ⟨⟨x⟩⟩
  · have : IsEmpty ↥(pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) : Scheme.{u}) :=
      ⟨fun y => hE.elim (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) y)⟩
    exact (size_le_aleph0_of_isEmpty _ this).trans_lt B.aleph0_lt_cutoff
  · refine (Scheme.size_pullback_le _ _).trans_lt (max_lt hX ?_)
    rw [Scheme.size_Spec]
    refine max_lt B.aleph0_lt_cutoff ?_
    have hk : Cardinal.mk k ≤ X.size := by
      let φ : k →+* X.residueField x :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.evaluation ⊤ x trivial).hom
      exact (Cardinal.mk_le_of_injective φ.injective).trans (Scheme.residueField_size_le X x)
    have hK : Cardinal.mk (AlgebraicClosure k) ≤ max (Cardinal.mk k) Cardinal.aleph0 :=
      calc Cardinal.mk (AlgebraicClosure k)
          = Cardinal.mk { y : AlgebraicClosure k // IsAlgebraic k y } :=
            (Cardinal.mk_congr (Equiv.subtypeUnivEquiv
              fun y => Algebra.IsAlgebraic.isAlgebraic y)).symm
        _ ≤ _ := Algebraic.cardinalMk_le_max k (AlgebraicClosure k)
    exact hK.trans_lt
      (max_lt (hk.trans_lt hX) B.aleph0_lt_cutoff)

/-- **Reduction to smooth curves over an algebraically closed field** (FK I.5). Let `k` be a
separably closed field, `X` a scheme of finite type over `k` with `dim X ≤ 1`, and `F` a
constructible abelian sheaf on the small étale site of `X` whose torsion is prime to the
characteristic exponent of `k`. Then there are an algebraically closed field `k'` with
`char k' = char k`, a smooth scheme `Y` of finite type over `k'` with `dim Y ≤ 1`, affine if `X`
is affine, and a constructible abelian sheaf `G` on the small étale site of `Y` whose torsion is
prime to the characteristic exponent of `k`, such that for every cohomology bound property `P`,
`P(X, F)` holds if and only if `P(Y, G)` holds. -/
@[weil "lem_fk105_curve_reduce_to_smooth_alg_closed"]
theorem exists_smooth_cohomologyBoundProperty_holds_iff
    (X : B.Scheme) (k : Type u) [Field k] [IsSepClosed k]
    (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X.obj ≤ 1)
    (F : SmallEtaleAbelianSheaf B X) (hF : IsConstructibleAbelianSheaf B X F)
    (hp : Stacks.Torsion.IsPrimeToCharacteristicTorsion (SmallEtale.topology B X.obj X.property)
      (ringExpChar k) F) :
    ∃ (k' : Type u) (_ : Field k') (_ : IsAlgClosed k'), ringChar k' = ringChar k ∧
      ∃ (Y : B.Scheme) (g : Y.obj ⟶ Spec (.of k')), Smooth g ∧ QuasiCompact g ∧
        topologicalKrullDim Y.obj ≤ 1 ∧ (IsAffine X.obj → IsAffine Y.obj) ∧
        ∃ G : SmallEtaleAbelianSheaf B Y, IsConstructibleAbelianSheaf B Y G ∧
          Stacks.Torsion.IsPrimeToCharacteristicTorsion (SmallEtale.topology B Y.obj Y.property)
            (ringExpChar k) G ∧
          ∀ P : Sheaf.CohomologyBoundProperty, P.Holds F ↔ P.Holds G := by
  -- Step 1: base change to an algebraic closure `K` of `k`.
  let K := AlgebraicClosure k
  let φk : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let X₁ : B.Scheme := ⟨pullback f φk, contains_pullback_algebraicClosure B X.property k f⟩
  let h₁ : X₁ ⟶ X := ObjectProperty.homMk (pullback.fst f φk)
  let f₁ : X₁.obj ⟶ Spec (.of K) := pullback.snd f φk
  have sq₁ : IsPullback (B.inclusion.map h₁) f₁ f φk := IsPullback.of_hasPullback f φk
  let F₁ := (smallEtaleInverseImage B h₁ AddCommGrpCat.{u + 1}).obj F
  have hh₁ : UniversalHomeomorphism (B.inclusion.map h₁) :=
    SmallEtale.universalHomeomorphism_of_isPullback_spec k K f h₁ f₁ sq₁
  have hdim₁ : topologicalKrullDim X₁.obj ≤ 1 := by
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (MorphismProperty.universally_le _ _ hh₁.1)).le.trans hdim
  have hF₁ : IsConstructibleAbelianSheaf B X₁ F₁ := hF.smallEtaleInverseImage B h₁
  have hp₁ := isPrimeToCharacteristicTorsion_smallEtaleInverseImage B h₁ _ F hp
  have e₁ : ∀ P : Sheaf.CohomologyBoundProperty, P.Holds F ↔ P.Holds F₁ := fun P =>
    P.holds_congr (SmallEtale.cohomologyAddEquivOfIsPullbackSpec k K f h₁ f₁ sq₁ F)
  -- Step 2: passage to the reduction.
  let X₂ : B.Scheme := ⟨X₁.obj.reduction,
    Scheme.size_lt_of_isClosedImmersion X₁.obj.reductionι X₁.property⟩
  let r : X₂ ⟶ X₁ := ObjectProperty.homMk X₁.obj.reductionι
  let f₂ : X₂.obj ⟶ Spec (.of K) := X₁.obj.reductionι ≫ f₁
  let F₂ := (smallEtaleInverseImage B r AddCommGrpCat.{u + 1}).obj F₁
  have hdim₂ : topologicalKrullDim X₂.obj ≤ 1 := by
    have : IsHomeomorph X₁.obj.reductionι.base :=
      (isHomeomorph_iff_isEmbedding_surjective).2
        ⟨X₁.obj.reductionι.isClosedEmbedding.isEmbedding, X₁.obj.surjective_reductionι⟩
    exact (IsHomeomorph.topologicalKrullDim_eq _ this).le.trans hdim₁
  have hF₂ : IsConstructibleAbelianSheaf B X₂ F₂ := hF₁.smallEtaleInverseImage B r
  have hp₂ := isPrimeToCharacteristicTorsion_smallEtaleInverseImage B r _ F₁ hp₁
  have e₂ : ∀ P : Sheaf.CohomologyBoundProperty, P.Holds F₁ ↔ P.Holds F₂ := fun P =>
    P.holds_congr (SmallEtale.cohomologyAddEquivOfIsPurelyInseparable r
      (Scheme.isPurelyInseparable_reductionι X₁.obj) F₁)
  -- Step 3: normalization.
  have : IsLocallyNoetherian X₂.obj := LocallyOfFiniteType.isLocallyNoetherian f₂
  have : CompactSpace X₂.obj := QuasiCompact.compactSpace_of_compactSpace f₂
  have : IsNoetherian X₂.obj := ⟨⟩
  have hX₂ := finite_irreducibleComponents_of_locallyOfFiniteType K f₂
  let ν := X₂.obj.normalization hX₂
  let Y : B.Scheme := ⟨X₂.obj.normalizationScheme hX₂,
    (Scheme.size_normalizationScheme_le _ hX₂).trans_lt X₂.property⟩
  let νB : Y ⟶ X₂ := ObjectProperty.homMk ν
  have : IsFinite ν := isFinite_normalizationOverField K f₂
  have : IsFinite (B.inclusion.map νB) := this
  let g : Y.obj ⟶ Spec (.of K) := ν ≫ f₂
  have : IsNormal Y.obj := Scheme.isNormal_normalizationScheme X₂.obj hX₂
  have hdimY : topologicalKrullDim Y.obj ≤ 1 :=
    topologicalKrullDim_normalizationScheme_le_one hdim₂ hX₂
  have hg : Smooth g := smooth_of_isGeometricallyRegular K _
    (isGeometricallyRegular_of_isGeometricallyNormal_of_topologicalKrullDim_le_one K _ hdimY
      (isGeometricallyNormal_of_isNormal_of_perfectField K _))
  let G := (smallEtaleInverseImage B νB AddCommGrpCat.{u + 1}).obj F₂
  have hG : IsConstructibleAbelianSheaf B Y G := hF₂.smallEtaleInverseImage B νB
  have hpG := isPrimeToCharacteristicTorsion_smallEtaleInverseImage B νB _ F₂ hp₂
  have e₄ : ∀ P : Sheaf.CohomologyBoundProperty,
      P.Holds ((B.smallPushforward νB AddCommGrpCat.{u + 1}).obj G) ↔ P.Holds G := by
    have := Stacks.EtaleCohomology.hasExt_sheaf_smallEtale_succ Y.obj
    have := Stacks.EtaleCohomology.hasExt_sheaf_smallEtale_succ X₂.obj
    exact fun P => P.holds_congr (BigEtaleSite.cohomologySmallPushforwardAddEquiv νB G)
  have e₃ : ∀ P : Sheaf.CohomologyBoundProperty,
      P.Holds F₂ ↔ P.Holds ((B.smallPushforward νB AddCommGrpCat.{u + 1}).obj G) := by
    intro P
    have : Finite (irreducibleComponents X₂.obj) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    have : IsLocallyNoetherian Y.obj := LocallyOfFiniteType.isLocallyNoetherian g
    have : CompactSpace Y.obj := QuasiCompact.compactSpace_of_compactSpace g
    have : IsNoetherian Y.obj := ⟨⟩
    have : Finite (irreducibleComponents Y.obj) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    obtain ⟨V, hVd, hViso⟩ := exists_dense_open_isIso_morphismRestrict_of_isIntegralHom ν
      (Scheme.isBirational_normalization X₂.obj hX₂) (Or.inl ⟨inferInstance, inferInstance⟩)
    have : IsIso (ν ∣_ V) := hViso
    let VB := B.openObj (X := X₂) V
    let jB : VB ⟶ X₂ := B.openObjι (X := X₂) V
    let V'B := B.openObj (X := Y) (ν ⁻¹ᵁ V)
    let j'B : V'B ⟶ Y := B.openObjι (X := Y) (ν ⁻¹ᵁ V)
    let νVB : V'B ⟶ VB := ObjectProperty.homMk (ν ∣_ V)
    have sq : IsPullback (B.inclusion.map j'B) (B.inclusion.map νVB) (B.inclusion.map νB)
        (B.inclusion.map jB) := (isPullback_morphismRestrict ν V).flip
    have : IsIso (B.inclusion.map νVB) := hViso
    let φ := (smallEtaleInverseImageUnit B νB AddCommGrpCat.{u + 1}).app F₂
    have hφ₀ : ∀ t₀ : GeometricPoint V'B.obj, IsIso ((geometricPointSitePoint B X₂.obj X₂.property
        ((t₀.map (B.inclusion.map νVB)).map (B.inclusion.map jB))).sheafFiber.map φ) := by
      intro t₀
      have heq : (t₀.map (B.inclusion.map j'B)).map (B.inclusion.map νB) =
          (t₀.map (B.inclusion.map νVB)).map (B.inclusion.map jB) := by
        rw [geometricPoint_map_map, geometricPoint_map_map, sq.w]
      have hsplit := exists_sheafFiber_map_unit_comp_eq_id B νB F₂ (t₀.map (B.inclusion.map j'B))
      have hne : Nonempty ((geometricPointSitePoint B X₂.obj X₂.property
          ((t₀.map (B.inclusion.map νVB)).map (B.inclusion.map jB))).sheafFiber.obj
            ((B.smallPushforward νB AddCommGrpCat.{u + 1}).obj G) ≅
          (geometricPointSitePoint B X₂.obj X₂.property
            ((t₀.map (B.inclusion.map j'B)).map (B.inclusion.map νB))).sheafFiber.obj F₂) := by
        obtain ⟨e⟩ := nonempty_sheafFiber_smallPushforward_iso B j'B νVB νB jB sq G t₀
        exact ⟨e ≪≫ ((smallEtaleInverseImageSheafFiberIso B νB (t₀.map (B.inclusion.map j'B))
          AddCommGrpCat.{u + 1}).app F₂).symm⟩
      rw [heq] at hsplit hne
      obtain ⟨ρ, hρ⟩ := hsplit
      obtain ⟨e⟩ := hne
      have : Finite ↑((geometricPointSitePoint B X₂.obj X₂.property
          ((t₀.map (B.inclusion.map νVB)).map (B.inclusion.map jB))).sheafFiber.obj
            ((𝟭 (SmallEtaleAbelianSheaf B X₂)).obj F₂)) :=
        finite_etaleStalk_of_isConstructibleAbelianSheaf.{u, 0} B X₂ F₂ hF₂ _
      exact isIso_of_comp_eq_id_of_finite _ ρ hρ ((forget AddCommGrpCat).mapIso e.symm).toEquiv
    have hTcl : ∀ x ∈ (V : Set X₂.obj)ᶜ, IsClosed ({x} : Set X₂.obj) := fun x hx =>
      TopologicalSpace.NoetherianSpace.isClosed_singleton_of_not_mem_of_dense hdim₂ V.isOpen hVd hx
    have hTfin : ((V : Set X₂.obj)ᶜ).Finite :=
      finite_of_isClosed_of_forall_isClosed_singleton V.isOpen.isClosed_compl hTcl
    have hφ : ∀ s : GeometricPoint X₂.obj, (∀ x ∈ (V : Set X₂.obj)ᶜ, ¬ s.LiesOver x) →
        IsIso ((geometricPointSitePoint B X₂.obj X₂.property s).sheafFiber.map φ) := by
      intro s hs
      have hmem : s.hom default ∈ V := by
        by_contra hc
        exact hs _ hc rfl
      have hrange : Set.range s.hom ⊆ Set.range V.ι := by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι, Subsingleton.elim y default]
        exact hmem
      let ι : V.toScheme ⟶ (ν ⁻¹ᵁ V).toScheme := inv (ν ∣_ V)
      have hι : ι ≫ ν ∣_ V = 𝟙 _ := IsIso.inv_hom_id _
      let t₀ : GeometricPoint V'B.obj :=
        ⟨s.residueField, IsOpenImmersion.lift V.ι s.hom hrange ≫ ι⟩
      have hs₀ : (t₀.map (B.inclusion.map νVB)).map (B.inclusion.map jB) = s := by
        rw [geometricPoint_map_map]
        refine geometricPoint_mk_eq s ?_
        have h' : (IsOpenImmersion.lift V.ι s.hom hrange ≫ ι) ≫
            (ν ∣_ V ≫ V.ι) = s.hom := by
          rw [Category.assoc, reassoc_of% hι]
          exact IsOpenImmersion.lift_fac _ _ _
        exact h'
      rw [← hs₀]
      exact hφ₀ t₀
    exact cohomologyBoundProperty_holds_iff_of_isIso_sheafFiber_map_of_notMem B X₂ K f₂ φ hF₂
      (isConstructibleAbelianSheaf_smallPushforward_of_isFinite B νB G hG) _ hTfin hTcl hφ P
  refine ⟨K, inferInstance, inferInstance, ?_, Y, g, hg, inferInstance, hdimY, ?_, G, hG, hpG,
    fun P => (e₁ P).trans ((e₂ P).trans ((e₃ P).trans (e₄ P)))⟩
  · exact (Algebra.ringChar_eq k K).symm
  · intro hXa
    have : IsAffine X₁.obj := inferInstanceAs (IsAffine (pullback f φk))
    have : IsAffine X₂.obj := isAffine_of_isAffineHom X₁.obj.reductionι
    exact isAffine_of_isAffineHom ν

end AlgebraicGeometry

end
