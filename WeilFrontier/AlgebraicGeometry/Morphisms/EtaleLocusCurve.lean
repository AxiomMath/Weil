module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.RingTheory.Etale.GenericFiniteEtaleFinitePresentation
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# A finite morphism of curves in characteristic zero is étale off finitely many points

Let `f : X ⟶ Y` be a finite dominant morphism of integral schemes, with `Y` locally noetherian
and the function field of `Y` of characteristic zero. Then `f` is étale at the generic point of
`X`: over a nonempty affine open `U = Spec A` of `Y` with preimage `Spec B`, the ring `B` is a
finite `A`-algebra of finite presentation, the extension of fraction fields is algebraic, hence
separable in characteristic zero, and the generic point of `Spec B` lies in the étale locus.

The set of points at which a morphism is étale is open
(`AlgebraicGeometry.isOpen_setOf_etaleAt`). If moreover `X` is noetherian of
Krull dimension at most one, a closed subset of `X` containing no irreducible component is a
finite set of closed points. Hence the points where `f` is not étale form
a finite set of closed points. This applies to a finite dominant morphism `f : C ⟶ C'` from a
curve to a variety over a field of characteristic zero.

## Main results

* `AlgebraicGeometry.etaleAt_genericPoint_of_isFinite`: a finite dominant morphism of integral
  schemes with locally noetherian target whose function field has characteristic zero is étale
  at the generic point of the source.
* `AlgebraicGeometry.exists_finite_setOf_not_etaleAt_of_isFinite`: if moreover the source is
  noetherian of Krull dimension at most one, the morphism is étale outside a finite set of
  closed points.
* `AlgebraicGeometry.IsCurve.exists_finite_setOf_not_etaleAt_of_isFinite`: the same for a
  finite dominant morphism from a curve to a variety over a field of characteristic zero, with
  étale affine open neighbourhoods of every point outside the finite set.

## Implementation notes

Étaleness at a point is `AlgebraicGeometry.EtaleAt`: the map of coordinate rings over some
affine open neighbourhoods of the point and of its image is étale. The curve statement assumes
neither smoothness, properness, connectedness nor an algebraically closed base field, and the
target `C'` need only be a variety; `f` need not be a morphism over the base field, which enters
only through the characteristic of the function field of `C'`. Dominance is weaker than the
surjectivity of a finite surjective morphism.

## References

* [Stacks Project, Tag 0C1C](https://stacks.math.columbia.edu/tag/0C1C)
* [R. Hartshorne, *Algebraic Geometry*, IV.2][Hartshorne]
-/

@[expose] public section

open CategoryTheory Set

universe u

namespace AlgebraicGeometry

/-- A dominant morphism of irreducible schemes maps the generic point to the generic point. -/
theorem map_genericPoint_eq_genericPoint_of_isDominant {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  rw [isGenericPoint_def, ← Set.univ_subset_iff, ← f.denseRange.closure_eq]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨x, rfl⟩
  exact ((genericPoint_specializes x).map f.continuous).mem_closure

attribute [local instance] FractionRing.liftAlgebra in
/-- A finite dominant morphism of integral schemes, with locally noetherian target whose function
field has characteristic zero, is étale at the generic point of its source. -/
theorem etaleAt_genericPoint_of_isFinite {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [CharZero Y.functionField] (f : X ⟶ Y) [IsFinite f]
    [IsDominant f] : EtaleAt f (genericPoint X) := by
  set η := genericPoint X
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f η)) isOpen_univ
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨η, hηU⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  set φ := f.app U
  have hfin : φ.hom.Finite := Scheme.Hom.finite_app f U hU
  have hinj : Function.Injective φ.hom := by
    have hYfield : IsField (Y.presheaf.stalk (f η)) := by
      rw [map_genericPoint_eq_genericPoint_of_isDominant f]
      exact Field.toIsField Y.functionField
    have h2 : Function.Injective (f.stalkMap η).hom := by
      let : Field (Y.presheaf.stalk (f η)) := hYfield.toField
      exact RingHom.injective _
    have h1 : Function.Injective (Y.presheaf.germ U (f η) hηU ≫ f.stalkMap η).hom := by
      rw [CommRingCat.hom_comp]
      exact h2.comp (germ_injective_of_isIntegral Y _ hηU)
    rw [Scheme.Hom.germ_stalkMap f U η hηU, CommRingCat.hom_comp] at h1
    exact Function.Injective.of_comp h1
  algebraize [φ.hom]
  have : FaithfulSMul Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have : CharZero (FractionRing Γ(Y, U)) :=
    charZero_of_injective_ringHom
      (FractionRing.algEquiv Γ(Y, U) Y.functionField).symm.toRingHom.injective
  obtain ⟨g, hg0, hg⟩ := Stacks.GenericFiniteEtale.exists_formallyEtale_away (R := Γ(Y, U))
    (B := Γ(X, f ⁻¹ᵁ U)) (FractionRing Γ(Y, U)) (FractionRing Γ(X, f ⁻¹ᵁ U))
  have hgη : η ∈ X.basicOpen g := by
    refine ((genericPoint_spec X).mem_open_set_iff (X.basicOpen g).isOpen).mpr ?_
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hg0 (by simpa using h)
  refine ⟨X.basicOpen g, hV.basicOpen g, hgη, U, hU, X.basicOpen_le g, ?_⟩
  set W := X.basicOpen g
  have : IsLocalization.Away g Γ(X, W) := hV.isLocalization_basicOpen g
  let : Algebra Γ(Y, U) Γ(X, W) :=
    ((algebraMap Γ(X, f ⁻¹ᵁ U) Γ(X, W)).comp (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U))).toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FinitePresentation Γ(X, f ⁻¹ᵁ U) (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FinitePresentation Γ(Y, U) (Localization.Away g) :=
    Algebra.FinitePresentation.trans _ Γ(X, f ⁻¹ᵁ U) _
  have : Algebra.Etale Γ(Y, U) (Localization.Away g) := ⟨hg, inferInstance⟩
  let e : Localization.Away g ≃ₐ[Γ(Y, U)] Γ(X, W) :=
    (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, W)).restrictScalars _
  have : Algebra.Etale Γ(Y, U) Γ(X, W) := Algebra.Etale.of_equiv e
  have key : (f.appLE U W (X.basicOpen_le g)).hom = algebraMap Γ(Y, U) Γ(X, W) := rfl
  rw [key, RingHom.etale_algebraMap]
  infer_instance

/-- A finite dominant morphism `f : X ⟶ Y` of integral schemes, with `X` noetherian of Krull
dimension at most one, `Y` locally noetherian and the function field of `Y` of characteristic
zero, is étale outside a finite set `Z` of closed points of `X`; the generic point of `X` is not
in `Z`. -/
theorem exists_finite_setOf_not_etaleAt_of_isFinite {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNoetherian X] [IsLocallyNoetherian Y] [CharZero Y.functionField]
    (hX : topologicalKrullDim X ≤ 1) (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    ∃ Z : Set X, IsClosed Z ∧ Z.Finite ∧ (∀ z ∈ Z, IsClosed ({z} : Set X)) ∧
      genericPoint X ∉ Z ∧ ∀ x ∉ Z, EtaleAt f x := by
  have hη : genericPoint X ∉ {x | ¬ EtaleAt f x} := fun h =>
    h (etaleAt_genericPoint_of_isFinite f)
  have hZ : IsClosed {x | ¬ EtaleAt f x} := (isOpen_setOf_etaleAt f).isClosed_compl
  -- the only irreducible component of `X` is `X`, which contains the generic point
  have hc : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ {x | ¬ EtaleAt f x} := fun C hC hsub =>
    hη (hsub ((hC.2 (IrreducibleSpace.isIrreducible_univ X) (subset_univ C)) (mem_univ _)))
  exact ⟨_, hZ, Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hX hZ hc,
    fun z hz => Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hX hZ hc hz, hη, fun x hx => not_not.1 hx⟩

/-- **A finite morphism of curves in characteristic zero is étale off finitely many points.**
Let `k` be a field of characteristic zero, `C` a curve and `C'` a variety over `k`, and
`f : C ⟶ C'` a finite dominant morphism (for instance a finite surjective one). Then there is a
finite set `Z` of closed points of `C`, closed in `C` and missing its generic point, such that
`f` is étale at every point `x ∉ Z`, and `x` has an affine open neighbourhood `U` with
`U ⟶ C'` étale. -/
theorem IsCurve.exists_finite_setOf_not_etaleAt_of_isFinite {k : Type u} [Field k] [CharZero k]
    {C C' : Scheme.{u}} (pC : C ⟶ Spec (.of k)) (pC' : C' ⟶ Spec (.of k)) [IsCurve k pC]
    [IsVariety k pC'] (f : C ⟶ C') [IsFinite f] [IsDominant f] :
    ∃ Z : Set C, IsClosed Z ∧ Z.Finite ∧ (∀ z ∈ Z, IsClosed ({z} : Set C)) ∧
      genericPoint C ∉ Z ∧ ∀ x ∉ Z, EtaleAt f x ∧
        ∃ U : C.Opens, IsAffineOpen U ∧ x ∈ U ∧ Etale (U.ι ≫ f) := by
  have : IsLocallyNoetherian C' := LocallyOfFiniteType.isLocallyNoetherian pC'
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pC
  have : IsNoetherian C := {}
  have : CharZero C'.functionField := by
    have : Nonempty (⊤ : C'.Opens) := ⟨⟨genericPoint C', trivial⟩⟩
    let φ : k →+* C'.functionField := (C'.germToFunctionField ⊤).hom.comp
      (pC'.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    exact charZero_of_injective_ringHom φ.injective
  obtain ⟨Z, hZ, hfin, hpt, hη, hEt⟩ :=
    AlgebraicGeometry.exists_finite_setOf_not_etaleAt_of_isFinite
      (IsCurve.topologicalKrullDim_eq_one pC).le f
  refine ⟨Z, hZ, hfin, hpt, hη, fun x hx => ⟨hEt x hx, ?_⟩⟩
  obtain ⟨U, hU, hxU, h⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt f x (hEt x hx)
  exact ⟨U, hU, hxU, h⟩

end AlgebraicGeometry
