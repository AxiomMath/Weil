module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIWeightBound
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointPurityReduction
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.RationalPoincareDuality
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.TrivialRepresentationPointCount
public import Weil.LinearAlgebra.Charpoly.PointCountPositivity
public import Weil.FieldTheory.IsAlgClosed.Classification

/-!
# The Frobenius on the top cohomology of a smooth proper scheme, without a rational point

Let `X` be connected, proper and smooth of relative dimension `d` over a finite field `k` with
`q` elements, with `X_k̄` connected, and let `ℱ_1` be the ℓ-adic sheaf of the trivial
representation. This file shows that the Frobenius acts on `H^{2d}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` as
multiplication by `q^d`, without assuming that `X` has a `k`-rational point, and that `X` has
points over every extension of `k` of large enough degree ("Lang–Weil-lite").

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_representationSheaf_one`: purity of
  weight `i` of the Frobenius on `Hⁱ(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` (Deligne, Tag 03VH at the trivial
  representation).
* `Stacks.EtaleCohomology.LAdicSheaf.finrank_top_representationSheaf_one_eq_one`:
  `H^{2d}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` is a line.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalFrobenius_top_representationSheaf_one_eq_smul`: the
  Frobenius acts on it as multiplication by `q^d`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_closedPoint_residueDegree_dvd_of_frobeniusTrivialOnH0`:
  `X` has a point over every extension of `k` of large enough degree.

## Implementation notes

The three results assume
`Stacks.EtaleCohomology.LAdicSheaf.FrobeniusTrivialOnH0FieldExtension`: the Frobenius is trivial
on the line `H⁰(X'_k̄, ℱ_1 ⊗ ℚ_ℓ)` for `X' = X ×_k k'` over every finite extension `k'` of `k`
over which `X'` has a rational point. Then `H^{2d}(X'_k̄, ℱ_1)` is a line by Poincaré duality
(`LAdicSheaf.rationalFrobenius_top_representationSheaf_one_of_rationalPoint`),
and so is `H^{2d}(X_k̄, ℱ_1)`, the Frobenius of `X'` being the `[k' : k]`-th power of that of `X`.
The eigenvalue on this line is then `q^d` by positivity of point counts
(`Module.End.eq_pow_smul_id_of_isPure_of_alternating_trace_eq_natCast`): the trace formula makes
the alternating sums of traces of the powers of the Frobenius natural numbers, and purity bounds
the contribution of the degrees `i < 2d`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Purity of the Frobenius on `Hⁱ(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`** for `X` connected, smooth and proper
over `k`: Deligne's theorem (`Stacks.EtaleCohomology.LAdicSheaf.weightBound`, Tag 03VH) at the
trivial representation, whose conclusions of Deligne's conjecture hold trivially
(`Weil.hasDeligneConclusions_one`). -/
theorem LAdicSheaf.isCharpolyPureOfWeight_representationSheaf_one (hℓ : ℓ ≠ p) (X : B.Scheme)
    [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (x : GeometricPoint X.1) {r : ℕ}
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])) (i : ℤ)
    (ι : ℚ_[ℓ] →+* ℂ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) i)] :
    IsCharpolyPureOfWeight (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
        i).hom :=
  (LAdicSheaf.weightBound B ℓ kbar p q hcard hℓ X f (CompactificationOf.ofProper f) x 1 h1
    (fun ι => Weil.hasDeligneConclusions_one _ p ι r)).2 ‹_› ‹_› i ι

/-! ### The top cohomology without a rational point -/

/-- The statement that for every finite extension `k'` of `k` inside `k̄` over which
`X' = X ×_k k'` has a `k'`-rational point, the Frobenius of `X'` acts trivially on the line
`H⁰(X'_k̄, ℱ_1 ⊗ ℚ_ℓ)`, `ℱ_1` the sheaf of the trivial rank one representation of `π₁(X', x̄')`. -/
def LAdicSheaf.FrobeniusTrivialOnH0FieldExtension (X : B.Scheme) (f : X.1 ⟶ Spec (.of k))
    [IsProper f] : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k'] [Algebra k' kbar]
    [IsScalarTower k k' kbar] [CharP k' p] (q' : ℕ) (hcard' : Fintype.card k' = p ^ q')
    [IsNoetherian (fieldExtensionScheme B X f k').1]
    [ConnectedSpace (fieldExtensionScheme B X f k').1]
    (x' : GeometricPoint (fieldExtensionScheme B X f k').1)
    (h1 : Continuous (1 : EtaleFundamentalGroup (fieldExtensionScheme B X f k').1 x' →*
      GL (Fin 1) ℚ_[ℓ])),
    (∃ s : Spec (.of k') ⟶ (fieldExtensionScheme B X f k').1,
      s ≫ pullback.snd f (specAlgebraMap k k') = 𝟙 _) →
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k'))
        (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar p q' hcard'
        (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' 1 h1) 0).hom =
      LinearMap.id ∧
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar
      (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' 1 h1) 0) = 1

include hcard in
/-- **`H^{2d}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` is a line**, for `X` connected, proper and smooth of relative
dimension `d` over `k` with `X_k̄` connected, given that the Frobenius is trivial on the line
`H⁰` over the extensions of `k` where `X` acquires a rational point. For a closed point `x₀` of
`X` with residue field `k'` of degree `m + 1` over `k`, `X' = X ×_k k'` has a `k'`-rational
point, so Poincaré duality makes `H^{2d}(X'_k̄, ℱ_1)` a line; its Frobenius has the
characteristic polynomial of the `(m + 1)`-st power of that of `X` on `H^{2d}(X_k̄, ℱ_1)`, whose
degree is therefore one. -/
theorem LAdicSheaf.finrank_top_representationSheaf_one_eq_one (hℓ : ℓ ≠ p) (X : B.Scheme)
    [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hH0 : LAdicSheaf.FrobeniusTrivialOnH0FieldExtension B ℓ kbar p X f)
    (x : GeometricPoint X.1)
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) :
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
      ((2 * d : ℕ) : ℤ)) = 1 := by
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  obtain ⟨x₀, -, hx₀⟩ := IsClosed.exists_closed_singleton (X := X.1) isClosed_univ Set.univ_nonempty
  have := finite_residueField f x₀ hx₀
  let : Fintype (X.1.residueField x₀) := Fintype.ofFinite _
  let : Algebra k (X.1.residueField x₀) := (fieldToResidue f x₀).hom.toAlgebra
  have : Module.Finite k (X.1.residueField x₀) := Module.Finite.of_finite
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Module.finrank_pos (R := k) (M := X.1.residueField x₀)).ne'
  have ha := (fromSpecResidueField_comp_eq_iff f (X.1.residueField x₀) x₀ (𝟙 _)).2
    (by rw [Category.comp_id]; rfl)
  set k' := X.1.residueField x₀
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hcard' : Fintype.card k' = p ^ (q * (m + 1)) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hcard, hm, pow_mul]
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  let σ : k' →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra k' kbar := σ.toRingHom.toAlgebra
  have : IsScalarTower k k' kbar := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  have : IsAlgClosure k' kbar := ⟨inferInstance, inferInstance⟩
  have : IsNoetherian (fieldExtensionScheme B X f k').1 :=
    isNoetherian_fieldExtensionScheme B X f k'
  have : SmoothOfRelativeDimension d (pullback.snd f (specAlgebraMap k k')) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback f (specAlgebraMap k k')) ‹_›
  have hconn' : ConnectedSpace
      (fieldBaseChange (Over.mk (pullback.snd f (specAlgebraMap k k'))) kbar) :=
    Function.Surjective.connectedSpace
      (Scheme.Hom.surjective (fieldBaseChangeExtensionIso (Over.mk f) k' kbar).inv)
      (Scheme.Hom.continuous _)
  have : Surjective (specAlgebraMap k' kbar) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : ConnectedSpace (fieldExtensionScheme B X f k').1 :=
    Function.Surjective.connectedSpace
      (Scheme.Hom.surjective (fieldBaseChangeProj (Over.mk (pullback.snd f (specAlgebraMap k k')))
        kbar)) (Scheme.Hom.continuous _)
  have hpt := exists_section_fieldExtensionScheme B X f k' _ ha
  obtain ⟨x', rfl⟩ := exists_geometricPoint_map_fieldExtensionProj B X f k' x
  let φ₀ := (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').toMonoidHom
  have hφ₀ : Continuous φ₀ :=
    (etaleFundamentalGroupMap (fieldExtensionProj B X f k').hom x').continuous
  have hFD := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar
    p q hcard hℓ X f (CompactificationOf.ofProper f)
  have hFD' := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar
    p (q * (m + 1)) hcard' hℓ (fieldExtensionScheme B X f k') (pullback.snd f (specAlgebraMap k k'))
    (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k')))
  have := hFD (LAdicSheaf.representationSheaf B X (x'.map (fieldExtensionProj B X f k').hom) 1 h1)
    ((2 * d : ℕ) : ℤ)
  have := hFD' (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x'
      ((1 : EtaleFundamentalGroup X.1 (x'.map (fieldExtensionProj B X f k').hom) →*
        GL (Fin 1) ℚ_[ℓ]).comp φ₀) (h1.comp hφ₀)) ((2 * d : ℕ) : ℤ)
  have hc := LAdicSheaf.charpoly_representationSheaf_fieldExtension B ℓ kbar p q hcard X f k' hℓ m
    hcard' x' 1 h1 ((2 * d : ℕ) : ℤ)
  have key : ∀ (ρ' : EtaleFundamentalGroup (fieldExtensionScheme B X f k').1 x' →*
      GL (Fin 1) ℚ_[ℓ]) (hρ' : Continuous ρ'), ρ' = 1 →
      ∀ _ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
        (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar
        (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' ρ' hρ')
        ((2 * d : ℕ) : ℤ)),
      Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
        (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar
        (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' ρ' hρ')
        ((2 * d : ℕ) : ℤ)) = 1 := by
    rintro ρ' hρ' rfl _
    have h0 := hH0 k' (q * (m + 1)) hcard' x' hρ' hpt
    exact ((LAdicSheaf.rationalFrobenius_top_representationSheaf_one_of_rationalPoint B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k')) kbar p (q * (m + 1))
      hcard' hℓ d hpt x' hρ' h0.1).2).trans h0.2
  have hφ1 : (1 : EtaleFundamentalGroup X.1 (x'.map (fieldExtensionProj B X f k').hom) →*
      GL (Fin 1) ℚ_[ℓ]).comp φ₀ = 1 := MonoidHom.one_comp φ₀
  rw [← LinearMap.charpoly_natDegree ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X
    ℓ f (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X
      (x'.map (fieldExtensionProj B X f k').hom) 1 h1) ((2 * d : ℕ) : ℤ)).hom ^ (m + 1)), ← hc,
    LinearMap.charpoly_natDegree]
  exact key _ _ hφ1 inferInstance

include hcard in
/-- **The trace formula for `ℱ_1` of rank one, in degrees `0 ≤ i ≤ 2d`.** For `X` connected,
proper and smooth of relative dimension `d` over `k`, and `N ≥ 1`,
`∑_{i=0}^{2d} (-1)ⁱ Tr((π_X^*)^N | Hⁱ(X_k̄, ℱ_1 ⊗ ℚ_ℓ))` is the number of points of `X` over the
extension of degree `N` of `k`: the cohomology vanishes outside `[0, 2d]`. -/
theorem LAdicSheaf.sum_range_neg_one_pow_trace_pow_rationalFrobenius_representationSheaf_one
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f] (x : GeometricPoint X.1)
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) (N : ℕ)
    (hN : N ≠ 0) :
    ∑ i ∈ Finset.range (2 * d + 1), (-1 : ℚ_[ℓ]) ^ i * LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard
          (LAdicSheaf.representationSheaf B X x 1 h1) (i : ℤ)).hom ^ N) =
      ((∑ᶠ (y : closedPoints X.1) (_ : residueDegree f y.1 ∣ N), residueDegree f y.1 : ℕ) :
        ℚ_[ℓ]) := by
  have hT := LAdicSheaf.finsum_trace_pow_rationalFrobenius_representationSheaf_one B X x ℓ 1 f
    (CompactificationOf.ofProper f) kbar p q hcard hℓ N hN
  rw [one_mul] at hT
  rw [← hT]
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  have hdim : topologicalKrullDim X.1 ≤ d :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d f).le
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (2 * d + 1)).map Nat.castEmbedding),
    Finset.sum_map]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.castEmbedding_apply, Int.even_coe_nat]
    rcases Nat.even_or_odd i with hi | hi
    · simp only [hi, hi.neg_one_pow, ite_true]
      rfl
    · simp only [Nat.not_even_iff_odd.2 hi, hi.neg_one_pow, ite_false]
      rfl
  · intro i hi
    by_contra hmem
    refine hi ?_
    have hz : IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) i) := by
      rcases lt_or_ge i 0 with hneg | hnn
      · exact LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg B X ℓ f
          (CompactificationOf.ofProper f) kbar _ i hneg
      · refine LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_two_mul_lt B X ℓ
          f (CompactificationOf.ofProper f) kbar _ d hdim i ?_
        by_contra hle
        refine hmem ?_
        obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
        simp only [Finset.coe_map, Nat.castEmbedding, Set.mem_image, Finset.mem_coe,
          Finset.mem_range, Function.Embedding.coeFn_mk]
        exact ⟨n, by omega, rfl⟩
    have : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) i) :=
      ModuleCat.subsingleton_of_isZero hz
    dsimp only
    rw [show (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard
        (LAdicSheaf.representationSheaf B X x 1 h1) i).hom ^ N = 0 from
      LinearMap.ext fun _ => Subsingleton.elim _ _, map_zero, mul_zero]

/-- An embedding `ℚ_ℓ →+* ℂ` exists: `ℚ_ℓ` has at most the cardinality of the continuum. -/
theorem Padic.nonempty_ringHom_complex (ℓ : ℕ) [Fact ℓ.Prime] : Nonempty (ℚ_[ℓ] →+* ℂ) :=
  let ⟨ι, _⟩ := RingHom.exists_comp_algebraMap_eq_of_countable (K := ℚ) (L := ℚ_[ℓ])
    (Padic.cardinalMk_le_continuum ℓ) (Rat.castHom ℂ)
  ⟨ι⟩

include hcard in
/-- The family of Frobenius endomorphisms of `Hⁱ(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`, `0 ≤ i ≤ 2d`, satisfies the
hypotheses of the point count positivity lemmas: purity of weight `i` (Deligne) read along an
embedding `ι : ℚ_ℓ →+* ℂ`. -/
theorem LAdicSheaf.norm_eq_of_isRoot_charpoly_rationalFrobenius_representationSheaf_one
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f] (x : GeometricPoint X.1)
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) (ι : ℚ_[ℓ] →+* ℂ)
    (i : ℕ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) (i : ℤ))]
    (z : ℂ) (hz : ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
      (i : ℤ)).hom.charpoly.map ι).IsRoot z) :
    ‖z‖ = ((p ^ q : ℕ) : ℝ) ^ ((i : ℝ) / 2) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have h := (LAdicSheaf.isCharpolyPureOfWeight_representationSheaf_one B ℓ kbar p q hcard hℓ X f x
    h1 (i : ℤ) ι z hz).norm_eq
  rwa [Int.cast_natCast] at h

include hcard in
/-- **The Frobenius on the top cohomology of `ℱ_1`, without a rational point.** Let `X` be
connected, proper and smooth of relative dimension `d` over the finite field `k` with `p ^ q`
elements, with `X_k̄` connected, and suppose the Frobenius is trivial on the line `H⁰` over the
extensions of `k` where `X` acquires a rational point. Then `H^{2d}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` is a line
on which the Frobenius acts as multiplication by `q^d`: the alternating sums of the traces of its
powers count points, hence are natural numbers, and the eigenvalues in degree `i < 2d` are
smaller (Deligne). -/
theorem LAdicSheaf.rationalFrobenius_top_representationSheaf_one_eq_smul (hℓ : ℓ ≠ p)
    (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hH0 : LAdicSheaf.FrobeniusTrivialOnH0FieldExtension B ℓ kbar p X f)
    (x : GeometricPoint X.1)
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
      ((2 * d : ℕ) : ℤ)).hom = (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) • LinearMap.id ∧
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
      ((2 * d : ℕ) : ℤ)) = 1 := by
  have hline := LAdicSheaf.finrank_top_representationSheaf_one_eq_one B ℓ kbar p q hcard hℓ X f d
    hH0 x h1
  refine ⟨?_, hline⟩
  obtain ⟨ι⟩ := Padic.nonempty_ringHom_complex ℓ
  have hFD := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar
    p q hcard hℓ X f (CompactificationOf.ofProper f)
  have : ∀ i : ℕ, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
        (i : ℤ)) := fun i => hFD _ _
  have hQ : 1 < p ^ q := hcard ▸ Fintype.one_lt_card
  have h := Module.End.eq_pow_smul_id_of_isPure_of_alternating_trace_eq_natCast ι hQ (d := d)
    (V := fun i : ℕ => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) (i : ℤ))
    (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
      (i : ℤ)).hom)
    (fun i _ z hz => LAdicSheaf.norm_eq_of_isRoot_charpoly_rationalFrobenius_representationSheaf_one
      B ℓ kbar p q hcard hℓ X f d x h1 ι i z hz) hline
    (fun N hN => ⟨_,
      LAdicSheaf.sum_range_neg_one_pow_trace_pow_rationalFrobenius_representationSheaf_one
        B ℓ kbar p q hcard hℓ X f d x h1 N (by omega)⟩)
  rw [Nat.cast_pow]
  exact h

include hcard in
/-- **Lang–Weil-lite: `X` has points over every extension of large enough degree.** Let `X` be
connected, proper and smooth of relative dimension `d` over the finite field `k`, with `X_k̄`
connected, and suppose the Frobenius is trivial on the line `H⁰` over the extensions of `k`
where `X` acquires a rational point. Then for all large `N` some closed point of `X` has residue
degree dividing `N`, i.e. `X` has a point over the extension of degree `N` of `k`: the number of
such points is the alternating sum of the traces of `(π_X^*)^N` on `H^*(X_k̄, ℚ_ℓ)`, which is
dominated by `q^{dN}` on the line `H^{2d}`. -/
theorem LAdicSheaf.exists_closedPoint_residueDegree_dvd_of_frobeniusTrivialOnH0 (hℓ : ℓ ≠ p)
    (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hH0 : LAdicSheaf.FrobeniusTrivialOnH0FieldExtension B ℓ kbar p X f) :
    ∃ N₀, ∀ N ≥ N₀, ∃ y : closedPoints X.1, residueDegree f y.1 ∣ N := by
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  let x : GeometricPoint X.1 := X.1.algClosedPoint (Classical.arbitrary X.1)
  have h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ]) := continuous_const
  have hline := LAdicSheaf.finrank_top_representationSheaf_one_eq_one B ℓ kbar p q hcard hℓ X f d
    hH0 x h1
  obtain ⟨ι⟩ := Padic.nonempty_ringHom_complex ℓ
  have hFD := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar
    p q hcard hℓ X f (CompactificationOf.ofProper f)
  have : ∀ i : ℕ, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
        (i : ℤ)) := fun i => hFD _ _
  have hQ : 1 < p ^ q := hcard ▸ Fintype.one_lt_card
  obtain ⟨N₀, hN₀⟩ := Module.End.exists_forall_alternating_trace_pow_ne_zero_of_isPure ι hQ
    (d := d)
    (V := fun i : ℕ => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) (i : ℤ))
    (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
      (i : ℤ)).hom)
    (fun i _ z hz => LAdicSheaf.norm_eq_of_isRoot_charpoly_rationalFrobenius_representationSheaf_one
      B ℓ kbar p q hcard hℓ X f d x h1 ι i z hz) hline
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hne := hN₀ N (le_of_max_le_left hN)
  rw [LAdicSheaf.sum_range_neg_one_pow_trace_pow_rationalFrobenius_representationSheaf_one
    B ℓ kbar p q hcard hℓ X f d x h1 N (by omega)] at hne
  by_contra! hy
  refine hne ?_
  simp [hy]

end Stacks.EtaleCohomology

end
