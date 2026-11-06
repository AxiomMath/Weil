module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransitionSupplement
public import WeilFrontier.AlgebraicGeometry.FunctionField
public import WeilFrontier.Defs.AlgebraicGeometry.AffineTransitionLimit
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic

/-!
# The generic fibres of the étale neighbourhoods of the generic geometric point

Let `X` be an integral noetherian separated scheme with function field `K`, let
`η : Spec K ⟶ X` be the inclusion of the generic point, `θ : Spec K^sep ⟶ Spec K` the
separable closure and `η̄ = θ ≫ η` the generic geometric point. Let `X₀ ⊆ X` be a nonempty
affine open. Let `N` be the category of étale neighbourhoods `(U, u)` of `η̄` with `U` affine
and connected and `U ⟶ X` factoring through `X₀`, and for `(U, u)` in `N` let
`U_K = U ×_X Spec K` and `p_U = (u, θ) : Spec K^sep ⟶ U_K`.

Then `N` is cofinal in the category of all étale neighbourhoods of `η̄`, and the schemes `U_K`
with the maps `p_U` form a projective system with limit `Spec K^sep`.

The cofinality holds because a connected affine open neighbourhood of the image of `u` exists
inside any open of a locally noetherian scheme. For the limit, all `U_K` are affine, so it
suffices that `colim Γ(U_K) ⟶ K^sep` is bijective. It is surjective: an element `α` of `K^sep`
is a root of a monic polynomial over `A = Γ(X₀)` at which the derivative does not vanish, which
gives a standard étale `A`-algebra with a point over `η̄` carrying a function with value `α`.
It is injective: `Γ(U_K)` is a finite product of fields, so a function vanishing at `p_U`
vanishes on an open and closed subset `D(e) ∋ p_U` of `U_K`; since `U_K ⟶ U` is an embedding,
`D(e)` is cut out by an open of `U`, and a connected affine refinement inside that open kills
the function.

## Main definitions

* `AlgebraicGeometry.Scheme.connectedAffineNeighborhoods s X₀`: the étale neighbourhoods
  `(U, u)` of `s` with `U` affine and connected and `U ⟶ X` factoring through `X₀`.
* `AlgebraicGeometry.Scheme.neighborhoodBaseChange s y`: the diagram `(U, u) ↦ U ×_X Y`.
* `AlgebraicGeometry.Scheme.genericFibreDiagram X`, `AlgebraicGeometry.Scheme.genericFibreCone X`:
  the diagram `(U, u) ↦ U_K` and the cone `p_U : Spec K^sep ⟶ U_K`.
* `AlgebraicGeometry.Scheme.etaleNeighborhoodGenericEquiv X`: the étale neighbourhoods of the
  algebraically closed generic geometric point are those of `η̄`.

## Main results

* `AlgebraicGeometry.Scheme.initial_connectedAffineNeighborhoods_genericSepClosedPoint`: `N` is
  cofinal (its inclusion is initial).
* `AlgebraicGeometry.Scheme.nonempty_isLimit_genericFibreCone`: `Spec K^sep = lim U_K`.
* `AlgebraicGeometry.Scheme.isProjectiveSystemWithLimit_genericFibre`: over a small model of
  `N`, the `U_K` with the `p_U` form a projective system of schemes with limit `Spec K^sep`.

## Implementation notes

Étale neighbourhoods of the separably closed point `η̄` are the elements of the fibre functor of
Mathlib's point `AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site; the
accessors in `AlgebraicGeometry.Scheme.PointSmallEtale` name their components. The limit is the
spectrum of the separable closure, so the separably closed generic point is used rather than the
algebraically closed one; the two categories of étale neighbourhoods are equivalent
(`etaleNeighborhoodGenericEquiv`).

A projective system of schemes is indexed by a small category, and `N` is only essentially
small; it is replaced by `SmallModel N`, and more generally by any small cofiltered category
with an initial functor to `N` (`isProjectiveSystemWithLimit_genericFibre_of_initial`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
-/

/- FK's statement on generic fibres of a projective limit is the conjunction of the three
theorems at the end of the file. -/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- Let `ψ : K → C` be an étale ring map from a field and `φ : C → Ω` a ring map to a domain.
Then there is an idempotent `e ∈ C` with `φ e ≠ 0` killing the kernel of `φ`: `C` is a finite
product of fields and `φ` factors through the projection onto one of them. -/
theorem RingHom.Etale.exists_isIdempotentElem_mul_eq_zero {K C Ω : Type*} [Field K] [CommRing C]
    [CommRing Ω] [IsDomain Ω] {ψ : K →+* C} (hψ : ψ.Etale) (φ : C →+* Ω) :
    ∃ e : C, IsIdempotentElem e ∧ φ e ≠ 0 ∧ ∀ x, φ x = 0 → x * e = 0 := by
  algebraize [ψ]
  have : Algebra.Etale K C := hψ
  obtain ⟨I, _, A, _, _, σ, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (K := K) (A := C)).mp inferInstance
  have := Fintype.ofFinite I
  classical
  let φ' : (Π i, A i) →+* Ω := φ.comp σ.symm.toRingEquiv.toRingHom
  have hsum : ∑ i, (Pi.single i 1 : Π i, A i) = 1 := Finset.univ_sum_single 1
  obtain ⟨i₀, hi₀⟩ : ∃ i, φ' (Pi.single i 1) ≠ 0 := by
    by_contra! h
    have := congrArg φ' hsum
    simp [map_sum, h] at this
  refine ⟨σ.symm (Pi.single i₀ 1), ?_, hi₀, fun x hx => ?_⟩
  · rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one]
  · apply σ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
    by_cases h : σ x i₀ = 0
    · ext i
      by_cases hi : i = i₀
      · subst hi; simp [h]
      · simp [hi]
    · exfalso
      apply hi₀
      have : (Pi.single i₀ 1 : Π i, A i) = σ x * Pi.single i₀ (σ x i₀)⁻¹ := by
        ext i
        by_cases hi : i = i₀
        · subst hi; simp [h]
        · simp [hi]
      rw [this, map_mul]
      simp [φ', hx]


open Polynomial in
/-- Let `A` be a domain with fraction field `K`, and `α` an element of a field extension `L` of
`K`, separable over `K`. Then `α` is the image of an element of a standard étale `A`-algebra
under an `A`-algebra map to `L`. -/
theorem StandardEtalePair.exists_lift_eq {A K L : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] (α : L) (hα : IsSeparable K α) :
    ∃ (P : StandardEtalePair A) (x : L) (hx : P.HasMap x) (t : P.Ring), P.lift x hx t = α := by
  have hinjK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp hinjK
  set h := minpoly K α
  have hsep : h.Separable := hα
  have hhα : aeval α h = 0 := minpoly.aeval K α
  obtain ⟨b, hb, hH⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) h
  set H := IsLocalization.integerNormalization (nonZeroDivisors A) h
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap A K)]; exact fun e => hb0 (hinjK e)
  have hbL : algebraMap A L b ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap A L)]; exact fun e => hb0 (hinj e)
  have hh0 : h ≠ 0 := minpoly.ne_zero hα.isIntegral
  have hHmap : H.map (algebraMap A K) ≠ 0 := by
    rw [hH]; exact smul_ne_zero hb0 hh0
  have hH0 : H ≠ 0 := fun e => hHmap (by rw [e, Polynomial.map_zero])
  have hdeg : H.natDegree = h.natDegree := by
    rw [← natDegree_map_eq_of_injective hinjK, hH, natDegree_smul_of_smul_regular]
    exact fun x y e => by
      simpa [Algebra.smul_def, hbK] using e
  have hdeg1 : 1 ≤ H.natDegree := by
    rw [hdeg]; exact minpoly.natDegree_pos hα.isIntegral
  set a := H.leadingCoeff
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hH0
  have haL : algebraMap A L a ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap A L)]; exact fun e => ha0 (hinj e)
  have hHα : aeval α H = 0 := by
    rw [← aeval_map_algebraMap K, hH, ← algebraMap_smul K b h, map_smul, hhα, smul_zero]
  have hH'α : aeval α (derivative H) ≠ 0 := by
    rw [← aeval_map_algebraMap K, ← derivative_map, hH, derivative_smul,
      ← algebraMap_smul K b, map_smul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    exact mul_ne_zero hbL (hsep.aeval_derivative_ne_zero hhα)
  set f := H.integralNormalization
  set β := algebraMap A L a * α
  have hfβ : aeval β f = 0 := integralNormalization_aeval_eq_zero hHα
    (fun x hx => hinj (by rw [hx, map_zero]))
  have hcomp : f.comp (C a * X) = C a ^ (H.natDegree - 1) * H := by
    have := integralNormalization_eval₂_leadingCoeff_mul hdeg1 (C : A →+* A[X]) X
    rwa [eval₂_C_X, ← comp] at this
  have hf'β : aeval β (derivative f) ≠ 0 := by
    intro h0
    have := congrArg (fun p => aeval α (derivative p)) hcomp
    simp only [derivative_comp] at this
    simp only [derivative_mul, map_add, map_mul, derivative_C, derivative_X, aeval_C,
      mul_one, zero_mul, zero_add] at this
    rw [aeval_comp] at this
    simp only [map_mul, aeval_C, aeval_X] at this
    rw [show (algebraMap A L) a * α = β from rfl, h0, hHα, mul_zero, mul_zero, zero_add] at this
    rw [← C_pow, aeval_C, map_pow] at this
    exact mul_ne_zero (pow_ne_zero _ haL) hH'α this.symm
  let P : StandardEtalePair A :=
    ⟨f, monic_integralNormalization hH0, C a * derivative f, C a, 0, 1, by ring⟩
  have hP : P.HasMap β := ⟨hfβ, by
    simp only [P, map_mul, aeval_C]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero haL hf'β)⟩
  have hg : IsUnit (aeval P.X P.g) := IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X
  refine ⟨P, β, hP, P.X * aeval P.X (derivative f) * ↑hg.unit⁻¹, ?_⟩
  have hlg : P.lift β hP (aeval P.X P.g) = algebraMap A L a * aeval β (derivative f) := by
    rw [← aeval_algHom_apply, P.lift_X]
    simp [P]
  rw [map_mul, map_mul, ← aeval_algHom_apply, P.lift_X, map_units_inv, IsUnit.unit_spec, hlg]
  field_simp
  ring

namespace AlgebraicGeometry.Scheme.PointSmallEtale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X}

/-- The scheme underlying an étale neighbourhood `(U, u)`. -/
def scheme (e : (pointSmallEtale s).fiber.Elements) : Scheme.{u} :=
  ((CategoryOfElements.π _).obj e).left

/-- The structure morphism `U ⟶ X`. -/
def toBase (e : (pointSmallEtale s).fiber.Elements) : scheme e ⟶ X :=
  ((CategoryOfElements.π _).obj e).hom

instance (e : (pointSmallEtale s).fiber.Elements) : Etale (toBase e) :=
  ((CategoryOfElements.π _).obj e).prop

/-- The lift `u : Spec Ω ⟶ U`. -/
def point (e : (pointSmallEtale s).fiber.Elements) : Spec (.of Ω) ⟶ scheme e :=
  e.2.left

/-- The morphism of schemes underlying a morphism of étale neighbourhoods. -/
def homLeft {e e' : (pointSmallEtale s).fiber.Elements} (f : e ⟶ e') : scheme e ⟶ scheme e' :=
  ((CategoryOfElements.π _).map f).left

/-- `u ≫ π_U = s`. -/
@[reassoc (attr := simp)]
lemma point_toBase (e : (pointSmallEtale s).fiber.Elements) : point e ≫ toBase e = s :=
  Over.w e.2

/-- Morphisms of étale neighbourhoods are over `X`. -/
@[reassoc (attr := simp)]
lemma homLeft_toBase {e e' : (pointSmallEtale s).fiber.Elements} (f : e ⟶ e') :
    homLeft f ≫ toBase e' = toBase e :=
  Over.w ((CategoryOfElements.π _).map f).1

/-- Morphisms of étale neighbourhoods carry the lift to the lift. -/
@[reassoc (attr := simp)]
lemma point_homLeft {e e' : (pointSmallEtale s).fiber.Elements} (f : e ⟶ e') :
    point e ≫ homLeft f = point e' :=
  congrArg Over.Hom.left f.2

/-- `homLeft` of the identity. -/
@[simp]
lemma homLeft_id (e : (pointSmallEtale s).fiber.Elements) : homLeft (𝟙 e) = 𝟙 _ := rfl

/-- `homLeft` of a composite. -/
@[simp]
lemma homLeft_comp {e e' e'' : (pointSmallEtale s).fiber.Elements} (f : e ⟶ e') (g : e' ⟶ e'') :
    homLeft (f ≫ g) = homLeft f ≫ homLeft g := rfl


/-- The image of the lift `u` lies in any open containing its point. -/
lemma range_point_subset (e : (pointSmallEtale s).fiber.Elements) (V : (scheme e).Opens)
    (hV : point e default ∈ V) : Set.range (point e) ⊆ Set.range V.ι := by
  rintro _ ⟨a, rfl⟩
  have : Subsingleton (Spec (.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  rw [Subsingleton.elim (α := Spec (.of Ω)) a default, V.range_ι]
  exact hV

/-- The restriction of an étale neighbourhood `(U, u)` to an open `V ⊆ U` containing the image
of `u`. -/
def restrict (e : (pointSmallEtale s).fiber.Elements) (V : (scheme e).Opens)
    (hV : point e default ∈ V) : (pointSmallEtale s).fiber.Elements :=
  Functor.elementsMk _ (Etale.mk (V.ι ≫ toBase e))
    (Over.homMk (IsOpenImmersion.lift V.ι (point e) (range_point_subset e V hV)) (by
      change IsOpenImmersion.lift V.ι (point e) _ ≫ V.ι ≫ toBase e = s
      rw [IsOpenImmersion.lift_fac_assoc, point_toBase]))

/-- The morphism from the restriction of an étale neighbourhood to an open. -/
def restrictHom (e : (pointSmallEtale s).fiber.Elements) (V : (scheme e).Opens)
    (hV : point e default ∈ V) : restrict e V hV ⟶ e :=
  ⟨MorphismProperty.Over.homMk V.ι rfl (by simp), by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _⟩

/-- The scheme underlying a restriction. -/
lemma scheme_restrict (e : (pointSmallEtale s).fiber.Elements) (V : (scheme e).Opens)
    (hV : point e default ∈ V) : scheme (restrict e V hV) = V.toScheme := rfl

/-- The structure morphism of a restriction. -/
lemma toBase_restrict (e : (pointSmallEtale s).fiber.Elements) (V : (scheme e).Opens)
    (hV : point e default ∈ V) : toBase (restrict e V hV) = V.ι ≫ toBase e := rfl

/-- The morphism underlying `restrictHom` is the open immersion. -/
lemma homLeft_restrictHom (e : (pointSmallEtale s).fiber.Elements) (V : (scheme e).Opens)
    (hV : point e default ∈ V) : homLeft (restrictHom e V hV) = V.ι := rfl

end AlgebraicGeometry.Scheme.PointSmallEtale

namespace AlgebraicGeometry.Scheme

open PointSmallEtale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
variable {Y : Scheme.{u}} (y : Y ⟶ X)

/-- The diagram `(U, u) ↦ U ×_X Y` on the étale neighbourhoods of `s`, for a morphism
`y : Y ⟶ X`. -/
@[simps]
def neighborhoodBaseChange :
    (pointSmallEtale s).fiber.Elements ⥤ Scheme.{u} where
  obj e := pullback (toBase e) y
  map f := pullback.map _ _ _ _ (homLeft f) (𝟙 Y) (𝟙 X) (by simp) (by simp)
  map_id e := by ext <;> simp
  map_comp f g := by ext <;> simp [pullback.map]

variable {s} in
/-- The cone `(u, θ) : Spec Ω ⟶ U ×_X Y` over `neighborhoodBaseChange s y`, for a
factorisation `s = θ ≫ y`. -/
@[simps]
def neighborhoodBaseChangeCone (θ : Spec (.of Ω) ⟶ Y) (h : θ ≫ y = s) :
    Cone (neighborhoodBaseChange s y) where
  pt := Spec (.of Ω)
  π :=
    { app e := pullback.lift (point e) θ (by simp [h])
      naturality {e e'} f := by apply pullback.hom_ext <;> simp [pullback.map] }

/-- In a locally noetherian scheme every open neighbourhood of a point contains a connected
affine open neighbourhood of it. -/
theorem exists_isAffineOpen_connected {Y : Scheme.{u}} [IsLocallyNoetherian Y] (W : Y.Opens)
    (y : Y) (hy : y ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ V ≤ W ∧ y ∈ V ∧ _root_.IsConnected (V : Set Y) := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV₀, hV₀W⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
  have := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  have : TopologicalSpace.NoetherianSpace V₀ := noetherianSpace_of_isAffineOpen V₀ hV₀
  let y' : V₀ := ⟨y, hyV₀⟩
  let Zs := {Z ∈ irreducibleComponents V₀ | y' ∉ Z}
  have hZs : Zs.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset
    (fun Z hZ => hZ.1)
  let O' : Set V₀ := (⋃ Z ∈ Zs, Z)ᶜ
  have hO' : IsOpen O' := by
    exact (hZs.isClosed_biUnion fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  have hyO' : y' ∈ O' := by
    intro h
    obtain ⟨Z, hZ, h⟩ := Set.mem_iUnion₂.mp h
    exact hZ.2 h
  let O : Set Y := Subtype.val '' O'
  have hO : IsOpen O := V₀.isOpen.isOpenMap_subtype_val _ hO'
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (show y ∈ O from ⟨y', hyO', rfl⟩) hO
  have hVV₀ : (V : Set Y) ⊆ V₀ := fun z hz => by
    obtain ⟨z', -, rfl⟩ := hVO hz; exact z'.2
  refine ⟨V, hV, fun z hz => hV₀W (hVV₀ hz), hyV, ⟨y, hyV⟩, ?_⟩
  refine isPreconnected_of_forall y fun z hz => ?_
  let z' : V₀ := ⟨z, hVV₀ hz⟩
  let Z := _root_.irreducibleComponent z'
  have hZ : Z ∈ irreducibleComponents V₀ := irreducibleComponent_mem_irreducibleComponents z'
  have hyZ : y' ∈ Z := by
    by_contra h
    obtain ⟨w, hw, hwz⟩ := hVO hz
    have : w = z' := Subtype.ext hwz
    subst this
    exact hw (Set.mem_biUnion (x := Z) ⟨hZ, h⟩ (mem_irreducibleComponent))
  have hirr : IsIrreducible (Subtype.val '' Z : Set Y) :=
    (isIrreducible_irreducibleComponent).image _ continuous_subtype_val.continuousOn
  refine ⟨(V : Set Y) ∩ Subtype.val '' Z, Set.inter_subset_left, ⟨hyV, y', hyZ, rfl⟩,
    ⟨hz, z', mem_irreducibleComponent, rfl⟩, ?_⟩
  refine IsPreirreducible.isPreconnected ?_
  intro u v hu hv ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := hirr.2 ((V : Set Y) ∩ u) ((V : Set Y) ∩ v) (V.isOpen.inter hu)
    (V.isOpen.inter hv) ⟨a, ha.1.2, ha.1.1, ha.2⟩ ⟨b, hb.1.2, hb.1.1, hb.2⟩
  exact ⟨c, ⟨hc.2.1.1, hc.1⟩, hc.2.1.2, hc.2.2.2⟩


variable (X₀ : X.Opens)

/-- The étale neighbourhoods `(U, u)` of `s` with `U` affine and connected and `U ⟶ X`
factoring through the open `X₀`. -/
def connectedAffineNeighborhoods : ObjectProperty (pointSmallEtale s).fiber.Elements :=
  fun e => IsAffine (scheme e) ∧ ConnectedSpace (scheme e) ∧ Set.range (toBase e) ⊆ X₀

variable {s X₀}

/-- Every étale neighbourhood `(U, u)` of `s`, with `s` lying in `X₀`, is refined by a
connected affine one inside any given open neighbourhood of the image of `u`. -/
theorem exists_connectedAffineNeighborhoods_hom [IsLocallyNoetherian X]
    (hs : s default ∈ X₀) (e : (pointSmallEtale s).fiber.Elements) (W : (scheme e).Opens)
    (hW : point e default ∈ W) :
    ∃ (e' : (pointSmallEtale s).fiber.Elements) (f : e' ⟶ e),
      connectedAffineNeighborhoods s X₀ e' ∧ Set.range (homLeft f) ⊆ W := by
  have : IsLocallyNoetherian (scheme e) := LocallyOfFiniteType.isLocallyNoetherian (toBase e)
  have hx : point e default ∈ W ⊓ toBase e ⁻¹ᵁ X₀ := by
    refine ⟨hW, ?_⟩
    change (point e ≫ toBase e) default ∈ X₀
    rwa [point_toBase]
  obtain ⟨V, hV, hVW, hxV, hVc⟩ := exists_isAffineOpen_connected _ _ hx
  refine ⟨PointSmallEtale.restrict e V hxV, restrictHom e V hxV, ⟨hV, ?_, ?_⟩, ?_⟩
  · exact isConnected_iff_connectedSpace.mp hVc
  · rintro _ ⟨a, rfl⟩
    exact (hVW a.2).2
  · rintro _ ⟨a, rfl⟩
    exact (hVW a.2).1


/-- The connected affine étale neighbourhoods of `s` over `X₀` are cofinal (the inclusion is
initial). -/
theorem initial_connectedAffineNeighborhoods_ι [IsLocallyNoetherian X] (hs : s default ∈ X₀) :
    (connectedAffineNeighborhoods s X₀).ι.Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun e => by
    obtain ⟨e', f, he', -⟩ := exists_connectedAffineNeighborhoods_hom hs e ⊤ trivial
    exact ⟨⟨e', he'⟩, ⟨f⟩⟩

/-- The connected affine étale neighbourhoods of `s` over `X₀` form a cofiltered category. -/
theorem isCofiltered_connectedAffineNeighborhoods [IsLocallyNoetherian X] (hs : s default ∈ X₀) :
    IsCofiltered (connectedAffineNeighborhoods s X₀).FullSubcategory :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (connectedAffineNeighborhoods s X₀).ι
    fun e => by
      obtain ⟨e', f, he', -⟩ := exists_connectedAffineNeighborhoods_hom hs e ⊤ trivial
      exact ⟨⟨e', he'⟩, ⟨f⟩⟩

variable (s X₀) in
/-- Every connected affine étale neighbourhood comes from the small affine étale site. -/
theorem connectedAffineNeighborhoods_le_essImage :
    connectedAffineNeighborhoods s X₀ ≤
      (Functor.Elements.precomp (AffineEtale.Spec X) (pointSmallEtale s).fiber).essImage := by
  rintro e ⟨he, -, -⟩
  let A : X.AffineEtale := AffineEtale.mk ((scheme e).isoSpec.inv ≫ toBase e)
  let x : ((AffineEtale.Spec X) ⋙ (pointSmallEtale s).fiber).obj A :=
    Over.homMk (point e ≫ (scheme e).isoSpec.hom) (by
      change (point e ≫ (scheme e).isoSpec.hom) ≫ (scheme e).isoSpec.inv ≫ toBase e = s
      simp)
  refine ⟨Functor.elementsMk _ A x, ⟨CategoryOfElements.isoMk _ _
    (MorphismProperty.Over.isoMk (scheme e).isoSpec.symm rfl) ?_⟩⟩
  apply Over.OverMorphism.ext
  change (point e ≫ (scheme e).isoSpec.hom) ≫ (scheme e).isoSpec.inv = point e
  simp

/-- The category of connected affine étale neighbourhoods is essentially small. -/
instance essentiallySmall_connectedAffineNeighborhoods :
    EssentiallySmall.{u} (connectedAffineNeighborhoods s X₀).FullSubcategory := by
  have : ObjectProperty.EssentiallySmall.{u} (connectedAffineNeighborhoods s X₀) :=
    ObjectProperty.EssentiallySmall.of_le (connectedAffineNeighborhoods_le_essImage s X₀)
  infer_instance


/-- A global section whose basic open is everything is a unit. -/
private theorem isUnit_of_basicOpen_eq_top' {Z : Scheme} (f : Γ(Z, ⊤)) (hf : Z.basicOpen f = ⊤) :
    IsUnit f := by
  have key : ∀ (V : Z.Opens) (_ : V = ⊤) (h : V ≤ ⊤),
      IsUnit (Z.presheaf.map (homOfLE h).op f) → IsUnit f := by
    rintro V rfl h hu
    simpa using hu
  exact key _ hf (Z.basicOpen_le f) (Z.toRingedSpace.isUnit_res_basicOpen f)

section GenericPoint

open Stacks.EtaleCohomology

variable (X) [IsIntegral X]

/-- The generic geometric point lies in every nonempty open. -/
lemma genericSepClosedPoint_default_mem (X₀ : X.Opens) (hX₀ : (X₀ : Set X).Nonempty) :
    genericSepClosedPoint X default ∈ X₀ := by
  rw [genericSepClosedPoint_apply]
  exact ((genericPoint_spec X).mem_open_set_iff X₀.isOpen).mpr (by simpa using hX₀)

instance isPreimmersion_genericPointInclusion : IsPreimmersion (genericPointInclusion X) :=
  inferInstanceAs (IsPreimmersion (X.fromSpecStalk (genericPoint X)))

/-- The diagram `(U, u) ↦ U_K = U ×_X Spec K` on étale neighbourhoods of the generic geometric
point. -/
abbrev genericFibreDiagram :
    (pointSmallEtale (genericSepClosedPoint X)).fiber.Elements ⥤ Scheme.{u} :=
  neighborhoodBaseChange (genericSepClosedPoint X) (genericPointInclusion X)

/-- The cone `p_U = (u, θ) : Spec K^sep ⟶ U_K` over `genericFibreDiagram`. -/
abbrev genericFibreCone : Cone (genericFibreDiagram X) :=
  neighborhoodBaseChangeCone (genericPointInclusion X) (separableClosureι X.functionField)
    (genericSepClosedPoint_eq X).symm

/-- The étale neighbourhoods of the algebraically closed generic geometric point
`Spec K̄ ⟶ X` are the étale neighbourhoods of the separably closed one `η̄ : Spec K^sep ⟶ X`. -/
def etaleNeighborhoodGenericEquiv :
    GeometricPoint.EtaleNeighborhood (genericGeometricPoint X) ≌
      (pointSmallEtale (genericSepClosedPoint X)).fiber.Elements :=
  (GeometricPoint.EtaleNeighborhood.equivFiberElements _).trans
    (Cat.equivOfIso (Functor.elementsFunctor.mapIso
      { hom := (pointSmallEtaleGenericIso X).inv.hom
        inv := (pointSmallEtaleGenericIso X).hom.hom
        hom_inv_id := congrArg GrothendieckTopology.Point.Hom.hom
          (pointSmallEtaleGenericIso X).hom_inv_id
        inv_hom_id := congrArg GrothendieckTopology.Point.Hom.hom
          (pointSmallEtaleGenericIso X).inv_hom_id }))

variable {X}

/-- A section of the generic fibre `U_K` of an étale neighbourhood, with `U_K` affine, which
vanishes at the generic geometric point vanishes on the generic fibre of a connected affine
refinement. -/
theorem exists_connectedAffineNeighborhoods_hom_appTop_eq_zero [IsLocallyNoetherian X]
    {X₀ : X.Opens} (hX₀ : (X₀ : Set X).Nonempty)
    (e : (pointSmallEtale (genericSepClosedPoint X)).fiber.Elements)
    [IsAffine (pullback (toBase e) (genericPointInclusion X))]
    (c : Γ(pullback (toBase e) (genericPointInclusion X), ⊤))
    (hc : ((genericFibreCone X).π.app e).appTop c = 0) :
    ∃ (e' : (pointSmallEtale (genericSepClosedPoint X)).fiber.Elements) (f : e' ⟶ e),
      connectedAffineNeighborhoods (genericSepClosedPoint X) X₀ e' ∧
      ((genericFibreDiagram X).map f).appTop c = 0 := by
  let π : Spec (.of (SeparableClosure X.functionField)) ⟶
      pullback (toBase e) (genericPointInclusion X) := (genericFibreCone X).π.app e
  let ψ : X.functionField →+* Γ(pullback (toBase e) (genericPointInclusion X), ⊤) :=
    (pullback.snd (toBase e) (genericPointInclusion X)).appTop.hom.comp
      (Scheme.ΓSpecIso X.functionField).inv.hom
  have hψ : ψ.Etale := by
    have := HasRingHomProperty.appTop @Etale (pullback.snd (toBase e) (genericPointInclusion X))
      inferInstance
    exact RingHom.Etale.respectsIso.2 _
      (Scheme.ΓSpecIso X.functionField).symm.commRingCatIsoToRingEquiv this
  let φ : Γ(pullback (toBase e) (genericPointInclusion X), ⊤) →+*
      SeparableClosure X.functionField :=
    (Scheme.ΓSpecIso (.of (SeparableClosure X.functionField))).hom.hom.comp π.appTop.hom
  obtain ⟨e₀, -, he₀, hker⟩ := hψ.exists_isIdempotentElem_mul_eq_zero φ
  have hce : c * e₀ = 0 := hker _ ((congrArg (Scheme.ΓSpecIso _).hom.hom hc).trans (map_zero _))
  have hπ : π ⁻¹ᵁ (pullback (toBase e) (genericPointInclusion X)).basicOpen e₀ = ⊤ := by
    rw [Scheme.preimage_basicOpen π e₀]
    refine Scheme.basicOpen_of_isUnit _ ?_
    have h2 := (isUnit_iff_ne_zero.mpr he₀).map
      (Scheme.ΓSpecIso (.of (SeparableClosure X.functionField))).inv.hom
    simpa [φ] using h2
  have hξ : π default ∈ (pullback (toBase e) (genericPointInclusion X)).basicOpen e₀ := by
    change default ∈ π ⁻¹ᵁ (pullback (toBase e) (genericPointInclusion X)).basicOpen e₀
    rw [hπ]; trivial
  obtain ⟨W, hW, hWe⟩ :=
    ((pullback.fst (toBase e) (genericPointInclusion X)).isEmbedding.isInducing.isOpen_iff).mp
      ((pullback (toBase e) (genericPointInclusion X)).basicOpen e₀).isOpen
  have hπfst : π ≫ pullback.fst (toBase e) (genericPointInclusion X) = point e :=
    pullback.lift_fst _ _ _
  have hxW : point e default ∈ W := by
    have : π default ∈ (pullback.fst (toBase e) (genericPointInclusion X)) ⁻¹' W := by
      rw [hWe]; exact hξ
    rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, hπfst] at this
  obtain ⟨e', f, he', hf⟩ := exists_connectedAffineNeighborhoods_hom
    (genericSepClosedPoint_default_mem X X₀ hX₀) e ⟨W, hW⟩ hxW
  refine ⟨e', f, he', ?_⟩
  let g : pullback (toBase e') (genericPointInclusion X) ⟶
      pullback (toBase e) (genericPointInclusion X) := (genericFibreDiagram X).map f
  have hg : (pullback (toBase e') (genericPointInclusion X)).basicOpen (g.appTop e₀) = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    change z ∈ (pullback (toBase e') (genericPointInclusion X)).basicOpen (g.app ⊤ e₀)
    rw [← Scheme.preimage_basicOpen g e₀]
    change g z ∈ ((pullback (toBase e) (genericPointInclusion X)).basicOpen e₀ : Set _)
    rw [← hWe]
    have : g ≫ pullback.fst (toBase e) (genericPointInclusion X) =
        pullback.fst (toBase e') (genericPointInclusion X) ≫ homLeft f :=
      pullback.lift_fst _ _ _
    change (g ≫ pullback.fst (toBase e) (genericPointInclusion X)) z ∈ W
    rw [this]
    exact hf ⟨_, rfl⟩
  have hu := isUnit_of_basicOpen_eq_top' _ hg
  have : g.appTop c * g.appTop e₀ = 0 := by rw [← map_mul, hce, map_zero]
  exact (hu.mul_left_eq_zero).mp this


/-- `Spec K ⟶ X` factors through any nonempty affine open `X₀` as `Spec K ⟶ Spec Γ(X₀) ⟶ X`. -/
lemma genericPointInclusion_eq_fromSpec {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀) [Nonempty X₀] :
    genericPointInclusion X = Spec.map (X.germToFunctionField X₀) ≫ hX₀.fromSpec := by
  change X.fromSpecStalk (genericPoint X) = _
  rw [← hX₀.fromSpecStalk_eq_fromSpecStalk]
  rfl

/-- Every element of `K^sep` is the value at the generic geometric point of a function on an
affine étale neighbourhood factoring through `X₀`. -/
theorem exists_neighborhood_appTop_eq {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀) [Nonempty X₀]
    (α : SeparableClosure X.functionField) :
    ∃ (e : (pointSmallEtale (genericSepClosedPoint X)).fiber.Elements) (t : Γ(scheme e, ⊤)),
      (point e).appTop t = (Scheme.ΓSpecIso (.of (SeparableClosure X.functionField))).inv α := by
  let A := Γ(X, X₀)
  have : IsFractionRing A X.functionField := functionField_isFractionRing_of_isAffineOpen X X₀ hX₀
  let _ : Algebra A (SeparableClosure X.functionField) :=
    ((algebraMap X.functionField (SeparableClosure X.functionField)).comp
      (algebraMap A X.functionField)).toAlgebra
  have : IsScalarTower A X.functionField (SeparableClosure X.functionField) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨P, x, hx, t, ht⟩ := StandardEtalePair.exists_lift_eq (A := A) α
    (Algebra.IsSeparable.isSeparable X.functionField α)
  let ℓ : P.Ring →+* SeparableClosure X.functionField := (P.lift x hx).toRingHom
  let j : Spec (.of P.Ring) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))
  have : Etale j := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale A P.Ring)))
  let p : Spec (.of (SeparableClosure X.functionField)) ⟶ Spec (.of P.Ring) :=
    Spec.map (CommRingCat.ofHom ℓ)
  have hp : p ≫ j ≫ hX₀.fromSpec = genericSepClosedPoint X := by
    rw [genericSepClosedPoint_eq, genericPointInclusion_eq_fromSpec hX₀, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (P.lift x hx).commutes r
  refine ⟨Functor.elementsMk _ (Etale.mk (j ≫ hX₀.fromSpec)) (Over.homMk p hp),
    (Scheme.ΓSpecIso (.of P.Ring)).inv t, ?_⟩
  change p.appTop ((Scheme.ΓSpecIso (.of P.Ring)).inv t) = _
  rw [← ht]
  exact (congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ℓ))).symm


variable [IsNoetherian X] [X.IsSeparated]

/-- The generic fibre of a connected affine étale neighbourhood is affine. -/
instance isAffine_pullback_toBase
    (e : (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).FullSubcategory) :
    IsAffine (pullback (toBase e.obj) (genericPointInclusion X)) := by
  have := e.property.1
  have : IsAffineHom (toBase e.obj ≫ terminal.from X) := by
    rw [terminal.comp_from]; exact isAffineHom_of_isAffine _
  have : IsAffineHom (toBase e.obj) := IsAffineHom.of_comp _ (terminal.from X)
  have : IsAffineHom (pullback.snd (toBase e.obj) (genericPointInclusion X)) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  exact isAffine_of_isAffineHom (pullback.snd (toBase e.obj) (genericPointInclusion X))

/-- The generic fibre of a connected affine étale neighbourhood is noetherian. -/
instance isNoetherian_pullback_toBase
    (e : (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).FullSubcategory) :
    IsNoetherian (pullback (toBase e.obj) (genericPointInclusion X)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (toBase e.obj) (genericPointInclusion X))
  exact {}

variable (X₀) in
/-- The colimit of the rings `Γ(U_K)` over the connected affine étale neighbourhoods is
`Γ(Spec K^sep)`, at the level of types. -/
def isColimitForgetΓGenericFibreCone (hX₀ : IsAffineOpen X₀) [Nonempty X₀] :
    IsColimit ((CategoryTheory.forget CommRingCat).mapCocone (Scheme.Γ.mapCocone
      ((genericFibreCone X).whisker (connectedAffineNeighborhoods _ X₀).ι).op)) := by
  have hne : (X₀ : Set X).Nonempty := Set.nonempty_coe_sort.mp ‹_›
  have := isCofiltered_connectedAffineNeighborhoods (genericSepClosedPoint_default_mem X X₀ hne)
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i a b hab => ?_)
  · obtain ⟨e, t, ht⟩ := exists_neighborhood_appTop_eq hX₀
      ((Scheme.ΓSpecIso (.of (SeparableClosure X.functionField))).hom x)
    obtain ⟨e', f, he', -⟩ := exists_connectedAffineNeighborhoods_hom
      (genericSepClosedPoint_default_mem X X₀ hne) e ⊤ trivial
    refine ⟨op ⟨e', he'⟩,
      (pullback.fst (toBase e') (genericPointInclusion X)).appTop ((homLeft f).appTop t), ?_⟩
    have h1 : (genericFibreCone X).π.app e' ≫ pullback.fst (toBase e') (genericPointInclusion X) ≫
        homLeft f = point e := by
      rw [← Category.assoc, show (genericFibreCone X).π.app e' ≫ pullback.fst _ _ = point e' from
        pullback.lift_fst _ _ _, point_homLeft]
    have h2 := congrArg (fun g => g.appTop.hom t) h1
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
    change x = ((genericFibreCone X).π.app e').appTop.hom
      ((pullback.fst (toBase e') (genericPointInclusion X)).appTop.hom ((homLeft f).appTop.hom t))
    refine Eq.symm (h2.trans (ht.trans ?_))
    exact (Scheme.ΓSpecIso _).hom_inv_id_apply x
  · obtain ⟨e', f, he', hf⟩ := exists_connectedAffineNeighborhoods_hom_appTop_eq_zero hne
      i.unop.obj (a - b) (by
        change ((genericFibreCone X).π.app i.unop.obj).appTop.hom (a - b) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr hab)
    refine ⟨op ⟨e', he'⟩, (ObjectProperty.homMk f : (⟨e', he'⟩ : (connectedAffineNeighborhoods
      _ X₀).FullSubcategory) ⟶ i.unop).op, ?_⟩
    change ((genericFibreDiagram X).map f).appTop.hom a =
      ((genericFibreDiagram X).map f).appTop.hom b
    rw [← sub_eq_zero, ← map_sub]
    exact hf

variable (X₀) in
/-- Along any initial functor from a small cofiltered category, the cone
`p_U : Spec K^sep ⟶ U_K` over the connected affine étale neighbourhoods is a limit cone. -/
def isLimitGenericFibreConeWhisker (hX₀ : IsAffineOpen X₀) [Nonempty X₀] {J : Type u}
    [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).FullSubcategory)
    [F.Initial] :
    IsLimit (((genericFibreCone X).whisker (connectedAffineNeighborhoods _ X₀).ι).whisker F) := by
  have (j : J) : IsAffine
      ((F ⋙ (connectedAffineNeighborhoods _ X₀).ι ⋙ genericFibreDiagram X).obj j) :=
    isAffine_pullback_toBase (F.obj j)
  have h1 := isColimitForgetΓGenericFibreCone X₀ hX₀
  have h2 : IsColimit ((CategoryTheory.forget CommRingCat).mapCocone (Scheme.Γ.mapCocone
      ((((genericFibreCone X).whisker (connectedAffineNeighborhoods _ X₀).ι).whisker F).op))) :=
    IsColimit.ofIsoColimit ((Functor.Final.isColimitWhiskerEquiv F.op _).symm h1)
      (Cocone.ext (Iso.refl _))
  have : ReflectsFilteredColimits (CategoryTheory.forget CommRingCat) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have : IsAffine (((genericFibreCone X).whisker
      (connectedAffineNeighborhoods _ X₀).ι).whisker F).pt :=
    inferInstanceAs (IsAffine (Spec (.of (SeparableClosure X.functionField))))
  exact isLimitOfIsColimitΓ _ _ (isColimitOfReflects (CategoryTheory.forget CommRingCat) h2)

variable (X₀) in
/-- Along any initial functor from a small cofiltered category, the generic fibres `U_K` of the
connected affine étale neighbourhoods `(U, u)` of the generic geometric point, with the maps
`p_U = (u, θ)`, form a projective system of schemes with limit `Spec K^sep`. -/
theorem isProjectiveSystemWithLimit_genericFibre_of_initial (hX₀ : IsAffineOpen X₀)
    [Nonempty X₀] {J : Type u} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).FullSubcategory)
    [F.Initial] :
    IsProjectiveSystemWithLimit (F ⋙ (connectedAffineNeighborhoods _ X₀).ι ⋙ genericFibreDiagram X)
      (((genericFibreCone X).whisker (connectedAffineNeighborhoods _ X₀).ι).whisker F) := by
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom
      ((F ⋙ (connectedAffineNeighborhoods _ X₀).ι ⋙ genericFibreDiagram X).map f) :=
    fun f => @isAffineHom_of_isAffine _ _ _ (isAffine_pullback_toBase _)
      (isAffine_pullback_toBase _)
  have (j : J) : IsNoetherian
      ((F ⋙ (connectedAffineNeighborhoods _ X₀).ι ⋙ genericFibreDiagram X).obj j) :=
    isNoetherian_pullback_toBase (F.obj j)
  have (j : J) : IsAffine
      ((F ⋙ (connectedAffineNeighborhoods _ X₀).ι ⋙ genericFibreDiagram X).obj j) :=
    isAffine_pullback_toBase (F.obj j)
  have : IsNoetherian (((genericFibreCone X).whisker
      (connectedAffineNeighborhoods _ X₀).ι).whisker F).pt :=
    inferInstanceAs (IsNoetherian (Spec (.of (SeparableClosure X.functionField))))
  have : (((genericFibreCone X).whisker
      (connectedAffineNeighborhoods _ X₀).ι).whisker F).pt.IsSeparated :=
    inferInstanceAs (Spec (.of (SeparableClosure X.functionField))).IsSeparated
  exact .of_isLimit (isLimitGenericFibreConeWhisker X₀ hX₀ F)

omit [X.IsSeparated] in
variable (X₀) in
/-- **The connected affine étale neighbourhoods are cofinal.** The étale neighbourhoods `(U, u)` of
the generic geometric point with `U` affine and connected and `U ⟶ X` factoring through a
nonempty open `X₀` form an initial (cofinal) full subcategory of all étale neighbourhoods. -/
@[weil "lem_fk105_generic_fibres_projective_limit"]
theorem initial_connectedAffineNeighborhoods_genericSepClosedPoint
    (hX₀ : (X₀ : Set X).Nonempty) :
    (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).ι.Initial :=
  initial_connectedAffineNeighborhoods_ι (genericSepClosedPoint_default_mem X X₀ hX₀)

variable (X₀) in
omit [X.IsSeparated] in
/-- A small model of the connected affine étale neighbourhoods is cofiltered. -/
lemma isCofiltered_smallModel_connectedAffineNeighborhoods (hX₀ : (X₀ : Set X).Nonempty) :
    IsCofiltered (SmallModel.{u}
      (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).FullSubcategory) :=
  have := isCofiltered_connectedAffineNeighborhoods (genericSepClosedPoint_default_mem X X₀ hX₀)
  IsCofiltered.of_equivalence (equivSmallModel _)

variable (X₀) in
/-- **The generic fibres of the connected affine étale neighbourhoods form a projective system
with limit `Spec K^sep`.** Indexed by a small model of the category of connected affine étale
neighbourhoods `(U, u)` of the generic geometric point over the nonempty affine open `X₀`, the
generic fibres `U_K = U ×_X Spec K` with the maps `p_U = (u, θ) : Spec K^sep ⟶ U_K` form a
projective system of schemes with limit `Spec K^sep`. -/
@[weil "lem_fk105_generic_fibres_projective_limit"]
theorem isProjectiveSystemWithLimit_genericFibre (hX₀ : IsAffineOpen X₀) [Nonempty X₀] :
    IsProjectiveSystemWithLimit
      ((equivSmallModel.{u} (connectedAffineNeighborhoods _ X₀).FullSubcategory).inverse ⋙
        (connectedAffineNeighborhoods (genericSepClosedPoint X) X₀).ι ⋙ genericFibreDiagram X)
      (((genericFibreCone X).whisker (connectedAffineNeighborhoods _ X₀).ι).whisker
        (equivSmallModel.{u} (connectedAffineNeighborhoods _ X₀).FullSubcategory).inverse) :=
  have := isCofiltered_smallModel_connectedAffineNeighborhoods X₀
    (Set.nonempty_coe_sort.mp ‹Nonempty X₀›)
  isProjectiveSystemWithLimit_genericFibre_of_initial X₀ hX₀ _

variable (X₀) in
/-- The cone `p_U : Spec K^sep ⟶ U_K` over the generic fibres of the connected affine étale
neighbourhoods of the generic geometric point is a limit cone. -/
@[weil "lem_fk105_generic_fibres_projective_limit"]
theorem nonempty_isLimit_genericFibreCone (hX₀ : IsAffineOpen X₀) [Nonempty X₀] :
    Nonempty (IsLimit ((genericFibreCone X).whisker (connectedAffineNeighborhoods _ X₀).ι)) :=
  have := isCofiltered_smallModel_connectedAffineNeighborhoods X₀
    (Set.nonempty_coe_sort.mp ‹Nonempty X₀›)
  ⟨(IsLimit.whiskerEquivalenceEquiv (equivSmallModel.{u} _).symm).symm
    (isLimitGenericFibreConeWhisker X₀ hX₀ _)⟩

end GenericPoint
end AlgebraicGeometry.Scheme

end
