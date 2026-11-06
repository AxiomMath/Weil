module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnitySecondCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.Curves.SmoothCurveHIGmVanish

/-!
# The Kummer sequence of a smooth curve in degrees one and two

Let `X` be a scheme and `n ≥ 1` an integer invertible on `X`. The long exact cohomology sequence
of the Kummer sequence `0 → μ_n → 𝐆_m →ⁿ 𝐆_m → 0` on the small étale site of `X`, together with
`H⁰(X, 𝐆_m) = Γ(X, 𝒪_X)ˣ` and the identification `H¹(X, 𝐆_m) = Pic X` of [Stacks, Tag 03P8],
gives the exact sequence

`Γ(X, 𝒪_X)ˣ →ⁿ Γ(X, 𝒪_X)ˣ → H¹(X, μ_n) → Pic X →ⁿ Pic X → H²(X, μ_n) → H²(X, 𝐆_m)`,

where the first map is `s ↦ sⁿ` and the fourth is `[ℒ] ↦ [ℒ^{⊗ n}]`. When `X` is a smooth curve
over an algebraically closed field `k` and `n` is invertible in `k`, `H²(X, 𝐆_m) = 0`
([Stacks, Tag 03RM]), so the sequence ends with `H²(X, μ_n) → 0`.

## Main definitions

* `Stacks.Kummer.globalUnitsAddEquivSheafHZero`: `Γ(X, 𝒪_X)ˣ ≅ H⁰(X, 𝐆_m)`.
* `Stacks.Kummer.globalUnitsToSheafHOneRootsOfUnity`: the Kummer boundary
  `Γ(X, 𝒪_X)ˣ → H¹(X, μ_n)`.
* `Stacks.Kummer.picardToSheafHTwoRootsOfUnity`: the Kummer boundary `Pic X → H²(X, μ_n)`.

## Main results

* `Stacks.Kummer.exact_globalUnits_sheafH_rootsOfUnity_picard`: exactness of the five-term
  sequence for any scheme on which `n` is invertible, and surjectivity of the last map when
  `H²(X, 𝐆_m) = 0`.
* `Stacks.Kummer.exact_globalUnits_sheafH_rootsOfUnity_picard_of_smoothCurve`: the six-term
  exact sequence on a smooth curve over an algebraically closed field.

## Implementation notes

The groups of global units are written additively, as `Additive Γ(X, ⊤)ˣ`, so that the whole
sequence lives in abelian groups; multiplication by `n` there is `s ↦ sⁿ`
(`Stacks.Kummer.nsmul_ofMul_globalUnits`). On `Pic X = Stacks.Picard.ofScheme X` the group law is
the tensor product of invertible sheaves, so multiplication by `n` is `[ℒ] ↦ [ℒ^{⊗ n}]`.

Cohomology is that of the small étale site `X.smallEtaleTopology` with coefficients in
`AddCommGrpCat.{max (u + 1) v}`. A smooth curve, not necessarily connected, complete or affine,
is a morphism `f : X ⟶ Spec k` which is separated, quasi-compact and smooth of relative
dimension one. The integer `n ≥ 1` prime to the characteristic of `k` is expressed as
`IsUnit (n : k)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §5.
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v u

namespace Stacks.Kummer

section General

variable (X : Scheme.{u}) {n : ℕ}

/-- The identity of `X` is a terminal object of the small étale site of `X`. -/
def etaleMkIdIsTerminal : IsTerminal (Scheme.Etale.mk (𝟙 X)) := by
  letI : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  exact MorphismProperty.Over.mkIdTerminal _ _

/-- In the additive notation of `Additive Γ(X, ⊤)ˣ`, multiplication by `n` is `s ↦ sⁿ`. -/
theorem nsmul_ofMul_globalUnits (a : (Γ(X, ⊤))ˣ) :
    n • Additive.ofMul a = Additive.ofMul (a ^ n) :=
  (ofMul_pow n a).symm

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **`H⁰(X, 𝐆_m)` is the group of global units of `X`**, written additively. -/
def globalUnitsAddEquivSheafHZero :
    Additive (Γ(X, ⊤))ˣ ≃+ Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 0 :=
  (AddEquiv.ulift.symm : Additive (Γ(X, ⊤))ˣ ≃+
      ULift.{max (u + 1) v} (Additive (Γ(X, ⊤))ˣ)).trans
    (Sheaf.H.equiv₀.{w} (multiplicativeSheaf.{u, v} X) (etaleMkIdIsTerminal X)).symm

theorem sheafH_equiv₀_globalUnitsAddEquivSheafHZero (a : (Γ(X, ⊤))ˣ) :
    Sheaf.H.equiv₀.{w} (multiplicativeSheaf.{u, v} X) (etaleMkIdIsTerminal X)
        (globalUnitsAddEquivSheafHZero.{w, v, u} X (Additive.ofMul a)) =
      ofUnit (U := Scheme.Etale.mk (𝟙 X)) a :=
  (Sheaf.H.equiv₀.{w} (multiplicativeSheaf.{u, v} X) (etaleMkIdIsTerminal X)).apply_symm_apply _

/-- Under `Γ(X, 𝒪_X)ˣ ≅ H⁰(X, 𝐆_m)`, the map induced by the `n`-th power map of `𝐆_m` is
`s ↦ sⁿ`. -/
theorem sheafH_map_powMap_globalUnitsAddEquivSheafHZero (a : Additive (Γ(X, ⊤))ˣ) :
    Sheaf.H.map (powMap.{u, v} X n) 0 (globalUnitsAddEquivSheafHZero.{w, v, u} X a) =
      globalUnitsAddEquivSheafHZero.{w, v, u} X (n • a) := by
  rw [sheafH_map_powMap, map_nsmul]

variable (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))

/-- The Kummer boundary `Γ(X, 𝒪_X)ˣ → H¹(X, μ_n)`. -/
def globalUnitsToSheafHOneRootsOfUnity :
    Additive (Γ(X, ⊤))ˣ →+ Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 1 :=
  (kummerδ.{w, u, v} X hn0 hX 0).comp (globalUnitsAddEquivSheafHZero.{w, v, u} X).toAddMonoidHom

/-- The Kummer boundary `Pic X → H²(X, μ_n)`, through `H¹(X, 𝐆_m) = Pic X`. -/
def picardToSheafHTwoRootsOfUnity :
    Picard.ofScheme X →+ Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2 :=
  (kummerδ.{w, u, v} X hn0 hX 1).comp
    (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).symm.toAddMonoidHom

include hn0 hX in
/-- **The Kummer sequence in degrees one and two.** Let `n ≥ 1` be invertible on `X`. Then

`Γ(X, 𝒪_X)ˣ →ⁿ Γ(X, 𝒪_X)ˣ → H¹(X, μ_n) → Pic X →ⁿ Pic X → H²(X, μ_n)`

is exact, and the last map is onto when `H²(X, 𝐆_m) = 0`. -/
theorem exact_globalUnits_sheafH_rootsOfUnity_picard :
    Function.Exact (nsmulAddMonoidHom n : Additive (Γ(X, ⊤))ˣ →+ Additive (Γ(X, ⊤))ˣ)
        (globalUnitsToSheafHOneRootsOfUnity.{w, v, u} X hn0 hX) ∧
      Function.Exact (globalUnitsToSheafHOneRootsOfUnity.{w, v, u} X hn0 hX)
        (h1RootsOfUnityToPicard.{w, v, u} X n) ∧
      Function.Exact (h1RootsOfUnityToPicard.{w, v, u} X n)
        (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X) ∧
      Function.Exact (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X)
        (picardToSheafHTwoRootsOfUnity.{w, v, u} X hn0 hX) ∧
      (Subsingleton (Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 2) →
        Function.Surjective (picardToSheafHTwoRootsOfUnity.{w, v, u} X hn0 hX)) := by
  set e₀ := globalUnitsAddEquivSheafHZero.{w, v, u} X
  set e₁ := etaleH1MultiplicativeAddEquivPicard.{w, v, u} X
  refine ⟨fun y => ?_, fun x => ?_, fun p => ?_, fun p => ?_, fun h2 => ?_⟩
  · -- exactness at the second `Γ(X, 𝒪_X)ˣ`
    change kummerδ X hn0 hX 0 (e₀ y) = 0 ↔ _
    rw [← mem_range_sheafH_map_powMap_iff X hn0 hX 0 (e₀ y)]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e₀.symm z, e₀.injective ?_⟩
      rw [nsmulAddMonoidHom_apply, ← sheafH_map_powMap_globalUnitsAddEquivSheafHZero,
        AddEquiv.apply_symm_apply, hz]
    · rintro ⟨z, rfl⟩
      exact ⟨e₀ z, sheafH_map_powMap_globalUnitsAddEquivSheafHZero X z⟩
  · -- exactness at `H¹(X, μ_n)`
    change e₁ (Sheaf.H.map (rootsOfUnityι.{u, v} X n) 1 x) = 0 ↔ _
    rw [AddEquiv.map_eq_zero_iff, ← mem_range_kummerδ_iff X hn0 hX 0 x]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨e₀.symm z, ?_⟩
      change kummerδ X hn0 hX 0 (e₀ (e₀.symm z)) = _
      rw [AddEquiv.apply_symm_apply]
    · rintro ⟨z, rfl⟩
      exact ⟨e₀ z, rfl⟩
  · -- exactness at the first `Pic X`
    change n • p = 0 ↔ p ∈ (h1RootsOfUnityToPicard.{w, v, u} X n).range
    rw [range_h1RootsOfUnityToPicard X n hn0 hX, AddSubgroup.torsionBy.nsmul_iff]
  · -- exactness at the second `Pic X`
    change kummerδ X hn0 hX 1 (e₁.symm p) = 0 ↔ _
    rw [← AddMonoidHom.mem_ker, ker_kummerδ_one X hn0 hX]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e₁ z, ?_⟩
      rw [nsmulAddMonoidHom_apply, ← map_nsmul, ← nsmulAddMonoidHom_apply, hz,
        AddEquiv.apply_symm_apply]
    · rintro ⟨z, rfl⟩
      exact ⟨e₁.symm z, (map_nsmul e₁.symm n z).symm⟩
  · -- surjectivity onto `H²(X, μ_n)`
    intro x
    obtain ⟨y, rfl⟩ := surjective_kummerδ_one X hn0 hX h2 x
    refine ⟨e₁ y, ?_⟩
    change kummerδ X hn0 hX 1 (e₁.symm (e₁ y)) = _
    rw [AddEquiv.symm_apply_apply]

end General

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {n : ℕ} (hn : IsUnit (n : k))

omit [IsAlgClosed k] in
include hn in
/-- An integer invertible in a field is nonzero. -/
theorem ne_zero_of_isUnit_natCast : n ≠ 0 := by
  rintro rfl
  simp at hn

include f hn in
/-- **The Kummer sequence of a smooth curve in degrees one and two.** Let `X` be a smooth curve
over an algebraically closed field `k`, not necessarily connected, and `n ≥ 1` an integer
invertible in `k`. Then

`Γ(X, 𝒪_X)ˣ →ⁿ Γ(X, 𝒪_X)ˣ → H¹(X, μ_n) → Pic X →ⁿ Pic X → H²(X, μ_n) → 0`

is exact: the first map is `s ↦ sⁿ`, the fourth is `[ℒ] ↦ [ℒ^{⊗ n}]`, and the others come from
the long exact cohomology sequence of the Kummer sequence and `H¹(X, 𝐆_m) = Pic X`. -/
@[weil "lem_fk105_smooth_curve_h1_mu_n_exact_sequence"]
theorem exact_globalUnits_sheafH_rootsOfUnity_picard_of_smoothCurve :
    Function.Exact (nsmulAddMonoidHom n : Additive (Γ(X, ⊤))ˣ →+ Additive (Γ(X, ⊤))ˣ)
        (globalUnitsToSheafHOneRootsOfUnity.{w, v, u} X (ne_zero_of_isUnit_natCast hn)
          (isUnit_natCast_globalSections X n f hn)) ∧
      Function.Exact
        (globalUnitsToSheafHOneRootsOfUnity.{w, v, u} X (ne_zero_of_isUnit_natCast hn)
          (isUnit_natCast_globalSections X n f hn))
        (h1RootsOfUnityToPicard.{w, v, u} X n) ∧
      Function.Exact (h1RootsOfUnityToPicard.{w, v, u} X n)
        (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X) ∧
      Function.Exact (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X)
        (picardToSheafHTwoRootsOfUnity.{w, v, u} X (ne_zero_of_isUnit_natCast hn)
          (isUnit_natCast_globalSections X n f hn)) ∧
      Function.Surjective
        (picardToSheafHTwoRootsOfUnity.{w, v, u} X (ne_zero_of_isUnit_natCast hn)
          (isUnit_natCast_globalSections X n f hn)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := exact_globalUnits_sheafH_rootsOfUnity_picard.{w, v, u} X
    (ne_zero_of_isUnit_natCast hn) (isUnit_natCast_globalSections X n f hn)
  exact ⟨h₁, h₂, h₃, h₄, h₅
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one f 2 le_rfl)⟩

end Curve

end Stacks.Kummer

end
