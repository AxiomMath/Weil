module

public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import Weil.Attr

/-!
# Sheaves which are torsion prime to the residue characteristics of a base

Let `S` be a scheme and `F` an abelian sheaf on the small étale site of a scheme `X` (in practice
`X` comes with a morphism `f : X ⟶ S`, and `X = S` with `f = 𝟙 S` is allowed). The sheaf `F` is
*torsion prime to the residue characteristics of `S`* when every local section of `F` is, on some
étale covering, annihilated by a positive integer which is invertible on `S`. An integer `n` is
invertible on `S`, that is a unit in `Γ(S, 𝒪_S)`, exactly when it is nonzero in every residue
field `κ(t)`, that is when no residue characteristic `char κ(t) = p > 0` of `S` divides `n`.

For a locally noetherian `X` this is the condition of Freitag and Kiehl: `F` is a torsion sheaf
and, for every noetherian separated étale `X`-scheme `U`, every `σ ∈ F(U)` and every `t ∈ S` of
residue characteristic `p > 0`, the order of `σ` is not divisible by `p`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsTorsionPrimeToResidueCharacteristics`: the property of an
  abelian sheaf on the small étale site of `X` of being torsion prime to the residue
  characteristics of `S`.

## Main results

* `AlgebraicGeometry.Scheme.isUnit_natCast_iff_forall_not_ringChar_dvd`: a positive integer is
  invertible on `S` if and only if no positive residue characteristic of `S` divides it.
* `AlgebraicGeometry.SmallEtale.IsTorsionPrimeToResidueCharacteristics.isTorsionSheaf`: such a
  sheaf is a torsion sheaf.
* `AlgebraicGeometry.SmallEtale.isTorsionPrimeToResidueCharacteristics_iff`: for a locally
  noetherian `X`, the condition in terms of the orders of the sections over the noetherian
  separated étale `X`-schemes.
* `AlgebraicGeometry.SmallEtale.isTorsionPrimeToResidueCharacteristics_toEtaleSite_iff`: the
  condition agrees with `Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn` on Mathlib's small
  étale site.

## Implementation notes

The definition is the local one, `Stacks.EtaleCohomology.LocallyAnnihilated` along the predicate
"positive and a unit in `Γ(S, ⊤)`", which is also the definition of
`Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn` on Mathlib's small étale site. The base
enters only through its residue characteristics, so the morphism `f : X ⟶ S` of the source is not
an argument. The sectionwise formulation over noetherian separated étale `X`-schemes is
`AlgebraicGeometry.SmallEtale.isTorsionPrimeToResidueCharacteristics_iff`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7][FreitagKiehl]
* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace Stacks.EtaleCohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **On a quasi-compact object a locally annihilated section is killed by one integer.** If `P`
holds for `1` and is stable under products, a section of an abelian sheaf which is locally
annihilated along `P`, over a quasi-compact object, is annihilated by one integer satisfying `P`:
the product of the annihilators on finitely many members of a refining covering family. -/
theorem LocallyAnnihilated.exists_nsmul_eq_zero_of_isQuasiCompactObject {P : ℕ → Prop}
    (hP1 : P 1) (hPmul : ∀ a b, P a → P b → P (a * b)) {F : Sheaf J AddCommGrpCat.{w}}
    (hF : LocallyAnnihilated J P F) {U : C} (hU : J.IsQuasiCompactObject U)
    (x : F.obj.obj (op U)) : ∃ n : ℕ, P n ∧ n • x = 0 := by
  classical
  obtain ⟨R, hR, hx⟩ := hF U x
  let 𝒰 : PreZeroHypercover.{max u v} U :=
    { I₀ := Σ V : C, {f : V ⟶ U // R f}, X := fun i ↦ i.1, f := fun i ↦ i.2.1 }
  have hle : R ≤ 𝒰.sieve₀ := fun V f hf ↦ 𝒰.sieve₀_f ⟨V, f, hf⟩
  choose n hn hnx using fun i : 𝒰.I₀ ↦ hx i.1 i.2.1 i.2.2
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := hU 𝒰 (J.superset_covering hle hR)
  refine ⟨∏ i ∈ hfin.toFinset, n i, Finset.prod_induction _ P hPmul hP1 fun i _ ↦ hn i, ?_⟩
  refine Stacks.Torsion.sheaf_section_eq_zero_of_mem F _ h𝒱 ?_
  rintro V f ⟨Y, h, g, ⟨j⟩, rfl⟩
  have hdvd : n (φ.s₀ j) ∣ ∏ i ∈ hfin.toFinset, n i :=
    Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr (Set.mem_range_self j))
  obtain ⟨e, he⟩ := hdvd
  rw [← φ.w₀ j, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, map_nsmul, he, mul_comm, mul_smul]
  change F.obj.map h.op (F.obj.map (φ.h₀ j).op (e • n (φ.s₀ j) • F.obj.map
    (φ.s₀ j).2.1.op x)) = 0
  rw [hnx, smul_zero, map_zero, map_zero]

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

namespace Scheme

/-- **Integers invertible on a scheme.** The image of a natural number in `Γ(S, ⊤)` is a unit
if and only if its image in every residue field of `S` is a unit. -/
theorem isUnit_natCast_iff_forall_residueField (S : Scheme.{u}) (n : ℕ) :
    IsUnit (n : Γ(S, ⊤)) ↔ ∀ t : S, IsUnit (n : S.residueField t) := by
  refine ⟨fun h t ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.map (S.presheaf.germ ⊤ t trivial ≫ S.residue t).hom
  · refine RingedSpace.isUnit_of_isUnit_germ S.toRingedSpace ⊤ _ fun t _ ↦ ?_
    have ht : IsUnit ((S.residue t).hom ((S.presheaf.germ ⊤ t trivial).hom n)) := by
      simpa using h t
    exact isUnit_of_map_unit (IsLocalRing.residue (S.presheaf.stalk t)) _ ht

/-- **Integers invertible on a scheme, by residue characteristics.** A positive integer `n` is
invertible on `S` if and only if, for every point `t` of `S` whose residue field has positive
characteristic `p`, the prime `p` does not divide `n`. -/
theorem isUnit_natCast_iff_forall_not_ringChar_dvd (S : Scheme.{u}) {n : ℕ} (hn : 0 < n) :
    IsUnit (n : Γ(S, ⊤)) ↔
      ∀ t : S, 0 < ringChar (S.residueField t) → ¬ ringChar (S.residueField t) ∣ n := by
  rw [isUnit_natCast_iff_forall_residueField]
  refine forall_congr' fun t ↦ ?_
  rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff _ (ringChar (S.residueField t))]
  refine ⟨fun h _ ↦ h, fun h hdvd ↦ ?_⟩
  rcases Nat.eq_zero_or_pos (ringChar (S.residueField t)) with h0 | h0
  · rw [h0, zero_dvd_iff] at hdvd
    exact hn.ne' hdvd
  · exact h h0 hdvd

end Scheme

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

variable (B X hX) in
/-- **Torsion prime to the residue characteristics of `S`.** An abelian sheaf on the small étale
site of `X` is *torsion prime to the residue characteristics of `S`* if every local section is,
on some étale covering, annihilated by a positive integer which is invertible on `S`. An integer
is invertible on `S` exactly when no positive residue characteristic of `S` divides it
(`AlgebraicGeometry.Scheme.isUnit_natCast_iff_forall_not_ringChar_dvd`); for a locally
noetherian `X` the condition is that `F` is a torsion sheaf whose sections over noetherian
separated étale `X`-schemes have orders prime to the residue characteristics of `S`
(`AlgebraicGeometry.SmallEtale.isTorsionPrimeToResidueCharacteristics_iff`). -/
@[weil "def_fk107_torsion_prime_to_residue_characteristics"]
abbrev IsTorsionPrimeToResidueCharacteristics (S : Scheme.{u}) :
    ObjectProperty (Sheaf (topology B X hX) AddCommGrpCat.{w}) :=
  fun F ↦ Stacks.EtaleCohomology.LocallyAnnihilated (topology B X hX)
    (fun n : ℕ ↦ 0 < n ∧ IsUnit (n : Γ(S, ⊤))) F

variable {S : Scheme.{u}}

/-- A sheaf which is torsion prime to the residue characteristics of `S` is a torsion sheaf. -/
theorem IsTorsionPrimeToResidueCharacteristics.isTorsionSheaf
    {F : Sheaf (topology B X hX) AddCommGrpCat.{w}}
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) : IsTorsionSheaf B X hX F := by
  intro U x
  obtain ⟨R, hR, hkill⟩ := hF U x
  exact ⟨R, hR, fun V f hf ↦ (hkill V f hf).imp fun _ h ↦ ⟨h.1.1, h.2⟩⟩

/-- Being torsion prime to the residue characteristics of `S` is invariant under isomorphism. -/
theorem IsTorsionPrimeToResidueCharacteristics.of_iso
    {F G : Sheaf (topology B X hX) AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) :
    IsTorsionPrimeToResidueCharacteristics B X hX S G :=
  Stacks.Torsion.IsLocallyAnnihilatedBy.of_iso (topology B X hX)
    (N := {n : ℕ | 0 < n ∧ IsUnit (n : Γ(S, ⊤))})
    ((sheafToPresheaf (topology B X hX) AddCommGrpCat.{w}).mapIso e) hF

/-- **A section over a quasi-compact object is killed by one integer invertible on `S`.** -/
theorem IsTorsionPrimeToResidueCharacteristics.exists_nsmul_eq_zero_of_compactSpace
    {F : Sheaf (topology B X hX) AddCommGrpCat.{w}}
    (hF : IsTorsionPrimeToResidueCharacteristics B X hX S F) (U : SmallEtale B X hX)
    [CompactSpace ((toScheme B X hX).obj U)] (x : F.obj.obj (op U)) :
    ∃ n : ℕ, (0 < n ∧ IsUnit (n : Γ(S, ⊤))) ∧ n • x = 0 :=
  Stacks.EtaleCohomology.LocallyAnnihilated.exists_nsmul_eq_zero_of_isQuasiCompactObject
    ⟨Nat.one_pos, by simp⟩
    (fun a b ha hb ↦ ⟨Nat.mul_pos ha.1 hb.1, by simpa using ha.2.mul hb.2⟩) hF
    (isQuasiCompactObject_of_compactSpace B X hX U inferInstance) x

/-- **Freitag and Kiehl's form of the condition.** For a locally noetherian `X`, an abelian
sheaf `F` on the small étale site of `X` is torsion prime to the residue characteristics of `S`
if and only if `F` is a torsion sheaf and, for every noetherian separated étale `X`-scheme `U`,
every section `σ ∈ F(U)` and every point `t ∈ S` whose residue field has characteristic `p > 0`,
the order of `σ` is not divisible by `p`. -/
@[weil "def_fk107_torsion_prime_to_residue_characteristics"]
theorem isTorsionPrimeToResidueCharacteristics_iff [IsLocallyNoetherian X]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{w}) :
    IsTorsionPrimeToResidueCharacteristics B X hX S F ↔
      IsTorsionSheaf B X hX F ∧ ∀ (U : SmallNoetherianSeparatedEtale B X hX)
        (σ : F.obj.obj (op ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U))) (t : S),
        0 < ringChar (S.residueField t) → ¬ ringChar (S.residueField t) ∣ addOrderOf σ := by
  refine ⟨fun hF ↦ ⟨hF.isTorsionSheaf, fun U σ t ht hdvd ↦ ?_⟩, fun ⟨hT, h⟩ X' x ↦ ?_⟩
  · have : _root_.AlgebraicGeometry.IsNoetherian
        ((toScheme B X hX).obj ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)) :=
      U.property.1
    obtain ⟨n, ⟨hn, hu⟩, hnσ⟩ := hF.exists_nsmul_eq_zero_of_compactSpace _ σ
    exact (S.isUnit_natCast_iff_forall_not_ringChar_dvd hn).mp hu t ht
      (hdvd.trans (addOrderOf_dvd_of_nsmul_eq_zero hnσ))
  have hTor := (isTorsionSheaf_iff_forall_isAddTorsion F).mp hT
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj X hX)) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian ((toScheme B X hX).obj X') :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map X'.obj.hom)
  let E : PreZeroHypercover.{u + 1} X' :=
    { I₀ := ULift.{u + 1} ((toScheme B X hX).obj X').affineOpens
      X := fun W ↦ openObject B X hX X' W.down.1
      f := fun W ↦ openObjectι B X hX X' W.down.1 }
  refine ⟨E.sieve₀, Precoverage.generate_mem_toGrothendieck
    (presieve₀_mem_precoverage_of_jointlySurjective B X hX E fun p ↦ ?_), ?_⟩
  · obtain ⟨W, hWa, hW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    refine ⟨ULift.up ⟨W, hWa⟩, ?_⟩
    change p ∈ Set.range ((toScheme B X hX).map (openObjectι B X hX X' W)).base
    rw [openObjectι_range]
    exact hW
  · rintro V f ⟨Y, g, k, ⟨W⟩, rfl⟩
    let W' : ((toScheme B X hX).obj X').Opens := W.down.1
    have : _root_.AlgebraicGeometry.IsAffine W' := W.down.2
    have : _root_.AlgebraicGeometry.IsNoetherian W' := { toCompactSpace := inferInstance }
    let U : SmallNoetherianSeparatedEtale B X hX :=
      ⟨openObject B X hX X' W', ‹IsNoetherian W'›, inferInstanceAs W'.toScheme.IsSeparated⟩
    let σ : F.obj.obj (op ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)) :=
      F.obj.map (openObjectι B X hX X' W').op x
    have hpos : 0 < addOrderOf σ := (hTor U σ).addOrderOf_pos
    refine ⟨addOrderOf σ, ⟨hpos, (S.isUnit_natCast_iff_forall_not_ringChar_dvd hpos).mpr
      (h U σ)⟩, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul]
    change F.obj.map g.op (addOrderOf σ • σ) = 0
    rw [addOrderOf_nsmul_eq_zero, map_zero]

/-- **The condition on Mathlib's small étale site.** An abelian sheaf `G` on Mathlib's small
étale site of `X` has torsion of orders invertible on `S`
(`Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn`) exactly when its restriction to the small
étale site `AlgebraicGeometry.SmallEtale` is torsion prime to the residue characteristics of
`S`. The restriction is the inverse of `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
theorem isTorsionPrimeToResidueCharacteristics_toEtaleSite_iff
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsTorsionPrimeToResidueCharacteristics B X hX S
        (((toEtaleSite B X hX).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology B X hX) X.smallEtaleTopology).obj G) ↔
      Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn S G :=
  Stacks.Torsion.isLocallyAnnihilatedBy_pushforward_iff (topology B X hX)
    X.smallEtaleTopology (toEtaleSite B X hX) {n : ℕ | 0 < n ∧ IsUnit (n : Γ(S, ⊤))} G

end SmallEtale

end AlgebraicGeometry

end
