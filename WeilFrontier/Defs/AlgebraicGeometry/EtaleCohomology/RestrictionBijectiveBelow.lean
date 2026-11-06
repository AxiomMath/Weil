module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.Attr

/-!
# Bijectivity of restriction on étale cohomology below a degree

Let `h : Y ⟶ X` be a morphism of schemes of a big étale site, `n` a natural number and `p` a
natural number. The proposition `B_p` says: for every abelian sheaf `H` on the small étale site of
`X` killed by `n` (a sheaf of `ℤ/n`-modules) and every degree `q < p`, the restriction map
`h^* : H^q(X, H) ⟶ H^q(Y, h^* H)` is bijective.

In the proof of the proper base change theorem over a strictly henselian base by Freitag and
Kiehl, `h` is the inclusion `i : X_s ⟶ X` of the special fibre of a projective `X` over a
noetherian strictly henselian local ring in which `n` is invertible, and `B_p` is the hypothesis of
the induction on the degree.

## Main definitions

* `AlgebraicGeometry.CohomologyRestrictionBijectiveBelow`: the proposition `B_p`.

## Main results

* `AlgebraicGeometry.CohomologyRestrictionBijectiveBelow.bijective`: the defining property.
* `AlgebraicGeometry.CohomologyRestrictionBijectiveBelow.mono`: `B_p` implies `B_{p'}` for
  `p' ≤ p`.
* `AlgebraicGeometry.cohomologyRestrictionBijectiveBelow_zero`: `B_0` holds.
* `AlgebraicGeometry.cohomologyRestrictionBijectiveBelow_succ_iff`: `B_{p+1}` holds if and only if
  `B_p` holds and restriction is bijective in degree `p`, which is the induction step.
* `AlgebraicGeometry.forall_cohomologyRestrictionBijectiveBelow_iff`: `B_p` holds for all `p` if
  and only if restriction is bijective in every degree.

## Implementation notes

The definition is stated for an arbitrary morphism `h` of a big étale site, with no hypothesis on
`n`; the strictly henselian setting enters only in the results that use it. A sheaf of
`ℤ/n`-modules is encoded as an abelian sheaf all of whose sections are killed by `n`, which is the
same datum (`ℤ/n`-module structures on an abelian group are unique when they exist), and its
cohomology is the cohomology of the underlying abelian sheaf. The restriction map is
`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`, on abelian sheaves with values in
`AddCommGrpCat.{u + 1}`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (h : Y ⟶ X)
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]

/-- **Restriction is bijective below degree `p`.** For a morphism `h : Y ⟶ X` of a big étale site
and natural numbers `n` and `p`: for every abelian sheaf `H` on the small étale site of `X` all of
whose sections are killed by `n` and every `q < p`, the restriction map
`h^* : H^q(X, H) ⟶ H^q(Y, h^* H)` is bijective. -/
@[weil "def_fk106_restriction_bijective_below"]
def CohomologyRestrictionBijectiveBelow (n p : ℕ) : Prop :=
  ∀ (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}),
    (∀ (U : SmallEtale B X.obj X.property) (x : H.obj.obj (op U)), n • x = 0) →
      ∀ q < p, Function.Bijective (smallEtaleCohomologyRestrictionMap.{w} B h H q)

variable {B h}

/-- Under `B_p`, restriction is bijective in every degree `q < p` on every sheaf killed by `n`. -/
theorem CohomologyRestrictionBijectiveBelow.bijective {n p : ℕ}
    (hB : CohomologyRestrictionBijectiveBelow.{w} B h n p)
    (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hH : ∀ (U : SmallEtale B X.obj X.property) (x : H.obj.obj (op U)), n • x = 0)
    {q : ℕ} (hq : q < p) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap.{w} B h H q) :=
  hB H hH q hq

/-- `B_p` implies `B_{p'}` for `p' ≤ p`. -/
theorem CohomologyRestrictionBijectiveBelow.mono {n p p' : ℕ}
    (hB : CohomologyRestrictionBijectiveBelow.{w} B h n p) (hp : p' ≤ p) :
    CohomologyRestrictionBijectiveBelow.{w} B h n p' :=
  fun H hH q hq ↦ hB H hH q (lt_of_lt_of_le hq hp)

variable (B h) in
/-- `B_0` holds: there is no degree below `0`. -/
theorem cohomologyRestrictionBijectiveBelow_zero (n : ℕ) :
    CohomologyRestrictionBijectiveBelow.{w} B h n 0 :=
  fun _ _ q hq ↦ absurd hq (Nat.not_lt_zero q)

/-- **The induction step.** `B_{p+1}` holds if and only if `B_p` holds and restriction is
bijective in degree `p` on every sheaf killed by `n`. -/
theorem cohomologyRestrictionBijectiveBelow_succ_iff {n p : ℕ} :
    CohomologyRestrictionBijectiveBelow.{w} B h n (p + 1) ↔
      CohomologyRestrictionBijectiveBelow.{w} B h n p ∧
        ∀ (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}),
          (∀ (U : SmallEtale B X.obj X.property) (x : H.obj.obj (op U)), n • x = 0) →
            Function.Bijective (smallEtaleCohomologyRestrictionMap.{w} B h H p) := by
  refine ⟨fun hB ↦ ⟨hB.mono (Nat.le_succ p), fun H hH ↦ hB H hH p (Nat.lt_succ_self p)⟩,
    fun ⟨hB, hp⟩ H hH q hq ↦ ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
  · exact hB H hH q hq
  · exact hp H hH

/-- `B_p` holds for every `p` if and only if restriction is bijective in every degree on every
sheaf killed by `n`. -/
theorem forall_cohomologyRestrictionBijectiveBelow_iff {n : ℕ} :
    (∀ p, CohomologyRestrictionBijectiveBelow.{w} B h n p) ↔
      ∀ (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}),
        (∀ (U : SmallEtale B X.obj X.property) (x : H.obj.obj (op U)), n • x = 0) →
          ∀ q, Function.Bijective (smallEtaleCohomologyRestrictionMap.{w} B h H q) :=
  ⟨fun hB H hH q ↦ hB (q + 1) H hH q (Nat.lt_succ_self q), fun hB _ H hH q _ ↦ hB H hH q⟩

end AlgebraicGeometry
