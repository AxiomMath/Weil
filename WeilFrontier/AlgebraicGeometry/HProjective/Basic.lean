module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.NonFlatLocusFibreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpenBetween
public import Weil.Attr

/-!
# Projective compactification of an affine curve

Let `Ω` be a field and `X` an affine scheme of finite type over `Ω` with `dim X ≤ 1`. Then `X` is
an open subscheme of a projective `Ω`-scheme `X̄` with `dim X̄ ≤ 1`.

The proof embeds `X` into a projective space `ℙⁿ_Ω` (a closed immersion into an affine space
followed by a standard chart) and takes for `X̄` the scheme-theoretic image of this quasi-compact
immersion. Then `X ⟶ X̄` is an open immersion with dense image, and `X̄ ⟶ ℙⁿ_Ω` is a closed
immersion, so `X̄` is H-projective over `Ω`. For the dimension, every point `y` of `X̄` is a
specialization of a point `x` of `X` (the closure of the image of a quasi-compact morphism is the
image of its scheme-theoretic image), so
`trdeg_Ω κ(y) ≤ trdeg_Ω κ(x) ≤ dim X`, and a scheme locally of finite type over a field whose
residue fields all have transcendence degree at most `n` has dimension at most `n`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_natCast_of_isOpenImmersion_of_denseRange`: a scheme
  locally of finite type over a field with a dense open subscheme of dimension at most `n`,
  embedded by a quasi-compact open immersion, has dimension at most `n`.
* `AlgebraicGeometry.exists_isOpenImmersion_isHProjective_of_isAffine`: the projective
  compactification of an affine scheme of finite type over a field of dimension at most `n`
  (`n = 1`: an affine curve).

## Implementation notes

"Projective over `Ω`" is expressed by `Stacks.HProjective.IsHProjective`, a closed immersion into
some `ℙⁿ_Ω` over `Ω`; this is the strongest of the usual notions of projectivity, and over a field
all of them agree. The dimension bound is proved for any bound `n`, not only `n = 1`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.8.8, p. 94.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In `WithBot ℕ∞`, being at most a natural number `n` is being less than `n + 1`. -/
private lemma withBot_le_natCast_iff_lt_succ (a : WithBot ℕ∞) (n : ℕ) :
    a ≤ (n : WithBot ℕ∞) ↔ a < ((n + 1 : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe c =>
    have h1 : ((n : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) := rfl
    have h2 : (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := rfl
    rw [← h1, ← h2, WithBot.coe_le_coe, WithBot.coe_lt_coe, Nat.cast_add, Nat.cast_one,
      ENat.lt_add_one_iff (ENat.natCast_ne_top n)]

/-- **A dense quasi-compact open subscheme controls the dimension.** Let `Y` be a scheme locally
of finite type over a field `k` and `j : X ⟶ Y` a quasi-compact open immersion with dense image
from a scheme `X` of dimension at most `n`. Then `Y` has dimension at most `n`.

Every point `y` of `Y` is a specialization of a point `j x`, so the transcendence degree of `κ(y)`
over `k` is at most that of `κ(j x) = κ(x)`, which is at most `dim X`; and the dimension of a
scheme locally of finite type over a field is controlled by the transcendence degrees of its
residue fields. -/
theorem topologicalKrullDim_le_natCast_of_isOpenImmersion_of_denseRange (k : Type u) [Field k]
    {X Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] (hj : DenseRange j) {n : ℕ}
    (hX : topologicalKrullDim X ≤ n) : topologicalKrullDim Y ≤ n := by
  have hdim : topologicalKrullDim (Set.univ : Set Y) = topologicalKrullDim Y :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
  rw [withBot_le_natCast_iff_lt_succ, ← hdim]
  refine (topologicalKrullDim_lt_iff_forall_toENat_trdeg_lt k Y q isClosed_univ (n + 1)).mpr ?_
  intro y _
  obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range j (hj.closure_eq ▸ Set.mem_univ y)
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  let : Algebra k (Y.residueField (j x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation (j x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ q).appTop ≫ X.Γevaluation x).hom.toAlgebra
  have h1 : Algebra.trdeg k (Y.residueField y) ≤ Algebra.trdeg k (Y.residueField (j x)) := by
    by_cases hxy : j x = y
    · subst hxy; exact le_rfl
    · exact (trdeg_residueField_lt_of_specialization k Y q hx hxy).le
  have h2 : Algebra.trdeg k (Y.residueField (j x)) = Algebra.trdeg k (X.residueField x) :=
    trdeg_residueField_of_surjectiveOnStalks k q j x
  have h3 : (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) ≤
      topologicalKrullDim X :=
    toENat_trdeg_le_topologicalKrullDim k X (j ≫ q) x
  rw [← withBot_le_natCast_iff_lt_succ]
  calc (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞)
      ≤ (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Cardinal.toENat.monotone' (h2 ▸ h1))
    _ ≤ topologicalKrullDim X := h3
    _ ≤ n := hX

/-- **An affine curve is an open subscheme of a projective curve.** Let `Ω` be a field and `X` an
affine scheme of finite type over `Ω` with `dim X ≤ 1`. Then there are a projective `Ω`-scheme
`X̄` with `dim X̄ ≤ 1` and an open immersion `X ⟶ X̄` over `Ω`.

`X̄` is the scheme-theoretic image of an immersion of `X` into some `ℙⁿ_Ω`. The statement holds
with any natural number in place of `1`. -/
@[weil "lem_fk108_affine_curve_projective_compactification"]
theorem exists_isOpenImmersion_isHProjective_of_isAffine (Ω : Type u) [Field Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of Ω)) [IsAffine X] [LocallyOfFiniteType p] {n : ℕ}
    (hX : topologicalKrullDim X ≤ n) :
    ∃ (Xbar : Scheme.{u}) (pbar : Xbar ⟶ Spec (.of Ω)) (j : X ⟶ Xbar),
      IsOpenImmersion j ∧ j ≫ pbar = p ∧ Stacks.HProjective.IsHProjective pbar ∧
        topologicalKrullDim Xbar ≤ n := by
  obtain ⟨m, i, hi, hip⟩ := exists_isImmersion_projectiveSpaceOver_of_isAffine p
  have := hi
  have : QuasiCompact i := by
    have : QuasiCompact (i ≫ (projectiveSpaceOver m (Spec (.of Ω)) ↘ Spec (.of Ω))) := by
      rw [hip]; infer_instance
    exact QuasiCompact.of_comp i (projectiveSpaceOver m (Spec (.of Ω)) ↘ Spec (.of Ω))
  let pbar := i.imageι ≫ (projectiveSpaceOver m (Spec (.of Ω)) ↘ Spec (.of Ω))
  have : LocallyOfFiniteType pbar := by
    have := (Stacks.HProjective.IsHProjective.comp_isClosedImmersion i.imageι
      (Stacks.HProjective.isHProjective_over m (Spec (.of Ω))))
    infer_instance
  refine ⟨i.image, pbar, i.toImage, inferInstance, ?_,
    Stacks.HProjective.IsHProjective.comp_isClosedImmersion i.imageι
      (Stacks.HProjective.isHProjective_over m (Spec (.of Ω))), ?_⟩
  · simp only [pbar, Scheme.Hom.toImage_imageι_assoc, hip]
  · exact topologicalKrullDim_le_natCast_of_isOpenImmersion_of_denseRange Ω pbar i.toImage
      i.toImage.denseRange hX

end AlgebraicGeometry
