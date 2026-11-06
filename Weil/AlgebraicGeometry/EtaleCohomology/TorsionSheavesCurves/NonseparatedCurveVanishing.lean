module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NonseparatedCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen

/-!
# Vanishing of `H²` of free `ℤ/n`-module sheaves on affine curves

Let `k` be an algebraically closed field, `X` an affine scheme of finite type over `k` of
dimension at most one, and `Λ` a ring in which some `n ≥ 1` vanishes, such as `ℤ/nℤ`. For every
étale sheaf of sets `M` on `X`, the free sheaf of `Λ`-modules `M^Λ` (the sheafification of
`U ↦ Λ^(M(U))`) is killed by `n`, hence
is a torsion abelian sheaf, and therefore `H²(X, M^Λ) = 0` by the vanishing of the cohomology of
torsion sheaves on affine curves above degree one. In particular, for an étale `X`-scheme `Y`
with representable sheaf `Ỹ`, `H²(X, (Ỹ)^Λ) = 0`.

## Main results

* `AlgebraicGeometry.torsionSheafProperty_forget_freeModuleSheaf`: the free sheaf of
  `Λ`-modules on an étale sheaf of sets, viewed as an abelian sheaf, is torsion when a positive
  integer vanishes in `Λ`.
* `AlgebraicGeometry.subsingleton_sheafH_two_freeModuleSheaf_of_isAffine`: its `H²` vanishes on
  an affine curve over an algebraically closed field.
* `AlgebraicGeometry.subsingleton_sheafH_two_freeModuleSheaf_uliftYoneda_of_isAffine`: the case
  `Λ = ℤ/nℤ` and `M = Ỹ` the sheaf represented by an étale `X`-scheme `Y`.

## Implementation notes

The source assumes `X` integral and smooth, `n` invertible in `k`, and `Y` affine, and argues by
compactifying `Y → X` to a finite morphism. None of these hypotheses is needed: `M^Λ` is torsion,
and the vanishing of `H²` of torsion sheaves on affine schemes of finite type and dimension at
most one over `k` holds without them (Stacks, Tag 03RT, which rests on Theorem 03SC).
The étale site is Mathlib's small étale site `X.smallEtaleTopology`, the site of the Stacks
cohomology results used; cohomology is `CategoryTheory.Sheaf.H`. The free module functor
`ModuleCat.free` needs the ring in the universe of the sheaves of sets, `Type (u + 1)` on the small
étale site of `X : Scheme.{u}`, so `ℤ/nℤ` enters as `ULift (ZMod n)`, and `Ỹ` is the representable
sheaf `uliftYoneda` (the étale topology is subcanonical).

## References

* [FK] Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 03RT](https://stacks.math.columbia.edu/tag/03RT)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]

/-- In a `Λ`-module, viewed as an abelian group, multiplication by an integer `n` vanishing in
`Λ` is zero. -/
theorem nsmul_forget₂_eq_zero {n : ℕ} (hnΛ : (n : Λ) = 0) (N : ModuleCat.{u + 1} Λ)
    (z : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat).obj N) : n • z = 0 := by
  let z' : N := z
  have h : n • z' = 0 := by rw [← Nat.cast_smul_eq_nsmul Λ, hnΛ, zero_smul]
  exact h

/-- The free sheaf of `Λ`-modules on an étale sheaf of sets `M`, viewed as an abelian sheaf, is
torsion when some positive integer `n` vanishes in `Λ`: every section is killed by `n`. -/
theorem torsionSheafProperty_forget_freeModuleSheaf {n : ℕ} (hn : n ≠ 0) (hnΛ : (n : Λ) = 0)
    (M : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)).obj
        ((Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.free Λ)).obj M)) := by
  intro U x
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V f _ ↦ ⟨n, Nat.pos_of_ne_zero hn, ?_⟩⟩
  exact nsmul_forget₂_eq_zero Λ hnΛ _ _

/-- **`H²` of a free module sheaf on an affine curve vanishes.** Let `k` be an algebraically
closed field, `X` an affine scheme of finite type over `k` of dimension at most one, `Λ` a ring in
which a positive integer `n` vanishes, and `M` an étale sheaf of sets on `X`. Then
`H²(X, M^Λ) = 0`, where `M^Λ` is the free sheaf of `Λ`-modules on `M`. -/
theorem subsingleton_sheafH_two_freeModuleSheaf_of_isAffine {k : Type u} [Field k] [IsAlgClosed k]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π]
    (hdim : topologicalKrullDim X ≤ 1) [IsAffine X] {n : ℕ} (hn : n ≠ 0) (hnΛ : (n : Λ) = 0)
    (M : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Subsingleton (Sheaf.H.{w}
      ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)).obj
        ((Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.free Λ)).obj M)) 2) :=
  Stacks.EtaleCohomology.subsingleton_sheafH_two_of_isAffine.{w, 0, u} π hdim _
    (torsionSheafProperty_forget_freeModuleSheaf Λ hn hnΛ M)

/-- **FK, Lemma I.5 (`H²` of `(Ỹ)^Λ` on an affine curve).** Let `k` be an algebraically closed
field, `n ≥ 1`, `Λ = ℤ/nℤ`, `X` an affine scheme of finite type over `k` of dimension at most one
(for instance an affine integral smooth curve), and `Y → X` étale. Then `H²(X, (Ỹ)^Λ) = 0`, where
`Ỹ` is the sheaf represented by `Y` on the small étale site of `X` and `(Ỹ)^Λ` the free sheaf of
`Λ`-modules on it. The ring `ℤ/nℤ` is lifted to the universe of the sheaves of sets on the site. -/
@[weil "lem_fk105_affine_curve_free_module_h2_vanish"]
theorem subsingleton_sheafH_two_freeModuleSheaf_uliftYoneda_of_isAffine {k : Type u} [Field k]
    [IsAlgClosed k] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π]
    (hdim : topologicalKrullDim X ≤ 1) [IsAffine X] (n : ℕ) [NeZero n] (Y : X.Etale)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Subsingleton (Sheaf.H.{w}
      ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat)).obj
        ((Sheaf.composeAndSheafify X.smallEtaleTopology
            (ModuleCat.free (ULift.{u + 1} (ZMod n)))).obj
          (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj Y))) 2) :=
  subsingleton_sheafH_two_freeModuleSheaf_of_isAffine _ π hdim (NeZero.ne n)
    (by ext; simp) _

end AlgebraicGeometry
