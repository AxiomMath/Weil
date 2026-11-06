module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ShortExactLongExactSequence
public import WeilFrontier.CategoryTheory.Sites.Cohomology.ShortExactLongExactSequence
public import Weil.Attr

/-!
# The Bockstein sequences of sheaf cohomology

Let `(C, J)` be a site and `n ≥ 1`. The short exact sequence of abelian groups
`0 → ℤ --n--> ℤ → ℤ/n → 0` stays exact after applying the constant sheaf functor, which is exact
(it is the constant presheaf functor followed by sheafification). Its long exact cohomology
sequence contains, for every `ν`, the exact sequence
`Hᵛ(ℤ) --n--> Hᵛ(ℤ) → Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ) --n--> Hᵛ⁺¹(ℤ)`,
where the map induced by multiplication by `n` on `ℤ` is multiplication by `n` on cohomology.
Equivalently there is a short exact sequence
`0 → Hᵛ(ℤ)/n Hᵛ(ℤ) → Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)[n] → 0`.
For `n' = n d` the reduction `ℤ/n' → ℤ/n` induces a morphism of these short exact sequences,
which is the quotient map `Hᵛ(ℤ)/n' → Hᵛ(ℤ)/n` on the left and multiplication by `d`,
`Hᵛ⁺¹(ℤ)[n'] → Hᵛ⁺¹(ℤ)[n]`, on the right.

## Main definitions

* `AddCommGrpCat.zmodShortComplex n`: the short complex `ℤ --n--> ℤ → ℤ/n` of abelian groups.
* `AddCommGrpCat.zmodShortComplexMap n d`: the morphism `(d, id, reduction)` from the complex
  for `n * d` to the complex for `n`.
* `CategoryTheory.Sheaf.zmodShortComplex J n`: its image under the constant sheaf functor.
* `CategoryTheory.Sheaf.H.reduction n ν : Hᵛ(ℤ) →+ Hᵛ(ℤ/n)` and
  `CategoryTheory.Sheaf.H.bockstein n ν : Hᵛ(ℤ/n) →+ Hᵛ⁺¹(ℤ)`.
* `CategoryTheory.Sheaf.H.bocksteinQuotient n ν : Hᵛ(ℤ) ⧸ n Hᵛ(ℤ) →+ Hᵛ(ℤ/n)` and
  `CategoryTheory.Sheaf.H.bocksteinTorsion n ν : Hᵛ(ℤ/n) →+ Hᵛ⁺¹(ℤ)[n]`.
* `CategoryTheory.Sheaf.H.zmodReduction n ν d : Hᵛ(ℤ/nd) →+ Hᵛ(ℤ/n)`, induced by the reduction.

## Main results

* `CategoryTheory.Sheaf.zmodShortComplex_shortExact`: `0 → ℤ → ℤ → ℤ/n → 0` is a short exact
  sequence of constant sheaves.
* `CategoryTheory.Sheaf.H.map_nsmul_id_apply`: multiplication by `n` on a sheaf induces
  multiplication by `n` on its cohomology.
* `CategoryTheory.Sheaf.H.exact_nsmul_reduction`,
  `CategoryTheory.Sheaf.H.exact_reduction_bockstein`,
  `CategoryTheory.Sheaf.H.exact_bockstein_nsmul`: the five-term Bockstein exact sequence.
* `CategoryTheory.Sheaf.H.injective_bocksteinQuotient`,
  `CategoryTheory.Sheaf.H.exact_bocksteinQuotient_bocksteinTorsion`,
  `CategoryTheory.Sheaf.H.surjective_bocksteinTorsion`: the short exact Bockstein sequence.
* `CategoryTheory.Sheaf.H.zmodReduction_bocksteinQuotient`,
  `CategoryTheory.Sheaf.H.bocksteinTorsion_zmodReduction`: its compatibility with the reduction
  `ℤ/nd → ℤ/n`, a morphism of short exact sequences whose outer maps are
  `CategoryTheory.Sheaf.H.quotientNSMulMap` and `CategoryTheory.Sheaf.H.torsionNSMulMap`.
* `TopCat.Sheaf.injective_bocksteinQuotient` and its companions: the same for the sheaf
  cohomology `Hᵛ(X, M)` of a topological space `X`.

## Implementation notes

The cohomology `Hᵛ(F)` is `CategoryTheory.Sheaf.H F ν`, the `Ext`-group from the constant sheaf
`ULift ℤ`; the coefficients are the constant sheaves on `ULift ℤ` and `ULift (ZMod n)`. The
`HasExt` structure is a hypothesis, so that every choice of it (for instance
`CategoryTheory.IsGrothendieckAbelian.hasExt`) specializes the results. Everything holds on an
arbitrary site with sheafification; in particular it applies to Mathlib's small étale site
`X.smallEtaleTopology` and to the site of open sets of a topological space, the latter being
recorded in the namespace `TopCat.Sheaf`. Multiplication by `n` is `n • AddMonoidHom.id`, so that
`n Hᵛ(ℤ)` is its range and the `n`-torsion `Hᵛ⁺¹(ℤ)[n]` its kernel.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl], IV.1.7.
* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w' w v u

namespace AddCommGrpCat

/-- The additive map `ULift ℤ → ULift (ZMod n)` reducing an integer modulo `n`. -/
noncomputable def uliftIntCastHom (n : ℕ) : ULift.{w} ℤ →+ ULift.{w} (ZMod n) :=
  (AddEquiv.ulift.symm : ZMod n ≃+ ULift.{w} (ZMod n)).toAddMonoidHom.comp
    ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom)

@[simp]
lemma uliftIntCastHom_apply_down (n : ℕ) (x : ULift.{w} ℤ) :
    (uliftIntCastHom n x).down = (x.down : ZMod n) := rfl

/-- The additive map `ULift (ZMod (n * d)) → ULift (ZMod n)` reducing modulo `n`. -/
noncomputable def uliftZModReduction (n d : ℕ) : ULift.{w} (ZMod (n * d)) →+ ULift.{w} (ZMod n) :=
  (AddEquiv.ulift.symm : ZMod n ≃+ ULift.{w} (ZMod n)).toAddMonoidHom.comp
    ((ZMod.castHom (dvd_mul_right n d) (ZMod n)).toAddMonoidHom.comp
      AddEquiv.ulift.toAddMonoidHom)

@[simp]
lemma uliftZModReduction_apply_down (n d : ℕ) (x : ULift.{w} (ZMod (n * d))) :
    (uliftZModReduction n d x).down = ZMod.castHom (dvd_mul_right n d) (ZMod n) x.down := rfl

lemma ofHom_nsmul_id {A : Type w} [AddCommGroup A] (n : ℕ) :
    ofHom (n • AddMonoidHom.id A) = n • 𝟙 (of A) := by
  ext x
  simp

lemma uliftIntCastHom_comp_reduction (n d : ℕ) :
    (uliftZModReduction.{w} n d).comp (uliftIntCastHom (n * d)) = uliftIntCastHom n := by
  ext x
  simp

/-- The short complex of abelian groups `ℤ --n--> ℤ → ℤ/n`, with values in `ULift`. -/
noncomputable abbrev zmodShortComplex (n : ℕ) : ShortComplex AddCommGrpCat.{w} where
  X₁ := of (ULift.{w} ℤ)
  X₂ := of (ULift.{w} ℤ)
  X₃ := of (ULift.{w} (ZMod n))
  f := ofHom (n • AddMonoidHom.id _)
  g := ofHom (uliftIntCastHom n)
  zero := by
    ext x
    simp

lemma zmodShortComplex_f (n : ℕ) : (zmodShortComplex.{w} n).f = n • 𝟙 _ :=
  ofHom_nsmul_id n

lemma zmodShortComplex_g_comp_reduction (n d : ℕ) :
    (zmodShortComplex.{w} (n * d)).g ≫ ofHom (uliftZModReduction n d) =
      (zmodShortComplex.{w} n).g := by
  change ofHom _ ≫ ofHom _ = ofHom _
  rw [← ofHom_comp, uliftIntCastHom_comp_reduction]

/-- For `n ≠ 0`, `0 → ℤ --n--> ℤ → ℤ/n → 0` is a short exact sequence of abelian groups. -/
lemma zmodShortComplex_shortExact (n : ℕ) [NeZero n] : (zmodShortComplex.{w} n).ShortExact where
  exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact (n • AddMonoidHom.id (ULift.{w} ℤ)) (uliftIntCastHom n)
    intro y
    constructor
    · intro hy
      have h0 : ((y.down : ℤ) : ZMod n) = 0 := congrArg ULift.down hy
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 h0
      refine ⟨⟨k⟩, ULift.ext _ _ ?_⟩
      simp [hk]
    · rintro ⟨x, rfl⟩
      apply ULift.ext
      simp
  mono_f := by
    rw [AddCommGrpCat.mono_iff_injective]
    change Function.Injective (n • AddMonoidHom.id (ULift.{w} ℤ))
    intro x y h
    apply ULift.ext
    have h' := congrArg ULift.down h
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, nsmul_eq_mul] at h'
    exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne n) h'
  epi_g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    change Function.Surjective (uliftIntCastHom.{w} n)
    intro y
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective y.down
    exact ⟨⟨k⟩, ULift.ext _ _ hk⟩

/-- The morphism of short complexes `(d, id, reduction)` from `ℤ --nd--> ℤ → ℤ/nd` to
`ℤ --n--> ℤ → ℤ/n`. -/
noncomputable def zmodShortComplexMap (n d : ℕ) :
    zmodShortComplex.{w} (n * d) ⟶ zmodShortComplex.{w} n where
  τ₁ := ofHom (d • AddMonoidHom.id _)
  τ₂ := 𝟙 _
  τ₃ := ofHom (uliftZModReduction n d)
  comm₁₂ := by
    change ofHom _ ≫ ofHom _ = ofHom _ ≫ 𝟙 _
    rw [Category.comp_id, ← ofHom_comp]
    congr 1
    ext x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, smul_smul,
      mul_comm n d]
  comm₂₃ := by
    rw [Category.id_comp, zmodShortComplex_g_comp_reduction]

end AddCommGrpCat

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The constant sheaf functor preserves finite limits: it is the constant presheaf functor
followed by sheafification. -/
instance preservesFiniteLimits_constantSheaf :
    PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{w}) :=
  inferInstanceAs (PreservesFiniteLimits (Functor.const Cᵒᵖ ⋙ presheafToSheaf J _))

/-- The constant sheaf functor preserves finite colimits. -/
instance preservesFiniteColimits_constantSheaf :
    PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{w}) :=
  inferInstanceAs (PreservesFiniteColimits (Functor.const Cᵒᵖ ⋙ presheafToSheaf J _))

namespace Sheaf

/-- The short complex of constant sheaves `ℤ --n--> ℤ → ℤ/n`. -/
noncomputable abbrev zmodShortComplex (n : ℕ) : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  (AddCommGrpCat.zmodShortComplex.{w} n).map (constantSheaf J AddCommGrpCat.{w})

/-- `0 → ℤ --n--> ℤ → ℤ/n → 0` is a short exact sequence of constant sheaves. -/
lemma zmodShortComplex_shortExact (n : ℕ) [NeZero n] : (zmodShortComplex J n).ShortExact :=
  (AddCommGrpCat.zmodShortComplex_shortExact n).map_of_exact _

lemma zmodShortComplex_f (n : ℕ) : (zmodShortComplex J n).f = n • 𝟙 _ := by
  change (constantSheaf J AddCommGrpCat.{w}).map (AddCommGrpCat.zmodShortComplex.{w} n).f = _
  rw [AddCommGrpCat.zmodShortComplex_f, Functor.map_nsmul, Functor.map_id]
  rfl

variable {J}

namespace H

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- Multiplication by `n` on a sheaf induces multiplication by `n` on its cohomology. -/
lemma map_nsmul_id_apply (F : Sheaf J AddCommGrpCat.{w}) (n ν : ℕ) (x : H.{w'} F ν) :
    H.map (n • 𝟙 F) ν x = n • x := by
  induction n with
  | zero => simp [H.map_apply]
  | succ n ih => rw [succ_nsmul, H.map_add_apply, ih, H.map_id_apply, succ_nsmul]

/-- Multiplication by `n` on a sheaf induces multiplication by `n` on its cohomology. -/
lemma map_nsmul_id (F : Sheaf J AddCommGrpCat.{w}) (n ν : ℕ) :
    H.map (n • 𝟙 F) ν = n • AddMonoidHom.id (H.{w'} F ν) := by
  ext x
  simp [map_nsmul_id_apply]

variable (n : ℕ) (ν : ℕ)

set_option hygiene false in
/-- The constant sheaf `ℤ`. -/
local notation "ℤ_[" J "]" =>
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

set_option hygiene false in
/-- The constant sheaf `ℤ/n`. -/
local notation "ℤ/[" J ", " n "]" =>
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} (ZMod n)))

/-- The reduction map `Hᵛ(ℤ) → Hᵛ(ℤ/n)`, induced by `ℤ → ℤ/n`. -/
noncomputable def reduction : H.{w'} ℤ_[J] ν →+ H.{w'} ℤ/[J, n] ν :=
  H.map (zmodShortComplex J n).g ν

/-- The Bockstein map `Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)`, the connecting homomorphism of
`0 → ℤ --n--> ℤ → ℤ/n → 0`. -/
noncomputable def bockstein [NeZero n] : H.{w'} ℤ/[J, n] ν →+ H.{w'} ℤ_[J] (ν + 1) :=
  Stacks.Cohomology.GlobalLongExactSequence.boundary (zmodShortComplex_shortExact J n) ν

lemma map_zmodShortComplex_f_apply (ν : ℕ) (x : H.{w'} ℤ_[J] ν) :
    H.map (zmodShortComplex J n).f ν x = n • x := by
  rw [zmodShortComplex_f, map_nsmul_id_apply]

/-- Exactness of `Hᵛ(ℤ) --n--> Hᵛ(ℤ) → Hᵛ(ℤ/n)`. -/
theorem exact_nsmul_reduction [NeZero n] :
    Function.Exact (fun x : H.{w'} ℤ_[J] ν ↦ n • x) (reduction n ν) := by
  have h := Stacks.Cohomology.GlobalLongExactSequence.exact_map_map.{w'}
    (zmodShortComplex_shortExact J n) ν
  have e : (⇑(H.map.{w'} (zmodShortComplex J n).f ν)) = fun x : H.{w'} ℤ_[J] ν ↦ n • x :=
    funext (map_zmodShortComplex_f_apply n ν)
  rw [e] at h
  exact h

/-- Exactness of `Hᵛ(ℤ) → Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)`. -/
theorem exact_reduction_bockstein [NeZero n] :
    Function.Exact (reduction.{w'} (J := J) n ν) (bockstein n ν) :=
  Stacks.Cohomology.GlobalLongExactSequence.exact_map_boundary (zmodShortComplex_shortExact J n) ν

/-- Exactness of `Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ) --n--> Hᵛ⁺¹(ℤ)`. -/
theorem exact_bockstein_nsmul [NeZero n] :
    Function.Exact (bockstein.{w'} (J := J) n ν) (fun x : H.{w'} ℤ_[J] (ν + 1) ↦ n • x) := by
  have h := Stacks.Cohomology.GlobalLongExactSequence.exact_boundary_map.{w'}
    (zmodShortComplex_shortExact J n) ν
  have e : (⇑(H.map.{w'} (zmodShortComplex J n).f (ν + 1))) =
      fun x : H.{w'} ℤ_[J] (ν + 1) ↦ n • x :=
    funext (map_zmodShortComplex_f_apply n (ν + 1))
  rw [e] at h
  exact h

lemma reduction_nsmul [NeZero n] (x : H.{w'} ℤ_[J] ν) : reduction n ν (n • x) = 0 :=
  (exact_nsmul_reduction n ν).apply_apply_eq_zero x

lemma nsmul_bockstein [NeZero n] (y : H.{w'} ℤ/[J, n] ν) : n • bockstein n ν y = 0 :=
  (exact_bockstein_nsmul n ν).apply_apply_eq_zero y

/-- The map `Hᵛ(ℤ)/n Hᵛ(ℤ) → Hᵛ(ℤ/n)` induced by the reduction. -/
noncomputable def bocksteinQuotient [NeZero n] :
    H.{w'} ℤ_[J] ν ⧸ (n • AddMonoidHom.id (H.{w'} ℤ_[J] ν)).range →+ H.{w'} ℤ/[J, n] ν :=
  QuotientAddGroup.lift _ (reduction n ν) (by
    rintro _ ⟨x, rfl⟩
    exact reduction_nsmul n ν x)

@[simp]
lemma bocksteinQuotient_mk [NeZero n] (x : H.{w'} ℤ_[J] ν) :
    bocksteinQuotient n ν (QuotientAddGroup.mk x) = reduction n ν x := rfl

/-- The map `Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)[n]` induced by the Bockstein map. -/
noncomputable def bocksteinTorsion [NeZero n] :
    H.{w'} ℤ/[J, n] ν →+ (n • AddMonoidHom.id (H.{w'} ℤ_[J] (ν + 1))).ker :=
  (bockstein n ν).codRestrict _ (fun y ↦ by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    exact nsmul_bockstein n ν y)

@[simp]
lemma coe_bocksteinTorsion [NeZero n] (y : H.{w'} ℤ/[J, n] ν) :
    (bocksteinTorsion n ν y : H.{w'} ℤ_[J] (ν + 1)) = bockstein n ν y := rfl

/-- `Hᵛ(ℤ)/n Hᵛ(ℤ) → Hᵛ(ℤ/n)` is injective. -/
theorem injective_bocksteinQuotient [NeZero n] :
    Function.Injective (bocksteinQuotient.{w'} (J := J) n ν) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨y, hy⟩ := ((exact_nsmul_reduction n ν) x).1 hq
    exact (QuotientAddGroup.eq_zero_iff x).2 ⟨y, by simpa using hy⟩

/-- `Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)[n]` is surjective. -/
theorem surjective_bocksteinTorsion [NeZero n] :
    Function.Surjective (bocksteinTorsion.{w'} (J := J) n ν) := by
  rintro ⟨z, hz⟩
  have hz' : n • z = 0 := by
    rwa [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at hz
  obtain ⟨y, rfl⟩ := ((exact_bockstein_nsmul n ν) z).1 hz'
  exact ⟨y, rfl⟩

/-- Exactness of `Hᵛ(ℤ)/n Hᵛ(ℤ) → Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)[n]`. -/
theorem exact_bocksteinQuotient_bocksteinTorsion [NeZero n] :
    Function.Exact (bocksteinQuotient.{w'} (J := J) n ν) (bocksteinTorsion n ν) := by
  intro y
  constructor
  · intro hy
    have hy' : bockstein n ν y = 0 := congrArg Subtype.val hy
    obtain ⟨x, rfl⟩ := ((exact_reduction_bockstein n ν) y).1 hy'
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  · rintro ⟨q, rfl⟩
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      apply Subtype.ext
      exact (exact_reduction_bockstein n ν).apply_apply_eq_zero x

/-! ### Compatibility with the reduction `ℤ/nd → ℤ/n` -/

variable (d : ℕ)

/-- The map `Hᵛ(ℤ/nd) → Hᵛ(ℤ/n)` induced by the reduction `ℤ/nd → ℤ/n`. -/
noncomputable def zmodReduction : H.{w'} ℤ/[J, (n * d)] ν →+ H.{w'} ℤ/[J, n] ν :=
  H.map ((constantSheaf J AddCommGrpCat.{w}).map
    (AddCommGrpCat.ofHom (AddCommGrpCat.uliftZModReduction.{w} n d))) ν

/-- The reduction maps commute with the reduction `ℤ/nd → ℤ/n`. -/
theorem zmodReduction_reduction (x : H.{w'} ℤ_[J] ν) :
    zmodReduction n ν d (reduction (n * d) ν x) = reduction n ν x := by
  simp only [reduction, zmodReduction]
  rw [← H.map_comp_apply]
  congr 2
  change (constantSheaf J AddCommGrpCat.{w}).map _ ≫ (constantSheaf J AddCommGrpCat.{w}).map _ =
    (constantSheaf J AddCommGrpCat.{w}).map _
  rw [← Functor.map_comp, AddCommGrpCat.zmodShortComplex_g_comp_reduction]

/-- The morphism of short exact sequences of constant sheaves `(d, id, reduction)`. -/
noncomputable abbrev zmodShortComplexMap : zmodShortComplex J (n * d) ⟶ zmodShortComplex J n :=
  (constantSheaf J AddCommGrpCat.{w}).mapShortComplex.map
    (AddCommGrpCat.zmodShortComplexMap.{w} n d)

/-- The Bockstein maps commute with the reduction `ℤ/nd → ℤ/n` up to multiplication by `d`:
`β_n (r y) = d β_{nd} y`. -/
theorem bockstein_zmodReduction [NeZero n] [NeZero d] (y : H.{w'} ℤ/[J, (n * d)] ν) :
    bockstein n ν (zmodReduction n ν d y) = d • bockstein (n * d) ν y := by
  have h := Sheaf.H.map_boundary (zmodShortComplex_shortExact J (n * d))
    (zmodShortComplex_shortExact J n) (zmodShortComplexMap n d) ν y
  have e : (zmodShortComplexMap (J := J) n d).τ₁ = d • 𝟙 _ := by
    change (constantSheaf J AddCommGrpCat.{w}).map (AddCommGrpCat.ofHom (d • AddMonoidHom.id _)) = _
    rw [AddCommGrpCat.ofHom_nsmul_id, Functor.map_nsmul, Functor.map_id]
    rfl
  rw [e, map_nsmul_id_apply] at h
  exact h.symm

/-- The quotient map `Hᵛ(ℤ)/nd → Hᵛ(ℤ)/n`. -/
noncomputable def quotientNSMulMap :
    H.{w'} ℤ_[J] ν ⧸ ((n * d) • AddMonoidHom.id (H.{w'} ℤ_[J] ν)).range →+
      H.{w'} ℤ_[J] ν ⧸ (n • AddMonoidHom.id (H.{w'} ℤ_[J] ν)).range :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id _) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨d • x, by simp [mul_smul]⟩)

@[simp]
lemma quotientNSMulMap_mk (x : H.{w'} ℤ_[J] ν) :
    quotientNSMulMap n ν d (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := rfl

/-- Multiplication by `d`, `Hᵛ⁺¹(ℤ)[nd] → Hᵛ⁺¹(ℤ)[n]`. -/
noncomputable def torsionNSMulMap :
    ((n * d) • AddMonoidHom.id (H.{w'} ℤ_[J] (ν + 1))).ker →+
      (n • AddMonoidHom.id (H.{w'} ℤ_[J] (ν + 1))).ker :=
  ((d • AddMonoidHom.id _).comp (AddSubgroup.subtype _)).codRestrict _ (fun z ↦ by
    have hz := z.2
    rw [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at hz
    rw [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
      AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
      AddSubgroup.coe_subtype, smul_smul]
    exact hz)

@[simp]
lemma coe_torsionNSMulMap (z : ((n * d) • AddMonoidHom.id (H.{w'} ℤ_[J] (ν + 1))).ker) :
    (torsionNSMulMap n ν d z : H.{w'} ℤ_[J] (ν + 1)) = d • (z : H.{w'} ℤ_[J] (ν + 1)) := rfl

/-- **Compatibility on the left.** The square formed by `Hᵛ(ℤ)/nd → Hᵛ(ℤ/nd)`,
`Hᵛ(ℤ)/n → Hᵛ(ℤ/n)`, the quotient map and the reduction commutes. -/
theorem zmodReduction_bocksteinQuotient [NeZero n] [NeZero d]
    (q : H.{w'} ℤ_[J] ν ⧸ ((n * d) • AddMonoidHom.id (H.{w'} ℤ_[J] ν)).range) :
    zmodReduction n ν d (bocksteinQuotient (n * d) ν q) =
      bocksteinQuotient n ν (quotientNSMulMap n ν d q) := by
  induction q using QuotientAddGroup.induction_on with
  | H x => exact zmodReduction_reduction n ν d x

/-- **Compatibility on the right.** The square formed by `Hᵛ(ℤ/nd) → Hᵛ⁺¹(ℤ)[nd]`,
`Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)[n]`, the reduction and multiplication by `d` commutes. -/
theorem bocksteinTorsion_zmodReduction [NeZero n] [NeZero d] (y : H.{w'} ℤ/[J, (n * d)] ν) :
    bocksteinTorsion n ν (zmodReduction n ν d y) =
      torsionNSMulMap n ν d (bocksteinTorsion (n * d) ν y) :=
  Subtype.ext (bockstein_zmodReduction n ν d y)

end H

end Sheaf

end CategoryTheory

namespace TopCat.Sheaf

open CategoryTheory.Sheaf.H TopologicalSpace

/-! ### The Bockstein sequences of a topological space

For a topological space `X`, `Hᵛ(X, M)` is the cohomology of the constant sheaf `M` on the site
of open sets of `X`. -/

set_option hygiene false in
/-- The cohomology `Hᵛ(X, ℤ)` of a topological space. -/
local notation "Hℤ[" X ", " ν "]" =>
  CategoryTheory.Sheaf.H.{w'} ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ν

set_option hygiene false in
/-- The cohomology `Hᵛ(X, ℤ/n)` of a topological space. -/
local notation "Hℤ/[" X ", " n ", " ν "]" =>
  CategoryTheory.Sheaf.H.{w'} ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod n)))) ν

variable (X : TopCat.{u})
  [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  (n ν : ℕ) [NeZero n]

/-- Exactness of `Hᵛ(X, ℤ) --n--> Hᵛ(X, ℤ) → Hᵛ(X, ℤ/n)`. -/
theorem exact_nsmul_reduction :
    Function.Exact (fun x : Hℤ[X, ν] ↦ n • x) (reduction n ν) :=
  CategoryTheory.Sheaf.H.exact_nsmul_reduction n ν

/-- Exactness of `Hᵛ(X, ℤ) → Hᵛ(X, ℤ/n) → Hᵛ⁺¹(X, ℤ)`. -/
theorem exact_reduction_bockstein :
    Function.Exact (reduction.{w'} (J := Opens.grothendieckTopology X) n ν) (bockstein n ν) :=
  CategoryTheory.Sheaf.H.exact_reduction_bockstein n ν

/-- Exactness of `Hᵛ(X, ℤ/n) → Hᵛ⁺¹(X, ℤ) --n--> Hᵛ⁺¹(X, ℤ)`. -/
theorem exact_bockstein_nsmul :
    Function.Exact (bockstein.{w'} (J := Opens.grothendieckTopology X) n ν)
      (fun x : Hℤ[X, ν + 1] ↦ n • x) :=
  CategoryTheory.Sheaf.H.exact_bockstein_nsmul n ν

/-- `Hᵛ(X, ℤ)/n → Hᵛ(X, ℤ/n)` is injective. -/
theorem injective_bocksteinQuotient :
    Function.Injective (bocksteinQuotient.{w'} (J := Opens.grothendieckTopology X) n ν) :=
  CategoryTheory.Sheaf.H.injective_bocksteinQuotient n ν

/-- Exactness of `Hᵛ(X, ℤ)/n → Hᵛ(X, ℤ/n) → Hᵛ⁺¹(X, ℤ)[n]`. -/
theorem exact_bocksteinQuotient_bocksteinTorsion :
    Function.Exact (bocksteinQuotient.{w'} (J := Opens.grothendieckTopology X) n ν)
      (bocksteinTorsion n ν) :=
  CategoryTheory.Sheaf.H.exact_bocksteinQuotient_bocksteinTorsion n ν

/-- `Hᵛ(X, ℤ/n) → Hᵛ⁺¹(X, ℤ)[n]` is surjective. -/
theorem surjective_bocksteinTorsion :
    Function.Surjective (bocksteinTorsion.{w'} (J := Opens.grothendieckTopology X) n ν) :=
  CategoryTheory.Sheaf.H.surjective_bocksteinTorsion n ν

variable (d : ℕ) [NeZero d]

/-- Compatibility of `Hᵛ(X, ℤ)/n → Hᵛ(X, ℤ/n)` with the reduction `ℤ/nd → ℤ/n`. -/
theorem zmodReduction_bocksteinQuotient
    (q : Hℤ[X, ν] ⧸ ((n * d) • AddMonoidHom.id (Hℤ[X, ν])).range) :
    zmodReduction n ν d (bocksteinQuotient (n * d) ν q) =
      bocksteinQuotient n ν (quotientNSMulMap n ν d q) :=
  CategoryTheory.Sheaf.H.zmodReduction_bocksteinQuotient n ν d q

/-- Compatibility of `Hᵛ(X, ℤ/n) → Hᵛ⁺¹(X, ℤ)[n]` with the reduction `ℤ/nd → ℤ/n`. -/
theorem bocksteinTorsion_zmodReduction (y : Hℤ/[X, n * d, ν]) :
    bocksteinTorsion n ν (zmodReduction n ν d y) =
      torsionNSMulMap n ν d (bocksteinTorsion (n * d) ν y) :=
  CategoryTheory.Sheaf.H.bocksteinTorsion_zmodReduction n ν d y

end TopCat.Sheaf
