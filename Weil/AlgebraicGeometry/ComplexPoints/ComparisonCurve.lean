/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.AlgebraicGeometry.ComplexPoints.GAGACurvePicard
public import Weil.AlgebraicGeometry.ComplexPoints.GAGACurveFunctions
public import Weil.AlgebraicGeometry.ComplexPoints.CurveUnitsCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.Curves.SmoothCurveHIGmVanish
public import Weil.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootOfUnityTrivializesMu
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnitySheaf
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveGeometry
public import Weil.Attr

/-!
# Artin's comparison theorem for a smooth projective complex curve

Let `C` be a smooth projective curve over `ℂ`, `ε : C(ℂ) → C_et` the comparison of the analytic
site with the small étale site, and `n ≥ 1`. The comparison map
`c^ν : H^ν_et(C, ℤ/n) → H^ν(C(ℂ), ε^* ℤ/n)` is bijective for every `ν`, and so is the comparison map
for the constant sheaf of any finite abelian group.

The proof compares the two Kummer sequences. On the étale side,
`0 → ℤ/n → 𝐆_m → 𝐆_m → 0`, the first map sending `1` to `ζ = e^{2πi/n}` and the second the
`n`-th power map, is short exact: `ℤ/n → μ_n` is locally bijective (an `n`-th root of unity is
Zariski-locally a power of `ζ`, distinct powers differ by a unit) and the `n`-th power map is
étale-locally surjective. On the analytic side, `0 → ℤ/n → 𝒪^× → 𝒪^× → 0` is short exact on
`C(ℂ)` (local `n`-th roots of nowhere vanishing holomorphic functions, and roots of unity are
locally constant). The units comparison `𝐆_m → ε_* 𝒪^×` and the map `ℤ/n → ε_* ℤ/n` adjoint to
`ε^* ℤ/n ≅ ℤ/n` form a morphism of short exact sequences; the first square commutes because both
composites send `1` to the constant function `ζ`. The induced maps `u^q` on the cohomology of the
units are bijective: for `q = 0` this is GAGA for functions (an invertible regular function is the
same as a nowhere vanishing holomorphic function on the compact Riemann surface `C(ℂ)`), for
`q = 1` GAGA for line bundles, and for `q ≥ 2` both groups vanish. The five lemma gives
bijectivity on `ℤ/n`. For a finite abelian group `A`, induction on `|A|` with a cyclic subgroup
and the five lemma for the middle term reduces to the cyclic case.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.etaleKummerSequence`: the étale Kummer sequence
  `0 → ℤ/n → 𝐆_m → 𝐆_m → 0`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticKummerSequence`: the analytic Kummer sequence
  `0 → ℤ/n → 𝒪^× → 𝒪^× → 0` on the analytic site.
* `AlgebraicGeometry.Scheme.ComplexPoints.kummerComparison`: the morphism from the first to `ε_*`
  of the second.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_comparisonMapAlong_τ₁`,
  `AlgebraicGeometry.Scheme.ComplexPoints.bijective_comparisonMapAlong_τ₂`: the five lemma for
  comparison maps along a morphism of short exact sequences.
* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_comparisonMap_of_shortExact`: two out of three
  for bijectivity of the comparison maps in a short exact sequence of étale sheaves.
* `AlgebraicGeometry.Scheme.ComplexPoints.shortExact_etaleKummerSequence`,
  `AlgebraicGeometry.Scheme.ComplexPoints.shortExact_analyticKummerSequence`.
* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_unitsComparisonH`: `u^q` is bijective for every
  `q` on a smooth projective curve.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_constant_zmod_bijective_of_curve`: the
  comparison map of `ℤ/n` is bijective in every degree.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_constant_finite_bijective_of_curve`: the
  same for the constant sheaf of a finite abelian group.

## Implementation notes

The second map of the analytic Kummer sequence is written `n • 𝟙`, which is the `n`-th power map
in the additive notation of `𝒪^×`; the étale `n`-th power map `Stacks.Kummer.powMap` is `n • 𝟙`
by definition. The constant sheaf `ℤ/n` has coefficients `ULift (ZMod n)` in the coefficient
universe of étale cohomology. The root of unity is `ComplexManifold.primitiveRootUnit n` and
`k ↦ ζ^k` is `ComplexManifold.zmodToUnits n` on both sides, so that the comparison of the two
first maps is a computation with constants.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11,
  proof of Theorem 11.6.
* [SGA4] *Théorie des topos et cohomologie étale des schémas*, Exposé XVI, §4.
-/

@[expose] public section

open CategoryTheory Limits Opposite Abelian

-- These instances leave the universe `w` of `AddCommGrpCat.{max v₁ w}` undetermined, and
-- unification against them gets stuck on `u + 1 =?= max (u + 1) ?w`.
attribute [-instance] Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction
  Stacks.Cohomology.DerivedLowerShriek.preservesColimits_abelianRestriction

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### The five lemma for comparison maps along a morphism of short exact sequences -/

section FiveLemma

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

theorem comparisonMapAlong_map_f {S : ShortComplex (EtSheaf Y)} {T : ShortComplex (AnSheaf y)}
    (ψ : S ⟶ T.map (analyticDirectImage y)) (n : ℕ) (x : Sheaf.H.{1} S.X₁ n) :
    comparisonMapAlong y ψ.τ₂ n (Sheaf.H.map S.f n x) =
      Sheaf.H.map T.f n (comparisonMapAlong y ψ.τ₁ n x) := by
  rw [comparisonMapAlong_apply, comparisonMapAlong_apply, comparisonMap_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  congr 2
  exact ((adjointShortComplexHom y ψ).comm₁₂).symm

theorem comparisonMapAlong_map_g {S : ShortComplex (EtSheaf Y)} {T : ShortComplex (AnSheaf y)}
    (ψ : S ⟶ T.map (analyticDirectImage y)) (n : ℕ) (x : Sheaf.H.{1} S.X₂ n) :
    comparisonMapAlong y ψ.τ₃ n (Sheaf.H.map S.g n x) =
      Sheaf.H.map T.g n (comparisonMapAlong y ψ.τ₂ n x) := by
  rw [comparisonMapAlong_apply, comparisonMapAlong_apply, comparisonMap_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  congr 2
  exact ((adjointShortComplexHom y ψ).comm₂₃).symm

/-- **The five lemma for comparison maps.** For a morphism `ψ : S ⟶ ε_* T` of short exact
sequences, the comparison map along `ψ.τ₁` is bijective in degree `n` as soon as the comparison
maps along `ψ.τ₂` and `ψ.τ₃` are bijective in degrees `n` and `n - 1` (only injectivity of the
one along `ψ.τ₃` in degree `n`, and only surjectivity of the one along `ψ.τ₂` in degree `n - 1`,
are used). -/
theorem bijective_comparisonMapAlong_τ₁ {S : ShortComplex (EtSheaf Y)}
    {T : ShortComplex (AnSheaf y)} (hS : S.ShortExact) (hT : T.ShortExact)
    (ψ : S ⟶ T.map (analyticDirectImage y)) (n : ℕ)
    (h₂ : Function.Bijective (comparisonMapAlong y ψ.τ₂ n))
    (h₃ : Function.Injective (comparisonMapAlong y ψ.τ₃ n))
    (h₂' : ∀ m, m + 1 = n → Function.Surjective (comparisonMapAlong y ψ.τ₂ m))
    (h₃' : ∀ m, m + 1 = n → Function.Bijective (comparisonMapAlong y ψ.τ₃ m)) :
    Function.Bijective (comparisonMapAlong y ψ.τ₁ n) := by
  have hSf := hS.mono_f
  have hTf := hT.mono_f
  -- `H.map f` in terms of `Ext.comp`
  have hmapS : ∀ (m : ℕ) (x : Sheaf.H.{1} S.X₁ m),
      Sheaf.H.map S.f m x = x.comp (Ext.mk₀ S.f) (add_zero m) := fun _ _ => rfl
  rcases n with _ | m
  · refine ⟨fun a b hab => ?_, fun z => ?_⟩
    · apply Ext.postcomp_mk₀_injective_of_mono _ S.f
      apply h₂.1
      change comparisonMapAlong y ψ.τ₂ 0 (Sheaf.H.map S.f 0 a) =
        comparisonMapAlong y ψ.τ₂ 0 (Sheaf.H.map S.f 0 b)
      rw [comparisonMapAlong_map_f, comparisonMapAlong_map_f, hab]
    · obtain ⟨w, hw⟩ := h₂.2 (Sheaf.H.map T.f 0 z)
      have hgw : Sheaf.H.map S.g 0 w = 0 := by
        apply h₃
        rw [comparisonMapAlong_map_g, hw, ← Sheaf.H.map_comp_apply, T.zero, map_zero]
        simp [Sheaf.H.map_apply]
      obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ hS w hgw
      refine ⟨x, ?_⟩
      apply Ext.postcomp_mk₀_injective_of_mono _ T.f
      change Sheaf.H.map T.f 0 _ = Sheaf.H.map T.f 0 z
      rw [← comparisonMapAlong_map_f, ← hw]
      exact congrArg _ hx
  · refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩
    · have h1 : Sheaf.H.map S.f (m + 1) x = 0 :=
        (injective_iff_map_eq_zero _).1 h₂.1 _ (by rw [comparisonMapAlong_map_f, hx, map_zero])
      obtain ⟨w, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x h1 rfl
      rw [comparisonMapAlong_comp_extClass y hS hT] at hx
      obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ rfl hx
      obtain ⟨z', rfl⟩ := (h₂' m rfl) z
      have hw : Sheaf.H.map S.g m z' = w :=
        (h₃' m rfl).1 (by rw [comparisonMapAlong_map_g]; exact hz)
      rw [← hw, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
    · obtain ⟨w, hw⟩ := h₂.2 (Sheaf.H.map T.f (m + 1) z)
      have hgw : Sheaf.H.map S.g (m + 1) w = 0 := by
        apply (injective_iff_map_eq_zero _).1 h₃
        rw [comparisonMapAlong_map_g, hw, ← Sheaf.H.map_comp_apply, T.zero]
        simp [Sheaf.H.map_apply]
      obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ hS w hgw
      have hd : Sheaf.H.map T.f (m + 1) (z - comparisonMapAlong y ψ.τ₁ (m + 1) x) = 0 := by
        rw [map_sub, ← comparisonMapAlong_map_f, ← hw, hmapS, hx, sub_self]
      obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁ _ hT _ hd rfl
      obtain ⟨t', rfl⟩ := (h₃' m rfl).2 t
      refine ⟨x + t'.comp hS.extClass rfl, ?_⟩
      rw [map_add, comparisonMapAlong_comp_extClass y hS hT, ht]
      abel

/-- The five lemma for the middle term: for a morphism `ψ : S ⟶ ε_* T` of short exact sequences
whose comparison maps along `ψ.τ₁` and `ψ.τ₃` are bijective in every degree, the comparison maps
along `ψ.τ₂` are bijective in every degree. -/
theorem bijective_comparisonMapAlong_τ₂ {S : ShortComplex (EtSheaf Y)}
    {T : ShortComplex (AnSheaf y)} (hS : S.ShortExact) (hT : T.ShortExact)
    (ψ : S ⟶ T.map (analyticDirectImage y))
    (h₁ : ∀ m, Function.Bijective (comparisonMapAlong y ψ.τ₁ m))
    (h₃ : ∀ m, Function.Bijective (comparisonMapAlong y ψ.τ₃ m)) (n : ℕ) :
    Function.Bijective (comparisonMapAlong y ψ.τ₂ n) := by
  have hTf := hT.mono_f
  have hmapS : ∀ (m : ℕ) (x : Sheaf.H.{1} S.X₁ m),
      Sheaf.H.map S.f m x = x.comp (Ext.mk₀ S.f) (add_zero m) := fun _ _ => rfl
  have hmapT : ∀ (m : ℕ) (x : Sheaf.H.{1} T.X₁ m),
      Sheaf.H.map T.f m x = x.comp (Ext.mk₀ T.f) (add_zero m) := fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩
  · have hgx : Sheaf.H.map S.g n x = 0 := (injective_iff_map_eq_zero _).1 (h₃ n).1 _
      (by rw [comparisonMapAlong_map_g, hx, map_zero])
    obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x hgx
    have hfx : Sheaf.H.map T.f n (comparisonMapAlong y ψ.τ₁ n x₁) = 0 := by
      rw [← comparisonMapAlong_map_f, hmapS]
      exact hx
    rcases n with _ | m
    · have h0 : comparisonMapAlong y ψ.τ₁ 0 x₁ = 0 :=
        Ext.postcomp_mk₀_injective_of_mono _ T.f (hfx.trans (by simp))
      rw [(injective_iff_map_eq_zero _).1 (h₁ 0).1 _ h0]
      simp
    · obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₁ _ hT _ (by rw [← hmapT]; exact hfx) rfl
      obtain ⟨w', rfl⟩ := (h₃ m).2 w
      rw [← comparisonMapAlong_comp_extClass y hS hT] at hw
      rw [← (h₁ (m + 1)).1 hw, Ext.comp_assoc_of_third_deg_zero,
        ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]
  · obtain ⟨u, hu⟩ := (h₃ n).2 (Sheaf.H.map T.g n z)
    have hδ : u.comp hS.extClass rfl = 0 := by
      apply (injective_iff_map_eq_zero _).1 (h₁ (n + 1)).1
      rw [comparisonMapAlong_comp_extClass y hS hT, hu, Sheaf.H.map_apply,
        Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
    obtain ⟨x, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS _ rfl hδ
    have hd : Sheaf.H.map T.g n (z - comparisonMapAlong y ψ.τ₂ n x) = 0 := by
      rw [map_sub, ← comparisonMapAlong_map_g, Sheaf.H.map_apply S.g x, hu, sub_self]
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₂ _ hT _ hd
    obtain ⟨t', rfl⟩ := (h₁ n).2 t
    refine ⟨x + Sheaf.H.map S.f n t', ?_⟩
    rw [map_add, comparisonMapAlong_map_f, hmapT, ht]
    abel

/-- The morphism of short complexes `S ⟶ ε_* ε^* S` given by the unit of `ε^* ⊣ ε_*`. -/
noncomputable def unitShortComplexHom (S : ShortComplex (EtSheaf Y)) :
    S ⟶ (S.map (analyticInverseImage y)).map (analyticDirectImage y) where
  τ₁ := (analyticAdjunction y).unit.app S.X₁
  τ₂ := (analyticAdjunction y).unit.app S.X₂
  τ₃ := (analyticAdjunction y).unit.app S.X₃
  comm₁₂ := ((analyticAdjunction y).unit.naturality S.f).symm
  comm₂₃ := ((analyticAdjunction y).unit.naturality S.g).symm

theorem comparisonMapAlong_unit (F : EtSheaf Y) (n : ℕ) (x : Sheaf.H.{1} F n) :
    comparisonMapAlong y ((analyticAdjunction y).unit.app F) n x = comparisonMap y F n x := by
  rw [comparisonMapAlong_apply, ← Adjunction.homEquiv_id]
  erw [Equiv.symm_apply_apply, Sheaf.H.map_id_apply]
  rfl

/-- **Two out of three for the comparison map**: in a short exact sequence `0 → F' → F → F'' → 0`
of étale sheaves, if the comparison maps of `F'` and `F''` are bijective in every degree, so are
those of `F`. -/
theorem bijective_comparisonMap_of_shortExact {S : ShortComplex (EtSheaf Y)} (hS : S.ShortExact)
    (h₁ : ∀ m, Function.Bijective (comparisonMap y S.X₁ m))
    (h₃ : ∀ m, Function.Bijective (comparisonMap y S.X₃ m)) (n : ℕ) :
    Function.Bijective (comparisonMap y S.X₂ n) := by
  have key : ∀ F m, ⇑(comparisonMapAlong y ((analyticAdjunction y).unit.app F) m) =
      ⇑(comparisonMap y F m) := fun F m => funext (comparisonMapAlong_unit y F m)
  have := bijective_comparisonMapAlong_τ₂ y hS (hS.map_of_exact (analyticInverseImage y))
    (unitShortComplexHom y S) (fun m => by rw [unitShortComplexHom, key]; exact h₁ m)
    (fun m => by rw [unitShortComplexHom, key]; exact h₃ m) n
  rwa [unitShortComplexHom, key] at this

/-- Bijectivity of the comparison map is invariant under isomorphisms of étale sheaves. -/
theorem bijective_comparisonMap_of_iso {F G : EtSheaf Y} (e : F ≅ G) (n : ℕ)
    (h : Function.Bijective (comparisonMap y F n)) :
    Function.Bijective (comparisonMap y G n) := by
  have key : ∀ x, comparisonMap y G n x = Sheaf.H.map ((analyticInverseImage y).map e.hom) n
      (comparisonMap y F n (Sheaf.H.map e.inv n x)) := fun x => by
    rw [← comparisonMap_naturality, ← Sheaf.H.map_comp_apply, Iso.inv_hom_id,
      Sheaf.H.map_id_apply]
  have hb : ∀ {A B : Sheaf _ AddCommGrpCat.{1}} (e : A ≅ B) (m : ℕ),
      Function.Bijective (Sheaf.H.map (J := Opens.grothendieckTopology (analyticSpace y)) e.hom m)
      := fun e m => ⟨fun a b hab => by
        simpa [← Sheaf.H.map_comp_apply] using congrArg (Sheaf.H.map e.inv m) hab,
      fun z => ⟨Sheaf.H.map e.inv m z, by rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id,
        Sheaf.H.map_id_apply]⟩⟩
  have hb' : Function.Bijective (Sheaf.H.map (J := Y.smallEtaleTopology) e.inv n) :=
    ⟨fun a b hab => by
      simpa [← Sheaf.H.map_comp_apply] using congrArg (Sheaf.H.map e.hom n) hab,
      fun z => ⟨Sheaf.H.map e.hom n z, by rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id,
        Sheaf.H.map_id_apply]⟩⟩
  have : ⇑(comparisonMap y G n) = Sheaf.H.map ((analyticInverseImage y).map e.hom) n ∘
      comparisonMap y F n ∘ Sheaf.H.map e.inv n := funext key
  rw [this]
  exact (hb ((analyticInverseImage y).mapIso e) n).comp (h.comp hb')

end FiveLemma

/-! ### The root of unity `e^{2πi/n}` -/

section Root

open ComplexManifold

variable (n : ℕ) [NeZero n]

theorem isPrimitiveRoot_coe_primitiveRootUnit : IsPrimitiveRoot (primitiveRootUnit n : ℂ) n :=
  IsPrimitiveRoot.coe_units_iff.mpr (isPrimitiveRoot_primitiveRootUnit n)

theorem primitiveRootUnit_pow : primitiveRootUnit n ^ n = 1 :=
  (isPrimitiveRoot_primitiveRootUnit n).pow_eq_one

theorem toMul_zmodToUnits (k : ZMod n) :
    (zmodToUnits n k).toMul = primitiveRootUnit n ^ k.val := by
  have h := (isPrimitiveRoot_primitiveRootUnit n).zmodEquivZPowers_apply_coe_nat k.val
  rw [ZMod.natCast_zmod_val] at h
  rw [zmodToUnits, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

end Root

/-! ### The étale Kummer sequence with constant coefficients -/

section Etale

open Stacks.Kummer

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) (n : ℕ) [NeZero n]

/-- The coefficient group `ℤ/n`, in the coefficient universe of étale cohomology. -/
abbrev zmodCoeff : AddCommGrpCat.{1} := AddCommGrpCat.of (ULift.{1} (ZMod n))

/-- The constants `ℂ → Γ(U, 𝒪_U)` of an étale `Y`-scheme `U`, through `Y`. -/
noncomputable def etaleConstHom (U : Y.Etale) : ℂ →+* Γ(U.left, ⊤) :=
  ((isTerminal_etaleTop Y).some.from U).left.appTop.hom.comp (constHom (y := y) ⊤)

/-- The global section `k ↦ ζ^k` of `𝐆_m`, `ζ = e^{2πi/n}`. -/
noncomputable def zmodToUnitsGlobal :
    zmodCoeff n ⟶ (multiplicativeSheaf.{0, 1} Y).obj.obj (op (etaleTop Y)) :=
  AddCommGrpCat.ofHom ((AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((Units.map (constHom (y := y) ⊤).toMonoidHom).toAdditive.comp
      (ComplexManifold.zmodToUnits n))).comp
      AddEquiv.ulift.toAddMonoidHom)

/-- The morphism `ℤ/n ⟶ 𝐆_m` of étale sheaves sending `1` to `ζ = e^{2πi/n}`. -/
noncomputable def etaleZetaMap :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (zmodCoeff n) ⟶
      multiplicativeSheaf.{0, 1} Y :=
  ((constantSheafAdj _ _ (isTerminal_etaleTop Y).some).homEquiv _ _).symm (zmodToUnitsGlobal y n)

/-- The morphism from the constant presheaf `ℤ/n` to `𝐆_m`, `k ↦ ζ^k`. -/
noncomputable def etaleZetaPresheafMap :
    (Functor.const Y.Etaleᵒᵖ).obj (zmodCoeff n) ⟶ (multiplicativeSheaf.{0, 1} Y).obj :=
  ((constantPresheafAdj AddCommGrpCat.{1} (isTerminal_etaleTop Y).some).homEquiv _ _).symm
    (zmodToUnitsGlobal y n)

theorem toSheafify_comp_etaleZetaMap :
    toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (zmodCoeff n)) ≫
      (etaleZetaMap y n).hom = etaleZetaPresheafMap y n := by
  apply ((constantPresheafAdj AddCommGrpCat.{1} (isTerminal_etaleTop Y).some).homEquiv
    _ _).injective
  rw [etaleZetaPresheafMap, Equiv.apply_symm_apply]
  have h1 : (constantSheafAdj _ AddCommGrpCat.{1} (isTerminal_etaleTop Y).some).homEquiv _ _
      (etaleZetaMap y n) = zmodToUnitsGlobal y n := Equiv.apply_symm_apply _ _
  rw [← h1]
  change _ = ((constantPresheafAdj AddCommGrpCat.{1} (isTerminal_etaleTop Y).some).comp
    (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{1})).homEquiv _ _
      (etaleZetaMap y n)
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  refine congrArg ((constantPresheafAdj AddCommGrpCat.{1} (isTerminal_etaleTop Y).some).homEquiv
    _ _) ?_
  erw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
  rfl

theorem etaleZetaPresheafMap_app (U : Y.Etale) (k : ZMod n) :
    (etaleZetaPresheafMap y n).app (op U) (ULift.up k) =
      ofUnit.{0, 1} (Units.map (etaleConstHom y U).toMonoidHom
        (ComplexManifold.primitiveRootUnit n ^ k.val)) := by
  change (multiplicativeSheaf.{0, 1} Y).obj.map ((isTerminal_etaleTop Y).some.from U).op
    (ofUnit.{0, 1} (Units.map (constHom (y := y) ⊤).toMonoidHom
      (Additive.toMul (ComplexManifold.zmodToUnits n k)))) = _
  rw [toMul_zmodToUnits]
  rfl

omit [NeZero n] in
theorem isUnit_natCast_of_ringHom {R : Type*} [CommRing R] (ρ : ℂ →+* R) [NeZero n] :
    IsUnit ((n : ℕ) : R) := by
  rw [← map_natCast ρ]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (NeZero.ne n))).map ρ

theorem pow_map_primitiveRootUnit {R : Type*} [CommRing R] (ρ : ℂ →+* R) :
    (Units.map ρ.toMonoidHom (ComplexManifold.primitiveRootUnit n)) ^ n = 1 := by
  rw [← map_pow, primitiveRootUnit_pow, map_one]

theorem isUnit_map_primitiveRootUnit_pow_sub_one {R : Type*} [CommRing R] (ρ : ℂ →+* R) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) : IsUnit (ρ (ComplexManifold.primitiveRootUnit n : ℂ) ^ k - 1) := by
  rw [← map_pow, ← map_one ρ, ← map_sub]
  refine (IsUnit.mk0 _ ?_).map ρ
  rw [sub_ne_zero]
  intro h
  have := (isPrimitiveRoot_coe_primitiveRootUnit n).pow_inj hkn (NeZero.pos n) (by rw [h, pow_zero])
  omega

theorem etaleZetaPresheafMap_comp_powMap :
    etaleZetaPresheafMap y n ≫ (powMap.{0, 1} Y n).hom = 0 := by
  ext ⟨U⟩ ⟨k⟩
  change (powMap.{0, 1} Y n).hom.app (op U) ((etaleZetaPresheafMap y n).app (op U) (ULift.up k)) = 0
  rw [etaleZetaPresheafMap_app, powMap_app_ofUnit, ← map_pow, ← pow_mul, mul_comm, pow_mul,
    primitiveRootUnit_pow, one_pow, map_one, ofUnit_one]

theorem etaleZetaMap_comp_powMap : etaleZetaMap y n ≫ powMap.{0, 1} Y n = 0 := by
  ext1
  apply sheafify_hom_ext _ _ _ (multiplicativeSheaf.{0, 1} Y).property
  rw [ObjectProperty.FullSubcategory.comp_hom]
  erw [← Category.assoc, toSheafify_comp_etaleZetaMap, etaleZetaPresheafMap_comp_powMap]
  exact (comp_zero).symm

/-- **The étale Kummer sequence with constant coefficients** `0 → ℤ/n → 𝐆_m → 𝐆_m → 0`, the first
map sending `1` to `e^{2πi/n}` and the second the `n`-th power map. -/
noncomputable def etaleKummerSequence : ShortComplex (EtSheaf Y) :=
  ShortComplex.mk (etaleZetaMap y n) (powMap.{0, 1} Y n) (etaleZetaMap_comp_powMap y n)

/-- The morphism `ℤ/n ⟶ μ_n` sending `1` to `e^{2πi/n}`. -/
noncomputable def etaleZetaToRoots :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (zmodCoeff n) ⟶
      Stacks.Kummer.rootsOfUnitySheaf.{0, 1} Y n :=
  kernel.lift _ (etaleZetaMap y n) (etaleZetaMap_comp_powMap y n)

theorem etaleZetaToRoots_comp_ι :
    etaleZetaToRoots y n ≫ Stacks.Kummer.rootsOfUnityι.{0, 1} Y n = etaleZetaMap y n :=
  kernel.lift_ι _ _ _

theorem mem_smallEtaleTopology_of_isEmpty {U : Y.Etale} (hU : IsEmpty U.left) (S : Sieve U) :
    S ∈ Y.smallEtaleTopology U := by
  have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := fun _ : PEmpty.{1} => U)
    (fun i => i.elim)).2 (Set.eq_univ_of_forall fun x : U.left => isEmptyElim x)
  refine Y.smallEtaleTopology.superset_covering ?_ h
  rintro V g ⟨W, h, g', ⟨i⟩, _⟩
  exact i.elim

theorem etaleZetaPresheafMap_isLocallyInjective :
    Presheaf.IsLocallyInjective Y.smallEtaleTopology (etaleZetaPresheafMap y n) := by
  refine ⟨fun {U} a b hab => ?_⟩
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  by_cases hab' : a = b
  · subst hab'
    simp
  · apply mem_smallEtaleTopology_of_isEmpty
    rw [etaleZetaPresheafMap_app, etaleZetaPresheafMap_app] at hab
    have h : etaleConstHom y U.unop ((ComplexManifold.primitiveRootUnit n : ℂ) ^ a.val) =
        etaleConstHom y U.unop ((ComplexManifold.primitiveRootUnit n : ℂ) ^ b.val) := by
      have := congrArg Units.val (ofUnit_injective.{0, 1} hab)
      rw [Units.coe_map, Units.coe_map, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val] at this
      exact this
    have hne : (ComplexManifold.primitiveRootUnit n : ℂ) ^ a.val -
      (ComplexManifold.primitiveRootUnit n : ℂ) ^ b.val ≠ 0 := by
      rw [sub_ne_zero]
      intro h'
      exact hab' (ZMod.val_injective n
        ((isPrimitiveRoot_coe_primitiveRootUnit n).pow_inj (ZMod.val_lt a)
        (ZMod.val_lt b) h'))
    have hu := (IsUnit.mk0 _ hne).map (etaleConstHom y U.unop)
    rw [map_sub, h, sub_self, isUnit_zero_iff] at hu
    exact ConstantRootsOfUnity.isEmpty_of_one_eq_zero hu.symm

theorem etaleConstHom_of_hom {U V : Y.Etale} (f : V ⟶ U) (c : ℂ) :
    etaleConstHom y V c = f.left.appTop (etaleConstHom y U c) := by
  have h : (isTerminal_etaleTop Y).some.from V = f ≫ (isTerminal_etaleTop Y).some.from U :=
    (isTerminal_etaleTop Y).some.hom_ext _ _
  simp only [etaleConstHom, h]
  change (f.left ≫ ((isTerminal_etaleTop Y).some.from U).left).appTop.hom (constHom ⊤ c) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem etaleZetaToRoots_isLocallySurjective :
    Sheaf.IsLocallySurjective (etaleZetaToRoots y n) := by
  refine ⟨fun {U} s => ?_⟩
  obtain ⟨w, hw⟩ := ofUnit_surjective.{0, 1}
    ((Stacks.Kummer.rootsOfUnityι.{0, 1} Y n).hom.app (op U) s)
  have hwn : w ^ n = 1 := pow_eq_one_of_rootsOfUnitySheaf Y n U s w hw.symm
  let ρ := etaleConstHom y U
  have hζn : (ρ (ComplexManifold.primitiveRootUnit n : ℂ)) ^ n = 1 := by
    rw [← map_pow, (isPrimitiveRoot_coe_primitiveRootUnit n).pow_eq_one, map_one]
  choose V j hpV hjn hpull using fun p => Scheme.exists_open_pullback_eq_pow U.left
    (isUnit_natCast_of_ringHom n ρ) hζn (isUnit_map_primitiveRootUnit_pow_sub_one n ρ)
      (w : Γ(U.left, ⊤))
    (by rw [← Units.val_pow_eq_pow_val, hwn, Units.val_one]) p
  have : Etale U.hom := U.prop
  let Z : U.left → Y.Etale := fun p => Scheme.Etale.mk ((V p).ι ≫ U.hom)
  let f : ∀ p, Z p ⟶ U := fun p => MorphismProperty.Over.homMk (V p).ι rfl
  have hcov : Sieve.ofArrows Z f ∈ Y.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨p, ?_⟩
    change p ∈ Set.range (V p).ι
    rw [Scheme.Opens.range_ι]
    exact hpV p
  refine Y.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  have hinj := injective_rootsOfUnityι_app.{0, 1} Y n
  let ιμ := Stacks.Kummer.rootsOfUnityι.{0, 1} Y n
  have hιμ : etaleZetaToRoots y n ≫ ιμ = etaleZetaMap y n := etaleZetaToRoots_comp_ι y n
  rintro W - ⟨p⟩
  refine ⟨(toSheafify _ ((Functor.const _).obj (zmodCoeff n))).app (op (Z p))
    (ULift.up (j p : ZMod n)), ?_⟩
  apply hinj (Z p)
  have h1 : ιμ.hom.app (op (Z p))
      ((etaleZetaToRoots y n).hom.app (op (Z p))
        ((toSheafify _ ((Functor.const _).obj (zmodCoeff n))).app (op (Z p))
          (ULift.up (j p : ZMod n)))) =
      (etaleZetaPresheafMap y n).app (op (Z p)) (ULift.up (j p : ZMod n)) := by
    rw [← toSheafify_comp_etaleZetaMap, ← hιμ]
    rfl
  rw [h1, NatTrans.naturality_apply ιμ.hom, ← hw,
    map_ofUnit, etaleZetaPresheafMap_app]
  congr 1
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, Units.val_pow_eq_pow_val, ZMod.val_natCast_of_lt (hjn p)]
  change etaleConstHom y (Z p) _ = _
  rw [etaleConstHom_of_hom y (f p), map_pow (etaleConstHom y U)]
  have := hpull p (V p) (V p).ι (fun z => z.2)
  rw [Scheme.Γ_map_op] at this
  exact this.symm

theorem isIso_etaleZetaToRoots : IsIso (etaleZetaToRoots y n) := by
  refine (Sheaf.isLocallyBijective_iff_isIso (etaleZetaToRoots y n)).1
    ⟨?_, etaleZetaToRoots_isLocallySurjective y n⟩
  have := etaleZetaPresheafMap_isLocallyInjective y n
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology (etaleZetaMap y n).hom := by
    refine @Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _ _ _ _ _ _ _
      _ _ _ _ _ (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (zmodCoeff n)))
      (etaleZetaMap y n).hom ?_ ?_
    · rw [toSheafify_comp_etaleZetaMap]
      infer_instance
    · infer_instance
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology
      ((etaleZetaToRoots y n).hom ≫ (Stacks.Kummer.rootsOfUnityι.{0, 1} Y n).hom) := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, etaleZetaToRoots_comp_ι]
    infer_instance
  exact Presheaf.isLocallyInjective_of_isLocallyInjective _ (etaleZetaToRoots y n).hom
    (Stacks.Kummer.rootsOfUnityι.{0, 1} Y n).hom

/-- **The étale Kummer sequence `0 → ℤ/n → 𝐆_m → 𝐆_m → 0` is short exact** on a scheme over
`ℂ`. -/
theorem shortExact_etaleKummerSequence : (etaleKummerSequence y n).ShortExact := by
  have hS := Stacks.Kummer.kummerSequence_shortExact.{0, 1} Y (NeZero.ne n)
    (isUnit_natCast_of_ringHom n (constHom (y := y) ⊤))
  let e : etaleKummerSequence y n ≅ Stacks.Kummer.kummerSequence.{0, 1} Y n :=
    ShortComplex.isoMk (@asIso _ _ _ _ (etaleZetaToRoots y n) (isIso_etaleZetaToRoots y n))
      (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact ShortComplex.shortExact_of_iso e.symm hS
  · simp only [Iso.refl_hom]
    exact etaleZetaToRoots_comp_ι y n
  · simp only [Iso.refl_hom]
    rfl

end Etale

/-! ### The analytic Kummer sequence with constant coefficients -/

section Analytic

open ComplexManifold
open scoped Manifold ContDiff

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 y] (n : ℕ)
  [NeZero n]

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one

/-- The morphism from the constant presheaf `ℤ/n` to `𝒪^×` on the analytic site, `k ↦ ζ^k`. -/
noncomputable def analyticZetaPresheafMap :
    (Functor.const (TopologicalSpace.Opens (analyticSpace y))ᵒᵖ).obj (zmodCoeff n) ⟶
      (analyticUnitsSheaf y).obj where
  app V := AddCommGrpCat.ofHom ((AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((unitsConstSections (I := 𝓘(ℂ)) (downOpens V.unop)).comp (zmodToUnits n))).comp
      AddEquiv.ulift.toAddMonoidHom)
  naturality _ _ _ := rfl

theorem analyticZetaPresheafMap_comp_nsmul :
    analyticZetaPresheafMap y n ≫ (n • 𝟙 (analyticUnitsSheaf y)).hom = 0 := by
  ext U a : 4
  obtain ⟨a⟩ := a
  apply ULift.ext
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun w => ?_
  exact zmodToUnits_pow n a

/-- The morphism `ℤ/n ⟶ 𝒪^×` of sheaves on the analytic site sending `1` to `e^{2πi/n}`. -/
noncomputable def analyticZetaMap :
    (constantSheaf (Opens.grothendieckTopology (analyticSpace y)) AddCommGrpCat.{1}).obj
      (zmodCoeff n) ⟶ analyticUnitsSheaf y :=
  TopCat.Sheaf.constantSheafLift (analyticZetaPresheafMap y n)

/-- **The analytic Kummer sequence with constant coefficients** `0 → ℤ/n → 𝒪^× → 𝒪^× → 0` on the
analytic site of `Y`, the second map being multiplication by `n` (the `n`-th power map). -/
noncomputable def analyticKummerSequence : ShortComplex (AnSheaf y) :=
  ShortComplex.mk (analyticZetaMap y n) (n • 𝟙 (analyticUnitsSheaf y))
    (TopCat.Sheaf.constantSheafLift_comp_eq_zero _ _ (analyticZetaPresheafMap_comp_nsmul y n))

theorem epi_nsmul_analyticUnitsSheaf : Epi (n • 𝟙 (analyticUnitsSheaf y)) := by
  have h1 : Epi (ComplexManifold.powMap (I := 𝓘(ℂ)) (M := ComplexPoints y) n) :=
    (kummerSequence_shortExact 𝓘(ℂ) (ComplexPoints y) n).epi_g
  have h2 : ComplexManifold.powMap (I := 𝓘(ℂ)) (M := ComplexPoints y) n = n • 𝟙 _ := by
    ext U : 3
    rfl
  have h3 : (liftToAnalytic y).map (ComplexManifold.powMap (I := 𝓘(ℂ)) (M := ComplexPoints y) n) =
      n • 𝟙 (analyticUnitsSheaf y) := by
    rw [h2, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rw [← h3]
  infer_instance

/-- **The analytic Kummer sequence `0 → ℤ/n → 𝒪^× → 𝒪^× → 0` is short exact.** -/
theorem shortExact_analyticKummerSequence : (analyticKummerSequence y n).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_constantSheafLift _ _ ?_
    (analyticZetaPresheafMap_comp_nsmul y n) ?_ ?_
  · rintro U ⟨p, hp⟩ ⟨a⟩ ⟨b⟩ hab
    have h : (zmodToUnits n a).toMul = (zmodToUnits n b).toMul :=
      congrArg (fun f : ToType ((analyticUnitsSheaf y).obj.obj (op U)) =>
        (show C^∞⟮𝓘(ℂ), ↥(downOpens U); 𝓘(ℂ), ℂˣ⟯ from Additive.toMul f.down) ⟨p.down, hp⟩) hab
    exact congrArg ULift.up (zmodToUnits_injective n (Additive.toMul.injective h))
  · intro U s hs x hx
    let u : C^∞⟮𝓘(ℂ), ↥(downOpens U); 𝓘(ℂ), ℂˣ⟯ := Additive.toMul s.down
    have hpow : ∀ w : downOpens U, u w ^ n = 1 := fun w =>
      congrArg (fun t : ToType ((analyticUnitsSheaf y).obj.obj (op U)) =>
        ((show C^∞⟮𝓘(ℂ), ↥(downOpens U); 𝓘(ℂ), ℂˣ⟯ from Additive.toMul t.down) w : ℂˣ)) hs
    let v : downOpens U → _root_.rootsOfUnity n ℂ := fun w =>
      ⟨u w, (_root_.mem_rootsOfUnity _ _).mpr (hpow w)⟩
    have hv : Continuous v := Continuous.subtype_mk u.2.continuous _
    have hlc : IsLocallyConstant v := (IsLocallyConstant.iff_continuous v).mpr hv
    let x₀ : downOpens U := ⟨x.down, hx⟩
    let S : Set (downOpens U) := {w | v w = v x₀}
    have hS : IsOpen S := hlc.isOpen_fiber _
    let V : TopologicalSpace.Opens (analyticSpace y) :=
      (TopCat.opensULiftEquivalence (ComplexPoints y)).inverse.obj
        (opensOfSubtype (downOpens U) S hS)
    have hVU : V ≤ U := fun q hq => opensOfSubtype_le (downOpens U) S hS hq
    obtain ⟨a, ha⟩ := exists_zmodToUnits_eq n (hpow x₀)
    refine ⟨V, hVU, mem_opensOfSubtype (hS := hS) (y := x₀) rfl, ULift.up a, ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    refine ContMDiffMap.ext fun w => ?_
    change (zmodToUnits n a).toMul = u ⟨w.1, hVU w.2⟩
    have hw : v ⟨w.1, hVU w.2⟩ = v x₀ := of_mem_opensOfSubtype (hS := hS) w.2
    rw [ha]
    exact (congrArg Subtype.val hw).symm
  · have := epi_nsmul_analyticUnitsSheaf y n
    exact (TopCat.Sheaf.isLocallySurjective_iff_epi (X := analyticSpace y) _).mpr this

end Analytic

/-! ### The comparison of the two Kummer sequences -/

section Ladder

open ComplexManifold
open scoped Manifold ContDiff

/-- Maps out of a constant sheaf on a topological space given by a morphism from the constant
presheaf correspond, under the constant-sheaf adjunction, to that morphism on the whole space. -/
theorem constantSheafAdj_homEquiv_constantSheafLift {X : TopCat.{1}} {A : AddCommGrpCat.{1}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{1}}
    (φ : (Functor.const (TopologicalSpace.Opens X)ᵒᵖ).obj A ⟶ F.obj) :
    (constantSheafAdj _ AddCommGrpCat.{1} isTerminalTop).homEquiv A F
      (TopCat.Sheaf.constantSheafLift φ) = φ.app (op ⊤) := by
  change ((constantPresheafAdj AddCommGrpCat.{1} isTerminalTop).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{1})).homEquiv _ _
      (TopCat.Sheaf.constantSheafLift φ) = _
  have h : (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{1}).homEquiv
      _ F (TopCat.Sheaf.constantSheafLift φ) = φ := by
    erw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
    exact TopCat.Sheaf.toSheafify_comp_constantSheafLift φ
  rw [Adjunction.comp_homEquiv]
  change (constantPresheafAdj AddCommGrpCat.{1} isTerminalTop).homEquiv _ _
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{1}).homEquiv
      _ F (TopCat.Sheaf.constantSheafLift φ)) = _
  rw [h]
  rfl

theorem eval_constHom_of_eq {Y : Scheme.{0}} {y y' : Y ⟶ Spec (.of ℂ)} (h : y' = y) (c : ℂ)
    (p : ComplexPoints y') {U : Y.Opens} (hp : p.Mem U) :
      eval (constHom (y := y) U c) p hp = c := by
  subst h
  exact eval_constHom c p hp

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 y] (n : ℕ)
  [NeZero n]

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one

/-- The first component of the comparison of the Kummer sequences: the map
`ℤ/n ⟶ ε_* ℤ/n` adjoint to `ε^* ℤ/n ≅ ℤ/n`. -/
noncomputable def kummerComparisonτ₁ :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (zmodCoeff n) ⟶
      (analyticDirectImage y).obj
        ((constantSheaf (Opens.grothendieckTopology (analyticSpace y)) AddCommGrpCat.{1}).obj
          (zmodCoeff n)) :=
  (analyticAdjunction y).homEquiv _ _ ((constantSheafIso y).hom.app (zmodCoeff n))

theorem kummerComparison_comm₁₂ :
    kummerComparisonτ₁ y n ≫ (analyticDirectImage y).map (analyticZetaMap y n) =
      etaleZetaMap y n ≫ unitsComparisonToDirectImage y := by
  rw [kummerComparisonτ₁, ← Adjunction.homEquiv_naturality_right, ← Equiv.eq_symm_apply,
    ← Iso.app_hom, ← Iso.eq_inv_comp]
  apply ((constantSheafAdj _ AddCommGrpCat.{1} isTerminalTop).homEquiv _ _).injective
  rw [analyticZetaMap, constantSheafAdj_homEquiv_constantSheafLift, Iso.app_inv]
  erw [constantSheafAdj_homEquiv_constantSheafIso_inv]
  rw [Adjunction.homEquiv_naturality_right, etaleZetaMap, Equiv.apply_symm_apply]
  ext ⟨k⟩
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  erw [globalSectionsIso_hom_app_apply, evalSection_unitsComparisonToDirectImage]
  apply ULift.ext
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun v => Units.ext ?_
  change ((Additive.toMul (zmodToUnits n k) : ℂˣ) : ℂ) = eval (constHom (y := y) ⊤ _) _
    (mem_top _)
  exact (eval_constHom_of_eq (Category.id_comp y) _ _ _).symm

omit [NeZero n] in
theorem kummerComparison_comm₂₃ :
    unitsComparisonToDirectImage y ≫ (analyticDirectImage y).map (n • 𝟙 (analyticUnitsSheaf y)) =
      Stacks.Kummer.powMap.{0, 1} Y n ≫ unitsComparisonToDirectImage y := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.comp_nsmul, Category.comp_id,
    Stacks.Kummer.powMap, Preadditive.nsmul_comp, Category.id_comp]

/-- **The comparison of the Kummer sequences** `(0 → ℤ/n → 𝐆_m → 𝐆_m → 0) ⟶
ε_* (0 → ℤ/n → 𝒪^× → 𝒪^× → 0)`: the units comparison on `𝐆_m`, and on `ℤ/n` the map adjoint to
`ε^* ℤ/n ≅ ℤ/n`. -/
noncomputable def kummerComparison :
    etaleKummerSequence y n ⟶ (analyticKummerSequence y n).map (analyticDirectImage y) where
  τ₁ := kummerComparisonτ₁ y n
  τ₂ := unitsComparisonToDirectImage y
  τ₃ := unitsComparisonToDirectImage y
  comm₁₂ := kummerComparison_comm₁₂ y n
  comm₂₃ := kummerComparison_comm₂₃ y n

omit [NeZero n] in
/-- The comparison map of `ℤ/n` is bijective as soon as the comparison map along the first
component of `kummerComparison` is. -/
theorem bijective_comparisonMap_of_bijective_comparisonMapAlong_τ₁ (ν : ℕ)
    (h : Function.Bijective (comparisonMapAlong y (kummerComparisonτ₁ y n) ν)) :
    Function.Bijective (comparisonMap y
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (zmodCoeff n)) ν) := by
  let e := (constantSheafIso y).app (zmodCoeff n)
  have he : ((analyticAdjunction y).homEquiv _ _).symm (kummerComparisonτ₁ y n) = e.hom :=
    Equiv.symm_apply_apply _ _
  have hA : ∀ x, comparisonMapAlong y (kummerComparisonτ₁ y n) ν x =
      Sheaf.H.map e.hom ν (comparisonMap y
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (zmodCoeff n)) ν x) :=
    fun x => by rw [comparisonMapAlong_apply, he]
  refine ⟨fun a b hab => h.1 (by rw [hA, hA, hab]), fun z => ?_⟩
  obtain ⟨x, hx⟩ := h.2 (Sheaf.H.map e.hom ν z)
  refine ⟨x, ?_⟩
  rw [hA] at hx
  have := congrArg (Sheaf.H.map e.inv ν) hx
  rwa [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, Iso.hom_inv_id,
    Sheaf.H.map_id_apply, Sheaf.H.map_id_apply] at this

end Ladder

/-! ### The comparison of the cohomology of the units -/

section Units

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one

/-- `u^q : H^q_et(Y, 𝐆_m) → H^q(Y(ℂ), 𝒪^×)` is bijective for `q ≥ 2`, both groups vanishing, for a
smooth projective curve. -/
theorem bijective_unitsComparisonH_of_two_le (hy : IsProjective y) {q : ℕ} (hq : 2 ≤ q) :
    Function.Bijective (unitsComparisonH y q) := by
  have h1 : Subsingleton (Sheaf.H.{1} (Stacks.Kummer.multiplicativeSheaf.{0, 1} Y) q) :=
    subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one y q hq
  let := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  have h2 : Subsingleton (Sheaf.H.{1} (analyticUnitsSheaf y) q) :=
    have := subsingleton_H_holomorphicUnitsSheaf_of_isProjective.{0} y hy hq
    (liftToAnalyticHAddEquiv y _ q).symm.injective.subsingleton
  exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

omit [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] in
/-- The value of a global function of `Y` along the section `Y(ℂ) → Y(ℂ)` of the étale
`Y`-scheme `Y`. -/
theorem eval_topSection (g : Γ(Y, ⊤))
    (w : downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y))) :
    eval g ((topSection y (op ⊤)).1 ⟨ULift.up w.1, w.2⟩).down (mem_top _) =
      eval g w.1 (mem_top _) := by
  change eval g (etaleTopPoint y w.1) _ = _
  refine (eval_map_point (𝟙 Y) _ g w.1 _).trans ?_
  rw [Scheme.Hom.id_app]
  rfl

open scoped Manifold ContDiff

omit [IsCurve ℂ y] in
theorem coe_unitsSection_topSection (a : (Γ((etaleTop Y).left, ⊤))ˣ)
    (w : downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y))) :
    (((show C^∞⟮𝓘(ℂ), ↥(downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y))); 𝓘(ℂ), ℂˣ⟯
      from Additive.toMul (unitsSection y (Stacks.Kummer.ofUnit.{0, 1} a) (op ⊤)
        (topSection y (op ⊤))).down) w : ℂˣ) : ℂ) =
      eval (show Γ(Y, ⊤) from (a : Γ((etaleTop Y).left, ⊤))) w.1 (mem_top _) := by
  rw [← eval_topSection]
  rfl

/-- **The units comparison in degree zero, on global sections**: an invertible regular function
on `Y` goes to the nowhere vanishing holomorphic function it defines on `Y(ℂ)`; for a smooth curve
with `Y(ℂ)` compact this is a bijection (GAGA for functions). -/
theorem bijective_unitsSection_topSection [IsLocallyNoetherian Y]
    [CompactSpace (ComplexPoints y)] :
    Function.Bijective (fun s : ToType
        ((Stacks.Kummer.multiplicativeSheaf.{0, 1} Y).obj.obj (op (etaleTop Y))) =>
      unitsSection y s (op ⊤) (topSection y (op ⊤))) := by
  have hmem : ∀ x : ComplexPoints y,
      x ∈ downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y)) := fun x => trivial
  refine ⟨fun a b h => ?_, fun t => ?_⟩
  · obtain ⟨a, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{0, 1} a
    obtain ⟨b, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{0, 1} b
    have hab : ∀ x : ComplexPoints y,
        eval (show Γ(Y, ⊤) from (a : Γ((etaleTop Y).left, ⊤))) x (mem_top _) =
        eval (show Γ(Y, ⊤) from (b : Γ((etaleTop Y).left, ⊤))) x (mem_top _) := fun x => by
      rw [← coe_unitsSection_topSection y a ⟨x, hmem x⟩,
        ← coe_unitsSection_topSection y b ⟨x, hmem x⟩]
      exact congrArg (fun t : ToType ((analyticUnitsSheaf y).obj.obj (op ⊤)) =>
        (((show C^∞⟮𝓘(ℂ), ↥(downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y)));
          𝓘(ℂ), ℂˣ⟯ from Additive.toMul t.down) ⟨x, hmem x⟩ : ℂˣ) : ℂ)) h
    have hv : evalOrZero (z := y) ⊤ (show Γ(Y, ⊤) from (a : Γ((etaleTop Y).left, ⊤))) =
        evalOrZero ⊤ (show Γ(Y, ⊤) from (b : Γ((etaleTop Y).left, ⊤))) :=
      funext fun x => by
        rw [evalOrZero_of_mem _ (mem_top x), evalOrZero_of_mem _ (mem_top x)]
        exact hab x
    exact congrArg _ (Units.ext (injective_evalOrZero_top (y := y) hv))
  · let u : C^∞⟮𝓘(ℂ), ↥(downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y)));
      𝓘(ℂ), ℂˣ⟯ := Additive.toMul t.down
    have hsm : ∀ (v : C^∞⟮𝓘(ℂ), ↥(downOpens (⊤ : TopologicalSpace.Opens (analyticSpace y)));
        𝓘(ℂ), ℂˣ⟯), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : ComplexPoints y => (v ⟨x, hmem x⟩ : ℂ)) :=
      fun v x => by
        have h := (Units.contMDiff_val.comp v.contMDiff) ⟨x, hmem x⟩
        exact ((contMDiffAt_subtype_iff (U := downOpens ⊤)
          (f := fun x : ComplexPoints y => (v ⟨x, hmem x⟩ : ℂ))).1 h).mdifferentiableAt
          (by simp)
    obtain ⟨s₁, hs₁⟩ := (bijective_evalOrZero_top (y := y)).2 ⟨_, hsm u⟩
    obtain ⟨s₂, hs₂⟩ := (bijective_evalOrZero_top (y := y)).2 ⟨_, hsm u⁻¹⟩
    have h₁ := congrArg Subtype.val hs₁
    have h₂ := congrArg Subtype.val hs₂
    simp only at h₁ h₂
    have h12 : s₁ * s₂ = 1 := injective_evalOrZero_top (y := y) (funext fun x => by
      have e₁ := congrFun h₁ x
      have e₂ := congrFun h₂ x
      rw [evalOrZero_of_mem _ (mem_top x)] at e₁ e₂ ⊢
      have h1 : eval (1 : Γ(Y, ⊤)) x (mem_top x) = 1 := by rw [← evalHom_apply, map_one]
      rw [evalOrZero_of_mem _ (mem_top x), h1, ← evalHom_apply, map_mul, evalHom_apply,
        evalHom_apply, e₁, e₂]
      change (u ⟨x, hmem x⟩ : ℂ) * ((u ⟨x, hmem x⟩)⁻¹ : ℂˣ) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    refine ⟨Stacks.Kummer.ofUnit.{0, 1} (U := etaleTop Y)
      ⟨s₁, s₂, h12, (mul_comm s₂ s₁).trans h12⟩, ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    refine ContMDiffMap.ext fun w => Units.ext ?_
    refine (coe_unitsSection_topSection y _ w).trans ?_
    have e₁ := congrFun h₁ w.1
    rw [evalOrZero_of_mem _ (mem_top _)] at e₁
    exact e₁

/-- **`u⁰ : H⁰_et(Y, 𝐆_m) → H⁰(Y(ℂ), 𝒪^×)` is bijective** for a smooth curve with `Y(ℂ)`
compact. -/
theorem bijective_unitsComparisonH_zero [IsLocallyNoetherian Y]
    [CompactSpace (ComplexPoints y)] : Function.Bijective (unitsComparisonH y 0) := by
  let e₁ := Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{0, 1} Y)
    (isTerminal_etaleTop Y).some
  let e₂ := Sheaf.H.equiv₀ (analyticUnitsSheaf y) isTerminalTop
  have key : ⇑(unitsComparisonH y 0) = e₂.symm ∘
      (fun s => unitsSection y s (op ⊤) (topSection y (op ⊤))) ∘ e₁ := by
    funext x
    apply e₂.injective
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply]
    have := equiv₀_comparisonMapAlong y (unitsComparisonToDirectImage y) (e₁ x)
    rw [AddEquiv.symm_apply_apply, globalSectionsIso_hom_app_apply,
      evalSection_unitsComparisonToDirectImage] at this
    exact this
  rw [key]
  exact e₂.symm.bijective.comp ((bijective_unitsSection_topSection y).comp e₁.bijective)

open Stacks.EtaleCohomology in
/-- **`u^q : H^q_et(Y, 𝐆_m) → H^q(Y(ℂ), 𝒪^×)` is bijective in every degree** for a smooth
projective curve `Y` over `ℂ` [FK, I.11, proof of Theorem 11.6]. -/
@[weil "lem_fk111_comparison_units_projective_curve"]
theorem bijective_unitsComparisonH (hy : IsProjective y) (q : ℕ) :
    Function.Bijective (unitsComparisonH y q) := by
  have := compactSpace_of_isProjective hy
  have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve y
  rcases q with _ | _ | q
  · exact bijective_unitsComparisonH_zero y
  · exact bijective_unitsComparisonH_one_of_isProjective y hy
  · exact bijective_unitsComparisonH_of_two_le y hy (by omega)

end Units

/-! ### Artin's comparison theorem for curves -/

section Main

/-- **Artin's comparison theorem for a smooth projective complex curve, `ℤ/n` coefficients**
[FK, I.11, proof of Theorem 11.6]: for a smooth projective curve `C` over `ℂ` and `n ≥ 1`, the
comparison map `H^ν_et(C, ℤ/n) → H^ν(C(ℂ), ε^* ℤ/n)` is bijective in every degree `ν`. -/
@[weil "lem_fk111_comparison_projective_curve_constant_sheaf"]
theorem comparisonMap_constant_zmod_bijective_of_curve {C : Scheme.{0}} (c : C ⟶ Spec (.of ℂ))
    [IsCurve ℂ c] [IsProjectiveVariety ℂ c] [Smooth c] (n : ℕ) [NeZero n] (ν : ℕ) :
    Function.Bijective (comparisonMap c ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.of (ULift (ZMod n)))) ν) := by
  have : SmoothOfRelativeDimension 1 c :=
    Stacks.Hilbert.Curve.smoothOfRelativeDimension_one_of_isCurve c
  have hc : IsProjective c := (IsProjectiveVariety.isProjective (k := ℂ) (f := c)).isProjective
  have hu := bijective_unitsComparisonH c hc
  exact bijective_comparisonMap_of_bijective_comparisonMapAlong_τ₁ c n ν
    (bijective_comparisonMapAlong_τ₁ c (shortExact_etaleKummerSequence c n)
      (shortExact_analyticKummerSequence c n) (kummerComparison c n) ν (hu ν) (hu ν).1
      (fun m _ => (hu m).2) (fun m _ => hu m))

/-- **Artin's comparison theorem for a smooth projective complex curve, finite constant
coefficients**: for a smooth projective curve `C` over `ℂ` and a finite abelian group `A`, the
comparison map `H^ν_et(C, A) → H^ν(C(ℂ), A)` is bijective in every degree `ν`. -/
theorem comparisonMap_constant_finite_bijective_of_curve {C : Scheme.{0}}
    (c : C ⟶ Spec (.of ℂ)) [IsCurve ℂ c] [IsProjectiveVariety ℂ c] [Smooth c]
    (A : AddCommGrpCat.{1}) [Finite A] (ν : ℕ) :
    Function.Bijective (comparisonMap c
      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).obj A) ν) := by
  have : PreservesFiniteLimits (constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}) :=
    inferInstanceAs (PreservesFiniteLimits (Functor.const _ ⋙ presheafToSheaf _ _))
  have : PreservesFiniteColimits (constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}) :=
    inferInstanceAs (PreservesFiniteColimits (Functor.const _ ⋙ presheafToSheaf _ _))
  -- the cyclic case
  have hcyc : ∀ (B : AddCommGrpCat.{1}) (m : ℕ) [NeZero m], (ULift.{1} (ZMod m) ≃+ B) →
      ∀ ν, Function.Bijective (comparisonMap c
        ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).obj B) ν) := fun B m _ e ν =>
    bijective_comparisonMap_of_iso c
      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).mapIso
        (e.toAddCommGrpIso : AddCommGrpCat.of (ULift.{1} (ZMod m)) ≅ B)) ν
      (comparisonMap_constant_zmod_bijective_of_curve c m ν)
  suffices h : ∀ k (B : AddCommGrpCat.{1}) [Finite B], Nat.card B = k → ∀ ν,
      Function.Bijective (comparisonMap c
        ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).obj B) ν) from h _ A rfl ν
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro B _ hk ν
  by_cases hB : ∀ b : B, b = 0
  · have : Subsingleton B := ⟨fun a b => (hB a).trans (hB b).symm⟩
    exact hcyc B 1
      { toFun := fun _ => 0
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ } ν
  · obtain ⟨b, hb⟩ := not_forall.1 hB
    let H := AddSubgroup.zmultiples b
    have : Finite H := inferInstance
    have hHc : IsAddCyclic H := AddSubgroup.isAddCyclic_zmultiples b
    have : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
    let S : ShortComplex AddCommGrpCat.{1} :=
      ShortComplex.mk (X₁ := AddCommGrpCat.of H) (X₂ := B) (X₃ := AddCommGrpCat.of (B ⧸ H))
        (AddCommGrpCat.ofHom H.subtype)
        (AddCommGrpCat.ofHom (QuotientAddGroup.mk' H)) (by
          ext ⟨x, hx⟩
          exact (QuotientAddGroup.eq_zero_iff x).2 hx)
    have hS : S.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · rw [ShortComplex.ab_exact_iff]
        intro x hx
        exact ⟨⟨x, (QuotientAddGroup.eq_zero_iff x).1 hx⟩, rfl⟩
      · exact (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
      · exact (AddCommGrpCat.epi_iff_surjective _).2 (QuotientAddGroup.mk'_surjective H)
    have hcard : Nat.card B = Nat.card (B ⧸ H) * Nat.card H :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
    have hH2 : 1 < Nat.card H := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨0, by simp⟩, ⟨b, AddSubgroup.mem_zmultiples b⟩,
        fun h => hb (congrArg Subtype.val h).symm⟩
    have : Finite (AddCommGrpCat.of (B ⧸ H)) := inferInstanceAs (Finite (B ⧸ H))
    have hlt : Nat.card (AddCommGrpCat.of (B ⧸ H)) < k := by
      rw [← hk, hcard]
      change Nat.card (B ⧸ H) < Nat.card (B ⧸ H) * Nat.card H
      have : 0 < Nat.card (B ⧸ H) := Nat.card_pos
      nlinarith
    have h₁ : ∀ m, Function.Bijective (comparisonMap c
        ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).obj (AddCommGrpCat.of H)) m) :=
      hcyc (AddCommGrpCat.of H) (Nat.card H) (AddEquiv.ulift.trans (zmodAddCyclicAddEquiv hHc))
    have h₃ : ∀ m, Function.Bijective (comparisonMap c
        ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}).obj
          (AddCommGrpCat.of (B ⧸ H))) m) :=
      ih _ hlt (AddCommGrpCat.of (B ⧸ H)) rfl
    exact bijective_comparisonMap_of_shortExact c
      (S := S.map (constantSheaf C.smallEtaleTopology AddCommGrpCat.{1}))
      (hS.map_of_exact _) h₁ h₃ ν

end Main

end AlgebraicGeometry.Scheme.ComplexPoints
