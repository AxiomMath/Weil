module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage

/-!
# The line bundle of a divisor

Let `X` be an integral scheme with function field `K` and generic point `j : Spec K ⟶ X`, and
let `D` be a divisor supported on the closed points of `X`, a finitely supported function
`D : X₀ → ℤ` on the set `X₀` of closed points. The sheaf of rational functions of `X` on the
Zariski topology is the direct image `𝓡_X = j_* 𝒪_{Spec K}`, a sheaf of `𝒪_X`-modules: its
sections over an open `W` are `K` when `W` is nonempty and `0` otherwise.

The sheaf `𝒪_X(D)` is the sub-`𝒪_X`-module of `𝓡_X` whose sections over an open `W` are the
`f ∈ 𝓡_X(W)` with `ord_w(f) + D(w) ≥ 0` at every closed point `w ∈ W`, where `ord_w` is the
order along the map `𝒪_{X,w} → K` (`IsLocalRing.ordAlong`), valued in `ℤ ∪ {±∞}` with
`ord_w(0) = +∞`. When `X` is a smooth curve over a field, every `𝒪_{X,w}` is a discrete
valuation ring with fraction field `K`, and `ord_w` is the usual order of vanishing at `w`.

## Main definitions

* `AlgebraicGeometry.Scheme.rationalFunctionsModule`: the sheaf of rational functions
  `𝓡_X = j_* 𝒪_{Spec K}` as a sheaf of `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.rationalFunctionsEval`: the value `ρ_W(f) ∈ K` of a section `f` of
  `𝓡_X` over an open `W` containing the generic point.
* `AlgebraicGeometry.Scheme.lineBundleOfDivisorSubmodule`: the subsheaf of `𝓡_X` defined by the
  conditions `ord_w(f) + D(w) ≥ 0`.
* `AlgebraicGeometry.Scheme.lineBundleOfDivisor`: the sheaf of `𝒪_X`-modules `𝒪_X(D)`.

## Main results

* `AlgebraicGeometry.Scheme.mem_lineBundleOfDivisor_iff`: the description of the sections of
  `𝒪_X(D)` over an open `W` as the `f ∈ 𝓡_X(W)` with `ord_w(ρ_W f) + D(w) ≥ 0` for every closed
  point `w ∈ W`.
* `AlgebraicGeometry.Scheme.rationalFunctionsEval_map`: the restriction maps of `𝓡_X` commute
  with the evaluation `ρ`.
* `AlgebraicGeometry.Scheme.rationalFunctionsEval_smul`: the `𝒪_X(W)`-module structure of
  `𝓡_X(W)` is multiplication by the image of `𝒪_X(W)` in `K`.

## Implementation notes

The sheaf of rational functions is taken on the Zariski topology as the direct image along the
generic point `j : Spec K ⟶ X`; its sections over `W` are `Γ(Spec K, j⁻¹ W)`, which is the ring
`Γ(W ×_X Spec K, 𝒪)` of sections of the étale sheaf of rational functions over `W ⟶ X`. For an
integral scheme the scheme of generic points is `Spec K`, the local ring of `X` at a closed
point `w` is `A_w = 𝒪_{X,w}`, `Spec A_w ×_X Spec K = Spec K`, and the map `ι_w : A_w → K` is the
canonical map `𝒪_{X,w} → K`.

Freitag and Kiehl do not assume a smooth curve connected; here `X` is integral, which for a
smooth curve over a field is the case of a connected curve. A smooth curve is the disjoint union
of its finitely many connected components, and `𝒪_X(D)` is computed on each of them.

The divisor `D` is given by its values at the closed points, `closedPoints X →₀ ℤ`, which is the
group of global sections of the sheaf of divisors. The condition `ord_w(f) + D(w) ≥ 0` is
equivalent to the membership of `ρ_W(f)` in the set `I_{-D(w)}` of `IsLocalRing.ordAlongSet`;
this is the form used to show that the conditions define a submodule.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

namespace IsLocalRing

variable {A L : Type*} [CommRing A] [IsLocalRing A] [Semiring L] (ι : A →+* L)

/-- The sets `I_m` decrease with `m`. -/
lemma ordAlongSet_anti {m m' : ℤ} (hm : m ≤ m') : ordAlongSet ι m' ⊆ ordAlongSet ι m := by
  intro g hg
  rcases le_or_gt 0 m with h0 | h0
  · obtain ⟨a, ha, rfl⟩ := (mem_ordAlongSet_of_nonneg (h0.trans hm)).1 hg
    refine (mem_ordAlongSet_of_nonneg h0).2 ⟨a, Ideal.pow_le_pow_right ?_ ha, rfl⟩
    omega
  · rw [mem_ordAlongSet_of_neg h0]
    rcases le_or_gt 0 m' with h0' | h0'
    · obtain ⟨a, -, rfl⟩ := (mem_ordAlongSet_of_nonneg h0').1 hg
      exact fun b _ => ⟨a * b, map_mul ι a b⟩
    · intro b hb
      refine (mem_ordAlongSet_of_neg h0').1 hg b (Ideal.pow_le_pow_right ?_ hb)
      omega

/-- The order of `g` is at least `n` exactly when `g` lies in `I_n`. -/
lemma coe_le_ordAlong_iff {g : L} {n : ℤ} :
    ((n : WithTop ℤ) : WithBot (WithTop ℤ)) ≤ ordAlong ι g ↔ g ∈ ordAlongSet ι n := by
  constructor
  · intro h
    by_contra hg
    have hub : ∀ b ∈ (fun m : ℤ => ((m : WithTop ℤ) : WithBot (WithTop ℤ))) ''
        {m | g ∈ ordAlongSet ι m}, b ≤ (((n - 1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
      rintro _ ⟨m, hm, rfl⟩
      refine WithBot.coe_le_coe.2 (WithTop.coe_le_coe.2 ?_)
      by_contra hlt
      exact hg (ordAlongSet_anti ι (by omega) hm)
    have := h.trans (sSup_le hub)
    have := WithTop.coe_le_coe.1 (WithBot.coe_le_coe.1 this)
    omega
  · intro hg
    exact le_sSup ⟨n, hg, rfl⟩

/-- Each `I_m` is closed under addition. -/
lemma add_mem_ordAlongSet {m : ℤ} {g h : L} (hg : g ∈ ordAlongSet ι m)
    (hh : h ∈ ordAlongSet ι m) : g + h ∈ ordAlongSet ι m := by
  rcases le_or_gt 0 m with h0 | h0
  · obtain ⟨a, ha, rfl⟩ := (mem_ordAlongSet_of_nonneg h0).1 hg
    obtain ⟨b, hb, rfl⟩ := (mem_ordAlongSet_of_nonneg h0).1 hh
    exact (mem_ordAlongSet_of_nonneg h0).2 ⟨a + b, Ideal.add_mem _ ha hb, map_add ι a b⟩
  · rw [mem_ordAlongSet_of_neg h0] at hg hh ⊢
    intro c hc
    obtain ⟨x, hx⟩ := hg c hc
    obtain ⟨y, hy⟩ := hh c hc
    exact ⟨x + y, by rw [map_add, hx, hy, add_mul]⟩

/-- Each `I_m` is stable under multiplication by the image of `A`. -/
lemma mul_mem_ordAlongSet {m : ℤ} (a : A) {g : L} (hg : g ∈ ordAlongSet ι m) :
    ι a * g ∈ ordAlongSet ι m := by
  rcases le_or_gt 0 m with h0 | h0
  · obtain ⟨b, hb, rfl⟩ := (mem_ordAlongSet_of_nonneg h0).1 hg
    exact (mem_ordAlongSet_of_nonneg h0).2 ⟨a * b, Ideal.mul_mem_left _ a hb, map_mul ι a b⟩
  · rw [mem_ordAlongSet_of_neg h0] at hg ⊢
    intro c hc
    obtain ⟨x, hx⟩ := hg c hc
    exact ⟨a * x, by rw [map_mul, hx, mul_assoc]⟩

/-- `ord(g) + n ≥ 0` in `ℤ ∪ {±∞}` exactly when `g` lies in `I_{-n}`. -/
lemma zero_le_ordAlong_add_iff {g : L} {n : ℤ} :
    0 ≤ ordAlong ι g + ((n : WithTop ℤ) : WithBot (WithTop ℤ)) ↔ g ∈ ordAlongSet ι (-n) := by
  rw [← coe_le_ordAlong_iff]
  induction ordAlong ι g using WithBot.recBotCoe with
  | bot => simp
  | coe o =>
    induction o using WithTop.recTopCoe with
    | top =>
      exact iff_of_true (by rw [← WithBot.coe_add, WithTop.top_add]; exact le_top) le_top
    | coe m =>
      rw [← WithBot.coe_add, ← WithTop.coe_add, ← WithBot.coe_zero, ← WithTop.coe_zero,
        WithBot.coe_le_coe, WithBot.coe_le_coe, WithTop.coe_le_coe, WithTop.coe_le_coe]
      omega

end IsLocalRing

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

variable (X : Scheme.{u}) [IsIntegral X]

/-- **The sheaf of rational functions on the Zariski topology** of an integral scheme `X`: the
direct image `j_* 𝒪_{Spec K}` along the generic point `j : Spec K ⟶ X`, a sheaf of
`𝒪_X`-modules whose sections over `W` are `Γ(Spec K, j⁻¹ W)`. -/
abbrev rationalFunctionsModule : X.Modules :=
  (Modules.pushforward (genericPointInclusion X)).obj
    (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)

variable {X}

/-- The value `ρ_W(f) ∈ K` of a section `f ∈ Γ(Spec K, j⁻¹ W)` of the sheaf of rational
functions over an open `W` containing the generic point: its germ at the point of `Spec K`. -/
def rationalFunctionsEval (W : X.Opens) (hW : genericPoint X ∈ W) :
    Γ(Spec X.functionField, genericPointInclusion X ⁻¹ᵁ W) ⟶ X.functionField :=
  (Spec X.functionField).presheaf.germ (genericPointInclusion X ⁻¹ᵁ W)
      (closedPoint X.functionField)
      (show genericPointInclusion X (closedPoint X.functionField) ∈ W by
        rw [genericPointInclusion_closedPoint X]; exact hW) ≫
    (stalkClosedPointIso X.functionField).hom

/-- The evaluation `ρ` commutes with the restriction maps of the sheaf of rational functions. -/
lemma rationalFunctionsEval_map {V W : X.Opens} (i : V ⟶ W) (hV : genericPoint X ∈ V)
    (f : Γ(Spec X.functionField, genericPointInclusion X ⁻¹ᵁ W)) :
    rationalFunctionsEval V hV
        ((Spec X.functionField).presheaf.map ((Opens.map (genericPointInclusion X).base).map i).op
          f) =
      rationalFunctionsEval W (leOfHom i hV) f := by
  simp only [rationalFunctionsEval, CommRingCat.comp_apply]
  exact congrArg _ (TopCat.Presheaf.germ_res_apply _ _ _ _ _)


/-- The evaluation `ρ` of the image of a function `r ∈ Γ(X, W)` is its germ at the generic
point. -/
lemma rationalFunctionsEval_app (W : X.Opens) (hW : genericPoint X ∈ W) (r : Γ(X, W)) :
    rationalFunctionsEval W hW ((genericPointInclusion X).app W r) =
      X.presheaf.germ W (genericPoint X) hW r := by
  have h := Scheme.Hom.germ_stalkMap_apply (genericPointInclusion X) W
    (closedPoint X.functionField) (show genericPointInclusion X (closedPoint X.functionField) ∈ W by
        rw [genericPointInclusion_closedPoint X]; exact hW) r
  simp only [rationalFunctionsEval, CommRingCat.comp_apply]
  rw [← h, ← CommRingCat.comp_apply, ← stalkClosedPointTo.eq_def,
    show stalkClosedPointTo (genericPointInclusion X) = _ from
      stalkClosedPointTo_fromSpecStalk (genericPoint X)]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- The `𝒪_X(W)`-module structure of `𝓡_X(W)`: under `ρ`, a function `r ∈ Γ(X, W)` acts by
multiplication with its germ at the generic point. -/
lemma rationalFunctionsEval_smul (W : X.Opens) (hW : genericPoint X ∈ W) (r : Γ(X, W))
    (f : Γ(X.rationalFunctionsModule, W)) :
    rationalFunctionsEval W hW (r • f) =
      X.presheaf.germ W (genericPoint X) hW r * rationalFunctionsEval W hW f := by
  change rationalFunctionsEval W hW ((genericPointInclusion X).app W r *
    (show Γ(Spec X.functionField, genericPointInclusion X ⁻¹ᵁ W) from f)) = _
  rw [map_mul, rationalFunctionsEval_app]

/-- The germ at the generic point of `r ∈ Γ(X, W)` is the image in `K` of its germ at any point
`w ∈ W`. -/
lemma algebraMap_stalk_germ (W : X.Opens) {w : X} (hw : w ∈ W) (hW : genericPoint X ∈ W)
    (r : Γ(X, W)) :
    algebraMap (X.presheaf.stalk w) X.functionField (X.presheaf.germ W w hw r) =
      X.presheaf.germ W (genericPoint X) hW r := by
  rw [RingHom.algebraMap_toAlgebra]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- An open set containing a point contains the generic point. -/
lemma genericPoint_mem_opens_of_mem {W : X.Opens} {w : X} (hw : w ∈ W) : genericPoint X ∈ W :=
  ((genericPoint_spec X).specializes (Set.mem_univ w)).mem_open W.isOpen hw

variable (X) in
/-- The condition defining the sections of `𝒪_X(D)` over `W`: `ord_w(ρ_W f) + D(w) ≥ 0` at every
closed point `w ∈ W`, the order being taken along `𝒪_{X,w} → K` with values in `ℤ ∪ {±∞}`. -/
def IsLineBundleOfDivisorSection (D : closedPoints X →₀ ℤ) (W : X.Opens)
    (f : Γ(X.rationalFunctionsModule, W)) : Prop :=
  ∀ (w : X) (hw : w ∈ closedPoints X) (hwW : w ∈ W),
    0 ≤ ordAlong (algebraMap (X.presheaf.stalk w) X.functionField)
        (rationalFunctionsEval W (genericPoint_mem_opens_of_mem hwW) f) +
      ((D ⟨w, hw⟩ : WithTop ℤ) : WithBot (WithTop ℤ))

/-- The condition `ord_w(f) + D(w) ≥ 0` is the membership of `ρ_W(f)` in `I_{-D(w)}`. -/
lemma isLineBundleOfDivisorSection_iff (D : closedPoints X →₀ ℤ) (W : X.Opens)
    (f : Γ(X.rationalFunctionsModule, W)) :
    X.IsLineBundleOfDivisorSection D W f ↔ ∀ (w : X) (hw : w ∈ closedPoints X) (hwW : w ∈ W),
      rationalFunctionsEval W (genericPoint_mem_opens_of_mem hwW) f ∈
        ordAlongSet (algebraMap (X.presheaf.stalk w) X.functionField) (-D ⟨w, hw⟩) := by
  simp only [IsLineBundleOfDivisorSection, zero_le_ordAlong_add_iff]

variable (X) in
/-- The subsheaf of `𝓡_X` of the sections `f` with `ord_w(f) + D(w) ≥ 0` at every closed
point `w`. -/
def lineBundleOfDivisorSubmodule (D : closedPoints X →₀ ℤ) :
    X.rationalFunctionsModule.Submodule where
  obj W :=
    { carrier := {f | X.IsLineBundleOfDivisorSection D W.unop f}
      add_mem' := by
        intro f g hf hg
        have hf' := (isLineBundleOfDivisorSection_iff _ _ _).1 hf
        have hg' := (isLineBundleOfDivisorSection_iff _ _ _).1 hg
        refine (isLineBundleOfDivisorSection_iff _ _ _).2 fun w hw hwW => ?_
        have := add_mem_ordAlongSet _ (hf' w hw hwW) (hg' w hw hwW)
        convert this using 1
        exact map_add (rationalFunctionsEval W.unop _).hom f g
      zero_mem' := by
        refine (isLineBundleOfDivisorSection_iff _ _ _).2 fun w hw hwW => ?_
        change rationalFunctionsEval W.unop _ 0 ∈ _
        rw [map_zero]
        exact zero_mem_ordAlongSet _
      smul_mem' := by
        intro r f hf
        have hf' := (isLineBundleOfDivisorSection_iff _ _ _).1 hf
        refine (isLineBundleOfDivisorSection_iff _ _ _).2 fun w hw hwW => ?_
        convert mul_mem_ordAlongSet _ (X.presheaf.germ W.unop w hwW r) (hf' w hw hwW) using 1
        exact (rationalFunctionsEval_smul W.unop _ r f).trans
          (congrArg (· * _) (algebraMap_stalk_germ W.unop hwW _ r).symm) }
  map {W V} i f hf := by
    have hf' := (isLineBundleOfDivisorSection_iff _ _ _).1 hf
    refine (isLineBundleOfDivisorSection_iff _ _ _).2 fun w hw hwV => ?_
    have := hf' w hw (leOfHom i.unop hwV)
    convert this using 1
    exact rationalFunctionsEval_map i.unop (genericPoint_mem_opens_of_mem hwV) f
  isSheaf W f hf := by
    refine (isLineBundleOfDivisorSection_iff D W.unop f).2 fun w hw hwW => ?_
    obtain ⟨V, i, hi, hwV⟩ := hf w hwW
    have := (isLineBundleOfDivisorSection_iff _ _ _).1 hi w hw hwV
    convert this using 1
    exact (rationalFunctionsEval_map i (genericPoint_mem_opens_of_mem hwV) f).symm

variable (X) in
/-- **The line bundle `𝒪_X(D)` of a divisor** `D` on an integral scheme `X`: the sheaf of
`𝒪_X`-modules whose sections over an open `W` are the rational functions `f ∈ 𝓡_X(W)` with
`ord_w(f) + D(w) ≥ 0` at every closed point `w ∈ W`, with the `𝒪_X(W)`-module structure and the
restriction maps of the sheaf of rational functions `𝓡_X`. -/
@[weil "def_fk105_line_bundle_of_divisor"]
abbrev lineBundleOfDivisor (D : closedPoints X →₀ ℤ) : X.Modules :=
  (X.lineBundleOfDivisorSubmodule D).toSheafOfModules

variable (D : closedPoints X →₀ ℤ)

/-- The inclusion `𝒪_X(D) ⟶ 𝓡_X` of sheaves of `𝒪_X`-modules. -/
abbrev lineBundleOfDivisorι : X.lineBundleOfDivisor D ⟶ X.rationalFunctionsModule :=
  (X.lineBundleOfDivisorSubmodule D).ι

/-- **The sections of `𝒪_X(D)`**: a rational function `f ∈ 𝓡_X(W)` is a section of `𝒪_X(D)`
over `W` exactly when `ord_w(ρ_W f) + D(w) ≥ 0` at every closed point `w ∈ W`. -/
@[weil "def_fk105_line_bundle_of_divisor"]
lemma mem_lineBundleOfDivisor_iff (W : X.Opens) (f : Γ(X.rationalFunctionsModule, W)) :
    f ∈ (X.lineBundleOfDivisorSubmodule D).obj (op W) ↔
      ∀ (w : X) (hw : w ∈ closedPoints X) (hwW : w ∈ W),
        0 ≤ ordAlong (algebraMap (X.presheaf.stalk w) X.functionField)
            (rationalFunctionsEval W (genericPoint_mem_opens_of_mem hwW) f) +
          ((D ⟨w, hw⟩ : WithTop ℤ) : WithBot (WithTop ℤ)) :=
  Iff.rfl

/-- The sections of `𝒪_X(D)` over `W` are the elements of the submodule of `𝓡_X(W)` cut out by
the conditions `ord_w(f) + D(w) ≥ 0`. -/
lemma lineBundleOfDivisor_sections (W : X.Opens) :
    Γ(X.lineBundleOfDivisor D, W) = ↥((X.lineBundleOfDivisorSubmodule D).obj (op W)) :=
  rfl

/-- The `𝒪_X(W)`-module structure of `𝒪_X(D)(W)` is the one of `𝓡_X(W)`: under `ρ`, a function
`r ∈ Γ(X, W)` acts by multiplication with its image in `K`. -/
@[weil "def_fk105_line_bundle_of_divisor"]
lemma rationalFunctionsEval_lineBundleOfDivisorι_smul (W : X.Opens) (hW : genericPoint X ∈ W)
    (r : Γ(X, W)) (s : Γ(X.lineBundleOfDivisor D, W)) :
    rationalFunctionsEval W hW ((lineBundleOfDivisorι D).app W (r • s)) =
      X.presheaf.germ W (genericPoint X) hW r *
        rationalFunctionsEval W hW ((lineBundleOfDivisorι D).app W s) :=
  rationalFunctionsEval_smul W hW r _

/-- The restriction maps of `𝒪_X(D)` are those of `𝓡_X`. -/
@[weil "def_fk105_line_bundle_of_divisor"]
lemma lineBundleOfDivisorι_app_map {V W : X.Opens} (i : V ⟶ W) (s : Γ(X.lineBundleOfDivisor D, W)) :
    (lineBundleOfDivisorι D).app V ((X.lineBundleOfDivisor D).presheaf.map i.op s) =
      X.rationalFunctionsModule.presheaf.map i.op ((lineBundleOfDivisorι D).app W s) :=
  rfl

/-- On an open `W` containing the generic point the evaluation `ρ_W : 𝓡_X(W) → K` is
bijective. -/
lemma rationalFunctionsEval_bijective (W : X.Opens) (hW : genericPoint X ∈ W) :
    Function.Bijective (rationalFunctionsEval W hW) := by
  have hU : genericPointInclusion X ⁻¹ᵁ W = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem _
      (show genericPointInclusion X (closedPoint X.functionField) ∈ W by
        rw [genericPointInclusion_closedPoint X]; exact hW)
  suffices ∀ (U : (Spec X.functionField).Opens) (hU : U = ⊤) (h),
      Function.Bijective ((Spec X.functionField).presheaf.germ U
        (closedPoint X.functionField) h ≫ (stalkClosedPointIso X.functionField).hom) from
    this _ hU _
  rintro U rfl h
  rw [germ_stalkClosedPointIso_hom]
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme
