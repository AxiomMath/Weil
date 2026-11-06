module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityCurvesFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwoPicard
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupBoundedSiteVanishing

/-!
# Étale cohomology of `μ_n` and `𝐆_m` on a smooth projective curve

Let `C` be a smooth projective curve over an algebraically closed field `k` and let `n` be
invertible in `k`. On the small étale site of `C` the Kummer sequence
`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` (the second map being `x ↦ x^n`) is short exact, and its long exact
sequence of cohomology, together with

* `H⁰(C, 𝐆_m) = k^×`, an `n`-divisible group,
* `H¹(C, 𝐆_m) = Pic(C)`,
* `H^q(C, 𝐆_m) = 0` for `q ≥ 2`,

computes the cohomology of `μ_n`:

* `H⁰(C, μ_n) = μ_n(k)`;
* `H¹(C, μ_n) = Pic(C)[n]`, through the map induced by `μ_n ⟶ 𝐆_m`;
* `H²(C, μ_n) = Pic(C)/n·Pic(C)`, through the Kummer connecting map, and `= 𝐙/n𝐙` through the
  degree;
* `H^q(C, μ_n) = 0` for `q ≥ 3`.

This file collects these statements, all on the small étale site `SmallEtale.topology B C hC` of
a big étale site and for the cohomology `CategoryTheory.Sheaf.H`, in the form a comparison of
long exact sequences needs: the three maps of the long exact sequence, the identification of the
middle one with multiplication by `n`, exactness at each of the three spots, and each
identification of a cohomology group as a named isomorphism with its value on generators.

## Main definitions

* `AlgebraicGeometry.SmoothProjectiveCurve.kummerConnecting`: the connecting map
  `H^q(C, 𝐆_m) ⟶ H^{q+1}(C, μ_n)` of the Kummer sequence.
* `AlgebraicGeometry.SmoothProjectiveCurve.unitsH0AddEquiv`: `H⁰(C, 𝐆_m) ≃ k^×`.
* `AlgebraicGeometry.SmoothProjectiveCurve.rootsOfUnityH0AddEquiv`: `H⁰(C, μ_n) ≃ μ_n(k)`.
* `AlgebraicGeometry.SmoothProjectiveCurve.rootsOfUnityH1AddEquivPicardTorsion`:
  `H¹(C, μ_n) ≃ Pic(C)[n]`.
* `AlgebraicGeometry.SmoothProjectiveCurve.picardQuotientAddEquivRootsOfUnityH2`:
  `Pic(C)/n·Pic(C) ≃ H²(C, μ_n)`.
* `AlgebraicGeometry.SmoothProjectiveCurve.rootsOfUnityH2AddEquivZMod`: `H²(C, μ_n) ≃ 𝐙/n𝐙`.

## Main results

* `AlgebraicGeometry.SmoothProjectiveCurve.kummer_shortExact`: the Kummer sequence is short exact.
* `AlgebraicGeometry.SmoothProjectiveCurve.sheafH_map_kummer_g`: its second map induces
  multiplication by `n` in every degree.
* `AlgebraicGeometry.SmoothProjectiveCurve.exists_sheafH_map_kummer_f_iff`,
  `AlgebraicGeometry.SmoothProjectiveCurve.kummerConnecting_eq_zero_iff`,
  `AlgebraicGeometry.SmoothProjectiveCurve.exists_kummerConnecting_iff`: exactness.
* `AlgebraicGeometry.SmoothProjectiveCurve.subsingleton_sheafH_units`: `H^q(C, 𝐆_m) = 0`, `q ≥ 2`.
* `AlgebraicGeometry.SmoothProjectiveCurve.exists_nsmul_eq_unitsH0`: `H⁰(C, 𝐆_m)` is divisible.
* `AlgebraicGeometry.SmoothProjectiveCurve.subsingleton_sheafH_rootsOfUnity`:
  `H^q(C, μ_n) = 0`, `q ≥ 3`.
* `AlgebraicGeometry.SmoothProjectiveCurve.exists_nsmul_eq_of_mem_curvePicardDegreeZero`:
  `Pic⁰(C)` is `n`-divisible.

## Implementation notes

`Pic(C)` is `AlgebraicGeometry.schemePicard C`, whose group structure is the instance
`AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup`, local in the library it comes from; it
is activated here, and a file using the declarations below activates it too. The sheaves `𝐆_m`
in the second and third places of `AlgebraicGeometry.kummerSmallEtale` are the same sheaf
(`(kummerSmallEtale B C hC n).X₂` and `.X₃`); the identifications of `H⁰` and `H¹` are stated at
the place where they are used. The universe `t` of the `Ext`-groups is a parameter, carried as a
`HasExt.{t}` hypothesis.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t u

namespace AlgebraicGeometry.SmoothProjectiveCurve

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

/-! ### The Kummer long exact sequence -/

section Kummer

include f in
/-- The Kummer sequence `0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` on the small étale site is short exact when
`n` is invertible in `k`. -/
theorem kummer_shortExact (hn : IsUnit (n : k)) : (kummerSmallEtale B X hX n).ShortExact :=
  kummerSmallEtale_shortExact k X f B hX n hn

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-- The connecting map `H^q(C, 𝐆_m) ⟶ H^{q+1}(C, μ_n)` of the Kummer sequence. -/
def kummerConnecting (hn : IsUnit (n : k)) (q : ℕ) :
    Sheaf.H.{t} (kummerSmallEtale B X hX n).X₃ q →+
      Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ (q + 1) :=
  Stacks.Cohomology.sheafHBoundary (kummer_shortExact k X f B hX n hn) q (q + 1) rfl

theorem kummerConnecting_apply (hn : IsUnit (n : k)) (q : ℕ)
    (x : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₃ q) :
    kummerConnecting k X f B hX n hn q x = x.comp (kummer_shortExact k X f B hX n hn).extClass
      rfl :=
  rfl

/-- The second map `x ↦ x^n` of the Kummer sequence induces multiplication by `n` on
`H^q(C, 𝐆_m)` in every degree. -/
theorem sheafH_map_kummer_g (q : ℕ) (y : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ q) :
    Sheaf.H.map (kummerSmallEtale B X hX n).g q y = n • y := by
  rw [kummerSequence_g_eq_nsmul_id]
  exact Stacks.Cohomology.sheafH_map_nsmul_id n q y

include f in
/-- Exactness of the Kummer long exact sequence at `H^q(C, 𝐆_m)` (the middle term). -/
theorem exists_sheafH_map_kummer_f_iff (hn : IsUnit (n : k)) (q : ℕ)
    (y : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ q) :
    (∃ x, Sheaf.H.map (kummerSmallEtale B X hX n).f q x = y) ↔
      Sheaf.H.map (kummerSmallEtale B X hX n).g q y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [← Sheaf.H.map_comp_apply, (kummerSmallEtale B X hX n).zero, Sheaf.H.map_apply,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  · intro hy
    exact ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Abelian.Ext.covariant_sequence_exact₂'
        ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) (kummer_shortExact k X f B hX n hn) q) y).mp hy

include f in
/-- Exactness of the Kummer long exact sequence at `H^q(C, 𝐆_m)` (the third term): the
connecting map kills exactly the `n`-th multiples. -/
theorem kummerConnecting_eq_zero_iff (hn : IsUnit (n : k)) (q : ℕ)
    (x : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₃ q) :
    kummerConnecting k X f B hX n hn q x = 0 ↔
      ∃ y : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ q, n • y = x := by
  rw [kummerConnecting, Stacks.Cohomology.sheafHBoundary_eq_zero_iff]
  simp only [sheafH_map_kummer_g]
  exact Iff.rfl

include f in
/-- Exactness of the Kummer long exact sequence at `H^{q+1}(C, μ_n)`: the image of the connecting
map is the kernel of the map induced by `μ_n ⟶ 𝐆_m`. -/
theorem exists_kummerConnecting_iff (hn : IsUnit (n : k)) (q : ℕ)
    (w : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ (q + 1)) :
    (∃ x, kummerConnecting k X f B hX n hn q x = w) ↔
      Sheaf.H.map (kummerSmallEtale B X hX n).f (q + 1) w = 0 :=
  Stacks.Cohomology.exists_sheafHBoundary_iff _ q (q + 1) rfl w

end Kummer

/-! ### The cohomology of `𝐆_m` -/

section Units

/-- The pullback `k ⟶ Γ(C, 𝒪_C)` of functions along the structure morphism. -/
abbrev structureRingHom : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

theorem injective_structureRingHom [Nonempty X] : Function.Injective (structureRingHom k X f) :=
  (structureRingHom k X f).injective

variable [IsAlgClosed k] [IsProjectiveVariety k f]

/-- The structure morphism identifies `k^×` with the invertible global functions of `C`. -/
def unitsAddEquivGlobalUnits : Additive kˣ ≃+ Additive (Γ(X, ⊤))ˣ :=
  (MulEquiv.ofBijective (Units.map (structureRingHom k X f).toMonoidHom)
    ⟨fun _ _ h => Units.ext (injective_structureRingHom k X f (congrArg Units.val h)),
      fun s => forall_units_mem_range_of_isAlgClosed k f s⟩).toAdditive

/-- **`H⁰(C, 𝐆_m) = k^×`**: degree-zero cohomology is global sections, and the invertible global
functions of a proper variety over an algebraically closed field are the constants. -/
def unitsH0AddEquiv [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ 0 ≃+ Additive kˣ :=
  (Sheaf.H.equiv₀ _ (SmallEtale.finalIsTerminal B X hX)).trans (unitsAddEquivGlobalUnits k X f).symm

/-- `unitsH0AddEquiv` sends a class to the constant whose pullback is its global section. -/
theorem unitsAddEquivGlobalUnits_unitsH0AddEquiv
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]
    (x : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ 0) :
    unitsAddEquivGlobalUnits k X f (unitsH0AddEquiv k X f B hX n x) =
      Sheaf.H.equiv₀ _ (SmallEtale.finalIsTerminal B X hX) x :=
  AddEquiv.apply_symm_apply _ _

include f in
/-- **`H⁰(C, 𝐆_m)` is divisible**: every class is an `m`-th multiple for every `m ≥ 1`,
`k` being algebraically closed. -/
theorem exists_nsmul_eq_unitsH0
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] {m : ℕ} (hm : m ≠ 0)
    (x : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ 0) : ∃ y, m • y = x := by
  set e := unitsH0AddEquiv k X f B hX n
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul (e x) : kˣ) : k)
    (Nat.pos_of_ne_zero hm)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hd
    exact (Additive.toMul (e x)).ne_zero hd.symm
  refine ⟨e.symm (Additive.ofMul (Units.mk0 d hd0)), ?_⟩
  rw [← map_nsmul, AddEquiv.symm_apply_eq]
  apply Additive.toMul.injective
  apply Units.ext
  simp [hd]

end Units

include f in
/-- **`H^q(C, 𝐆_m) = 0` for `q ≥ 2`** (Stacks, Tag 03RM), on any smooth curve over an
algebraically closed field. -/
theorem subsingleton_sheafH_units [IsAlgClosed k] [IsCurve k f] [Smooth f]
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ q) :=
  subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q hq

/-! ### The cohomology of `μ_n` -/

section RootsOfUnity

variable [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f]

omit [IsCurve k f] in
/-- The structure morphism identifies `μ_n(k)` with the global `n`-th roots of unity of `C`. -/
def rootsOfUnityMulEquivGlobal : _root_.rootsOfUnity n k ≃* _root_.rootsOfUnity n Γ(X, ⊤) :=
  MulEquiv.ofBijective (restrictRootsOfUnity (structureRingHom k X f) n)
    ⟨fun _ _ h => Subtype.ext (Units.ext (injective_structureRingHom k X f
        (congrArg (fun z : _root_.rootsOfUnity n Γ(X, ⊤) => ((z : Γ(X, ⊤)ˣ) : Γ(X, ⊤))) h))),
      fun ζ => by
        obtain ⟨c, hc⟩ := forall_units_mem_range_of_isAlgClosed k f (ζ : Γ(X, ⊤)ˣ)
        have hc' : Units.map (structureRingHom k X f).toMonoidHom (c ^ n) = 1 := by
          rw [map_pow, hc]
          exact (mem_rootsOfUnity n _).1 ζ.2
        have hcn : c ^ n = 1 := by
          apply Units.ext
          apply injective_structureRingHom k X f
          rw [Units.val_one, map_one]
          exact congrArg Units.val hc'
        exact ⟨⟨c, (mem_rootsOfUnity n c).2 hcn⟩, Subtype.ext hc⟩⟩

omit [IsCurve k f] in
/-- **`H⁰(C, μ_n) = μ_n(k)`**: degree-zero cohomology is the group of global `n`-th roots of unity,
and those are the constants. -/
def rootsOfUnityH0AddEquiv [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ 0 ≃+ Additive (_root_.rootsOfUnity n k) :=
  (etaleH0RootsOfUnityAddEquiv X B hX n).trans
    (rootsOfUnityMulEquivGlobal k X f n).symm.toAdditive

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-- **`H¹(C, μ_n) = Pic(C)[n]`**: the map induced by `μ_n ⟶ 𝐆_m` followed by
`H¹(C, 𝐆_m) = Pic(C)` (Stacks, Tag 03P8) is injective with image the `n`-torsion. -/
def rootsOfUnityH1AddEquivPicardTorsion (hn : IsUnit (n : k)) :
    Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ 1 ≃+ picardNTorsion X n :=
  AddEquiv.ofBijective (etaleH1RootsOfUnityToPicardNTorsion k X f B hX n hn)
    ⟨fun _ _ h => injective_etaleH1RootsOfUnityToPicard k X f B hX n hn
        (ne_zero_of_isUnit_natCast k X f n hn) (congrArg Subtype.val h),
      surjective_etaleH1RootsOfUnityToPicardNTorsion k X f B hX n hn⟩

omit [IsCurve k f] in
/-- The value of `rootsOfUnityH1AddEquivPicardTorsion`: the class in `Pic(C)` of the image of `x`
in `H¹(C, 𝐆_m)`. -/
theorem coe_rootsOfUnityH1AddEquivPicardTorsion (hn : IsUnit (n : k))
    (x : Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ 1) :
    (rootsOfUnityH1AddEquivPicardTorsion k X f B hX n hn x : schemePicard X) =
      etaleH1UnitsEquivPicard X B hX n (Sheaf.H.map (kummerSmallEtale B X hX n).f 1 x) :=
  rfl

/-- `n·Pic(C)`, the subgroup of `n`-th multiples in the Picard group. -/
abbrev picardNMultiples : AddSubgroup (schemePicard X) :=
  (n • AddMonoidHom.id (schemePicard X)).range

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] in
theorem mem_picardNMultiples_iff (x : schemePicard X) :
    x ∈ picardNMultiples X n ↔ ∃ y, x = n • y := by
  simp [picardNMultiples, eq_comm]

/-- The Kummer connecting map `Pic(C) = H¹(C, 𝐆_m) ⟶ H²(C, μ_n)` (Stacks, Tag 03P8 at the third
term of the Kummer sequence, then `kummerConnecting`). -/
abbrev picardToRootsOfUnityH2 (hn : IsUnit (n : k)) :
    schemePicard X →+ Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ 2 :=
  etaleH2RootsOfUnityFromPicard k X f B hX n hn

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] in
theorem picardToRootsOfUnityH2_apply (hn : IsUnit (n : k)) (x : schemePicard X) :
    picardToRootsOfUnityH2 k X f B hX n hn x =
      kummerConnecting k X f B hX n hn 1 ((etaleH1UnitsEquivPicardQuotient X B hX n).symm x) :=
  rfl

variable [Smooth f]

omit [IsProjectiveVariety k f] in
theorem surjective_picardToRootsOfUnityH2 (hn : IsUnit (n : k)) :
    Function.Surjective (picardToRootsOfUnityH2 k X f B hX n hn) :=
  surjective_etaleH2RootsOfUnityFromPicard k X f B hX n hn
    (subsingleton_sheafH_units k X f B hX n 2 le_rfl)

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] in
theorem ker_picardToRootsOfUnityH2 (hn : IsUnit (n : k)) :
    (picardToRootsOfUnityH2 k X f B hX n hn).ker = picardNMultiples X n := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_picardNMultiples_iff]
  exact etaleH2RootsOfUnityFromPicard_eq_zero_iff k X f B hX n hn x

/-- **`H²(C, μ_n) = Pic(C)/n·Pic(C)`** through the Kummer connecting map. -/
def picardQuotientAddEquivRootsOfUnityH2 (hn : IsUnit (n : k)) :
    (schemePicard X ⧸ picardNMultiples X n) ≃+ Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_picardToRootsOfUnityH2 k X f B hX n hn).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_picardToRootsOfUnityH2 k X f B hX n hn))

omit [IsProjectiveVariety k f] in
theorem picardQuotientAddEquivRootsOfUnityH2_mk (hn : IsUnit (n : k)) (x : schemePicard X) :
    picardQuotientAddEquivRootsOfUnityH2 k X f B hX n hn (QuotientAddGroup.mk x) =
      picardToRootsOfUnityH2 k X f B hX n hn x :=
  rfl

omit [HasExt (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat)] in
/-- **`Pic⁰(C)` is `n`-divisible** for `n` invertible in `k`: from Stacks, Tag 03RQ, whose degree
two clause makes the Kummer connecting map and the degree modulo `n` have the same kernel. -/
theorem exists_nsmul_eq_of_mem_curvePicardDegreeZero (hn : IsUnit (n : k)) (x : schemePicard X)
    (hx : x ∈ curvePicardDegreeZero k X f) : ∃ y, n • y = x := by
  let B' := BigEtaleSite.containing X
  have hX' := BigEtaleSite.contains_containing X
  have : HasExt.{u + 1} (Sheaf (SmallEtale.topology B' X hX') AddCommGrpCat.{u}) :=
    HasExt.standard _
  obtain ⟨-, -, ⟨e, he⟩, -⟩ :=
    etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus.{u + 1} k X f B' hX' n hn
  have h0 : picardDegreeZMod k X f n x = 0 := by
    have : curvePicardDegree k X f x = 0 := hx
    simp [this]
  rw [← he, AddEquiv.map_eq_zero_iff, etaleH2RootsOfUnityFromPicard_eq_zero_iff] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

/-- **`H²(C, μ_n) = 𝐙/n𝐙`** through the degree: the isomorphism carrying the Kummer image of a
Picard class to its degree modulo `n`. -/
def rootsOfUnityH2AddEquivZMod (hn : IsUnit (n : k)) :
    Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n :=
  etaleH2RootsOfUnityAddEquivZMod k X f B hX n hn
    (subsingleton_sheafH_units k X f B hX n 2 le_rfl) (surjective_curvePicardDegree k X f)
    (exists_nsmul_eq_of_mem_curvePicardDegreeZero k X f n hn)

theorem rootsOfUnityH2AddEquivZMod_picardToRootsOfUnityH2 (hn : IsUnit (n : k))
    (x : schemePicard X) :
    rootsOfUnityH2AddEquivZMod k X f B hX n hn (picardToRootsOfUnityH2 k X f B hX n hn x) =
      ((curvePicardDegree k X f x : ℤ) : ZMod n) :=
  etaleH2RootsOfUnityAddEquivZMod_apply k X f B hX n hn _ _ _ x

/-- **`Pic(C)/n·Pic(C) = 𝐙/n𝐙`** through the degree modulo `n`. -/
def picardQuotientAddEquivZMod (hn : IsUnit (n : k)) :
    (schemePicard X ⧸ picardNMultiples X n) ≃+ ZMod n :=
  (picardQuotientAddEquivRootsOfUnityH2.{t} k X f B hX n hn).trans
    (rootsOfUnityH2AddEquivZMod k X f B hX n hn)

theorem picardQuotientAddEquivZMod_mk (hn : IsUnit (n : k)) (x : schemePicard X) :
    picardQuotientAddEquivZMod.{t} k X f B hX n hn (QuotientAddGroup.mk x) =
      ((curvePicardDegree k X f x : ℤ) : ZMod n) :=
  rootsOfUnityH2AddEquivZMod_picardToRootsOfUnityH2 k X f B hX n hn x

include f in
omit [IsProjectiveVariety k f] in
/-- **`H^q(C, μ_n) = 0` for `q ≥ 3`**: both neighbours `H^{q-1}(C, 𝐆_m)` and `H^q(C, 𝐆_m)` in the
Kummer sequence vanish. -/
theorem subsingleton_sheafH_rootsOfUnity (hn : IsUnit (n : k)) (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{t} (kummerSmallEtale B X hX n).X₁ q) :=
  subsingleton_etaleH_rootsOfUnity_of_three_le k X f B hX n hn
    (subsingleton_sheafH_units k X f B hX n) q hq

omit [HasExt (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat)] in
/-- **The cohomology of the constant sheaf `𝐙/n𝐙`** (Stacks, Tag 03RQ, second list): `𝐙/n𝐙`,
`(𝐙/n𝐙)^{2g}` with `g` the genus, `𝐙/n𝐙`, and `0` in degrees `≥ 3`. These come from the
cohomology of `μ_n` along the isomorphism of sheaves `μ_n ≅ 𝐙/n𝐙`
(`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`), which depends on a choice of
primitive `n`-th root of unity in `k`. -/
theorem nonempty_sheafH_constantZMod (hn : IsUnit (n : k))
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    Nonempty (Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) 1 ≃+
        (Fin (2 * genus f) → ZMod n)) ∧
      Nonempty (Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) q) :=
  (etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus k X f B hX n hn).2.2.2.2

end RootsOfUnity

end AlgebraicGeometry.SmoothProjectiveCurve

end
