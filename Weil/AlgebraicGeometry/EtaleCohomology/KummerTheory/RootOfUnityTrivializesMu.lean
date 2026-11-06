module

public import Weil.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnitySupplement
public import Weil.Attr

/-!
# A global root of unity of exact order `n` trivializes `μ_n`

Let `X` be a scheme, `n ≥ 1` an integer invertible in `Γ(X, 𝒪_X)` and `ζ ∈ Γ(X, 𝒪_X)` an
element whose image in every local ring `𝒪_{X,x}` is a primitive `n`-th root of unity. Then
the morphism of étale sheaves of abelian groups `(𝐙/n𝐙)_X → (μ_n)_X` sending the global
section `1` to `ζ` is an isomorphism.

## The argument

*Local rings.* Let `R` be a local ring in which `n` is invertible and `ζ ∈ R` with `ζⁿ = 1`.
If `u ∈ R` satisfies `uⁿ = 1` and `u ≡ 1` modulo the maximal ideal, then `u = 1`: indeed
`0 = uⁿ - 1 = (u - 1)(1 + u + ⋯ + u^{n-1})` and the second factor is `≡ n`, a unit. Applied to
`u = ζ^d`, `d` the order of the residue class of `ζ`, this shows that the residue class of a
primitive `n`-th root of unity is again primitive, so that `ζ^k - 1` is a unit for `0 < k < n`.
These elements are then units of `Γ(X, 𝒪_X)`, and so of the ring of functions of every étale
`X`-scheme. Conversely, if `ζ^k - 1` is a unit of `R` for `0 < k < n`, the residue class of `ζ` is
a primitive root, so every `w ∈ R` with `wⁿ = 1` has residue class `ζ̄^j` for some `j`, and the
same argument applied to `u = w ζ^{n-j}` gives `w = ζ^j`.

*Injectivity.* For `i ≢ j mod n` the difference `ζ^i - ζ^j` is a unit, so two distinct residue
classes give the same function only over an empty scheme.

*Surjectivity.* A function `w` on an étale `X`-scheme `U` with `wⁿ = 1` is, in each local ring of
`U`, a power `ζ^j`, hence equal to `ζ^j` on a neighbourhood. These neighbourhoods form an open
cover of `U`, which is refined by a covering family of the small étale site.

So the morphism from the constant presheaf to `μ_n` is locally bijective and becomes an
isomorphism after sheafification.

## Main definitions

* `AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm`: the
  isomorphism `(𝐙/n𝐙)_X ≅ (μ_n)_X` attached to `ζ`.

## Main results

* `AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm_hom_one`: the
  isomorphism sends the global section `1` to `ζ`.
* `IsLocalRing.isUnit_pow_sub_one_of_isPrimitiveRoot`: in a local ring in which `n` is
  invertible, `ζ^k - 1` is a unit for a primitive `n`-th root of unity `ζ` and `0 < k < n`.
* `IsLocalRing.exists_eq_pow_of_pow_eq_one`: under the same hypotheses, every `n`-th root of
  unity is a power of `ζ`.

## Implementation notes

The site is the small étale site `SmallEtale B X hX` of `X` inside a big étale site `B`; the
constant sheaf is the sheafification of the constant presheaf with value `ULift (ZMod n)` and
`μ_n` is the kernel of the `n`-th power map of the sheaf of units on that site, as in
`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`, which is the case of a primitive root
of unity of an algebraically closed base field. The hypothesis that the image of `ζ` in
`𝒪_{X,x}^*` has order exactly `n` is written `IsPrimitiveRoot (germ ζ) n`, which is equivalent
by `IsPrimitiveRoot.iff_orderOf`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Roots of unity in a local ring -/

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In a local ring in which `m` is invertible, an `m`-th root of unity congruent to `1` modulo
the maximal ideal is `1`. -/
theorem eq_one_of_pow_eq_one_of_residue_eq_one {m : ℕ} (hm : IsUnit (m : R)) {u : R}
    (hu : u ^ m = 1) (hu1 : residue R u = 1) : u = 1 := by
  have hgeom : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  have hres : residue R (∑ i ∈ Finset.range m, u ^ i) = (m : ResidueField R) := by
    simp [map_sum, hu1]
  have hunit : IsUnit (∑ i ∈ Finset.range m, u ^ i) := by
    rw [← residue_ne_zero_iff_isUnit, hres]
    exact (hm.map (residue R)).ne_zero
  exact sub_eq_zero.1 ((hunit.mul_right_eq_zero).1 hgeom)

/-- In a local ring in which `n` is invertible, the residue class of a primitive `n`-th root of
unity is a primitive `n`-th root of unity of the residue field. -/
theorem isPrimitiveRoot_residue {n : ℕ} (hn : IsUnit (n : R)) {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (residue R ζ) n := by
  have hpow : residue R ζ ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨e, he⟩ : orderOf (residue R ζ) ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have he' : IsUnit (e : R) := by
    rw [he, Nat.cast_mul] at hn
    exact isUnit_of_mul_isUnit_right hn
  have hw : ζ ^ orderOf (residue R ζ) = 1 := by
    refine eq_one_of_pow_eq_one_of_residue_eq_one he' ?_ ?_
    · rw [← pow_mul, ← he, hζ.pow_eq_one]
    · rw [map_pow, pow_orderOf_eq_one]
  rw [IsPrimitiveRoot.iff_orderOf]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow) (hζ.dvd_of_pow_eq_one _ hw)

/-- In a local ring in which `n` is invertible, `ζ^k - 1` is a unit for a primitive `n`-th root
of unity `ζ` and `0 < k < n`. -/
theorem isUnit_pow_sub_one_of_isPrimitiveRoot {n : ℕ} (hn : IsUnit (n : R)) {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) {k : ℕ} (hk0 : 0 < k) (hkn : k < n) : IsUnit (ζ ^ k - 1) := by
  rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_one, sub_ne_zero]
  exact (isPrimitiveRoot_residue hn hζ).pow_ne_one_of_pos_of_lt hk0.ne' hkn

/-- If `ζⁿ = 1` and `ζ^k - 1` is a unit for `0 < k < n`, then the residue class of `ζ` is a
primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_residue_of_isUnit_pow_sub_one {n : ℕ} (hn0 : n ≠ 0) {ζ : R}
    (hζn : ζ ^ n = 1) (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1)) :
    IsPrimitiveRoot (residue R ζ) n := by
  refine IsPrimitiveRoot.mk_of_lt _ (Nat.pos_of_ne_zero hn0) (by rw [← map_pow, hζn, map_one])
    fun k hk0 hkn h => ?_
  have := (hζ k hk0 hkn).map (residue R)
  rw [map_sub, map_pow, map_one, h, sub_self] at this
  exact not_isUnit_zero this

/-- In a local ring in which `n` is invertible, if `ζⁿ = 1` and `ζ^k - 1` is a unit for
`0 < k < n`, then every `n`-th root of unity is a power `ζ^j` with `j < n`. -/
theorem exists_eq_pow_of_pow_eq_one {n : ℕ} (hn : IsUnit (n : R)) {ζ : R} (hζn : ζ ^ n = 1)
    (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1)) {w : R} (hw : w ^ n = 1) :
    ∃ j < n, w = ζ ^ j := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have : NeZero n := ⟨hn0⟩
  obtain ⟨j, hj, hjw⟩ :=
    (isPrimitiveRoot_residue_of_isUnit_pow_sub_one hn0 hζn hζ).eq_pow_of_pow_eq_one
      (ξ := residue R w) (by rw [← map_pow, hw, map_one])
  refine ⟨j, hj, ?_⟩
  have hu : w * ζ ^ (n - j) = 1 := by
    refine eq_one_of_pow_eq_one_of_residue_eq_one hn ?_ ?_
    · rw [mul_pow, hw, one_mul, ← pow_mul, mul_comm, pow_mul, hζn, one_pow]
    · rw [map_mul, map_pow, ← hjw, ← pow_add, Nat.add_sub_cancel' hj.le, ← map_pow, hζn,
        map_one]
  calc w = w * ζ ^ (n - j) * ζ ^ j := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj.le, hζn, mul_one]
    _ = ζ ^ j := by rw [hu, one_mul]

end IsLocalRing

/-! ### Roots of unity in a commutative ring -/

/-- If `ζⁿ = 1` and `ζ^k - 1` is a unit for `0 < k < n`, then `ζ^i - ζ^j` is a unit for
distinct `i, j < n`. -/
theorem isUnit_pow_sub_pow_of_isUnit_pow_sub_one {R : Type*} [CommRing R] {n : ℕ} {ζ : R}
    (hζn : ζ ^ n = 1) (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1)) {i j : ℕ} (hi : i < n)
    (hj : j < n) (hij : i ≠ j) : IsUnit (ζ ^ i - ζ ^ j) := by
  have hζu : IsUnit ζ := (Units.ofPowEqOne ζ n hζn (by omega)).isUnit
  have key : ∀ a b : ℕ, a < b → b < n → IsUnit (ζ ^ b - ζ ^ a) := by
    intro a b hab hb
    have : ζ ^ b - ζ ^ a = ζ ^ a * (ζ ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    rw [this]
    exact (hζu.pow a).mul (hζ _ (by omega) (by omega))
  rcases lt_or_gt_of_ne hij with h | h
  · have := (key i j h hj).neg
    rwa [neg_sub] at this
  · exact key j i h hi

namespace AlgebraicGeometry

/-! ### Global functions with primitive germs -/

namespace Scheme

variable {X : Scheme.{u}} {n : ℕ} {ζ : Γ(X, ⊤)}

/-- A global function whose germs are `n`-th roots of unity is an `n`-th root of unity. -/
theorem pow_eq_one_of_forall_isPrimitiveRoot_germ
    (hζ : ∀ x : X, IsPrimitiveRoot (X.presheaf.germ ⊤ x trivial ζ) n) : ζ ^ n = 1 :=
  TopCat.Presheaf.section_ext X.sheaf ⊤ _ _ fun x hx => by
    change X.presheaf.germ ⊤ x hx (ζ ^ n) = X.presheaf.germ ⊤ x hx 1
    rw [map_pow, (hζ x).pow_eq_one, map_one]

/-- If `n` is invertible on `X` and the germs of `ζ` are primitive `n`-th roots of unity, then
`ζ^k - 1` is invertible on `X` for `0 < k < n`. -/
theorem isUnit_pow_sub_one_of_forall_isPrimitiveRoot_germ (hn : IsUnit (n : Γ(X, ⊤)))
    (hζ : ∀ x : X, IsPrimitiveRoot (X.presheaf.germ ⊤ x trivial ζ) n) {k : ℕ} (hk0 : 0 < k)
    (hkn : k < n) : IsUnit (ζ ^ k - 1) :=
  X.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun x hx => by
    change IsUnit (X.presheaf.germ ⊤ x hx (ζ ^ k - 1))
    rw [map_sub, map_pow, map_one]
    refine IsLocalRing.isUnit_pow_sub_one_of_isPrimitiveRoot ?_ (hζ x) hk0 hkn
    simpa only [map_natCast] using hn.map (X.presheaf.germ ⊤ x hx).hom

/-- **An `n`-th root of unity is locally a power of `ζ`.** If `n` is invertible on `Y`,
`ζⁿ = 1` and `ζ^k - 1` is invertible for `0 < k < n`, then a function `w` on `Y` with `wⁿ = 1`
is equal to some `ζ^j` on a neighbourhood `V` of any given point; that is, every morphism
`Z ⟶ Y` landing in `V` pulls `w` back to `ζ^j`. -/
theorem exists_open_pullback_eq_pow (Y : Scheme.{u}) {n : ℕ} (hn : IsUnit (n : Γ(Y, ⊤)))
    {ζ : Γ(Y, ⊤)} (hζn : ζ ^ n = 1) (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1))
    (w : Γ(Y, ⊤)) (hw : w ^ n = 1) (y : Y) :
    ∃ (V : Y.Opens) (j : ℕ), y ∈ V ∧ j < n ∧
      ∀ (Z : Scheme.{u}) (ψ : Z ⟶ Y), (∀ z : Z, ψ z ∈ V) →
        (Scheme.Γ.map ψ.op).hom w = (Scheme.Γ.map ψ.op).hom (ζ ^ j) := by
  let g := (Y.presheaf.germ ⊤ y trivial).hom
  obtain ⟨j, hj, hjw⟩ := IsLocalRing.exists_eq_pow_of_pow_eq_one (R := Y.presheaf.stalk y)
    (n := n) (ζ := g ζ) (w := g w) (by simpa only [map_natCast] using hn.map g)
    (by rw [← map_pow, hζn, map_one])
    (fun k hk0 hkn => by simpa only [map_sub, map_pow, map_one] using (hζ k hk0 hkn).map g)
    (by rw [← map_pow, hw, map_one])
  obtain ⟨W, hyW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq Y.presheaf y
    (show y ∈ (⊤ : Y.Opens) from trivial) (show y ∈ (⊤ : Y.Opens) from trivial) w (ζ ^ j)
    (by
      change g w = g (ζ ^ j)
      rw [map_pow]
      exact hjw)
  have hiU : iU = homOfLE le_top := Subsingleton.elim _ _
  have hiV : iV = homOfLE le_top := Subsingleton.elim _ _
  subst hiU hiV
  refine ⟨W, j, hyW, hj, fun Z ψ hψ => ?_⟩
  have he : (ψ ⁻¹ᵁ (⊤ : Y.Opens)) ≤ ψ ⁻¹ᵁ W := fun z _ => hψ z
  have key : Scheme.Γ.map ψ.op =
      Y.presheaf.map (homOfLE (le_top (a := W))).op ≫ ψ.appLE W (ψ ⁻¹ᵁ ⊤) he := by
    rw [Scheme.Hom.map_appLE, Scheme.Γ_map_op, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [key]
  change (ψ.appLE W (ψ ⁻¹ᵁ ⊤) he).hom ((Y.presheaf.map _).hom w) =
    (ψ.appLE W (ψ ⁻¹ᵁ ⊤) he).hom ((Y.presheaf.map _).hom (ζ ^ j))
  rw [heq]

end Scheme

/-! ### The comparison from the constant presheaf -/

namespace GlobalRootOfUnity

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)

/-- Pullback of global functions of `X` to an object of the small étale site of `X`. -/
def globalHom (T : SmallEtale B X hX) :
    Γ(X, ⊤) →+* Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)) :=
  (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map
    ((SmallEtale.finalIsTerminal B X hX).from T)).op).hom

theorem globalHom_naturality {T T' : SmallEtale B X hX} (g : T' ⟶ T) (x : Γ(X, ⊤)) :
    (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map g).op).hom (globalHom B hX T x) =
      globalHom B hX T' x := by
  have hcomp : g ≫ (SmallEtale.finalIsTerminal B X hX).from T =
      (SmallEtale.finalIsTerminal B X hX).from T' :=
    (SmallEtale.finalIsTerminal B X hX).hom_ext _ _
  change ((Scheme.Γ.map ((SmallEtale.toScheme B X hX).map
        ((SmallEtale.finalIsTerminal B X hX).from T)).op) ≫
      (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map g).op)).hom x = _
  rw [← Scheme.Γ.map_comp, ← op_comp, ← Functor.map_comp, hcomp]
  rfl

theorem globalHom_final (x : Γ(X, ⊤)) : globalHom B hX (SmallEtale.final B X hX) x = x := by
  have h : (SmallEtale.finalIsTerminal B X hX).from (SmallEtale.final B X hX) = 𝟙 _ :=
    (SmallEtale.finalIsTerminal B X hX).hom_ext _ _
  rw [globalHom, h, CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

variable {n : ℕ} [NeZero n] {ζ : Γ(X, ⊤)} (hζn : ζ ^ n = 1)

/-- `ζ` as a unit of `Γ(X, 𝒪_X)`. -/
def rootUnit : (Γ(X, ⊤))ˣ :=
  Units.ofPowEqOne ζ n hζn (NeZero.ne n)

theorem rootUnit_pow : rootUnit hζn ^ n = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, rootUnit, Units.val_ofPowEqOne, hζn, Units.val_one])

theorem zmultiplesHom_rootUnit_natCast :
    zmultiplesHom (Additive (Γ(X, ⊤))ˣ) (Additive.ofMul (rootUnit hζn)) n = 0 := by
  change (n : ℤ) • (Additive.ofMul (rootUnit hζn) : Additive (Γ(X, ⊤))ˣ) = 0
  rw [natCast_zsmul, ← ofMul_pow, rootUnit_pow]
  rfl

/-- `j ↦ ζ^j`, from `𝐙/n𝐙` to the units of `Γ(X, 𝒪_X)`. -/
def zmodHom : ULift.{u} (ZMod n) →+ Additive ((Γ(X, ⊤))ˣ) :=
  (ZMod.lift n ⟨_, zmultiplesHom_rootUnit_natCast hζn⟩).comp
    (AddEquiv.ulift.{0, u} (α := ZMod n)).toAddMonoidHom

theorem zmodHom_apply (j : ZMod n) :
    ((Additive.toMul (zmodHom hζn (ULift.up j)) : (Γ(X, ⊤))ˣ) : Γ(X, ⊤)) = ζ ^ j.val := by
  have hj : zmodHom hζn (ULift.up j) = Additive.ofMul (rootUnit hζn ^ j.val) := by
    have key : ∀ m : ℤ, zmodHom hζn (ULift.up (m : ZMod n)) =
        m • Additive.ofMul (rootUnit hζn) := fun m => by
      change ZMod.lift n ⟨_, zmultiplesHom_rootUnit_natCast hζn⟩ (m : ZMod n) = _
      rw [ZMod.lift_coe]
      rfl
    have := key j.val
    rwa [Int.cast_natCast, ZMod.natCast_zmod_val, natCast_zsmul, ← ofMul_pow] at this
  rw [hj, toMul_ofMul, Units.val_pow_eq_pow_val, rootUnit, Units.val_ofPowEqOne]

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `𝐆_m`, `j ↦ ζ^j`. -/
def constToUnits :
    (Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶
      unitsPresheaf (SmallEtale.toScheme B X hX) where
  app T := (show AddCommGrpCat.of (ULift.{u} (ZMod n)) ⟶
        (unitsPresheaf (SmallEtale.toScheme B X hX)).obj (op (SmallEtale.final B X hX)) from
      AddCommGrpCat.ofHom (zmodHom hζn)) ≫
    (unitsPresheaf (SmallEtale.toScheme B X hX)).map
      ((SmallEtale.finalIsTerminal B X hX).from T.unop).op
  naturality T T' g := by
    have hcomp : (SmallEtale.finalIsTerminal B X hX).from T'.unop =
        g.unop ≫ (SmallEtale.finalIsTerminal B X hX).from T.unop :=
      (SmallEtale.finalIsTerminal B X hX).hom_ext _ _
    dsimp only [Functor.const_obj_map]
    rw [hcomp, op_comp, Functor.map_comp]
    exact (Category.assoc _ _ _).symm

theorem constToUnits_app_val (T : SmallEtale B X hX) (j : ZMod n) :
    ((Additive.toMul ((constToUnits B hX hζn).app (op T) (ULift.up j)) :
        (Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)))ˣ) :
        Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T))) =
      globalHom B hX T (ζ ^ j.val) := by
  rw [← zmodHom_apply hζn j]
  rfl

/-- The comparison to `𝐆_m` lands in the kernel of the `n`-th power map. -/
theorem constToUnits_comp_power :
    constToUnits B hX hζn ≫
      (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
        (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n) = 0 := by
  have key : ∀ (T : (SmallEtale B X hX)ᵒᵖ) (x : ULift.{u} (ZMod n)),
      ((constToUnits B hX hζn ≫
        (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
          (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) n)).app T).hom x = 0 := by
    intro T x
    have hx : (n • x : ULift.{u} (ZMod n)) = 0 := by
      apply ULift.ext
      change n • x.down = (0 : ZMod n)
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have h1 : ((constToUnits B hX hζn ≫
        (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
          (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) n)).app T).hom x =
        n • (((constToUnits B hX hζn).app T).hom x) := rfl
    rw [h1, ← map_nsmul, hx]
    exact map_zero _
  apply NatTrans.ext
  funext T
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  exact key T

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `μ_n`, `j ↦ ζ^j`. -/
def constToRoots :
    (Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶
      (rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj :=
  kernel.lift
      ((sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
        (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n))
      (constToUnits B hX hζn) (constToUnits_comp_power B hX hζn) ≫
    (PreservesKernel.iso
      (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})
      (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n)).inv

theorem constToRoots_comp_ι :
    constToRoots B hX hζn ≫
        (kernel.ι (powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom =
      constToUnits B hX hζn := by
  let E := sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}
  let p := powerSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  have h1 : (PreservesKernel.iso E p).inv ≫ E.map (kernel.ι p) = kernel.ι (E.map p) := by
    rw [Iso.inv_comp_eq, PreservesKernel.iso_hom]
    exact (kernelComparison_comp_ι p E).symm
  change (kernel.lift (E.map p) (constToUnits B hX hζn)
      (constToUnits_comp_power B hX hζn) ≫
      (PreservesKernel.iso E p).inv) ≫ E.map (kernel.ι p) = _
  rw [Category.assoc, h1]
  exact kernel.lift_ι _ _ _

variable (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1))

include hζ in
/-- Two residue classes with the same image in `𝐆_m` over an étale `X`-scheme agree locally:
distinct classes give powers of `ζ` whose difference is a unit, so they agree only over an
empty object, which is covered by the empty family. -/
theorem constToUnits_isLocallyInjective :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) (constToUnits B hX hζn) := by
  refine ⟨fun {T} a b hab => ?_⟩
  by_cases hab' : a = b
  · subst hab'
    simp
  · have hne : a.down.val ≠ b.down.val := fun h =>
      hab' (ULift.ext _ _ (ZMod.val_injective n h))
    have hunit := (isUnit_pow_sub_pow_of_isUnit_pow_sub_one hζn hζ (ZMod.val_lt a.down)
      (ZMod.val_lt b.down) hne).map (globalHom B hX T.unop)
    have hval : globalHom B hX T.unop (ζ ^ a.down.val) = globalHom B hX T.unop (ζ ^ b.down.val) :=
      (constToUnits_app_val B hX hζn T.unop a.down).symm.trans
        ((congrArg (fun z => (Additive.toMul z).val) hab).trans
          (constToUnits_app_val B hX hζn T.unop b.down))
    rw [map_sub, hval, sub_self, isUnit_zero_iff] at hunit
    have hempty : IsEmpty ((SmallEtale.toScheme B X hX).obj T.unop) :=
      ConstantRootsOfUnity.isEmpty_of_one_eq_zero hunit.symm
    have heq : Presheaf.equalizerSieve
        (F := (Functor.const (SmallEtale B X hX)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))) (X := T) a b = ⊥ := by
      ext Y g
      simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply]
      constructor
      · intro hf
        exact False.elim (hab' (by simpa using hf))
      · intro hf
        exact False.elim hf
    rw [heq]
    exact openCoverData_bottom (SmallEtale.toScheme B X hX) (SmallEtale.topology B X hX)
      (smallEtale_openCoverData B X hX) hempty

include hζ in
theorem constToRoots_isLocallyInjective :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) (constToRoots B hX hζn) := by
  refine ⟨fun {T} x y hxy => ?_⟩
  refine (constToUnits_isLocallyInjective B hX hζn hζ).equalizerSieve_mem x y ?_
  have hfac := NatTrans.congr_app (constToRoots_comp_ι B hX hζn) T
  exact (ConcreteCategory.congr_hom hfac x).symm.trans
    ((congrArg (fun z => (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
        n)).hom.app T) z)) hxy).trans (ConcreteCategory.congr_hom hfac y))

variable (hn : IsUnit (n : Γ(X, ⊤)))

omit [NeZero n] in
include hζn hζ hn in
/-- An `n`-th root of unity over an étale `X`-scheme is, on a covering family of the small
étale site, one of the powers of `ζ`. -/
theorem exists_cover_eq_pow (T : SmallEtale B X hX)
    (w : Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T))) (hw : w ^ n = 1) :
    ∃ (I : Type (u + 1)) (W : I → SmallEtale B X hX) (a : ∀ i, W i ⟶ T) (jj : I → ZMod n),
      Sieve.ofArrows W a ∈ SmallEtale.topology B X hX T ∧
        ∀ i, (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map (a i)).op).hom w =
          globalHom B hX (W i) (ζ ^ (jj i).val) := by
  classical
  let φ : Γ(X, ⊤) →+* Γ((SmallEtale.toScheme B X hX).obj T, ⊤) := globalHom B hX T
  have hgeom := fun y => Scheme.exists_open_pullback_eq_pow
    ((SmallEtale.toScheme B X hX).obj T) (n := n) (ζ := φ ζ)
    (by simpa only [map_natCast] using hn.map φ) (by rw [← map_pow, hζn, map_one])
    (fun k hk0 hkn => by simpa only [map_sub, map_pow, map_one] using (hζ k hk0 hkn).map φ)
    w hw y
  choose V jn hyV hjn hpull using hgeom
  have hVcover : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover]
    refine le_antisymm le_top ?_
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hyV x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtale_openCoverData B X hX V hVcover
  refine ⟨I, W, a, fun i => (jn (r i) : ZMod n), hcover, fun i => ?_⟩
  rw [ZMod.val_natCast_of_lt (hjn (r i)), ← globalHom_naturality B hX (a i)]
  exact (hpull (r i) _ ((SmallEtale.toScheme B X hX).map (a i)) (hmaps i)).trans
    (congrArg _ (map_pow φ ζ _).symm)

include hζ hn in
theorem constToRoots_isLocallySurjective :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X hX) (constToRoots B hX hζn) := by
  classical
  refine ⟨fun {T} s => ?_⟩
  have hnsmul : n • (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s) = 0 :=
    congrArg (fun φ : kernel (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n) ⟶
          unitsSheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) =>
      (φ.hom.app (op T)) s)
      (kernel.condition (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n))
  have hwn : ((Additive.toMul (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s)).val :
      Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T))) ^ n = 1 := by
    have h2 : (n • (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s) :
        Additive ((Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)))ˣ)) = 0 := hnsmul
    have h3 := congrArg Additive.toMul h2
    have h5 : (Additive.toMul (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op T)) s) :
        (Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj T)))ˣ) ^ n = 1 :=
      (ConstantRootsOfUnity.additive_nsmul_toMul _ n _).symm.trans h3
    have h6 := congrArg Units.val h5
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h6
    exact h6
  obtain ⟨I, W, a, jj, hcover, heq⟩ := exists_cover_eq_pow B hX hζn hζ hn T _ hwn
  refine (SmallEtale.topology B X hX).superset_covering ?_ hcover
  intro Z g hg
  obtain ⟨i, g', rfl⟩ := (Sieve.mem_ofArrows_iff W a g).mp hg
  apply (Presheaf.imageSieve (constToRoots B hX hζn) s).downward_closed
  refine ⟨ULift.up (jj i), ?_⟩
  apply ConstantRootsOfUnity.rootsSheaf_ι_app_injective B hX n (W i)
  have hstep1 : (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op (W i)))
        ((constToRoots B hX hζn).app (op (W i)) (ULift.up (jj i)))) =
      (constToUnits B hX hζn).app (op (W i)) (ULift.up (jj i)) :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (constToRoots_comp_ι B hX hζn) (op (W i))) (ULift.up (jj i))
  have hL := constToUnits_app_val B hX hζn (W i) (jj i)
  have hR : (Additive.toMul ((unitsPresheaf (SmallEtale.toScheme B X hX)).map (a i).op
        (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s))).val =
      (Scheme.Γ.map ((SmallEtale.toScheme B X hX).map (a i)).op).hom
        (Additive.toMul (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s)).val := rfl
  have hstep2 : (constToUnits B hX hζn).app (op (W i)) (ULift.up (jj i)) =
      (unitsPresheaf (SmallEtale.toScheme B X hX)).map (a i).op
        (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s) :=
    Additive.toMul.injective (Units.ext (hL.trans ((heq i).symm.trans hR.symm)))
  have hstep3 : (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
          n)).hom.app (op (W i)))
        ((rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj.map (a i).op s)) =
      (unitsPresheaf (SmallEtale.toScheme B X hX)).map (a i).op
        (((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX)
            n)).hom.app (op T)) s) :=
    NatTrans.naturality_apply (kernel.ι (powerSheaf (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom (a i).op s
  exact (hstep1.trans hstep2).trans hstep3.symm

include hζn in
/-- `ζ` raised to the representative of the class `1 ∈ 𝐙/n𝐙` is `ζ`. -/
theorem pow_val_one : ζ ^ (1 : ZMod n).val = ζ := by
  rw [ZMod.val_one_eq_one_mod]
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.mod_eq_of_lt h, pow_one]
  · have h1 : n = 1 := le_antisymm h (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
    subst h1
    rw [Nat.mod_self, pow_zero, ← hζn, pow_one]

end GlobalRootOfUnity

open GlobalRootOfUnity

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {n : ℕ} [NeZero n]
  {ζ : Γ(X, ⊤)}

/-- The isomorphism `(𝐙/n𝐙)_X ≅ (μ_n)_X`, `j ↦ ζ^j`, for `ζ ∈ Γ(X, 𝒪_X)` with `ζⁿ = 1` such
that `ζ^k - 1` is invertible for `0 < k < n`, and `n` invertible on `X`. -/
def constantZModSheafIsoRootsOfUnitySheafOfIsUnit (hn : IsUnit (n : Γ(X, ⊤)))
    (hζn : ζ ^ n = 1) (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1)) :
    (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) ≅
      rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n := by
  haveI := constToRoots_isLocallyInjective B hX hζn hζ
  haveI := constToRoots_isLocallySurjective B hX hζn hζ hn
  have hα : IsIso ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
      (constToRoots B hX hζn)) := by
    rw [← (SmallEtale.topology B X hX).W_iff]
    exact ((SmallEtale.topology B X hX).W_iff_isLocallyBijective _).mpr
      ⟨inferInstance, inferInstance⟩
  let R := rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  exact @asIso _ _ _ _ ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
      (constToRoots B hX hζn)) hα ≪≫
    asIso ((sheafificationAdjunction (SmallEtale.topology B X hX) AddCommGrpCat.{u}).counit.app R)

/-- The isomorphism `constantZModSheafIsoRootsOfUnitySheafOfIsUnit`, precomposed with the unit
of sheafification, is the comparison `j ↦ ζ^j` from the constant presheaf. -/
theorem toSheafify_comp_constantZModSheafIsoRootsOfUnitySheafOfIsUnit_hom
    (hn : IsUnit (n : Γ(X, ⊤))) (hζn : ζ ^ n = 1)
    (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1)) :
    toSheafify (SmallEtale.topology B X hX)
        ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n)))) ≫
      (constantZModSheafIsoRootsOfUnitySheafOfIsUnit B hX hn hζn hζ).hom.hom =
    constToRoots B hX hζn := by
  have h2 : ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
      (constToRoots B hX hζn)).hom =
        sheafifyMap (D := AddCommGrpCat.{u}) _ (constToRoots B hX hζn) := rfl
  simp only [constantZModSheafIsoRootsOfUnitySheafOfIsUnit, Iso.trans_hom, asIso_hom,
    ObjectProperty.FullSubcategory.comp_hom]
  erw [h2, ← toSheafify_naturality_assoc]
  rw [sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift, Category.comp_id]

theorem constantZModSheafIsoRootsOfUnitySheafOfIsUnit_hom_one (hn : IsUnit (n : Γ(X, ⊤)))
    (hζn : ζ ^ n = 1) (hζ : ∀ k, 0 < k → k < n → IsUnit (ζ ^ k - 1)) :
    rootsOfUnitySheafGlobalValue B hX
        ((constantZModSheafIsoRootsOfUnitySheafOfIsUnit B hX hn hζn hζ).hom.hom.app
          (op (SmallEtale.final B X hX)) (constantSheafOneSection B hX)) = ζ := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_constantZModSheafIsoRootsOfUnitySheafOfIsUnit_hom B hX hn hζn hζ)
      (op (SmallEtale.final B X hX))) (ULift.up (1 : ZMod n))
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app (constToRoots_comp_ι B hX hζn)
    (op (SmallEtale.final B X hX))) (ULift.up 1)
  unfold rootsOfUnitySheafGlobalValue constantSheafOneSection
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  erw [h]
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  erw [h', constToUnits_app_val, pow_val_one hζn, globalHom_final]

/-- **A root of unity of exact order `n` trivializes `μ_n`** [FK, I.2]. Let `n ≥ 1` be invertible
in `Γ(X, 𝒪_X)` and let `ζ ∈ Γ(X, 𝒪_X)` have image of order exactly `n` in `𝒪_{X,x}^*` for
every `x ∈ X`. Then there is an isomorphism of étale sheaves of abelian groups
`θ : (𝐙/n𝐙)_X ≅ (μ_n)_X` on the small étale site of `X`, sending the global section `1` to `ζ`
(`constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm_hom_one`); on sections over an
étale `X`-scheme, a residue class `j` goes to `ζ^j`. -/
@[weil "lem_fk102_root_of_unity_trivializes_mu"]
def constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm (hn : IsUnit (n : Γ(X, ⊤)))
    (hζ : ∀ x : X, IsPrimitiveRoot (X.presheaf.germ ⊤ x trivial ζ) n) :
    (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) ≅
      rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n :=
  constantZModSheafIsoRootsOfUnitySheafOfIsUnit B hX hn
    (Scheme.pow_eq_one_of_forall_isPrimitiveRoot_germ hζ)
    (fun _ hk0 hkn => Scheme.isUnit_pow_sub_one_of_forall_isPrimitiveRoot_germ hn hζ hk0 hkn)

/-- **`θ_X(1) = ζ`** [FK, I.2]: the isomorphism
`constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm` sends the global section `1` of
`(𝐙/n𝐙)_X` to `ζ`. -/
@[weil "lem_fk102_root_of_unity_trivializes_mu"]
theorem constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm_hom_one
    (hn : IsUnit (n : Γ(X, ⊤)))
    (hζ : ∀ x : X, IsPrimitiveRoot (X.presheaf.germ ⊤ x trivial ζ) n) :
    rootsOfUnitySheafGlobalValue B hX
        ((constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRootGerm B hX hn hζ).hom.hom.app
          (op (SmallEtale.final B X hX)) (constantSheafOneSection B hX)) = ζ :=
  constantZModSheafIsoRootsOfUnitySheafOfIsUnit_hom_one B hX hn _ _

end AlgebraicGeometry
