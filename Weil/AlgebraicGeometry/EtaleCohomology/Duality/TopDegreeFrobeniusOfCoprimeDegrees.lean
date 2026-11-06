module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilIIPurityAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafEndomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointPurityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The Frobenius on the top cohomology without a rational point

Let `X` be proper over a finite field `k` with `q = p ^ q₀` elements, with `Y = X_k̄` connected
and smooth of relative dimension `d` over `k̄`, and let `ℓ ≠ p` be a prime. When `X` has a
`k`-rational point, the geometric Frobenius `π̄` acts on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` as multiplication by
`q^d` (StacksFrontier's
`constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass`).
This file removes the rational point, assuming instead closed points of `X` whose degrees divide
two coprime integers.

Restriction `g^*` of `Hⁱ(X, ℤ/N) = Ext^i(Λ_X, Λ_X)` along a morphism of schemes is functorial,
`(g ≫ h)^* = g^* ∘ h^*` and `(𝟙_X)^* = id`, on a preconnected source: the two ways of identifying
the inverse image of `Λ_X` along the composite with `Λ_Z` differ by an automorphism of `Λ_Z`,
which is a scalar since `Z` is preconnected, and conjugation by a scalar is trivial. Hence
restriction along `π̄ ^ m` is the `m`-th iterate of restriction along `π̄`. For a closed point `y`
of `X` of degree `e` with residue field `k'`, the scheme `X' = X ×_k k'` has a `k'`-rational
point, `X'_k̄ ≅ Y`, and under this isomorphism the Frobenius of `X'` over `k'` is `π̄ ^ e`; so
`π̄ ^ e` acts on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` as `q^{de}`. Since `H^{2d}(Y, ℤ/ℓⁿ⁺¹) ≅ ℤ/ℓⁿ⁺¹`, the
Frobenius acts as multiplication by some `c` with `c^{e₁} = (q^d)^{e₁}` and `c^{e₂} = (q^d)^{e₂}`;
for `e₁`, `e₂` coprime and `q` prime to `ℓ` this forces `c = q^d`.

## Main results

* `Stacks.EtaleCohomology.constantExtRestriction_comp_apply`: `(g ≫ h)^* = g^* ∘ h^*`.
* `Stacks.EtaleCohomology.constantExtRestriction_id_apply`: `(𝟙_X)^* = id`.
* `Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChangePow_apply`:
  `(π̄ ^ m)^* = (π̄^*)^m`.
* `constantExtRestriction_geometricFrobeniusBaseChangePow_top_of_fieldExtension`:
  `(π̄ ^ m)^* = q^{dm}` on `H^{2d}` when `X` has a point over an extension of degree `m`.
* `Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_top_of_coprime`:
  `π̄^* = q^d` on `H^{2d}`, given closed points of degrees dividing two coprime integers.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

section Functoriality

open Stacks.ExtTransport

variable {N : ℕ} {X Y Z : Scheme.{u}}

/-- Restriction `g^*` is the conjugate of the action of the inverse image by `Λ_Y ≅ g⁻¹ Λ_X`. -/
theorem constantExtRestriction_eq_sandwich (g : Y ⟶ X) {i : ℕ}
    (x : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) i) :
    constantExtRestriction (ZMod N) g i x =
      sandwich (constantInverseImageIso (ZMod N) g).hom (constantInverseImageIso (ZMod N) g).inv i
        (x.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod N) g)) := by
  rw [constantExtRestriction_apply, sandwich_apply]
  exact Ext.comp_assoc _ _ _ _ _ (by omega)

/-- The restriction of `Ext` classes between constant sheaves through an exact functor `L` and an
identification `Λ_Z ≅ L Λ_X` does not depend on these choices, on a preconnected `Z`. -/
theorem sandwich_mapExactFunctor_eq_of_iso [NeZero N] [PreconnectedSpace Z]
    {L L' : EtaleModules.{u, 0} (ZMod N) X ⥤ EtaleModules.{u, 0} (ZMod N) Z}
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] (τ : L ≅ L')
    (e : Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) Z.smallEtaleTopology ≅
      L.obj (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology))
    (e' : Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) Z.smallEtaleTopology ≅
      L'.obj (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology))
    {i : ℕ}
    (x : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) i) :
    sandwich e.hom e.inv i (x.mapExactFunctor L) =
      sandwich e'.hom e'.inv i (x.mapExactFunctor L') := by
  have h1 : x.mapExactFunctor L = sandwich (τ.hom.app _) (τ.inv.app _) i
      (x.mapExactFunctor L') := by
    rw [sandwich_apply, ← Ext.comp_assoc _ _ _ (zero_add i) (add_zero i) (by omega),
      Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor τ.hom _ i x,
      Ext.comp_assoc _ _ _ (add_zero i) (zero_add 0) (by omega), Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id_app, Ext.comp_mk₀_id]
  have h2 : x.mapExactFunctor L' = sandwich e'.inv e'.hom i
      (sandwich e'.hom e'.inv i (x.mapExactFunctor L')) := by
    rw [sandwich_sandwich, Iso.inv_hom_id]
    simp [sandwich_apply]
  rw [h1, sandwich_sandwich]
  conv_lhs => rw [h2, sandwich_sandwich]
  refine Stacks.EtaleCohomology.KummerFlag.sandwich_eq_self_of_comp_eq_id
    (w' := e.hom ≫ τ.hom.app _ ≫ e'.inv) (w := e'.hom ≫ τ.inv.app _ ≫ e.inv) ?_ _
  simp

/-- **Restriction of `Hⁱ(X, ℤ/N)` is functorial**: `(g ≫ h)^* = g^* ∘ h^*` on a preconnected
`Z`. -/
theorem constantExtRestriction_comp_apply [NeZero N] [PreconnectedSpace Z] (g : Z ⟶ Y) (h : Y ⟶ X)
    {i : ℕ}
    (x : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) i) :
    constantExtRestriction (ZMod N) (g ≫ h) i x =
      constantExtRestriction (ZMod N) g i (constantExtRestriction (ZMod N) h i x) := by
  rw [constantExtRestriction_eq_sandwich, constantExtRestriction_eq_sandwich,
    constantExtRestriction_eq_sandwich,
    sandwich_mapExactFunctor_eq_of_iso (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) g h) _
      (constantInverseImageIso (ZMod N) g ≪≫
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).mapIso (constantInverseImageIso (ZMod N) h)),
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  simp only [sandwich_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Iso.trans_hom,
    Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, ← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]

/-- **Restriction along the identity is the identity**, on a preconnected `X`. -/
theorem constantExtRestriction_id_apply [NeZero N] [PreconnectedSpace X] {i : ℕ}
    (x : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) i) :
    constantExtRestriction (ZMod N) (𝟙 X) i x = x := by
  rw [constantExtRestriction_eq_sandwich,
    sandwich_mapExactFunctor_eq_of_iso (etaleModuleInverseImageIdIso.{u, 0} (ZMod N) X) _
      (Iso.refl _), Stacks.ExtFunctorial.mapExactFunctor_id, Iso.refl_hom, Iso.refl_inv]
  simp [sandwich_apply]

/-- **Restriction along `π̄^m` is the `m`-th iterate of restriction along `π̄`.** -/
theorem constantExtRestriction_geometricFrobeniusBaseChangePow_apply [NeZero N] {k : Type u}
    [Field k] [Fintype k] (W : Over (Spec (.of k))) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    [PreconnectedSpace (fieldBaseChange W kbar)] (m : ℕ) {i : ℕ}
    (x : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
        (fieldBaseChange W kbar).smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
        (fieldBaseChange W kbar).smallEtaleTopology) i) :
    constantExtRestriction (ZMod N) (geometricFrobeniusBaseChangePow W kbar p q hcard m) i x =
      (constantExtRestriction (ZMod N) (geometricFrobeniusBaseChange W kbar p q hcard) i)^[m]
        x := by
  induction m with
  | zero => exact constantExtRestriction_id_apply x
  | succ m ih =>
    rw [geometricFrobeniusBaseChangePow_succ, constantExtRestriction_comp_apply, ih,
      Function.iterate_succ_apply']

end Functoriality

section Scalar

/-- **An endomorphism of a cyclic group of order `N` with two coprime powers equal to the same
powers of a multiplication by a unit is that multiplication.** If `G ≅ ℤ/N`, `T : G → G` is
additive, `s` is prime to `N`, and `T^{e₁} = s^{e₁}` and `T^{e₂} = s^{e₂}` with `e₁`, `e₂`
coprime, then `T = s`. -/
theorem _root_.AddMonoidHom.eq_nsmul_of_iterate_eq_pow_nsmul {G : Type*} [AddCommGroup G] {N : ℕ}
    [NeZero N] (φ : G ≃+ ZMod N) (T : G →+ G) {s : ℕ} (hs : s.Coprime N) {e₁ e₂ : ℕ}
    (he : e₁.Coprime e₂) (h₁ : ∀ z, T^[e₁] z = s ^ e₁ • z) (h₂ : ∀ z, T^[e₂] z = s ^ e₂ • z)
    (z : G) : T z = s • z := by
  set c := φ (T (φ.symm 1)) with hc
  have hT : ∀ z, φ (T z) = φ z * c := by
    intro z
    have hz : z = (φ z).val • φ.symm 1 := by
      apply φ.injective
      rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    conv_lhs => rw [hz]
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hiter : ∀ (e : ℕ) (z : G), φ (T^[e] z) = φ z * c ^ e := by
    intro e
    induction e with
    | zero => intro z; simp
    | succ e ih => intro z; rw [Function.iterate_succ_apply', hT, ih, pow_succ, mul_assoc]
  have hpow : ∀ e, (∀ z, T^[e] z = s ^ e • z) → c ^ e = (s : ZMod N) ^ e := by
    intro e he
    have := hiter e (φ.symm 1)
    rw [he, map_nsmul, AddEquiv.apply_symm_apply, one_mul, nsmul_eq_mul, mul_one,
      Nat.cast_pow] at this
    exact this.symm
  set u := ZMod.unitOfCoprime s hs
  have hx : ∀ e, (∀ z, T^[e] z = s ^ e • z) → (c * ↑u⁻¹) ^ e = 1 := by
    intro e he
    rw [mul_pow, hpow e he, ← Units.val_pow_eq_pow_val, show (s : ZMod N) = (u : ZMod N) from rfl,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one]
  have h1 : (c * ↑u⁻¹) ^ e₁.gcd e₂ = 1 := pow_gcd_eq_one.2 ⟨hx e₁ h₁, hx e₂ h₂⟩
  rw [he, pow_one] at h1
  have hcs : c = s := by
    have := congrArg (· * (u : ZMod N)) h1
    simp only [mul_assoc, Units.inv_mul, mul_one, one_mul] at this
    exact this
  apply φ.injective
  rw [hT, hcs, map_nsmul, nsmul_eq_mul, mul_comm]

end Scalar

section FieldExtension

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The Frobenius on the top cohomology of `X_k̄`, through a point over an extension**: if `X`
has a point over a finite extension `k'` of `k` of degree `m`, restriction along `π̄ ^ m` is
multiplication by `q ^ (d m)` on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)`. -/
theorem constantExtRestriction_geometricFrobeniusBaseChangePow_top_of_fieldExtension
    [IsAlgClosure k kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (k' : Type u) [Field k'] [Finite k'] [Algebra k k'] [Module.Finite k k']
    (a : Spec (.of k') ⟶ X.1) (ha : a ≫ f = specAlgebraMap k k') :
    ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard (Module.finrank k k'))
          (2 * d) z = (((p ^ q) ^ d) ^ Module.finrank k k' : ℕ) • z := by
  intro n z
  let : Fintype k' := Fintype.ofFinite _
  set m := Module.finrank k k' with hm
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hcard' : Fintype.card k' = p ^ (q * m) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hcard, ← hm, pow_mul]
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  let σ : k' →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra k' kbar := σ.toRingHom.toAlgebra
  have : IsScalarTower k k' kbar := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  have : IsNoetherian (fieldExtensionScheme B X f k').1 :=
    isNoetherian_fieldExtensionScheme B X f k'
  set ψ := fieldBaseChangeExtensionIso (Over.mk f) k' kbar
  have : SmoothOfRelativeDimension d
      (pullback.snd (Over.mk (pullback.snd f (specAlgebraMap k k'))).hom
        (specAlgebraMap k' kbar)) := by
    have h := fieldBaseChangeExtensionIso_hom_snd (Over.mk f) k' kbar
    have : SmoothOfRelativeDimension (0 + d)
        (ψ.hom ≫ pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
      inferInstance
    rw [zero_add, h] at this
    exact this
  have hconn' : ConnectedSpace
      (fieldBaseChange (Over.mk (pullback.snd f (specAlgebraMap k k'))) kbar) :=
    Function.Surjective.connectedSpace (Scheme.Hom.surjective ψ.inv) (Scheme.Hom.continuous _)
  have : PreconnectedSpace (fieldBaseChange (extensionOver (Over.mk f) k') kbar) :=
    hconn'.toPreconnectedSpace
  have hpt := exists_section_fieldExtensionScheme B X f k' a ha
  have hX' : ∀ z, constantExtRestriction (ZMod (ℓ ^ (n + 1)))
      (geometricFrobeniusBaseChange (extensionOver (Over.mk f) k') kbar p (q * m) hcard') (2 * d) z
        = ((p ^ (q * m)) ^ d : ℕ) • z :=
    constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass
    B (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k')) kbar p (q * m)
    hcard' d hℓ hpt (topCohomologyPointClass ℓ kbar hℓ) n
  have hcomm : geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard m =
      ψ.inv ≫ geometricFrobeniusBaseChange (extensionOver (Over.mk f) k') kbar p (q * m) hcard' ≫
        ψ.hom := by
    rw [geometricFrobeniusBaseChange_extension_comp_hom, Iso.inv_hom_id_assoc]
  rw [hcomm, constantExtRestriction_comp_apply, constantExtRestriction_comp_apply, hX',
    map_nsmul, ← constantExtRestriction_comp_apply, Iso.inv_hom_id,
    constantExtRestriction_id_apply, ← pow_mul, ← pow_mul, ← pow_mul, mul_assoc, mul_comm m d]

/-- **The Frobenius on the top cohomology of `X_k̄`, through a closed point**: restriction along
`π̄ ^ deg y` is multiplication by `q ^ (d deg y)` on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)`, for a closed point `y`
of `X` of degree `deg y` over `k`. -/
theorem constantExtRestriction_geometricFrobeniusBaseChangePow_top_of_isClosed
    [IsAlgClosure k kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar)) (y : X.1)
    (hy : IsClosed ({y} : Set X.1)) :
    ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard (residueDegree f y))
          (2 * d) z = (((p ^ q) ^ d) ^ residueDegree f y : ℕ) • z := by
  have := finite_residueField f y hy
  let : Algebra k (X.1.residueField y) := (fieldToResidue f y).hom.toAlgebra
  have : Module.Finite k (X.1.residueField y) := Module.Finite.of_finite
  have ha := (fromSpecResidueField_comp_eq_iff f (X.1.residueField y) y (𝟙 _)).2
    (by rw [Category.comp_id]; rfl)
  exact constantExtRestriction_geometricFrobeniusBaseChangePow_top_of_fieldExtension B X ℓ f kbar
    p q hcard d hℓ (X.1.residueField y) _ ha

/-- **The Frobenius on the top cohomology of `X_k̄` is multiplication by `q^d`, without a rational
point**: for `X` proper over `k` with `Y = X_k̄` connected and smooth of relative dimension `d`
over `k̄`, and closed points of degrees dividing two coprime integers `m₁` and `m₂`, restriction
along `π̄` is multiplication by `q^d` on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` for every `n`. -/
theorem constantExtRestriction_geometricFrobeniusBaseChange_top_of_coprime
    [IsAlgClosure k kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : ℓ ≠ p) (m₁ m₂ : ℕ)
    (hcop : Nat.Coprime m₁ m₂)
    (hpt : ∀ m ∈ ({m₁, m₂} : Set ℕ),
      ∃ (y : X.1) (_ : IsClosed ({y} : Set X.1)), residueDegree f y ∣ m) :
    ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z := by
  intro n z
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hℓu : IsUnit (ℓ : kbar) := by
    refine Ne.isUnit fun h => hℓ ?_
    rw [CharP.cast_eq_zero_iff kbar p] at h
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 h).symm
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹IsProper f›
  obtain ⟨φ⟩ := nonempty_ext_unitSheaf_top_addEquiv_zmod_pow ℓ hℓu
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d n
  obtain ⟨y₁, hy₁, hd₁⟩ := hpt m₁ (by simp)
  obtain ⟨y₂, hy₂, hd₂⟩ := hpt m₂ (by simp)
  have hs : ((p ^ q) ^ d).Coprime (ℓ ^ (n + 1)) :=
    Nat.Coprime.pow _ _ (Nat.Coprime.pow_left _
      ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).2 (Ne.symm hℓ)))
  have hiter : ∀ (y : X.1) (_ : IsClosed ({y} : Set X.1)) (z : Ext
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      (constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d))^[residueDegree f y] z =
        ((p ^ q) ^ d) ^ residueDegree f y • z := by
    intro y hy z
    rw [← constantExtRestriction_geometricFrobeniusBaseChangePow_apply,
      constantExtRestriction_geometricFrobeniusBaseChangePow_top_of_isClosed B X ℓ f kbar p q hcard
        d hℓu y hy n z]
  exact AddMonoidHom.eq_nsmul_of_iterate_eq_pow_nsmul φ _ hs
    ((hcop.coprime_dvd_left hd₁).coprime_dvd_right hd₂) (hiter y₁ hy₁) (hiter y₂ hy₂) z

end FieldExtension

end Stacks.EtaleCohomology

end
