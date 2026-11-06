module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CompactSupportCohomologyDerived
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves

/-!
# The transition maps of `RΓ_c(X, Gₙ)` for an `ℓ`-adic sheaf

Let `X` be a separated scheme of finite type over a field `k`, with a compactification `j` of
its structure morphism, and let `G = (Gₙ, uₙ)` be an `ℓ`-adic sheaf on `X`, so that `Gₙ` is a
sheaf of `Λₙ = ℤ/ℓⁿ⁺¹ℤ`-modules. Through the quotient map `Λₙ₊₁ → Λₙ` the sheaf `Gₙ` is a sheaf
of `Λₙ₊₁`-modules, and the transition map `uₙ₊₁ : Gₙ₊₁ ⟶ Gₙ` is a map of sheaves of
`Λₙ₊₁`-modules. Applying compactly supported cohomology `RΓ_c(X, -)` over `Λₙ₊₁` gives the
morphism
`τₙ = RΓ_c(X, uₙ₊₁) : RΓ_c(X, Gₙ₊₁) ⟶ RΓ_c(X, Gₙ)`
of the bounded below derived category `D⁺(Λₙ₊₁)`, the target being `RΓ_c` of `Gₙ` with its
coefficients restricted to `Λₙ₊₁`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.compactlySupportedCohomologyTransition`: the morphism
  `τₙ : RΓ_c(X, Gₙ₊₁) ⟶ RΓ_c(X, Gₙ)` of `D⁺(ℤ/ℓⁿ⁺²ℤ)`.

## Implementation notes

The `ℓ`-adic sheaves are those of Stacks, Tag 03UM (`AlgebraicGeometry.SmallEtale.LAdicSheaf`),
whose transition map at `n` is a morphism from level `n + 1` into the restriction of scalars of
level `n` along `ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ`: this is exactly the source's reading of `uₙ₊₁` as a map of
sheaves of `Λₙ₊₁`-modules. A sheaf is viewed in `D⁺` as a complex concentrated in degree `0`.
Compactly supported cohomology is `AlgebraicGeometry.SmallEtale.compactlySupportedCohomology`,
with the compactification an explicit argument. The source works over a separably closed field;
the construction uses no hypothesis on the field.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], II.4.1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [Fact ℓ.Prime]
  (k : Type u) [Field k] (f : X.obj ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))

/-- **The transition map of `RΓ_c(X, Gₙ)`.** For an `ℓ`-adic sheaf `G` on `X` and `n ≥ 0`, the
morphism `τₙ = RΓ_c(X, uₙ₊₁) : RΓ_c(X, Gₙ₊₁) ⟶ RΓ_c(X, Gₙ)` of `D⁺(ℤ/ℓⁿ⁺²ℤ)` induced by the
transition map `uₙ₊₁ : Gₙ₊₁ ⟶ Gₙ`, a map of sheaves of `ℤ/ℓⁿ⁺²ℤ`-modules, `Gₙ` being one through
`ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ`. -/
@[weil "not_fk204_rgamma_c_transition"]
def LAdicSheaf.compactlySupportedCohomologyTransition (G : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) :
    (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (G.level (n + 1))) ⟶
      (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((G.level n).restrictScalars B X ℓ n)) :=
  (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).map
    ((DerivedCategory.Plus.singleFunctor _ 0).map (G.transition n))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- `τₙ` is `RΓ_c(X, -)` applied to the transition map `uₙ₊₁`, placed in degree `0`. -/
theorem LAdicSheaf.compactlySupportedCohomologyTransition_eq (G : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) :
    LAdicSheaf.compactlySupportedCohomologyTransition B X ℓ k f j G n =
      (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map (G.transition n)) :=
  rfl

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- `τₙ` is natural in the `ℓ`-adic sheaf: a morphism `φ : G ⟶ G'` of `ℓ`-adic sheaves
commutes with the transition maps of `RΓ_c`. -/
theorem LAdicSheaf.compactlySupportedCohomologyTransition_naturality
    {G G' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : LAdicSheaf.Hom B X ℓ G G') (n : ℕ) :
    LAdicSheaf.compactlySupportedCohomologyTransition B X ℓ k f j G n ≫
        (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((sheafCompose (SmallEtale.topology B X.obj X.property)
              (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map
                (φ.app n))) =
      (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map (φ.app (n + 1))) ≫
        LAdicSheaf.compactlySupportedCohomologyTransition B X ℓ k f j G' n := by
  simp only [compactlySupportedCohomologyTransition, ← Functor.map_comp, φ.naturality]

end AlgebraicGeometry.SmallEtale

end
