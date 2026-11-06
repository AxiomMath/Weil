module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CohomologyEndomorphismOfPair
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import Weil.Attr

/-!
# The endomorphism of `RΓ_c(X, Gₙ)` induced by a homomorphism of ℓ-adic sheaves

Let `k` be a field, `X` a separated `k`-scheme of finite type with a compactification `j`,
`φ : X ⟶ X` an endomorphism, `G = (Gₙ)` an ℓ-adic sheaf on the small étale site of `X`, and
`f : φ^* G ⟶ G` a homomorphism of ℓ-adic sheaves over `φ`, with components
`fₙ : φ^* Gₙ ⟶ Gₙ`. For every `n`, the pair `(φ, fₙ)`, with `Gₙ` viewed as a complex
concentrated in degree `0`, is a pair on `X`, and so induces an endomorphism
`RΓ_c(φ, fₙ) = RΓ_c(X, fₙ) ∘ φ^♮` of `RΓ_c(X, Gₙ)` in the derived category of
`ℤ/ℓⁿ⁺¹ℤ`-modules, where `φ^♮ : RΓ_c(X, Gₙ) ⟶ RΓ_c(X, φ^* Gₙ)` is the pull-back.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.levelSingleComplex`: the level `Gₙ` of an ℓ-adic
  sheaf, as a bounded below complex concentrated in degree `0`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.levelPair`: the pair `(φ, fₙ)` on that
  complex.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.compactlySupportedCohomologyEndomorphism`:
  the endomorphism `RΓ_c(φ, fₙ)` of `RΓ_c(X, Gₙ)`.

## Main results

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.compactlySupportedCohomologyEndomorphism_eq`:
  `RΓ_c(φ, fₙ)` is the pull-back `φ^♮` followed by `RΓ_c(X, fₙ)`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.levelPair_map`: the morphism of the pair is
  `fₙ` placed in degree `0`.

## Implementation notes

`AlgebraicGeometry.SmallEtale.LAdicSheaf.levelSingleComplex` is the counterpart, on the small
étale site `AlgebraicGeometry.SmallEtale`, of `Stacks.EtaleCohomology.LAdicSheaf.levelComplex`,
which lives on Mathlib's small étale site.

As in `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyEndomorphism`, the
isomorphism `ε : RΓ_c(X, φ_* -) ≅ RΓ_c(X, -)` coming from `Rφ_! = φ_*` for finite `φ` is an
argument of the definition; the source assumes `φ` finite over `k` exactly so that the canonical
`ε` exists. The formula uses neither finiteness nor the structure over `k`, so neither is a
hypothesis here; the canonical `ε` of a finite `φ` is one admissible argument. The
coefficient ring at level `n` is `ℤ/ℓⁿ⁺¹ℤ` (levels indexed from `0`), as in
`AlgebraicGeometry.SmallEtale.LAdicSheaf`. All constructions are linear over it because the
sheaves, the inverse image and the unit of `φ^* ⊣ φ_*` are taken in sheaves of modules over it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], II.4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

universe u

namespace AlgebraicGeometry.SmallEtale.LAdicSheaf

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj]

variable (G : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)

/-- The level `Gₙ` of an ℓ-adic sheaf, as a bounded below complex of sheaves of
`ℤ/ℓⁿ⁺¹ℤ`-modules concentrated in degree `0`. -/
def levelSingleComplex :
    CochainComplex.Plus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj (G.level n), 0, inferInstance⟩

@[simp]
theorem levelSingleComplex_obj :
    (levelSingleComplex G n).obj = (CochainComplex.singleFunctor _ 0).obj (G.level n) :=
  rfl

namespace HomOver

variable {G} {φ : X ⟶ X} (f : HomOver φ G)

/-- The pair `(φ, fₙ)` on the complex `Gₙ` concentrated in degree `0`: the morphism
`φ^*(Gₙ[0]) ≅ (φ^* Gₙ)[0] ⟶ Gₙ[0]` is `fₙ` in degree `0`. -/
def levelPair :
    SmallEtaleComplexPair B X (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) (ComplexShape.up ℤ)
      (levelSingleComplex G n).obj where
  hom := φ
  map := (HomologicalComplex.singleMapHomologicalComplex
      (smallEtaleInverseImage B φ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (ComplexShape.up ℤ) 0).hom.app (G.level n) ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (f.level n)

@[simp]
theorem levelPair_hom : (f.levelPair n).hom = φ :=
  rfl

/-- The morphism of the pair `(φ, fₙ)` is `fₙ` placed in degree `0`, through the identification
of `φ^*(Gₙ[0])` with `(φ^* Gₙ)[0]`. -/
theorem levelPair_map :
    (f.levelPair n).map =
      (HomologicalComplex.singleMapHomologicalComplex
        (smallEtaleInverseImage B φ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        (ComplexShape.up ℤ) 0).hom.app (G.level n) ≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (f.level n) :=
  rfl

variable {k : Type u} [Field k] {σ : X.obj ⟶ Spec (.of k)} {j : CompactificationOf (Over.mk σ)}

/-- **The endomorphism `RΓ_c(φ, fₙ)` of `RΓ_c(X, Gₙ)`** induced by a homomorphism
`f : φ^* G ⟶ G` of ℓ-adic sheaves over an endomorphism `φ` of `X`, at level `n`: the
endomorphism of the pair `(φ, fₙ)` on `Gₙ` concentrated in degree `0`, a morphism in the
derived category of `ℤ/ℓⁿ⁺¹ℤ`-modules. It is computed with the isomorphisms
`ε_F : RΓ_c(X, φ_* F) ≅ RΓ_c(X, F)`, natural in the complex `F`, which for `φ` finite over `k`
come from `Rφ_! = φ_*`. -/
@[weil "def_fk204_induced_map_rgamma_c"]
def compactlySupportedCohomologyEndomorphism
    (ε : ((smallEtaleBaseChange B φ).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (topology B X.obj X.property) (topology B X.obj X.property)).mapCochainComplexPlus ⋙
          compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j ≅
        compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j) :
    (compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j).obj
        (levelSingleComplex G n) ⟶
      (compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j).obj
        (levelSingleComplex G n) :=
  SmallEtale.compactlySupportedCohomologyEndomorphism (f.levelPair n) ε

/-- `RΓ_c(φ, fₙ)` is the pull-back `φ^♮ : RΓ_c(X, Gₙ) ⟶ RΓ_c(X, φ^* Gₙ)` followed by
`RΓ_c(X, fₙ)`. -/
theorem compactlySupportedCohomologyEndomorphism_eq
    (ε : ((smallEtaleBaseChange B φ).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (topology B X.obj X.property) (topology B X.obj X.property)).mapCochainComplexPlus ⋙
          compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j ≅
        compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j) :
    f.compactlySupportedCohomologyEndomorphism n ε =
      (compactlySupportedCohomologyPullback ε).app (levelSingleComplex G n) ≫
        (compactlySupportedCohomologyComplex B (ZMod (ℓ ^ (n + 1))) k σ j).map
          (ObjectProperty.homMk (f.levelPair n).map) :=
  rfl

end HomOver

end AlgebraicGeometry.SmallEtale.LAdicSheaf

end
