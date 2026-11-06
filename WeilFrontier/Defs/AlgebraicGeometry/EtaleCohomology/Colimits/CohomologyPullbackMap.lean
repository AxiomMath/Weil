module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Scheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen

/-!
# The key-lemma assertion in one degree

Let `A` be a ring, `𝔭 ⊂ A` a prime ideal with residue field `κ(𝔭) = A_𝔭 / 𝔭 A_𝔭`, `K` a field
extension of `κ(𝔭)` (in the source, a separable closure), `M` an abelian group (in the source,
finite), `B` an `A`-algebra and `v ≥ 0`. For a finite subextension `κ(𝔭) ⊆ L ⊆ K` put
`X_L = Spec (B ⊗[A] L)`, with the morphisms `X_{L'} ⟶ X_L` for `L ⊆ L'`. The *key-lemma
assertion* `KL_v(A, 𝔭, K, M, B)` is:

* for `v = 0`, the map `M → colim_L H⁰(X_L, M_{X_L})` induced by the constant sections is
  bijective;
* for `v > 0`, `colim_L H^v(X_L, M_{X_L}) = 0`,

where `M_{X_L}` is the constant sheaf with value `M` on the small étale site of `X_L`, `H^v` is
étale cohomology, and the colimits run over the finite subextensions `L` of `K / κ(𝔭)`, along the
pull back maps `H^v(X_L, M) → H^v(X_{L'}, M)`.

## Main definitions

* `AlgebraicGeometry.KeyLemmaDegree.transitionMap`: the morphism `X_{L'} ⟶ X_L` for `L ≤ L'`.
* `AlgebraicGeometry.KeyLemmaDegree.cohomologyTransition`: the pull back map
  `H^v(X_L, M_{X_L}) →+ H^v(X_{L'}, M_{X_{L'}})`.
* `AlgebraicGeometry.KeyLemmaDegree.constSheaf`: the constant sheaf `M_X` on the small étale site.
* `AlgebraicGeometry.KeyLemmaDegree.constClass`: the class in `H⁰(X_L, M_{X_L})` of the constant
  section with value `m ∈ M`.
* `AlgebraicGeometry.KeyLemmaDegree`: the assertion `KL_v(A, 𝔭, K, M, B)`.

## Main results

* `AlgebraicGeometry.KeyLemmaDegree.etaleCohomologyPullback_constClass`,
  `AlgebraicGeometry.KeyLemmaDegree.cohomologyTransition_constClass`: the pull back maps carry
  constant sections to constant sections, so the classes `constClass L m` define one map
  `M → colim_L H⁰(X_L, M_{X_L})`.
* `AlgebraicGeometry.KeyLemmaDegree.zero_iff`, `AlgebraicGeometry.KeyLemmaDegree.succ_iff`: the
  two cases of the definition.

## Implementation notes

The finite subextensions of `K / κ(𝔭)` form a directed set (`FExt κ(𝔭) K`, a filtered category),
so the colimits are filtered colimits of abelian groups, and the assertion is stated through the
elementwise description of such a colimit: every element is represented at some stage, and an
element represented at a stage `L` is zero if and only if it becomes zero at some stage
`L' ⊇ L`. In degree zero, the map `M → colim_L H⁰` sends `m` to the class of
`constClass L m` for any `L` (independently of `L` by `cohomologyTransition_constClass`); it is
injective if and only if `constClass L m = 0` forces `m = 0` for every `L`, and surjective if and
only if every `x ∈ H⁰(X_L, M)` becomes a constant section at some stage `L' ⊇ L`. In positive
degree the colimit vanishes if and only if every class dies at some stage.

Étale cohomology is `CategoryTheory.Sheaf.H` on Mathlib's small étale site
`AlgebraicGeometry.Scheme.smallEtaleTopology`, with coefficients in `AddCommGrpCat.{u + 1}` for
schemes in `Scheme.{u}`; the constant sheaf has value `ULift M`. This is the site on which the
pull back maps of étale cohomology
(`Stacks.EtaleCohomology.etaleCohomologyPullback`) and the limit theorems for base changes to
the finite subextensions of a field extension are available. The scheme `X_L` is
`AlgebraicGeometry.henselianLineGeneric A B L`, which makes sense for any `A`-algebra `B`.

The `A`-algebra structure of `L` comes from an `A`-algebra structure on `K` compatible with
`κ(𝔭) → K`. The definition does not use that `A` is local, that `K` is a separable closure of
`κ(𝔭)`, or that `M` is finite; these hypotheses are carried by the results about it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

namespace KeyLemmaDegree

variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
  (K : Type u) [Field K] [Algebra p.ResidueField K] [Algebra A K]
  [IsScalarTower A p.ResidueField K] (B : Type u) [CommRing B] [Algebra A B]

/-- The morphism `X_{L'} ⟶ X_L`, `X_L = Spec (B ⊗[A] L)`, attached to an inclusion `L ≤ L'` of
finite subextensions of `K / κ(𝔭)`. -/
def transitionMap {L L' : FExt p.ResidueField K} (h : L ≤ L') :
    henselianLineGeneric A B L'.1 ⟶ henselianLineGeneric A B L.1 :=
  henselianLineGenericMap B
    ((IntermediateField.inclusion (show L.1 ≤ L'.1 from h)).restrictScalars A)

variable (M : Type u) [AddCommGroup M]

/-- The constant abelian sheaf with value `M` on the small étale site of a scheme, with
coefficients one universe up. -/
abbrev constSheaf (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} M))

/-- The pull back map `H^v(X_L, M_{X_L}) →+ H^v(X_{L'}, M_{X_{L'}})` for `L ≤ L'`: pull back
along `X_{L'} ⟶ X_L`, followed by the identification of the inverse image of the constant
sheaf with the constant sheaf. -/
def cohomologyTransition {L L' : FExt p.ResidueField K} (h : L ≤ L') (v : ℕ) :
    Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L.1)) v →+
      Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L'.1)) v :=
  etaleCohomologyPullback (transitionMap p K B h)
    ((smallEtalePullbackAbConstantIso (transitionMap p K B h)).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} M))) v

/-- The homomorphism `ℤ → M`, `n ↦ n • m`, between the universe lifts. -/
def constHom (m : M) : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of (ULift.{u + 1} M) :=
  AddCommGrpCat.ofHom ((AddEquiv.ulift.{u, u + 1}.symm : M ≃+ ULift.{u + 1} M).toAddMonoidHom.comp
    ((zmultiplesHom M m).comp (AddEquiv.ulift.{0, u + 1} : ULift.{u + 1} ℤ ≃+ ℤ).toAddMonoidHom))

/-- The class in `H⁰(X, M_X)` of the constant section with value `m ∈ M`: the morphism
`ℤ_X ⟶ M_X` of constant sheaves induced by `n ↦ n • m`. -/
def constClass (X : Scheme.{u}) (m : M) : Sheaf.H.{u + 1} (constSheaf M X) 0 :=
  Ext.mk₀ ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (constHom M m))

/-- **Pull back carries constant sections to constant sections.** For a morphism of schemes
`f : X ⟶ Y`, pulling back the constant section with value `m` on `Y` gives the constant
section with value `m` on `X`. -/
theorem etaleCohomologyPullback_constClass {X Y : Scheme.{u}} (f : X ⟶ Y) (m : M) :
    etaleCohomologyPullback f ((smallEtalePullbackAbConstantIso f).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} M))) 0 (constClass M Y m) = constClass M X m := by
  rw [constClass, etaleCohomologyPullback_mk₀, constClass]
  congr 1
  have h := (smallEtalePullbackAbConstantIso f).inv.naturality (constHom M m)
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The pull back maps of the system `L ↦ H⁰(X_L, M_{X_L})` carry constant sections to constant
sections. -/
theorem cohomologyTransition_constClass {L L' : FExt p.ResidueField K} (h : L ≤ L') (m : M) :
    cohomologyTransition p K B M h 0 (constClass M (henselianLineGeneric A B L.1) m) =
      constClass M (henselianLineGeneric A B L'.1) m :=
  etaleCohomologyPullback_constClass M _ m

end KeyLemmaDegree

variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
  (K : Type u) [Field K] [Algebra p.ResidueField K] [Algebra A K]
  [IsScalarTower A p.ResidueField K] (M : Type u) [AddCommGroup M]
  (B : Type u) [CommRing B] [Algebra A B]

open KeyLemmaDegree in
/-- **The key-lemma assertion `KL_v(A, 𝔭, K, M, B)`.** With `X_L = Spec (B ⊗[A] L)` for the
finite subextensions `L` of `K / κ(𝔭)`:

* for `v = 0`, the map `M → colim_L H⁰(X_L, M_{X_L})` induced by the constant sections is
  bijective: it is injective (a value whose constant section vanishes on some `X_L` is zero) and
  surjective (every section over some `X_L` becomes constant over some `X_{L'}`, `L ⊆ L'`);
* for `v > 0`, `colim_L H^v(X_L, M_{X_L}) = 0`: every class on some `X_L` vanishes on some
  `X_{L'}`, `L ⊆ L'`.

The colimits are filtered (see the implementation notes for this elementwise form). -/
@[weil "def_fk107_key_lemma_degree_statement"]
def KeyLemmaDegree : ℕ → Prop
  | 0 =>
      (∀ (L : FExt p.ResidueField K) (m : M),
        constClass M (henselianLineGeneric A B L.1) m = 0 → m = 0) ∧
      ∀ (L : FExt p.ResidueField K)
        (x : Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L.1)) 0),
        ∃ (L' : FExt p.ResidueField K) (h : L ≤ L') (m : M),
          cohomologyTransition p K B M h 0 x = constClass M (henselianLineGeneric A B L'.1) m
  | v + 1 =>
      ∀ (L : FExt p.ResidueField K)
        (x : Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L.1)) (v + 1)),
        ∃ (L' : FExt p.ResidueField K) (h : L ≤ L'), cohomologyTransition p K B M h (v + 1) x = 0

namespace KeyLemmaDegree

/-- `KL_0`: the constant sections give a bijection `M → colim_L H⁰(X_L, M_{X_L})`. -/
theorem zero_iff : KeyLemmaDegree p K M B 0 ↔
    (∀ (L : FExt p.ResidueField K) (m : M),
      constClass M (henselianLineGeneric A B L.1) m = 0 → m = 0) ∧
    ∀ (L : FExt p.ResidueField K)
      (x : Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L.1)) 0),
      ∃ (L' : FExt p.ResidueField K) (h : L ≤ L') (m : M),
        cohomologyTransition p K B M h 0 x = constClass M (henselianLineGeneric A B L'.1) m :=
  Iff.rfl

/-- `KL_v` for `v > 0`: `colim_L H^v(X_L, M_{X_L}) = 0`. -/
theorem succ_iff (v : ℕ) : KeyLemmaDegree p K M B (v + 1) ↔
    ∀ (L : FExt p.ResidueField K)
      (x : Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L.1)) (v + 1)),
      ∃ (L' : FExt p.ResidueField K) (h : L ≤ L'), cohomologyTransition p K B M h (v + 1) x = 0 :=
  Iff.rfl

/-- `KL_v` for `v > 0`, for any positive `v`. -/
theorem iff_of_pos {v : ℕ} (hv : 0 < v) : KeyLemmaDegree p K M B v ↔
    ∀ (L : FExt p.ResidueField K)
      (x : Sheaf.H.{u + 1} (constSheaf M (henselianLineGeneric A B L.1)) v),
      ∃ (L' : FExt p.ResidueField K) (h : L ≤ L'), cohomologyTransition p K B M h v x = 0 := by
  cases v with
  | zero => exact absurd hv (lt_irrefl 0)
  | succ v => exact succ_iff p K M B v

end KeyLemmaDegree

end AlgebraicGeometry
