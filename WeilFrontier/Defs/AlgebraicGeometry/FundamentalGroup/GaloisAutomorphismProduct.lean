module

public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Weil.Attr

/-!
# The product of the automorphism groups of the pointed Galois covering spaces

Let `s` be a geometric point of a scheme `X`. The group `P(X, s)` is the product
`∏_{(Y, α)} G(Y/X)` of the automorphism groups `G(Y/X) = Aut Y` of the covering spaces underlying
the pointed Galois covering spaces `(Y, α)` of `(X, s)`, each factor carrying the discrete
topology and the product the product topology. Its elements are the families
`σ = (σ_{(Y, α)})`, multiplied componentwise. The fundamental group `π₁(X, s)` is a closed
subgroup of `P(X, s)`.

Since each factor is a finite discrete group, `P(X, s)` is a compact, Hausdorff, totally
disconnected topological group. Over a connected base it is the product
`∏_A Aut A` over Mathlib's pointed Galois objects `A` of the Galois category of covering spaces
with the geometric fibre functor at `s`, i.e. the product of the groups of the system
`CategoryTheory.PreGaloisCategory.autGaloisSystem`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.GaloisAutomorphismProduct s` — the topological group
  `P(X, s)`.
* `AlgebraicGeometry.GeometricPoint.GaloisAutomorphismProduct.proj P` — the projection
  `P(X, s) → G(Y/X)` to the factor of a pointed Galois covering space `P = (Y, α)`.
* `AlgebraicGeometry.GeometricPoint.GaloisAutomorphismProduct.mulEquivPiPointedGaloisObject` —
  over a connected base, `P(X, s)` is the product of the automorphism groups of Mathlib's pointed
  Galois objects.

## Main results

* `AlgebraicGeometry.GeometricPoint.GaloisAutomorphismProduct.isOpen_preimage_proj` — every
  projection is continuous for the discrete topology on its target.
* Instances: `P(X, s)` is a topological group, compact, Hausdorff and totally disconnected.

## Implementation notes

The discrete topology on each factor `Aut Y` is not declared as an instance on `Aut Y` (a global
topology on all automorphism groups would be wrong elsewhere); it enters only through the
topology of `P(X, s)`, which is `Pi.topologicalSpace` with `⊥` on every factor.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} (s : GeometricPoint X)

/-- **The product group `P(X, s)`.** For a geometric point `s` of `X`, `P(X, s)` is the product
of the automorphism groups `G(Y/X)` of the pointed Galois covering spaces `(Y, α)` of `(X, s)`:
its elements are the families `σ = (σ_{(Y, α)})` with `σ_{(Y, α)} ∈ G(Y/X)`, multiplied
componentwise, and its topology is the product of the discrete topologies. -/
@[weil "def_fka1_galois_automorphism_product"]
def GaloisAutomorphismProduct : Type (u + 1) :=
  ∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover

namespace GaloisAutomorphismProduct

variable {s}

/-- Componentwise multiplication on `P(X, s)`. -/
@[weil "def_fka1_galois_automorphism_product"]
instance instGroup : Group s.GaloisAutomorphismProduct :=
  inferInstanceAs (Group (∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover))

/-- The product of the discrete topologies on the factors `G(Y/X)`. -/
@[weil "def_fka1_galois_automorphism_product"]
instance instTopologicalSpace : TopologicalSpace s.GaloisAutomorphismProduct :=
  @Pi.topologicalSpace _ _ fun _ ↦ ⊥

instance : CoeFun s.GaloisAutomorphismProduct
    fun _ ↦ ∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover :=
  ⟨id⟩

@[ext]
theorem ext {σ τ : s.GaloisAutomorphismProduct} (h : ∀ P, σ P = τ P) : σ = τ :=
  funext h

@[simp]
theorem mul_apply (σ τ : s.GaloisAutomorphismProduct) (P : s.PointedGaloisCoveringSpace) :
    (σ * τ) P = σ P * τ P :=
  rfl

@[simp]
theorem one_apply (P : s.PointedGaloisCoveringSpace) :
    (1 : s.GaloisAutomorphismProduct) P = 1 :=
  rfl

@[simp]
theorem inv_apply (σ : s.GaloisAutomorphismProduct) (P : s.PointedGaloisCoveringSpace) :
    σ⁻¹ P = (σ P)⁻¹ :=
  rfl

/-- A family of automorphisms, as an element of `P(X, s)`. -/
def mk (σ : ∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover) : s.GaloisAutomorphismProduct :=
  σ

@[simp]
theorem mk_apply (σ : ∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover)
    (P : s.PointedGaloisCoveringSpace) : mk σ P = σ P :=
  rfl

variable (s) in
/-- `P(X, s)` is the group of families: the identity, as a multiplicative equivalence. -/
def mulEquivPi :
    s.GaloisAutomorphismProduct ≃* ∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover :=
  MulEquiv.refl _

/-- The projection `p_{(Y, α)} : P(X, s) → G(Y/X)` to the factor of `P = (Y, α)`. -/
def proj (P : s.PointedGaloisCoveringSpace) : s.GaloisAutomorphismProduct →* Aut P.obj.cover :=
  Pi.evalMonoidHom (fun P : s.PointedGaloisCoveringSpace ↦ Aut P.obj.cover) P

@[simp]
theorem proj_apply (P : s.PointedGaloisCoveringSpace) (σ : s.GaloisAutomorphismProduct) :
    proj P σ = σ P :=
  rfl

section Topology

/-- The local discrete topologies on the factors, used to transport instances from the Pi type. -/
private abbrev factorTop : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) :=
  fun _ ↦ ⊥

private theorem discrete_factorTop (P : s.PointedGaloisCoveringSpace) :
    @DiscreteTopology (Aut P.obj.cover) (factorTop P) :=
  @DiscreteTopology.mk _ (factorTop P) rfl

/-- Each projection `P(X, s) → G(Y/X)` is continuous for the discrete topology on `G(Y/X)`: the
preimage of every subset is open. -/
theorem isOpen_preimage_proj (P : s.PointedGaloisCoveringSpace) (S : Set (Aut P.obj.cover)) :
    IsOpen ((fun σ : s.GaloisAutomorphismProduct ↦ σ P) ⁻¹' S) := by
  let : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) := factorTop
  have : ∀ P : s.PointedGaloisCoveringSpace, DiscreteTopology (Aut P.obj.cover) :=
    discrete_factorTop
  exact (isOpen_discrete S).preimage
    (continuous_apply (A := fun P : s.PointedGaloisCoveringSpace ↦ Aut P.obj.cover) P)

/-- The family of elements of `P(X, s)` agreeing with `σ` at a given factor is open. -/
theorem isOpen_setOf_apply_eq (P : s.PointedGaloisCoveringSpace) (g : Aut P.obj.cover) :
    IsOpen {σ : s.GaloisAutomorphismProduct | σ P = g} :=
  isOpen_preimage_proj P {g}

/-- `P(X, s)` is a topological group. -/
instance : IsTopologicalGroup s.GaloisAutomorphismProduct :=
  letI : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) := factorTop
  haveI : ∀ P : s.PointedGaloisCoveringSpace, DiscreteTopology (Aut P.obj.cover) :=
    discrete_factorTop
  inferInstanceAs (IsTopologicalGroup (∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover))

/-- `P(X, s)` is Hausdorff. -/
instance : T2Space s.GaloisAutomorphismProduct :=
  letI : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) := factorTop
  haveI : ∀ P : s.PointedGaloisCoveringSpace, DiscreteTopology (Aut P.obj.cover) :=
    discrete_factorTop
  inferInstanceAs (T2Space (∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover))

/-- `P(X, s)` is totally disconnected. -/
instance : TotallyDisconnectedSpace s.GaloisAutomorphismProduct :=
  letI : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) := factorTop
  haveI : ∀ P : s.PointedGaloisCoveringSpace, DiscreteTopology (Aut P.obj.cover) :=
    discrete_factorTop
  inferInstanceAs
    (TotallyDisconnectedSpace (∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover))

/-- `P(X, s)` is compact: it is a product of finite discrete groups (Tychonoff). -/
instance : CompactSpace s.GaloisAutomorphismProduct :=
  letI : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) := factorTop
  haveI : ∀ P : s.PointedGaloisCoveringSpace, DiscreteTopology (Aut P.obj.cover) :=
    discrete_factorTop
  haveI : ∀ P : s.PointedGaloisCoveringSpace, Finite (Aut P.obj.cover) :=
    fun P ↦ P.isGalois.finite_aut
  inferInstanceAs (CompactSpace (∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover))

end Topology

section Connected

variable [ConnectedSpace X]

variable (s) in
/-- **`P(X, s)` as a product over Mathlib's pointed Galois objects.** Over a connected base,
`P(X, s)` is the product of the automorphism groups `Aut A` of the pointed Galois objects `A` of
the Galois category of covering spaces with the geometric fibre functor at `s` — the product of
the groups of the system `CategoryTheory.PreGaloisCategory.autGaloisSystem`. -/
def mulEquivPiPointedGaloisObject :
    s.GaloisAutomorphismProduct ≃*
      ∀ A : PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s), Aut A.obj where
  toFun σ A := σ ((PointedGaloisCoveringSpace.ofPointedGaloisObject s).obj A)
  invFun τ P := τ ((PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem mulEquivPiPointedGaloisObject_apply (σ : s.GaloisAutomorphismProduct)
    (A : PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s)) :
    mulEquivPiPointedGaloisObject s σ A =
      σ ((PointedGaloisCoveringSpace.ofPointedGaloisObject s).obj A) :=
  rfl

theorem mulEquivPiPointedGaloisObject_symm_apply
    (τ : ∀ A : PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s), Aut A.obj)
    (P : s.PointedGaloisCoveringSpace) :
    (mulEquivPiPointedGaloisObject s).symm τ P =
      τ ((PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P) :=
  rfl

end Connected

end GaloisAutomorphismProduct

end GeometricPoint

end AlgebraicGeometry

end
