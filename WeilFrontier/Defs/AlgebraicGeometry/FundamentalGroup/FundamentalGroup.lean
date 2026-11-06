module

public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.GaloisAutomorphismProduct
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.PointedCoveringMorphism
public import WeilFrontier.Defs.CategoryTheory.Galois.GaloisObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import Mathlib.CategoryTheory.Galois.Topology
public import Weil.Attr

/-!
# The fundamental group `π₁(X, s)`

Let `s` be a geometric point of a scheme `X`. The fundamental group `π₁(X, s)` is the subgroup
of the topological group `P(X, s) = ∏_{(Y, α)} G(Y/X)` of the families `σ = (σ_{(Y, α)})`
indexed by the pointed Galois covering spaces of `(X, s)` that are compatible with the mappings
of pointed covering spaces: for every mapping `f : (Z, γ) → (Y, α)` between pointed Galois
covering spaces, `σ_{(Y, α)}` is a restriction of `σ_{(Z, γ)}` along `f`, i.e.
`σ_{(Y, α)} ∘ f = f ∘ σ_{(Z, γ)}`. It carries the subspace topology of `P(X, s)`.

Over a connected base, the compatible families are the elements of Mathlib's limit
`CategoryTheory.PreGaloisCategory.AutGalois` of the automorphism groups of the pointed Galois
objects of the Galois category of covering spaces with the geometric fibre functor at `s`, and
`π₁(X, s)` is isomorphic, as a topological group, to the étale fundamental group
`AlgebraicGeometry.EtaleFundamentalGroup X s` of the Stacks project, the automorphism group of the
geometric fibre functor.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.fundamentalGroup s` — the fundamental group `π₁(X, s)`, a
  subgroup of `P(X, s)`.
* `AlgebraicGeometry.GeometricPoint.fundamentalGroupMulEquivAutGalois s` — over a connected base,
  `π₁(X, s)` is the group `AutGalois` of compatible families over the pointed Galois objects.
* `AlgebraicGeometry.GeometricPoint.fundamentalGroupContinuousMulEquiv s` — over a connected base,
  `π₁(X, s)` is isomorphic as a topological group to `EtaleFundamentalGroup X s`.

## Main results

* `AlgebraicGeometry.GeometricPoint.mem_fundamentalGroup_iff_isHom` — membership in `π₁(X, s)`
  in terms of mappings of pointed covering spaces, as morphisms of schemes.
* `AlgebraicGeometry.GeometricPoint.fundamentalGroupMulEquivAut_hom_app_point` — the
  automorphism of the fibre functor attached to `σ` moves the base point `α` of `(Y, α)` by
  `σ_{(Y, α)}⁻¹`.

## Implementation notes

Composition of automorphisms in `Aut Y` and composition of automorphisms of the fibre functor are
related by an anti-isomorphism: Mathlib's `CategoryTheory.PreGaloisCategory.autMulEquivAutGalois`
identifies `Aut F` with the opposite group of `AutGalois F`. The isomorphism
`fundamentalGroupMulEquivAut` composes it with the inversion `g ↦ g⁻¹`, so a family `σ` corresponds
to the automorphism of the fibre functor acting on the fibre of a Galois covering space through the
inverses `σ_{(Y, α)}⁻¹`. The topological isomorphism is obtained from a continuous bijection from
the compact group `Aut F` onto the Hausdorff space `π₁(X, s)`.

Geometric points take values in algebraically closed fields, following the Stacks project; the
source allows separably closed fields.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 0BNC](https://stacks.math.columbia.edu/tag/0BNC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} (s : GeometricPoint X)

/-- **The fundamental group `π₁(X, s)`.** The subgroup of `P(X, s)` of the families
`σ = (σ_{(Y, α)})` such that for every morphism `f : (Z, γ) ⟶ (Y, α)` of pointed Galois covering
spaces, `σ_{(Y, α)}` is a restriction of `σ_{(Z, γ)}` along `f`: `σ_{(Y, α)} ∘ f = f ∘ σ_{(Z, γ)}`.
It carries the subspace topology of `P(X, s)`. -/
@[weil "def_fka1_fundamental_group"]
def fundamentalGroup : Subgroup s.GaloisAutomorphismProduct where
  carrier := {σ | ∀ ⦃P Q : s.PointedGaloisCoveringSpace⦄ (f : P ⟶ Q),
    Aut.IsRestrictionAlong f.hom.1 (σ P) (σ Q)}
  one_mem' _ _ f := Aut.IsRestrictionAlong.one f.hom.1
  mul_mem' hσ hτ _ _ f := (hσ f).mul (hτ f)
  inv_mem' hσ _ _ f := (hσ f).inv

variable {s}

theorem mem_fundamentalGroup_iff (σ : s.GaloisAutomorphismProduct) :
    σ ∈ s.fundamentalGroup ↔ ∀ ⦃P Q : s.PointedGaloisCoveringSpace⦄ (f : P ⟶ Q),
      Aut.IsRestrictionAlong f.hom.1 (σ P) (σ Q) :=
  Iff.rfl

/-- A family `σ ∈ P(X, s)` lies in `π₁(X, s)` if and only if `σ_{(Y, α)} ∘ f = f ∘ σ_{(Z, γ)}`
for every mapping of pointed covering spaces `f : (Z, γ) → (Y, α)` between pointed Galois
covering spaces, as a morphism of schemes. -/
theorem mem_fundamentalGroup_iff_isHom (σ : s.GaloisAutomorphismProduct) :
    σ ∈ s.fundamentalGroup ↔ ∀ (P Q : s.PointedGaloisCoveringSpace)
      (f : P.obj.cover.left ⟶ Q.obj.cover.left), PointedCoveringSpace.IsHom P.obj Q.obj f →
        f ≫ (σ Q).hom.left = (σ P).hom.left ≫ f := by
  constructor
  · intro h P Q f hf
    have := h ((PointedGaloisCoveringSpace.homEquivIsHom P Q).symm ⟨f, hf⟩)
    exact congrArg (fun k ↦ k.left) this
  · intro h P Q f
    exact MorphismProperty.Over.Hom.ext (h P Q f.hom.1.left (PointedCoveringSpace.isHom_left f.hom))

section Connected

variable [ConnectedSpace X]

variable (s) in
/-- **`π₁(X, s)` as compatible families over the pointed Galois objects.** Over a connected base,
`π₁(X, s)` is Mathlib's group `AutGalois` of compatible families of automorphisms of the pointed
Galois objects of `Cov(X)` with the geometric fibre functor at `s`. -/
@[weil "def_fka1_fundamental_group"]
def fundamentalGroupMulEquivAutGalois :
    s.fundamentalGroup ≃* AutGalois (finiteEtaleFiberFintypeFunctor X s) where
  toFun σ := ⟨fun A ↦ σ.1 ((PointedGaloisCoveringSpace.ofPointedGaloisObject s).obj A),
    fun {_ _} f ↦ (Aut.isRestrictionAlong_iff_autMap_eq f.val _ _).1
      (σ.2 ((PointedGaloisCoveringSpace.ofPointedGaloisObject s).map f))⟩
  invFun τ := ⟨fun P ↦ τ.1 ((PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P),
    fun P Q f ↦
      have := (Scheme.CoveringSpace.isGalois_iff_isGalois _).1 P.property
      have := (Scheme.CoveringSpace.isGalois_iff_isGalois _).1 Q.property
      (Aut.isRestrictionAlong_iff_autMap_eq f.hom.1 _ _).2
        (τ.2 ((PointedGaloisCoveringSpace.toPointedGaloisObject s).map f))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem π_fundamentalGroupMulEquivAutGalois (σ : s.fundamentalGroup)
    (A : PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s)) :
    AutGalois.π _ A (fundamentalGroupMulEquivAutGalois s σ) =
      σ.1 ((PointedGaloisCoveringSpace.ofPointedGaloisObject s).obj A) :=
  rfl

theorem fundamentalGroupMulEquivAutGalois_symm_apply_apply
    (τ : AutGalois (finiteEtaleFiberFintypeFunctor X s)) (P : s.PointedGaloisCoveringSpace) :
    ((fundamentalGroupMulEquivAutGalois s).symm τ).1 P =
      AutGalois.π _ ((PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P) τ :=
  rfl

variable (s) in
/-- Over a connected base, `π₁(X, s)` is isomorphic to the automorphism group of the geometric
fibre functor at `s`: a family `σ` goes to the automorphism acting through the `σ_{(Y, α)}⁻¹`. -/
def fundamentalGroupMulEquivAut :
    s.fundamentalGroup ≃* Aut (finiteEtaleFiberFintypeFunctor X s) :=
  (fundamentalGroupMulEquivAutGalois s).trans
    ((MulEquiv.inv' _).trans (autMulEquivAutGalois _).symm)

/-- The automorphism of the fibre functor attached to `σ ∈ π₁(X, s)` acts on the base point `α`
of a pointed Galois covering space `(Y, α)` through the inverse of the component `σ_{(Y, α)}`. -/
theorem fundamentalGroupMulEquivAut_hom_app_point (σ : s.fundamentalGroup)
    (P : s.PointedGaloisCoveringSpace) :
    (fundamentalGroupMulEquivAut s σ).hom.app P.obj.cover P.obj.2 =
      (finiteEtaleFiberFintypeFunctor X s).map (σ.1 P)⁻¹.hom P.obj.2 := by
  have := (Scheme.CoveringSpace.isGalois_iff_isGalois _).1 P.property
  exact autMulEquivAutGalois_symm_app (finiteEtaleFiberFintypeFunctor X s) _ P.obj.cover
    (show (finiteEtaleFiberFintypeFunctor X s).obj P.obj.cover from P.obj.2)

theorem fundamentalGroupMulEquivAut_symm_apply_apply
    (φ : Aut (finiteEtaleFiberFintypeFunctor X s)) (P : s.PointedGaloisCoveringSpace) :
    ((fundamentalGroupMulEquivAut s).symm φ).1 P =
      (AutGalois.π _ ((PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P)
        (autMulEquivAutGalois _ φ).unop)⁻¹ :=
  rfl

/-- The isomorphism from the automorphism group of the fibre functor to `π₁(X, s)` is
continuous. -/
theorem continuous_fundamentalGroupMulEquivAut_symm :
    Continuous (fundamentalGroupMulEquivAut s).symm := by
  let F := finiteEtaleFiberFintypeFunctor X s
  refine continuous_induced_rng.2 ?_
  let _ : ∀ P : s.PointedGaloisCoveringSpace, TopologicalSpace (Aut P.obj.cover) := fun _ ↦ ⊥
  have : ∀ P : s.PointedGaloisCoveringSpace, DiscreteTopology (Aut P.obj.cover) :=
    fun _ ↦ ⟨rfl⟩
  change @Continuous _ (∀ P : s.PointedGaloisCoveringSpace, Aut P.obj.cover) _
    (@Pi.topologicalSpace _ _ fun _ ↦ ⊥) _
  refine continuous_pi fun P ↦ ?_
  let A := (PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P
  let e : Aut F → Aut (F.obj A.obj) := fun φ ↦ autEmbedding F φ A.obj
  let f : Aut F → Aut P.obj.cover := fun φ ↦ ((fundamentalGroupMulEquivAut s).symm φ).1 P
  have he : Continuous e := (continuous_apply _).comp continuous_induced_dom
  have hfac : Function.FactorsThrough f e := by
    intro φ ψ h
    simp only [f, fundamentalGroupMulEquivAut_symm_apply_apply]
    congr 1
    refine evaluation_aut_injective_of_isConnected F A.obj A.pt ?_
    change F.map (AutGalois.π F ⟨A.obj, A.pt, inferInstance⟩ (autMulEquivAutGalois F φ).unop).hom
        A.pt = F.map (AutGalois.π F ⟨A.obj, A.pt, inferInstance⟩
          (autMulEquivAutGalois F ψ).unop).hom A.pt
    rw [autMulEquivAutGalois_π, autMulEquivAutGalois_π]
    exact congrArg (fun i : F.obj A.obj ≅ F.obj A.obj ↦ i.hom A.pt) h
  have hf : f = Function.extend e f 1 ∘ e := funext fun φ ↦ (hfac.extend_apply 1 φ).symm
  change Continuous f
  rw [hf]
  exact continuous_of_discreteTopology.comp he

variable (s) in
/-- Over a connected base, `π₁(X, s)` is isomorphic, as a topological group, to the automorphism
group of the geometric fibre functor at `s`. -/
def fundamentalGroupContinuousMulEquivAut :
    s.fundamentalGroup ≃ₜ* Aut (finiteEtaleFiberFintypeFunctor X s) where
  __ := fundamentalGroupMulEquivAut s
  continuous_toFun :=
    continuous_fundamentalGroupMulEquivAut_symm.continuous_symm_of_equiv_compact_to_t2
      (f := (fundamentalGroupMulEquivAut s).symm.toEquiv)
  continuous_invFun := continuous_fundamentalGroupMulEquivAut_symm

variable (s) in
/-- **`π₁(X, s)` is the étale fundamental group.** Over a connected base, `π₁(X, s)` is
isomorphic, as a topological group, to the étale fundamental group
`AlgebraicGeometry.EtaleFundamentalGroup X s` of the Stacks project (Tag 0BNC). -/
@[weil "def_fka1_fundamental_group"]
def fundamentalGroupContinuousMulEquiv : s.fundamentalGroup ≃ₜ* EtaleFundamentalGroup X s :=
  (fundamentalGroupContinuousMulEquivAut s).trans (autContinuousMulEquivEtaleFundamentalGroup X s)

end Connected


end GeometricPoint

end AlgebraicGeometry

end
