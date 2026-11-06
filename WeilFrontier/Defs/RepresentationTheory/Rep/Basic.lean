module

public import Weil.Attr
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Finitely generated `ℤ_l`-modules with a continuous action of a profinite group

Let `π` be a profinite group and `l` a prime. The category `Mod^cont_{ℤ_l}(π)` has as objects
the finitely generated `ℤ_l`-modules `M` with a `ℤ_l`-linear action of `π` such that the action
map `π × M → M` is continuous for the topology of `π` and the `l`-adic topology on `M`; its
morphisms are the `π`-equivariant `ℤ_l`-linear maps.

We realise it as a full subcategory of the category `Rep ℤ_[l] π` of `ℤ_l`-linear
representations of `π`, whose morphisms are exactly the equivariant linear maps.

## Main definitions

* `Rep.IsContinuousAdic I`: the property of a `k`-linear representation of a topological monoid
  `G` that the action map `G × V → V` is continuous for the `I`-adic topology on `V`.
* `ContinuousZlModule.isContinuousZlModule l π`: the property of an object of `Rep ℤ_[l] π` of
  being finitely generated over `ℤ_[l]` with continuous action for the `l`-adic topology.
* `ContinuousZlModule l π`: the category `Mod^cont_{ℤ_l}(π)`.
* `ContinuousZlModule.of`: the object attached to a finitely generated `ℤ_[l]`-module with a
  continuous representation.
* `ContinuousZlModule.homMk`: the morphism attached to an equivariant linear map.

## Main results

* `Ideal.hasBasis_nhds_zero_adicModuleTopology`: the submodules `I ^ n • ⊤` form a basis of
  neighbourhoods of `0` for the `I`-adic topology on a module.
* `LinearMap.continuous_adicModuleTopology`: linear maps are continuous for the `I`-adic
  topologies.
* `Rep.IsContinuousAdic.isClosedUnderIsomorphisms`, and the same for
  `ContinuousZlModule.isContinuousZlModule`: the defining properties are invariant under
  isomorphism of representations.

## Implementation notes

The group `π` is only required to be a monoid with a topology; the case of a profinite group
(for instance a fundamental group `π₁(X, s)`) is a special case.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I.
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory Filter Topology

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The submodules `I ^ n • ⊤` form a basis of neighbourhoods of `0` for the `I`-adic topology
on `M`. -/
theorem hasBasis_nhds_zero_adicModuleTopology :
    HasBasis (@nhds M (I.adicModuleTopology M) 0) (fun _ : ℕ => True)
      fun n => ((I ^ n • ⊤ : Submodule R M) : Set M) := by
  let _ := I.adicTopology
  have h := (I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis M)).toAddGroupFilterBasis.nhds_zero_hasBasis
  refine ⟨fun t => ?_⟩
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, ⟨n, rfl⟩, hV⟩
    exact ⟨n, trivial, hV⟩
  · rintro ⟨n, -, hn⟩
    exact ⟨_, ⟨n, rfl⟩, hn⟩

/-- A module with its `I`-adic topology is a topological additive group. -/
theorem isTopologicalAddGroup_adicModuleTopology :
    @IsTopologicalAddGroup M (I.adicModuleTopology M) _ :=
  let _ := I.adicTopology
  AddGroupFilterBasis.isTopologicalAddGroup
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis

end Ideal

namespace LinearMap

variable {R : Type u} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A linear map is continuous for the `I`-adic topologies on source and target. -/
theorem continuous_adicModuleTopology (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let _ := I.adicModuleTopology M
  let _ := I.adicModuleTopology N
  have := I.isTopologicalAddGroup_adicModuleTopology M
  have := I.isTopologicalAddGroup_adicModuleTopology N
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((I.hasBasis_nhds_zero_adicModuleTopology M).tendsto_iff
    (I.hasBasis_nhds_zero_adicModuleTopology N)).2 fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  have : (I ^ n • ⊤ : Submodule R M).map f ≤ I ^ n • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨x, hx, rfl⟩

end LinearMap

namespace Rep

variable {k : Type u} [CommRing k] (I : Ideal k) {G : Type v} [Monoid G] [TopologicalSpace G]

/-- The property of a representation `A` of a topological monoid `G` that the action map
`G × A → A`, `(g, a) ↦ g • a`, is continuous for the `I`-adic topology on `A`. -/
def IsContinuousAdic : ObjectProperty (Rep.{w} k G) := fun A =>
  @Continuous (G × A.V) A.V (@instTopologicalSpaceProd _ _ _ (I.adicModuleTopology A.V))
    (I.adicModuleTopology A.V) fun p => A.ρ p.1 p.2

variable {I} in
theorem isContinuousAdic_iff (A : Rep.{w} k G) :
    IsContinuousAdic I A ↔
      @Continuous (G × A.V) A.V (@instTopologicalSpaceProd _ _ _ (I.adicModuleTopology A.V))
        (I.adicModuleTopology A.V) fun p => A.ρ p.1 p.2 :=
  Iff.rfl

instance IsContinuousAdic.isClosedUnderIsomorphisms :
    (IsContinuousAdic.{w} I (G := G)).IsClosedUnderIsomorphisms where
  of_iso {A B} e hA := by
    let _ := I.adicModuleTopology A.V
    let _ := I.adicModuleTopology B.V
    have hf : Continuous e.hom.hom := e.hom.hom.toLinearMap.continuous_adicModuleTopology I
    have hg : Continuous e.inv.hom := e.inv.hom.toLinearMap.continuous_adicModuleTopology I
    have hA' : Continuous fun p : G × A.V => A.ρ p.1 p.2 := hA
    have key : (fun p : G × B.V => B.ρ p.1 p.2) =
        fun p => e.hom.hom (A.ρ p.1 (e.inv.hom p.2)) := by
      funext p
      rw [Representation.IntertwiningMap.isIntertwining]
      congr 1
      rw [← Rep.comp_apply, e.inv_hom_id, Rep.id_apply]
    change Continuous fun p : G × B.V => B.ρ p.1 p.2
    rw [key]
    exact hf.comp (hA'.comp (continuous_fst.prodMk (hg.comp continuous_snd)))

end Rep

namespace ContinuousZlModule

variable (l : ℕ) [Fact l.Prime] (π : Type v) [Monoid π] [TopologicalSpace π]

/-- The property of a `ℤ_[l]`-linear representation `A` of `π` of being an object of
`Mod^cont_{ℤ_l}(π)`: `A` is finitely generated over `ℤ_[l]` and the action map `π × A → A` is
continuous for the `l`-adic topology on `A`. -/
def isContinuousZlModule : ObjectProperty (Rep.{w} ℤ_[l] π) := fun A =>
  Module.Finite ℤ_[l] A.V ∧ Rep.IsContinuousAdic (Ideal.span {(l : ℤ_[l])}) A

instance isContinuousZlModule.isClosedUnderIsomorphisms :
    (isContinuousZlModule.{w} l π).IsClosedUnderIsomorphisms where
  of_iso {A B} e hA :=
    have := hA.1
    ⟨Module.Finite.of_surjective e.hom.hom.toLinearMap fun b =>
        ⟨e.inv.hom b, by
          change (e.inv ≫ e.hom) b = b
          rw [e.inv_hom_id, Rep.id_apply]⟩,
      (Rep.IsContinuousAdic _).prop_of_iso e hA.2⟩

end ContinuousZlModule

/-- The category `Mod^cont_{ℤ_l}(π)` of finitely generated `ℤ_l`-modules with a `ℤ_l`-linear
action of `π` whose action map `π × M → M` is continuous for the `l`-adic topology on `M`;
morphisms are the `π`-equivariant `ℤ_l`-linear maps. -/
@[weil "def_fka1_continuous_zl_pi1_module"]
abbrev ContinuousZlModule (l : ℕ) [Fact l.Prime] (π : Type v) [Monoid π] [TopologicalSpace π] :=
  (ContinuousZlModule.isContinuousZlModule.{w} l π).FullSubcategory

namespace ContinuousZlModule

variable {l : ℕ} [Fact l.Prime] {π : Type v} [Monoid π] [TopologicalSpace π]

theorem mem_isContinuousZlModule_iff (A : Rep.{w} ℤ_[l] π) :
    isContinuousZlModule l π A ↔
      Module.Finite ℤ_[l] A.V ∧
        @Continuous (π × A.V) A.V
          (@instTopologicalSpaceProd _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology A.V))
          ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology A.V) fun p => A.ρ p.1 p.2 :=
  Iff.rfl

/-- The object of `Mod^cont_{ℤ_l}(π)` attached to a finitely generated `ℤ_[l]`-module `M` with
a representation `ρ` of `π` whose action map is continuous for the `l`-adic topology. -/
abbrev of {M : Type w} [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (ρ : Representation ℤ_[l] π M)
    (hρ : @Continuous (π × M) M
      (@instTopologicalSpaceProd _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology M))
      ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology M) fun p => ρ p.1 p.2) :
    ContinuousZlModule.{w} l π :=
  ⟨Rep.of ρ, ‹Module.Finite ℤ_[l] M›, hρ⟩

instance (A : ContinuousZlModule.{w} l π) : Module.Finite ℤ_[l] A.obj.V := A.property.1

/-- The morphism of `Mod^cont_{ℤ_l}(π)` attached to a `π`-equivariant `ℤ_[l]`-linear map. -/
abbrev homMk {A B : ContinuousZlModule.{w} l π} (f : A.obj.ρ.IntertwiningMap B.obj.ρ) :
    A ⟶ B :=
  ObjectProperty.homMk (ConcreteCategory.ofHom (C := Rep.{w} ℤ_[l] π) f)

@[simp]
theorem homMk_hom_hom {A B : ContinuousZlModule.{w} l π} (f : A.obj.ρ.IntertwiningMap B.obj.ρ) :
    (homMk f).hom.hom = f :=
  rfl

@[ext]
theorem hom_ext {A B : ContinuousZlModule.{w} l π} {f g : A ⟶ B} (h : f.hom.hom = g.hom.hom) :
    f = g :=
  ObjectProperty.hom_ext _ (Rep.hom_ext h)

end ContinuousZlModule
