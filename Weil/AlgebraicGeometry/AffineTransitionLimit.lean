module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import Weil.Defs.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange

/-!
# The induced system of a projective system of schemes

Let `X = lim Dᵢ` be a projective system of schemes with limit, `i₀` an index and
`g : Y ⟶ D.obj i₀` a morphism of finite type with `Y` separated. The base changes
`Y_a = D.obj a.left ×_{D.obj i₀} Y` (`a : j ⟶ i₀`), with the base-changed transition morphisms,
form again a projective system of schemes with limit `X ×_{D.obj i₀} Y`.

## Main results

- `AlgebraicGeometry.IsProjectiveSystemWithLimit.inducedProjectiveSystem`: the induced system
  and its cone form a projective system of schemes with limit.

## Implementation notes

The condition on sections is not checked by hand on affine covers: the induced cone is a limit
cone (`AlgebraicGeometry.isLimitInducedProjectiveSystemCone`), and a limit cone of a cofiltered
system with affine transition maps satisfies it
(`AlgebraicGeometry.IsProjectiveSystemWithLimit.of_isLimit`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- The projective system induced by a morphism of finite type `g : Y ⟶ D.obj i` with separated
source is a projective system of schemes with limit `c.pt ×_{D.obj i} Y`. -/
@[weil "lem_fk104_induced_system_is_projective_system"]
theorem IsProjectiveSystemWithLimit.inducedProjectiveSystem (h : IsProjectiveSystemWithLimit D c)
    (i : I) {Y : Scheme.{u}} (g : Y ⟶ D.obj i) [LocallyOfFiniteType g] [QuasiCompact g]
    [Y.IsSeparated] :
    IsProjectiveSystemWithLimit (AlgebraicGeometry.inducedProjectiveSystem D i g)
      (inducedProjectiveSystemCone D c i g) := by
  have := h.isCofiltered
  have : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f) := fun f ↦ h.isAffineHom_map f
  have := h.isNoetherian_obj
  have := h.isSeparated_obj
  have := h.isNoetherian_pt
  have := h.isSeparated_pt
  have hc := (h.nonempty_isLimit).some
  have : ∀ {a b : Over i} (f : a ⟶ b),
      IsAffineHom ((AlgebraicGeometry.inducedProjectiveSystem D i g).map f) := fun f ↦
    MorphismProperty.of_isPullback (isPullback_inducedProjectiveSystem_map D i g f).flip
      inferInstance
  have : ∀ a : Over i, IsNoetherian ((AlgebraicGeometry.inducedProjectiveSystem D i g).obj a) :=
    fun a ↦ by
      dsimp only [inducedProjectiveSystem_obj]
      have : CompactSpace ↥(pullback (D.map a.hom) g) :=
        QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map a.hom) g)
      exact ⟨⟩
  have : ∀ a : Over i,
      ((AlgebraicGeometry.inducedProjectiveSystem D i g).obj a).IsSeparated := fun a ↦ by
    dsimp only [inducedProjectiveSystem_obj]
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst (D.map a.hom) g)]
    infer_instance
  have : IsNoetherian (((Functor.const I).obj c.pt).obj i) := h.isNoetherian_pt
  have : (((Functor.const I).obj c.pt).obj i).IsSeparated := h.isSeparated_pt
  have : IsNoetherian (inducedProjectiveSystemCone D c i g).pt := by
    dsimp only [inducedProjectiveSystemCone_pt]
    have : CompactSpace ↥(pullback (c.π.app i) g) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst (c.π.app i) g)
    exact ⟨⟩
  have : (inducedProjectiveSystemCone D c i g).pt.IsSeparated := by
    dsimp only [inducedProjectiveSystemCone_pt]
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst (c.π.app i) g)]
    infer_instance
  exact .of_isLimit (isLimitInducedProjectiveSystemCone i g hc)

end AlgebraicGeometry
