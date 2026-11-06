module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange

/-!
# The projective system induced by a morphism to a stage

Let `D : I ⥤ Scheme` be a projective system of schemes with a cone `c` (in the applications a
limit cone, `X = lim Dᵢ`), let `i₀` be an index and `g : Y ⟶ D.obj i₀` a morphism of schemes.
The *induced system* is indexed by the later stages `j ⟶ i₀` (the category `Over i₀`). Its
stage at `a : j ⟶ i₀` is the base change `Y_a = D.obj j ×_{D.obj i₀} Y`, its apex is
`c.pt ×_{D.obj i₀} Y`, its transition morphisms and its cone legs are the base changes of the
transition morphisms of `D` and of the legs of `c`, and the first projections
`g_a : Y_a ⟶ D.obj j` and `c.pt ×_{D.obj i₀} Y ⟶ c.pt` form a morphism to the system `D`
(restricted to the later stages) and its cone.

The diagram and its cone are the base-change diagram and cone of Stacks Project, Tag 01ZM, as
built in `AlgebraicGeometry.baseChangeDiagram` and `AlgebraicGeometry.baseChangeCone`; this file
adds the projections `g_a` and `g` and the facts that every square of the induced system is a
pullback square over the corresponding square of the original system.

## Main definitions

- `AlgebraicGeometry.inducedProjectiveSystem D i₀ g`: the diagram `a ↦ D.obj a.left ×_{D.obj i₀} Y`
  indexed by `Over i₀`.
- `AlgebraicGeometry.inducedProjectiveSystemCone c i₀ g`: its cone with apex `c.pt ×_{D.obj i₀} Y`.
- `AlgebraicGeometry.inducedProjectiveSystemProjection D i₀ g`: the projections
  `g_a : Y_a ⟶ D.obj a.left`, a natural transformation to `Over.forget i₀ ⋙ D`.
- `AlgebraicGeometry.inducedProjectiveSystemConeProjection c i₀ g`: the projection
  `c.pt ×_{D.obj i₀} Y ⟶ c.pt`.

## Main results

- `AlgebraicGeometry.isPullback_inducedProjectiveSystem_map`: each transition morphism
  `Y_a ⟶ Y_b` is the base change of `D.map (a.left ⟶ b.left)` along `g_b`.
- `AlgebraicGeometry.isPullback_inducedProjectiveSystemCone_π_app`: each leg
  `c.pt ×_{D.obj i₀} Y ⟶ Y_a` is the base change of the leg `c.π.app a.left` along `g_a`.
- `AlgebraicGeometry.inducedProjectiveSystemCone_π_app_comp_projection`: the projections commute
  with the cone legs.
- `AlgebraicGeometry.isLimitInducedProjectiveSystemCone`: for a cofiltered limit cone `c`, the
  induced cone is a limit cone.

## Implementation notes

The index set `{α ∈ I : α ≥ α₀}` of a directed set is the category `Over i₀` of a cofiltered
index category. The fibre products are written `D.obj a.left ×_{D.obj i₀} Y`, with the stage of
`D` as first factor, following `AlgebraicGeometry.baseChangeDiagram`. No hypothesis (finite
type, noetherian, separated) is needed to build the system; they are carried by the results
that use it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks] Stacks Project, Tag 01ZM.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

section

variable {I : Type v} [Category.{w} I]

/-- The square comparing two base changes of `X` along `h : T' ⟶ T` over `S`: the morphism
`T' ×_S X ⟶ T ×_S X` is the base change of `h` along the first projection `T ×_S X ⟶ T`. -/
lemma isPullback_baseChangeTransition_fst {S T T' : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ S)
    (h : T' ⟶ T) (hg : h ≫ g = g') (X : Over S) :
    IsPullback (baseChangeTransition g g' h hg X) (pullback.fst g' X.hom) (pullback.fst g X.hom)
      h := by
  subst hg
  refine IsPullback.of_right (h₁₂ := pullback.snd g X.hom) (v₁₃ := X.hom) (h₂₂ := g) ?_
    (baseChangeTransition_fst g (h ≫ g) h rfl X) (IsPullback.of_hasPullback g X.hom).flip
  rw [baseChangeTransition_snd]
  exact (IsPullback.of_hasPullback (h ≫ g) X.hom).flip

variable (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {Y : Scheme.{u}} (g : Y ⟶ D.obj i)

/-- The projective system induced by a morphism `g : Y ⟶ D.obj i` to a stage: indexed by the
later stages `a : j ⟶ i`, it sends `a` to `D.obj j ×_{D.obj i} Y`, and its transition morphisms
are the base changes of those of `D`. -/
@[weil "def_fk104_induced_projective_system_of_schemes"]
noncomputable abbrev inducedProjectiveSystem : Over i ⥤ Scheme.{u} :=
  baseChangeDiagram D i (Over.mk g)

/-- The cone of the induced projective system: its apex is `c.pt ×_{D.obj i} Y` and its legs are
the base changes of the legs of `c`. -/
@[weil "def_fk104_induced_projective_system_of_schemes"]
noncomputable abbrev inducedProjectiveSystemCone : Cone (inducedProjectiveSystem D i g) :=
  baseChangeCone D c i (Over.mk g)

/-- The projections `g_a : D.obj a.left ×_{D.obj i} Y ⟶ D.obj a.left` from the induced system to
the original system restricted to the later stages. -/
@[weil "def_fk104_induced_projective_system_of_schemes"]
noncomputable def inducedProjectiveSystemProjection :
    inducedProjectiveSystem D i g ⟶ Over.forget i ⋙ D where
  app a := pullback.fst (D.map a.hom) g
  naturality a b f :=
    baseChangeTransition_fst (D.map b.hom) (D.map a.hom) (D.map f.left)
      (by rw [← D.map_comp, Over.w f]) (Over.mk g)

/-- The projection `c.pt ×_{D.obj i} Y ⟶ c.pt` from the apex of the induced cone. -/
@[weil "def_fk104_induced_projective_system_of_schemes"]
noncomputable def inducedProjectiveSystemConeProjection :
    (inducedProjectiveSystemCone D c i g).pt ⟶ c.pt :=
  pullback.fst (c.π.app i) g

@[simp]
lemma inducedProjectiveSystem_obj (a : Over i) :
    (inducedProjectiveSystem D i g).obj a = pullback (D.map a.hom) g :=
  rfl

lemma inducedProjectiveSystem_map {a b : Over i} (f : a ⟶ b) :
    (inducedProjectiveSystem D i g).map f =
      baseChangeTransition (D.map b.hom) (D.map a.hom) (D.map f.left)
        (by rw [← D.map_comp, Over.w f]) (Over.mk g) :=
  rfl

@[simp]
lemma inducedProjectiveSystemCone_pt :
    (inducedProjectiveSystemCone D c i g).pt = pullback (c.π.app i) g :=
  rfl

lemma inducedProjectiveSystemCone_π_app (a : Over i) :
    (inducedProjectiveSystemCone D c i g).π.app a =
      baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) (Over.mk g) :=
  rfl

@[simp]
lemma inducedProjectiveSystemProjection_app (a : Over i) :
    (inducedProjectiveSystemProjection D i g).app a = pullback.fst (D.map a.hom) g :=
  rfl

@[simp]
lemma inducedProjectiveSystemConeProjection_eq :
    inducedProjectiveSystemConeProjection D c i g = pullback.fst (c.π.app i) g :=
  rfl

/-- The transition morphism `Y_a ⟶ Y_b` of the induced system is the base change of the
transition morphism `D.obj a.left ⟶ D.obj b.left` along the projection `g_b`. -/
lemma isPullback_inducedProjectiveSystem_map {a b : Over i} (f : a ⟶ b) :
    IsPullback ((inducedProjectiveSystem D i g).map f)
      ((inducedProjectiveSystemProjection D i g).app a)
      ((inducedProjectiveSystemProjection D i g).app b) (D.map f.left) :=
  isPullback_baseChangeTransition_fst _ _ _ (Over.w ((Over.post D).map f)) _

/-- The leg `c.pt ×_{D.obj i} Y ⟶ Y_a` of the induced cone is the base change of the leg
`c.π.app a.left` along the projection `g_a`. -/
lemma isPullback_inducedProjectiveSystemCone_π_app (a : Over i) :
    IsPullback ((inducedProjectiveSystemCone D c i g).π.app a)
      (inducedProjectiveSystemConeProjection D c i g)
      ((inducedProjectiveSystemProjection D i g).app a) (c.π.app a.left) :=
  isPullback_baseChangeTransition_fst _ _ _ (Over.w (((Over.conePost D i).obj c).π.app a)) _

/-- The projections commute with the legs of the cones. -/
@[reassoc]
lemma inducedProjectiveSystemCone_π_app_comp_projection (a : Over i) :
    (inducedProjectiveSystemCone D c i g).π.app a ≫
        (inducedProjectiveSystemProjection D i g).app a =
      inducedProjectiveSystemConeProjection D c i g ≫ c.π.app a.left :=
  (isPullback_inducedProjectiveSystemCone_π_app D c i g a).w

/-- The second projections `Y_a ⟶ Y` are compatible with the transition morphisms. -/
@[reassoc (attr := simp)]
lemma inducedProjectiveSystem_map_snd {a b : Over i} (f : a ⟶ b) :
    (inducedProjectiveSystem D i g).map f ≫ pullback.snd (D.map b.hom) g =
      pullback.snd (D.map a.hom) g :=
  baseChangeTransition_snd _ _ _ (Over.w ((Over.post D).map f)) _

variable {D c} in
/-- For a limit cone `c` of a cofiltered system, the induced cone is a limit cone:
`c.pt ×_{D.obj i} Y = lim_a (D.obj a.left ×_{D.obj i} Y)`. -/
noncomputable def isLimitInducedProjectiveSystemCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (inducedProjectiveSystemCone D c i g) :=
  baseChangeConeIsLimit D hc i (Over.mk g)

end

end AlgebraicGeometry
