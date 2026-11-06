module

public import Weil.Attr
public import Weil.Defs.Algebra.Category.ModuleCat.Limits
public import Weil.Algebra.Category.ModuleCat.ArLimitFunctorWellDefined
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.ArCategorySheaves
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.StalkSystem

/-!
# The stalk of a projective system of `l`-torsion sheaves

Let `S` be a scheme, `l` a natural number and `s` a geometric point of `S`. For a projective
system `F = (F_n)_{n ∈ ℤ}` of `l`-torsion sheaves on the small étale site of `S` (in particular
an A–R `l`-adic sheaf), its *stalk* at `s` is the projective limit
`F_s = lim_n F_{n,s}` of the system of stalks `F_{•,s}`. For an A–R morphism `φ = [f] : F → G`
represented by `f : F[r] ⟶ G`, the map `φ_s : F_s → G_s` is `(x_n)_n ↦ (f_{n,s}(x_{n+r}))_n`; it
does not depend on the representative, and `F ↦ F_s`, `φ ↦ φ_s` is an additive functor from the
A–R category to abelian groups.

## Main definitions

* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalk s`: the functor
  `F ↦ F_s = lim_n F_{n,s}`, `[f] ↦ [f]_s`, from the A–R category of projective systems of
  `l`-torsion sheaves to `ℤ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalk_obj`: `F_s` is the module of
  families `(x_n) ∈ ∏_n F_{n,s}` compatible with the transition maps.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalk_map_homMk_apply`: for
  `f : F[r] ⟶ G`, `[f]_s` sends `(x_n)_n` to `(f_{n,s}(x_{n+r}))_n`.
* The functor `stalk s` is additive (instance).

## Implementation notes

The stalk is the composite of the functor of systems of stalks
`AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalkSystem s` and the projective-limit
functor `CategoryTheory.ProjectiveSystem.ArCategory.limFunctor` of the A–R category of
projective systems of `l`-power torsion modules; its well-definedness on A–R classes is that of
the projective-limit functor. The sheaves are abelian sheaves, so the stalk is a `ℤ`-module; an
`l`-adic limit of `l`-power torsion abelian groups is the same thing as a `ℤ_l`-module (Freitag
and Kiehl's coefficient ring). For `l`-adic sheaves in the sense of strict systems of
`ℤ/l^{n+1}`-module sheaves, the Stacks project's stalk is
`Stacks.EtaleCohomology.LAdicSheaf.stalk`, defined by the same projective limit.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
* [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

/-- **The stalk of a projective system of `l`-torsion sheaves** at a geometric point `s`: the
functor from the A–R category sending `F` to `F_s = lim_n F_{n,s}` (`stalk_obj`), and the A–R
morphism `[f]` represented by `f : F[r] ⟶ G` to `(x_n)_n ↦ (f_{n,s}(x_{n+r}))_n`
(`stalk_map_homMk_apply`). -/
@[weil "def_fk112_l_adic_stalk"]
def stalk (s : GeometricPoint S) : ArLTorsionProjectiveSystem.{u} B S hS l ⥤ ModuleCat.{u} ℤ :=
  stalkSystem s ⋙ CategoryTheory.ProjectiveSystem.ArCategory.limFunctor

/-- The stalk `F_s` is the module of families `(x_n) ∈ ∏_n F_{n,s}` compatible with the transition
maps of the system of stalks `F_{•,s}`. -/
@[weil "def_fk112_l_adic_stalk"]
lemma stalk_obj (s : GeometricPoint S) (F : ArLTorsionProjectiveSystem.{u} B S hS l) :
    (stalk s).obj F = ModuleCat.of ℤ (ModuleCat.sectionsSubmodule
      (F.obj.obj ⋙ sheafFiberInt B S hS s)) :=
  rfl

/-- For an A–R morphism `[f] : F → G` represented by `f : F[r] ⟶ G`, the map of stalks sends
`(x_n)_n` to `(f_{n,s}(x_{n+r}))_n`. -/
@[weil "def_fk112_l_adic_stalk"]
lemma stalk_map_homMk_apply (s : GeometricPoint S) {F G : LTorsionProjectiveSystem.{u} B S hS l}
    (r : ℕ) (f : (LTorsionProjectiveSystem.shift B S hS l (r : ℤ)).obj F ⟶ G)
    (x : (stalk s).obj (of F)) (n : ℤ) :
    (((stalk s).map (homMk r f)).hom x).1 (op n) =
      ((sheafFiberInt B S hS s).map (f.hom.app (op n))).hom (x.1 (op (n + r))) :=
  rfl

/-- Taking stalks is additive. -/
instance (s : GeometricPoint S) : (stalk (B := B) (hS := hS) (l := l) s).Additive :=
  inferInstanceAs (stalkSystem s ⋙ CategoryTheory.ProjectiveSystem.ArCategory.limFunctor).Additive

end AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem
