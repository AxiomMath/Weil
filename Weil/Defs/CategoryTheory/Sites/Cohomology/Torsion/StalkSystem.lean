module

public import Weil.Defs.CategoryTheory.ObjectProperty.ArCategory
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.ArCategorySheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectAcyclic
public import Weil.Attr

/-!
# The projective system of stalks

Let `S` be a scheme, `l` a natural number and `s` a geometric point of `S`. For a projective
system `F = (F_n, u_n)_{n ∈ ℤ}` of `l`-torsion sheaves on the small étale site of `S`, the
*system of stalks* `F_{•,s} = (F_{n,s}, (u_n)_s)_{n ∈ ℤ}` is the projective system of the stalks
of the `F_n` at `s`. The stalk of an `l`-torsion sheaf is an `l`-power torsion abelian group,
since a germ is represented by a local section killed by some `l ^ v`; and `F_{n,s} = 0` when
`F_n = 0`. So `F_{•,s}` is a projective system of `l`-power torsion `ℤ`-modules, and a morphism
`f = (f_n)_n` of systems induces `f_s = (f_{n,s})_n`.

Taking stalks commutes with the shifts, `(F[r])_{•,s} = F_{•,s}[r]`, and with the natural maps
`ε_r`, so an A–R morphism `[f]` represented by `f : F[r] ⟶ G` induces the A–R morphism
`[f]_s = [f_s]`; this is well defined and functorial.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafFiberInt B S hS s`: the stalk at `s` of an abelian sheaf,
  read as a `ℤ`-module.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.stalkSystem s`: the functor
  `F ↦ F_{•,s}` from projective systems of `l`-torsion sheaves to projective systems of `l`-power
  torsion `ℤ`-modules.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalkSystemShiftHom s f`: for
  `f : F[r] ⟶ G`, the morphism `f_s : F_{•,s}[r] ⟶ G_{•,s}`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalkSystem s`: the induced functor
  `[f] ↦ [f_s]` between the A–R categories.

## Main results

* `AlgebraicGeometry.SmallEtale.isTorsion'_sheafFiberInt_obj`: the stalk of an `l`-torsion
  sheaf is `l`-power torsion.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.stalkSystem_map_app`:
  `(f_s)_n = f_{n,s}`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.stalkSystem_obj_shift`,
  `stalkSystem_map_shiftMap`, `stalkSystem_map_shiftι`, `stalkSystem_map_shiftShift`: taking
  stalks commutes with shifts and with the natural maps of shifted systems.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.stalkSystem_map_homMk`:
  `[r, f]_s = [r, f_s]`.
* The functors `sheafFiberInt B S hS s`, `LTorsionProjectiveSystem.stalkSystem s` and
  `ArLTorsionProjectiveSystem.stalkSystem s` are additive (instances).

## Implementation notes

The stalk is the fiber functor of the point of the small étale site attached to the geometric
point `s` (`AlgebraicGeometry.geometricPointSitePoint`), whose geometric points are over
algebraically closed fields. The sheaves are abelian sheaves, so the stalks are abelian groups;
they are read as `ℤ`-modules, and the target is the category of projective systems of `l`-power
torsion `ℤ`-modules. Freitag and Kiehl's coefficient ring is `ℤ_l`; an `l`-power torsion abelian
group is the same thing as an `l`-power torsion `ℤ_l`-module.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

variable (B S hS) in
/-- The stalk at a geometric point `s` of an abelian sheaf on the small étale site of `S`, read as
a `ℤ`-module. -/
abbrev sheafFiberInt (s : GeometricPoint S) :
    Sheaf (topology B S hS) AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ :=
  (geometricPointSitePoint B S hS s).sheafFiber ⋙ Stacks.InjectiveAcyclic.ofAb.{u}

instance (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := AddCommGrpCat.{u})).Additive :=
  Functor.additive_of_preserves_binary_products _

instance : Stacks.InjectiveAcyclic.ofAb.{u}.Additive where
  map_add := rfl

/-- Taking stalks of abelian sheaves is additive. -/
instance (s : GeometricPoint S) : (sheafFiberInt B S hS s).Additive :=
  inferInstanceAs ((geometricPointSitePoint B S hS s).sheafFiber ⋙
    Stacks.InjectiveAcyclic.ofAb.{u}).Additive

/-- **The stalk of an `l`-torsion sheaf is `l`-power torsion**: a germ is represented by a local
section, which is killed by a power of `l` after restriction to a smaller neighbourhood. -/
theorem isTorsion'_sheafFiberInt_obj (s : GeometricPoint S)
    {F : Sheaf (topology B S hS) AddCommGrpCat.{u}} (hF : IsLTorsionSheaf.{u} B S hS l F) :
    Module.IsTorsion' ((sheafFiberInt B S hS s).obj F) (Submonoid.powers (l : ℤ)) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ :=
    (geometricPointSitePoint B S hS s).toPresheafFiber_jointly_surjective (P := F.obj) p
  obtain ⟨R, hR, hkill⟩ := hF X z
  obtain ⟨Y, f, hf, y, rfl⟩ := (geometricPointSitePoint B S hS s).jointly_surjective R hR x
  obtain ⟨v, hv⟩ := hkill Y f hf
  refine ⟨⟨(l : ℤ) ^ v, v, rfl⟩, ?_⟩
  change ((l : ℤ) ^ v) • (geometricPointSitePoint B S hS s).toPresheafFiber X _ F.obj z = 0
  rw [← GrothendieckTopology.Point.toPresheafFiber_w_apply, ← Nat.cast_pow, natCast_zsmul,
    ← map_nsmul, hv, map_zero]

namespace LTorsionProjectiveSystem

/-- The system of stalks of a projective system of `l`-torsion sheaves is a projective system of
`l`-power torsion `ℤ`-modules. -/
theorem isTorsionBounded_comp_sheafFiberInt (s : GeometricPoint S)
    (F : LTorsionProjectiveSystem.{u} B S hS l) :
    CategoryTheory.ProjectiveSystem.isTorsionBounded.{u} ℤ (l : ℤ)
      (F.obj ⋙ sheafFiberInt B S hS s) := by
  obtain ⟨n₀, hn₀⟩ := F.exists_isZero_obj
  exact ⟨fun n ↦ isTorsion'_sheafFiberInt_obj s (F.isLTorsionSheaf_obj n),
    n₀ - 1, fun n hn ↦ (sheafFiberInt B S hS s).map_isZero (hn₀ n (by omega))⟩

/-- **The projective system of stalks.** For a geometric point `s`, the functor sending a
projective system `F = (F_n, u_n)_n` of `l`-torsion sheaves to the projective system
`F_{•,s} = (F_{n,s}, (u_n)_s)_n` of its stalks, an `l`-power torsion `ℤ`-module in each degree,
and a morphism `f = (f_n)_n` to `f_s = (f_{n,s})_n` (`stalkSystem_map_app`). -/
@[weil "def_fk112_stalk_system"]
def stalkSystem (s : GeometricPoint S) :
    LTorsionProjectiveSystem.{u} B S hS l ⥤ CategoryTheory.ProjectiveSystem.{u} ℤ (l : ℤ) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringRight _ _ _).obj (sheafFiberInt B S hS s))
    (isTorsionBounded_comp_sheafFiberInt s)

variable (s : GeometricPoint S)

@[simp]
lemma stalkSystem_obj_obj (F : LTorsionProjectiveSystem.{u} B S hS l) :
    ((stalkSystem s).obj F).obj = F.obj ⋙ sheafFiberInt B S hS s :=
  rfl

/-- The `n`-th term of `F_{•,s}` is the stalk `F_{n,s}`. -/
lemma stalkSystem_obj_term (F : LTorsionProjectiveSystem.{u} B S hS l) (n : ℤ) :
    ((stalkSystem s).obj F).term n = (sheafFiberInt B S hS s).obj (F.obj.obj (op n)) :=
  rfl

/-- The transition map of `F_{•,s}` is the stalk `(u_n)_s` of the transition map of `F`. -/
lemma stalkSystem_obj_transition (F : LTorsionProjectiveSystem.{u} B S hS l) (n : ℤ) :
    ((stalkSystem s).obj F).transition n = (sheafFiberInt B S hS s).map (F.transition n) :=
  rfl

/-- The `n`-th component of `f_s` is the stalk `f_{n,s}` of `f_n`. -/
@[weil "def_fk112_stalk_system", simp]
lemma stalkSystem_map_app {F G : LTorsionProjectiveSystem.{u} B S hS l} (f : F ⟶ G) (n : ℤ) :
    CategoryTheory.ProjectiveSystem.app ((stalkSystem s).map f) n =
      (sheafFiberInt B S hS s).map (f.hom.app (op n)) :=
  rfl

/-- Taking stalks commutes with shifts: `(F[r])_{•,s} = F_{•,s}[r]`. -/
lemma stalkSystem_obj_shift (r : ℤ) (F : LTorsionProjectiveSystem.{u} B S hS l) :
    (stalkSystem s).obj ((shift B S hS l r).obj F) =
      (CategoryTheory.ProjectiveSystem.shift r).obj ((stalkSystem s).obj F) :=
  rfl

instance (s : GeometricPoint S) :
    (stalkSystem (B := B) (hS := hS) (l := l) s).Additive where
  map_add := CategoryTheory.ProjectiveSystem.hom_ext fun _ ↦ by
    exact (sheafFiberInt B S hS s).map_add

/-- `(f[r])_s = f_s[r]`. -/
lemma stalkSystem_map_shift_map (r : ℤ) {F G : LTorsionProjectiveSystem.{u} B S hS l}
    (f : F ⟶ G) :
    (stalkSystem s).map ((shift B S hS l r).map f) =
      (CategoryTheory.ProjectiveSystem.shift r).map ((stalkSystem s).map f) :=
  rfl

/-- `(ε_r^F)_s = ε_r^{F_{•,s}}`. -/
lemma stalkSystem_map_shiftι (r : ℕ) (F : LTorsionProjectiveSystem.{u} B S hS l) :
    (stalkSystem s).map ((shiftι B S hS l r).app F) =
      CategoryTheory.ProjectiveSystem.natMap ((stalkSystem s).obj F) r :=
  rfl

/-- Taking stalks commutes with the maps `F[t] ⟶ F[r]` for `r ≤ t`. -/
lemma stalkSystem_map_shiftMap (F : LTorsionProjectiveSystem.{u} B S hS l) {r t : ℕ}
    (h : r ≤ t) :
    (stalkSystem s).map (shiftMap F h) =
      CategoryTheory.ProjectiveSystem.shiftMap ((stalkSystem s).obj F) h :=
  rfl

/-- Taking stalks commutes with the identifications `F[r + s] ⟶ F[r][s]`. -/
lemma stalkSystem_map_shiftShift (F : LTorsionProjectiveSystem.{u} B S hS l) (r t : ℕ) :
    (stalkSystem s).map (shiftShift F r t) =
      CategoryTheory.ProjectiveSystem.shiftShift ((stalkSystem s).obj F) r t :=
  rfl

end LTorsionProjectiveSystem

namespace ArLTorsionProjectiveSystem

open LTorsionProjectiveSystem

/-- The morphism `f_s : F_{•,s}[r] ⟶ G_{•,s}` of systems of stalks induced by `f : F[r] ⟶ G`,
with `(F[r])_{•,s}` identified with `F_{•,s}[r]`. -/
def stalkSystemShiftHom (s : GeometricPoint S) {F G : LTorsionProjectiveSystem.{u} B S hS l}
    {r : ℕ} (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    (CategoryTheory.ProjectiveSystem.shift (r : ℤ)).obj
        ((LTorsionProjectiveSystem.stalkSystem s).obj F) ⟶
      (LTorsionProjectiveSystem.stalkSystem s).obj G :=
  (LTorsionProjectiveSystem.stalkSystem s).map f

/-- **The A–R morphism of stalks.** For a geometric point `s`, the functor from the A–R category
of projective systems of `l`-torsion sheaves to the A–R category of projective systems of
`l`-power torsion `ℤ`-modules sending `F` to `F_{•,s}` and the A–R morphism `[f]` represented by
`f : F[r] ⟶ G` to `[f]_s = [f_s]` (`stalkSystem_map_homMk`). -/
@[weil "def_fk112_stalk_system"]
def stalkSystem (s : GeometricPoint S) :
    ArLTorsionProjectiveSystem.{u} B S hS l ⥤
      CategoryTheory.ProjectiveSystem.ArCategory.{u} ℤ (l : ℤ) where
  obj F := .of ((LTorsionProjectiveSystem.stalkSystem s).obj F.obj)
  map {F G} φ := ArHom.lift
    (fun p ↦ CategoryTheory.ProjectiveSystem.ArCategory.homMk p.1 (stalkSystemShiftHom s p.2))
    (fun r t h f ↦ by
      dsimp only [stalkSystemShiftHom]
      rw [Functor.map_comp, stalkSystem_map_shiftMap]
      exact CategoryTheory.ProjectiveSystem.ArCategory.homMk_shiftMap_comp h _) φ
  map_id F := by
    change CategoryTheory.ProjectiveSystem.ArCategory.homMk 0
      (stalkSystemShiftHom s ((shiftι B S hS l 0).app F.obj)) = _
    rfl
  map_comp {F G H} φ ψ := by
    induction φ using hom_induction with
    | h r f =>
    induction ψ using hom_induction with
    | h t g =>
    rw [homMk_comp_homMk]
    change CategoryTheory.ProjectiveSystem.ArCategory.homMk _ (stalkSystemShiftHom s _) =
      CategoryTheory.ProjectiveSystem.ArCategory.homMk _ (stalkSystemShiftHom s f) ≫
        CategoryTheory.ProjectiveSystem.ArCategory.homMk _ (stalkSystemShiftHom s g)
    rw [CategoryTheory.ProjectiveSystem.ArCategory.homMk_comp_homMk]
    simp only [stalkSystemShiftHom, Functor.map_comp]
    rfl

/-- `[f]_s = [f_s]`: the A–R morphism of stalks of the class of `f : F[r] ⟶ G` is the class of
`f_s : F_{•,s}[r] ⟶ G_{•,s}`. -/
@[weil "def_fk112_stalk_system", simp]
lemma stalkSystem_map_homMk (s : GeometricPoint S) {F G : LTorsionProjectiveSystem.{u} B S hS l}
    (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    (stalkSystem s).map (homMk r f) =
      CategoryTheory.ProjectiveSystem.ArCategory.homMk r (stalkSystemShiftHom s f) :=
  rfl

/-- Taking A–R morphisms of stalks is additive. -/
instance (s : GeometricPoint S) : (stalkSystem (B := B) (hS := hS) (l := l) s).Additive where
  map_add {F G} {φ ψ} := by
    induction φ using hom_induction with
    | h r f =>
    induction ψ using hom_induction with
    | h t g =>
    rw [homMk_add_homMk (max r t) (le_max_left r t) (le_max_right r t), stalkSystem_map_homMk,
      stalkSystem_map_homMk, stalkSystem_map_homMk]
    refine Eq.trans ?_ (CategoryTheory.ProjectiveSystem.ArCategory.homMk_add_homMk
      (F := (LTorsionProjectiveSystem.stalkSystem s).obj F.obj) (max r t) (le_max_left r t)
        (le_max_right r t) _ _).symm
    congr 1
    simp only [stalkSystemShiftHom, Functor.map_add, Functor.map_comp]
    rfl

@[simp]
lemma stalkSystem_obj (s : GeometricPoint S) (F : ArLTorsionProjectiveSystem.{u} B S hS l) :
    (stalkSystem s).obj F = .of ((LTorsionProjectiveSystem.stalkSystem s).obj F.obj) :=
  rfl

end ArLTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale
