module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.BigEtale.DiagonalSection
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import StacksFrontier.CategoryTheory.Sites.FreeModuleSheafSections

/-!
# Diagonal maps of an étale morphism

Let `f : U ⟶ V` be an étale morphism and `Λ` a commutative ring. Regard `U` as an object of the
small étale site of `V` through `f`, and write `(Ũ)^Λ` for the free sheaf of `Λ`-modules on the
sheafified representable `h_U^#`, with tautological section `ι(id_U)` over `U`. Let `Λ_U` be the
sheaf of locally constant `Λ`-valued maps on the small étale site of `U`, so that the sections of
its direct image `f_* Λ_U` over `U` are the locally constant maps `U ×_V U → Λ`.

A `Λ`-linear map `φ : (Ũ)^Λ ⟶ f_* Λ_U` is a **diagonal map for `f`** if `φ_U(ι(id_U)) = s_f`,
where `s_f` is the diagonal section (`AlgebraicGeometry.BigEtaleSite.diagonalSection`), equal to
`1` on the connected components of `U ×_V U` meeting the diagonal and to `0` on the others.

Since maps out of `(Ũ)^Λ` are the same as sections over `U`
(`CategoryTheory.Sheaf.freeSectionEquiv`), there is exactly one diagonal map.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.freeModuleSheafOfEtale`: the free sheaf of `Λ`-modules
  `(Ũ)^Λ` on the small étale site of `V`.
* `AlgebraicGeometry.BigEtaleSite.pushforwardConstantModuleSheaf`: the direct image `f_* Λ_U`.
* `AlgebraicGeometry.BigEtaleSite.IsDiagonalMap`: the property of being a diagonal map for `f`.
* `AlgebraicGeometry.BigEtaleSite.diagonalMap`: the diagonal map `φ_f`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.isDiagonalMap_iff`: a map is a diagonal map if and only if it
  is `AlgebraicGeometry.BigEtaleSite.diagonalMap`.
* `AlgebraicGeometry.BigEtaleSite.existsUnique_isDiagonalMap`: there is exactly one diagonal map.

## Implementation notes

The coefficient ring `Λ` lives in `Type (u + 1)`, the universe of the sheaves of modules on the
small étale site of a big étale site `B : BigEtaleSite.{u}` for which free module sheaves and
sheafification are available; a ring in a smaller universe is used through `ULift`. The diagonal
section requires the connected components of `U ×_V U` to be open, an instance argument.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.5.3 c),
  p. 59][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {U V : B.Scheme} (f : U ⟶ V) [Etale (B.inclusion.map f)]
  (Λ : Type (u + 1)) [CommRing Λ]

/-- The free sheaf of `Λ`-modules `(Ũ)^Λ` on the sheafified representable of `U`, regarded as an
object of the small étale site of `V` through the étale morphism `f : U ⟶ V`. -/
abbrev freeModuleSheafOfEtale :
    Sheaf (SmallEtale.topology B V.obj V.property) (ModuleCat.{u + 1} Λ) :=
  (Sheaf.freeModuleSheaf (SmallEtale.topology B V.obj V.property) Λ).obj
    (SmallEtale.ofEtaleHom B f)

/-- The direct image `f_* Λ_U` of the sheaf of `Λ`-modules of locally constant `Λ`-valued maps on
the small étale site of `U`. -/
abbrev pushforwardConstantModuleSheaf :
    Sheaf (SmallEtale.topology B V.obj V.property) (ModuleCat.{u + 1} Λ) :=
  (B.smallPushforward f (ModuleCat.{u + 1} Λ)).obj
    (SmallEtale.locallyConstantModuleSheaf.{0, u} B U.obj U.property Λ Λ)

variable [DiscreteTopology (_root_.ConnectedComponents
    ((SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))))]

/-- The diagonal section `s_f`, as a section over `U` of the sheaf of `Λ`-modules `f_* Λ_U`. -/
def diagonalSectionModule :
    (forget (ModuleCat.{u + 1} Λ)).obj
      ((pushforwardConstantModuleSheaf B f Λ).obj.obj (op (SmallEtale.ofEtaleHom B f))) :=
  show LocallyConstant _ Λ from diagonalSection B f Λ

/-- A `Λ`-linear map `φ : (Ũ)^Λ ⟶ f_* Λ_U` is a **diagonal map for `f`** if it sends the
tautological section `ι(id_U)` of `(Ũ)^Λ` over `U` to the diagonal section `s_f`. -/
@[weil "def_fk105_etale_free_module_to_pushforward_map"]
def IsDiagonalMap (φ : freeModuleSheafOfEtale B f Λ ⟶ pushforwardConstantModuleSheaf B f Λ) :
    Prop :=
  φ.hom.app (op (SmallEtale.ofEtaleHom B f))
      (Sheaf.freeTautologicalSection (SmallEtale.topology B V.obj V.property) Λ _) =
    diagonalSectionModule B f Λ

/-- **The diagonal map** `φ_f : (Ũ)^Λ ⟶ f_* Λ_U`: the map corresponding to the diagonal section
`s_f` under the identification of maps out of `(Ũ)^Λ` with sections over `U`. -/
def diagonalMap : freeModuleSheafOfEtale B f Λ ⟶ pushforwardConstantModuleSheaf B f Λ :=
  (Sheaf.freeSectionEquiv (SmallEtale.topology B V.obj V.property) Λ _ _).symm
    (diagonalSectionModule B f Λ)

/-- A map is a diagonal map exactly when the section over `U` it corresponds to is `s_f`. -/
lemma isDiagonalMap_iff_freeSectionEquiv (φ) :
    IsDiagonalMap B f Λ φ ↔
      Sheaf.freeSectionEquiv (SmallEtale.topology B V.obj V.property) Λ _ _ φ =
        diagonalSectionModule B f Λ := by
  rw [Sheaf.freeSectionEquiv_eq_app]
  rfl

/-- The diagonal map is a diagonal map. -/
lemma isDiagonalMap_diagonalMap : IsDiagonalMap B f Λ (diagonalMap B f Λ) :=
  (isDiagonalMap_iff_freeSectionEquiv B f Λ _).2 (Equiv.apply_symm_apply _ _)

/-- A diagonal map is the diagonal map. -/
lemma IsDiagonalMap.eq_diagonalMap {φ} (h : IsDiagonalMap B f Λ φ) : φ = diagonalMap B f Λ :=
  (Equiv.eq_symm_apply _).2 ((isDiagonalMap_iff_freeSectionEquiv B f Λ _).1 h)

/-- A map is a diagonal map if and only if it is the diagonal map. -/
lemma isDiagonalMap_iff (φ) : IsDiagonalMap B f Λ φ ↔ φ = diagonalMap B f Λ :=
  ⟨fun h => h.eq_diagonalMap, fun h => h ▸ isDiagonalMap_diagonalMap B f Λ⟩

/-- There is exactly one diagonal map for `f`. -/
lemma existsUnique_isDiagonalMap : ∃! φ, IsDiagonalMap B f Λ φ :=
  ⟨_, isDiagonalMap_diagonalMap B f Λ, fun _ h => h.eq_diagonalMap⟩

end AlgebraicGeometry.BigEtaleSite
