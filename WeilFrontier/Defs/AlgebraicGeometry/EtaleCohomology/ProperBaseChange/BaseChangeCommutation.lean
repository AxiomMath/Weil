module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import Weil.Attr

/-!
# The base change theorem for a morphism, for torsion sheaves and for `ℤ/n`-sheaves

Let `f : X ⟶ S` be a morphism of schemes. For a morphism `g : T ⟶ S` and an abelian sheaf `F` on
the small étale site of `X`, *base change holds for `(f, g, F)`*
(`Stacks.EtaleCohomology.EtaleAbelianBaseChangeHolds`) when the base change map
`g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` of the cartesian square of `X ×_S T` is an isomorphism.

The morphism `f` *satisfies the base change theorem for torsion sheaves*, `BC_tor(f)`, when base
change holds for `(f, g, F)` for every `g : T ⟶ S` and every torsion sheaf `F` on `X`. This is the
property `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange f` of the Stacks project, which
quantifies over all cartesian squares over `f`; the two formulations agree, because the base
change map of a cartesian square is identified with that of the chosen fibre product through the
canonical isomorphism of the two.

For `n : ℕ`, the morphism `f` *satisfies the base change theorem for `ℤ/n`-sheaves*,
`BC_{ℤ/n}(f)`, when base change holds for `(f, g, F)` for every `g : T ⟶ S` and every sheaf `F`
of `ℤ/nℤ`-modules on `X` (read through its underlying abelian sheaf). For `n ≥ 1` such a sheaf is
a torsion sheaf, so `BC_tor(f)` implies `BC_{ℤ/n}(f)`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleZModBaseChangeTheoremHolds f n`: the base change theorem for
  `ℤ/n`-sheaves holds for `f`.

## Main results

* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_iff_forall_etaleAbelianBaseChangeHolds`:
  `CohomologyCommutesWithBaseChange f` holds if and only if base change holds for `(f, g, F)` for
  every `g : T ⟶ S` and every torsion sheaf `F` on `X`.
* `Stacks.EtaleCohomology.etaleZModBaseChangeTheoremHolds_iff_forall_higherBaseChange`: the base
  change theorem for `ℤ/n`-sheaves in terms of the base change homomorphisms
  `g^*(R^p f_* F) ⟶ R^p f'_*(g'^* F)`, `p ≥ 0`.
* `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.etaleZModBaseChangeTheoremHolds`:
  the base change theorem for torsion sheaves implies the one for `ℤ/n`-sheaves, `n ≥ 1`.

## Implementation notes

The base change theorem for torsion sheaves is not given a new definition: it is
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange f`, and
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_iff_forall_etaleAbelianBaseChangeHolds`
identifies it with the formulation through the chosen fibre products `X ×_S T`.

Freitag and Kiehl define `BC_{ℤ/n}(f)` only for `n` invertible on `S`. The definition here takes
any `n : ℕ` and no invertibility hypothesis; statements that need invertibility carry it.

Sheaves of `ℤ/nℤ`-modules are sheaves on `X.smallEtaleTopology` valued in `ModuleCat (ZMod n)`;
their underlying abelian sheaves are obtained by composing with the forgetful functor to abelian
groups. Torsion sheaves are those satisfying `Stacks.Torsion.torsionSheafProperty`, the predicate
underlying `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`, here on Mathlib's small étale site, the
setting of `Stacks.EtaleCohomology.EtaleAbelianBaseChangeHolds`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
* [Stacks Project, Tag 095S](https://stacks.math.columbia.edu/tag/095S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The base change map of a cartesian square over `f` is invertible as soon as the base change
map of the chosen fibre product `X ×_S T` is. -/
private theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isPullback {X' T : Scheme.{u}}
    {g : T ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ T} (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g (pullback.fst f g)
      (pullback.snd f g) pullback.condition F)) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F) := by
  have h₂ : sq.isoPullback.hom ≫ pullback.snd f g = f' ≫ 𝟙 T := by simp
  have sq' : IsPullback sq.isoPullback.hom f' (pullback.snd f g) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨h₂⟩
  have : IsIso (etaleAbelianDerivedBaseChange.{u, v} (pullback.snd f g) (𝟙 T)
      sq.isoPullback.hom f' h₂) :=
    isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} _ _ _ _ sq'
  exact etaleAbelianDerivedBaseChange_isIso_of_comp.{u, v} g f (pullback.snd f g)
    (pullback.fst f g) (𝟙 T) f' sq.isoPullback.hom pullback.condition h₂ g
    (Category.id_comp g).symm g' (by simp) sq.w _ hF inferInstance

/-- **The base change theorem for torsion sheaves.** Cohomology commutes with base change for
`f : X ⟶ S` if and only if base change holds for `(f, g, F)` for every morphism `g : T ⟶ S` and
every torsion sheaf `F` on the small étale site of `X`: the base change map
`g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` of the cartesian square of `X ×_S T` is an isomorphism. -/
@[weil "def_fk106_base_change_theorem_holds"]
theorem cohomologyCommutesWithBaseChange_iff_forall_etaleAbelianBaseChangeHolds :
    CohomologyCommutesWithBaseChange.{u, v} f ↔
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
          EtaleAbelianBaseChangeHolds.{u, v} f g
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) := by
  refine ⟨fun h T g F hF ↦ ?_, fun h X' T g g' f' sq F hF ↦ ?_⟩
  · rw [etaleAbelianBaseChangeHolds_single_iff]
    exact h g (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g) F hF
  · exact isIso_etaleAbelianSheafDerivedBaseChange_of_isPullback.{u, v} f sq F
      ((etaleAbelianBaseChangeHolds_single_iff.{u, v} f g F).1 (h g F hF))

/-- **The base change theorem for `ℤ/n`-sheaves.** The morphism `f : X ⟶ S` satisfies the base
change theorem for `ℤ/n`-sheaves if base change holds for `(f, g, F)` for every morphism
`g : T ⟶ S` and every sheaf `F` of `ℤ/nℤ`-modules on the small étale site of `X`, read through its
underlying abelian sheaf. -/
@[weil "def_fk106_base_change_theorem_holds"]
def EtaleZModBaseChangeTheoremHolds (n : ℕ) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod n))),
    EtaleAbelianBaseChangeHolds.{u, v} f g
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{max (u + 1) v} (ZMod n)) AddCommGrpCat.{max (u + 1) v})).obj F))

/-- **The base change theorem for `ℤ/n`-sheaves, by base change homomorphisms.** It holds for `f`
if and only if, for every `g : T ⟶ S`, every sheaf `F` of `ℤ/nℤ`-modules on `X` and every
`p ≥ 0`, the base change homomorphism `g^*(R^p f_* F) ⟶ R^p f'_*(g'^* F)` is an isomorphism. -/
theorem etaleZModBaseChangeTheoremHolds_iff_forall_higherBaseChange (n : ℕ) :
    EtaleZModBaseChangeTheoremHolds.{u, v} f n ↔
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod n))) (p : ℕ),
        IsIso ((etaleAbelianHigherBaseChange.{u, v} f g (pullback.fst f g)
          (pullback.snd f g) pullback.condition p).app
            ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{max (u + 1) v} (ZMod n))
                AddCommGrpCat.{max (u + 1) v})).obj F)) :=
  forall₃_congr fun _ g _ ↦ etaleAbelianBaseChangeHolds_single_iff_forall_higherBaseChange f g _

/-- The underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules, `n ≥ 1`, is a torsion sheaf: every
section is killed by `n`. -/
private theorem torsionSheafProperty_sheafCompose_forget₂_zmod {n : ℕ} (hn : 0 < n)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod n))) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{max (u + 1) v} (ZMod n)) AddCommGrpCat.{max (u + 1) v})).obj F) := by
  intro U x
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V φ _ ↦ ⟨n, hn, ?_⟩⟩
  change n • (F.obj.map φ.op).hom x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

/-- **The base change theorem for torsion sheaves implies the one for `ℤ/n`-sheaves**, `n ≥ 1`:
the underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules is a torsion sheaf. -/
theorem CohomologyCommutesWithBaseChange.etaleZModBaseChangeTheoremHolds
    (h : CohomologyCommutesWithBaseChange.{u, v} f) {n : ℕ} (hn : 0 < n) :
    EtaleZModBaseChangeTheoremHolds.{u, v} f n := fun _ g F ↦
  (cohomologyCommutesWithBaseChange_iff_forall_etaleAbelianBaseChangeHolds.{u, v} f).1 h g _
    (torsionSheafProperty_sheafCompose_forget₂_zmod hn F)

end Stacks.EtaleCohomology

end
