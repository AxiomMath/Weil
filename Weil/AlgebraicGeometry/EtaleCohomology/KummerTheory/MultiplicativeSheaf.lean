module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnitySheaf
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Attr

/-!
# The presheaf of `n`-th roots of unity is an étale sheaf

For a scheme `X` and an integer `n`, the presheaf `μ_n` on the small étale site of `X` assigns
to an étale `X`-scheme `U` the group `rootsOfUnity n Γ(U, 𝒪_U)` of `n`-th roots of unity among
the invertible global functions on `U`, with restriction of functions as restriction maps.
This file shows that `μ_n` is a sheaf of abelian groups for the étale topology: it is
isomorphic, as a presheaf, to the underlying presheaf of the kernel
`Stacks.Kummer.rootsOfUnitySheaf` of the `n`-th power map on `𝐆_m`, whose sections were
identified with the `n`-th roots of unity in
`AlgebraicGeometry.rootsOfUnitySheafAddEquiv`.

## Main definitions

* `AlgebraicGeometry.rootsOfUnityPresheaf`: the presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` of abelian
  groups (written additively) on the small étale site `X.Etale`.
* `AlgebraicGeometry.rootsOfUnityPresheafIso`: its isomorphism with the underlying presheaf of
  `Stacks.Kummer.rootsOfUnitySheaf`.

## Main results

* `AlgebraicGeometry.isSheaf_rootsOfUnityPresheaf`: `μ_n` is a sheaf of abelian groups on
  `X.Etale`.
* `AlgebraicGeometry.SmallEtale.isSheaf_rootsOfUnityPresheaf`: the same on the bounded small
  étale site `SmallEtale B X hX`.

## Implementation notes

Neither `n ≥ 1` nor the invertibility of `n` on `X` is needed for the sheaf property; they are
not assumed. The coefficients are `AddCommGrpCat.{max (u + 1) v}`, as for
`Stacks.Kummer.rootsOfUnitySheaf`, so sections are raised by `ULift`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

open Stacks.Kummer

variable (X : Scheme.{u}) (n : ℕ)

/-- Restriction of `n`-th roots of unity along a morphism of the small étale site. -/
def rootsOfUnityRestrict {U V : X.Etale} (f : V ⟶ U) :
    rootsOfUnity n Γ(U.left, ⊤) →* rootsOfUnity n Γ(V.left, ⊤) :=
  restrictRootsOfUnity f.left.appTop.hom n

@[simp]
lemma coe_rootsOfUnityRestrict {U V : X.Etale} (f : V ⟶ U) (ζ : rootsOfUnity n Γ(U.left, ⊤)) :
    ((rootsOfUnityRestrict X n f ζ : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
      f.left.appTop.hom ((ζ : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)) :=
  restrictRootsOfUnity_coe_apply _ _

lemma rootsOfUnityRestrict_id (U : X.Etale) :
    rootsOfUnityRestrict X n (𝟙 U) = MonoidHom.id _ := by
  ext ζ
  exact coe_rootsOfUnityRestrict X n (𝟙 U) ζ

lemma rootsOfUnityRestrict_comp {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V) :
    rootsOfUnityRestrict X n (g ≫ f) =
      (rootsOfUnityRestrict X n g).comp (rootsOfUnityRestrict X n f) := by
  ext ζ
  exact coe_rootsOfUnityRestrict X n (g ≫ f) ζ

/-- **The presheaf `μ_n` of `n`-th roots of unity** on the small étale site of `X`: its
sections over `U` are the `n`-th roots of unity in `Γ(U, 𝒪_U)`, written additively, and its
restriction maps are restriction of functions. -/
def rootsOfUnityPresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} where
  obj U := AddCommGrpCat.of (ULift.{max (u + 1) v} (Additive (rootsOfUnity n Γ(U.unop.left, ⊤))))
  map f := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((rootsOfUnityRestrict X n f.unop).toAdditive.comp AddEquiv.ulift.toAddMonoidHom))
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

/-- The presheaf of `n`-th roots of unity is isomorphic to the underlying presheaf of the
kernel `Stacks.Kummer.rootsOfUnitySheaf` of the `n`-th power map on `𝐆_m`. -/
def rootsOfUnityPresheafIso :
    rootsOfUnityPresheaf.{u, v} X n ≅ (rootsOfUnitySheaf.{u, v} X n).obj :=
  NatIso.ofComponents
    (fun U => (AddEquiv.ulift.trans
      (rootsOfUnitySheafAddEquiv.{u, v} X n U.unop).symm).toAddCommGrpIso)
    (by
      intro U V f
      ext ⟨ζ⟩
      apply (rootsOfUnitySheafAddEquiv.{u, v} X n V.unop).injective
      change rootsOfUnitySheafAddEquiv.{u, v} X n V.unop
          ((rootsOfUnitySheafAddEquiv.{u, v} X n V.unop).symm
            (Additive.ofMul (rootsOfUnityRestrict X n f.unop (Additive.toMul ζ)))) =
        rootsOfUnitySheafAddEquiv.{u, v} X n V.unop
          ((rootsOfUnitySheaf.{u, v} X n).obj.map f
            ((rootsOfUnitySheafAddEquiv.{u, v} X n U.unop).symm ζ))
      rw [AddEquiv.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      have h := rootsOfUnitySheafAddEquiv_map.{u, v} X n f.unop
        ((rootsOfUnitySheafAddEquiv.{u, v} X n U.unop).symm ζ)
      rw [AddEquiv.apply_symm_apply] at h
      exact (Units.ext (coe_rootsOfUnityRestrict X n f.unop _)).trans h.symm)

/-- **`μ_n` is an étale sheaf** [FK, I.2]: the presheaf of `n`-th roots of unity is a sheaf of
abelian groups on the small étale site of `X`. -/
@[weil "lem_fk102_roots_of_unity_sheaf_is_sheaf"]
theorem isSheaf_rootsOfUnityPresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (rootsOfUnityPresheaf.{u, v} X n) :=
  (Presheaf.isSheaf_of_iso_iff (rootsOfUnityPresheafIso.{u, v} X n)).2
    (rootsOfUnitySheaf.{u, v} X n).property

/-- **`μ_n` is an étale sheaf on the bounded small étale site** [FK, I.2]: the restriction of
the presheaf of `n`-th roots of unity to the small étale site `SmallEtale B X hX` of
Stacks 021B is a sheaf of abelian groups. -/
@[weil "lem_fk102_roots_of_unity_sheaf_is_sheaf"]
theorem SmallEtale.isSheaf_rootsOfUnityPresheaf (B : BigEtaleSite.{u}) (hX : B.Contains X) :
    Presheaf.IsSheaf (SmallEtale.topology B X hX)
      ((SmallEtale.toEtaleSite B X hX).op ⋙ rootsOfUnityPresheaf.{u, v} X n) :=
  ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
    ⟨_, AlgebraicGeometry.isSheaf_rootsOfUnityPresheaf.{u, v} X n⟩).property

end AlgebraicGeometry

end
