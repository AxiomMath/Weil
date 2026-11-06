module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction

/-!
# Representable sheaves on `Et(S)` and on the small étale site

Let `S` be a locally noetherian scheme. Restriction along the inclusion of the étale category
`Et(S)` of noetherian separated étale `S`-schemes into the small étale site of `S` is an
equivalence of categories of sheaves. On this comparison, a sheaf of sets on `Et(S)` is
representable if and only if the corresponding sheaf on the small étale site is represented by
an object with noetherian separated underlying scheme, and the same holds for the restrictions
to an object `U` of `Et(S)`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.inclusionOpCompYonedaObjIso`: the restriction to `Et(S)` of the
  Yoneda presheaf of an object of `Et(S)` is its Yoneda presheaf on `Et(S)`.

## Main results

* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_iff_isRepresentable_comp_inclusion`: a sheaf
  of sets on the small étale site of a locally noetherian scheme is representable in `Et(S)` if
  and only if its restriction to `Et(S)` is representable.
* `AlgebraicGeometry.EtalePresheaf.isRepresentable_iff_isRepresentableInEt_sheafEquiv`: a sheaf
  of sets on `Et(S)` is representable if and only if the corresponding sheaf on the small étale
  site is representable in `Et(S)`.
* `AlgebraicGeometry.EtalePresheaf.isRepresentable_restrict_iff_restrictIsRepresentableInEt`:
  the same for the restrictions to an object `U` of `Et(S)`.

## Implementation notes

The statements are about sheaves, not presheaves: restriction to `Et(S)` is an equivalence only
on sheaves, and the representing object is moved between the two sites through it. Every
hypothesis `[IsLocallyNoetherian S]` is the one of the comparison equivalence
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace SmallEtale

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The restriction to `Et(S)` of the Yoneda presheaf of an object of `Et(S)` is its Yoneda
presheaf on `Et(S)`. -/
noncomputable def inclusionOpCompYonedaObjIso (Y : SmallNoetherianSeparatedEtale B S hS) :
    (SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙
        yoneda.obj ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj Y) ≅ yoneda.obj Y :=
  NatIso.ofComponents
    (fun V ↦ ((ObjectProperty.fullyFaithfulι (IsNoetherianSeparated B S hS)).homEquiv
      (X := V.unop) (Y := Y)).symm.toIso)
    (fun {V W} g ↦ by
      ext (f : (SmallNoetherianSeparatedEtale.inclusion B S hS).obj V.unop ⟶
        (SmallNoetherianSeparatedEtale.inclusion B S hS).obj Y)
      rfl)

/-- **Transport of `AlgebraicGeometry.EtalePresheaf.isRepresentable_iff`.** A sheaf of sets on
the small étale site of a locally noetherian scheme is representable in `Et(S)` if and only if
its restriction to `Et(S)` is representable. -/
theorem isRepresentableInEt_iff_isRepresentable_comp_inclusion [IsLocallyNoetherian S]
    (F : Sheaf (topology B S hS) (Type u)) :
    IsRepresentableInEt F.obj ↔
      ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ F.obj).IsRepresentable := by
  refine ⟨fun h ↦ h.isRepresentable_comp_inclusion, fun h ↦ ?_⟩
  obtain ⟨Y, ⟨e⟩⟩ := (EtalePresheaf.isRepresentable_iff _).1 h
  let E := SmallNoetherianSeparatedEtale.sheafEquiv B S hS (Type u)
  let e' : E.inverse.obj
      (representedSheaf ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj Y)) ≅
        E.inverse.obj F :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (inclusionOpCompYonedaObjIso Y ≪≫ e)
  exact ⟨(SmallNoetherianSeparatedEtale.inclusion B S hS).obj Y, Y.property,
    ⟨(sheafToPresheaf _ _).mapIso (E.inverse.preimageIso e')⟩⟩

end SmallEtale

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsLocallyNoetherian S]

/-- **Transport of `AlgebraicGeometry.EtalePresheaf.isRepresentable_iff`.** A sheaf of sets on
`Et(S)` is representable if and only if the corresponding sheaf on the small étale site is
representable in `Et(S)`. -/
theorem isRepresentable_iff_isRepresentableInEt_sheafEquiv
    (G : Sheaf (SmallNoetherianSeparatedEtale.topology B S hS) (Type u)) :
    G.obj.IsRepresentable ↔
      SmallEtale.IsRepresentableInEt ((sheafEquiv B S hS (Type u)).functor.obj G).obj := by
  rw [SmallEtale.isRepresentableInEt_iff_isRepresentable_comp_inclusion]
  let i : ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙
      ((sheafEquiv B S hS (Type u)).functor.obj G).obj) ≅ G.obj :=
    (sheafToPresheaf _ _).mapIso ((sheafEquiv B S hS (Type u)).unitIso.app G).symm
  exact ⟨fun _ ↦ isRepresentable_of_natIso _ i.symm,
    fun _ ↦ isRepresentable_of_natIso _ i⟩

/-- **Transport of `AlgebraicGeometry.EtalePresheaf.isRepresentable_restrict_iff`.** For a sheaf
of sets `F` on the small étale site of a locally noetherian scheme `S` and `U ∈ Et(S)`, the
restriction `F|_U` is representable in `Et(U)` if and only if the restriction to `Et(U)` of the
corresponding sheaf on `Et(S)` is representable. -/
theorem isRepresentable_restrict_iff_restrictIsRepresentableInEt
    (F : Sheaf (SmallEtale.topology B S hS) (Type u)) (U : SmallNoetherianSeparatedEtale B S hS) :
    (restrict ((sheafEquiv B S hS (Type u)).inverse.obj F).obj U).IsRepresentable ↔
      SmallEtale.RestrictIsRepresentableInEt F.obj
        ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U) := by
  have : IsLocallyNoetherian
      ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U).obj.left.1 :=
    show IsLocallyNoetherian ((toScheme B S hS).obj U) from inferInstance
  exact (SmallEtale.isRepresentableInEt_iff_isRepresentable_comp_inclusion
    ((smallEtalePostcompose B S hS
      ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U)).sheafPushforwardContinuous
        (Type u) (SmallEtale.topology _ _ _) (SmallEtale.topology B S hS) |>.obj F)).symm

end EtalePresheaf

end AlgebraicGeometry

end
