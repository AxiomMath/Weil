module

public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Attr

/-!
# Representable étale sheaves

Let `X` be a scheme. An étale sheaf of sets `G` on `X` is *representable* if there are an
object `Y` of the étale category `Et(X)` of noetherian separated étale `X`-schemes and an
isomorphism of presheaves `Ỹ ≅ G`, where `Ỹ(U) = Hom_X(U, Y)` is the sheaf represented by `Y`.
For an étale `X`-scheme `U`, "`G|_U` is representable in `Et(U)`" means that the restriction of
`G` to the étale schemes over `U` is representable in this sense.

The notion is given on both étale categories in use:

* on the small étale site `SmallEtale B X hX`, for a presheaf `F` of sets: `F` is isomorphic to
  the represented sheaf `Ỹ` of an object `Y` whose underlying scheme is noetherian and
  separated;
* on the étale category `Et(X) = SmallNoetherianSeparatedEtale B X hX`, where every object is
  noetherian and separated and the represented presheaf is the Yoneda presheaf, so that the
  notion is Mathlib's `CategoryTheory.Functor.IsRepresentable`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsRepresentableInEt`: a presheaf of sets on the small étale
  site is isomorphic to `Ỹ` for an object `Y` with noetherian separated underlying scheme.
* `AlgebraicGeometry.SmallEtale.RestrictIsRepresentableInEt`: the restriction of a presheaf to
  the small étale site of an object `U` is representable in this sense.

## Main results

* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_iff_representableBy`: the definition in
  terms of Mathlib's `CategoryTheory.Functor.RepresentableBy`.
* `AlgebraicGeometry.SmallEtale.IsRepresentableInEt.isRepresentable`: a representable presheaf
  is representable in the sense of Mathlib.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_representedSheaf`: `Ỹ` is representable
  for `Y` noetherian and separated.
* `AlgebraicGeometry.SmallEtale.IsRepresentableInEt.isRepresentable_comp_inclusion`: the
  restriction of a representable presheaf to `Et(X)` is a representable presheaf on `Et(X)`.
* `AlgebraicGeometry.EtalePresheaf.isRepresentable_iff`: on `Et(X)`, a presheaf of sets is
  representable if and only if it is isomorphic to the Yoneda presheaf of an object of `Et(X)`.
* `AlgebraicGeometry.EtalePresheaf.isRepresentable_restrict_iff`: on `Et(X)`, "`G|_U` is
  representable in `Et(U)`" spelled out with the restriction `G|_U`.

## Implementation notes

The representing object is required to be noetherian and separated, i.e. an object of `Et(X)`;
for a non-separated étale representing object the difference loci of `Ỹ` need not be open, and
the representability criterion fails. The predicates are stated for presheaves of sets: an
étale sheaf is one through its underlying presheaf, and the sheaf condition plays no part in the
definition (a represented presheaf is a sheaf, the étale topology being subcanonical).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Representable étale sheaves.** A presheaf of sets `F` on the small étale site of `X` is
representable (in `Et(X)`) if there are an object `Y` whose underlying scheme is noetherian and
separated and an isomorphism `Ỹ ≅ F` from the sheaf represented by `Y`. -/
@[weil "def_fk103_representable_etale_sheaf"]
def IsRepresentableInEt (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ Y : SmallEtale B X hX, IsNoetherianSeparated B X hX Y ∧
    Nonempty ((representedSheaf Y).obj ≅ F)

/-- **Local representability.** For an object `U` of the small étale site of `X`, the
restriction `F|_U` of a presheaf `F` to the small étale site of `U` (étale `U`-schemes `V`,
viewed over `X` by composition with `U ⟶ X`) is representable in `Et(U)`. -/
@[weil "def_fk103_representable_etale_sheaf"]
abbrev RestrictIsRepresentableInEt (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    (U : SmallEtale B X hX) : Prop :=
  IsRepresentableInEt ((smallEtalePostcompose B X hX U).op ⋙ F)

/-- The represented sheaf `Ỹ`, as a presheaf, is the Yoneda presheaf of `Y`. -/
noncomputable def representedSheafObjIsoYoneda (Y : SmallEtale B X hX) :
    (representedSheaf Y).obj ≅ yoneda.obj Y :=
  Iso.refl _

theorem isRepresentableInEt_iff_representableBy (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u) :
    IsRepresentableInEt F ↔
      ∃ Y : SmallEtale B X hX, IsNoetherianSeparated B X hX Y ∧ Nonempty (F.RepresentableBy Y) :=
  exists_congr fun Y ↦ and_congr_right fun _ ↦
    ⟨fun ⟨e⟩ ↦ ⟨Functor.representableByEquiv.symm ((representedSheafObjIsoYoneda Y).symm ≪≫ e)⟩,
      fun ⟨r⟩ ↦ ⟨representedSheafObjIsoYoneda Y ≪≫ Functor.representableByEquiv r⟩⟩

theorem IsRepresentableInEt.of_iso {F G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (hF : IsRepresentableInEt F) (e : F ≅ G) : IsRepresentableInEt G := by
  obtain ⟨Y, hY, ⟨f⟩⟩ := hF
  exact ⟨Y, hY, ⟨f ≪≫ e⟩⟩

theorem isRepresentableInEt_congr {F G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    IsRepresentableInEt F ↔ IsRepresentableInEt G :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- A representable presheaf is representable in the sense of Mathlib. -/
theorem IsRepresentableInEt.isRepresentable {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (hF : IsRepresentableInEt F) : F.IsRepresentable := by
  obtain ⟨Y, -, ⟨r⟩⟩ := (isRepresentableInEt_iff_representableBy F).1 hF
  exact r.isRepresentable

/-- The sheaf represented by an object with noetherian separated underlying scheme is
representable. -/
theorem isRepresentableInEt_representedSheaf {Y : SmallEtale B X hX}
    (hY : IsNoetherianSeparated B X hX Y) : IsRepresentableInEt (representedSheaf Y).obj :=
  ⟨Y, hY, ⟨Iso.refl _⟩⟩

/-- The restriction of a representable presheaf to `Et(X)` is a representable presheaf on
`Et(X)`, represented by the same object. -/
theorem IsRepresentableInEt.isRepresentable_comp_inclusion
    {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} (hF : IsRepresentableInEt F) :
    ((SmallNoetherianSeparatedEtale.inclusion B X hX).op ⋙ F).IsRepresentable := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := (isRepresentableInEt_iff_representableBy F).1 hF
  let Y' : SmallNoetherianSeparatedEtale B X hX := ⟨Y, hY⟩
  exact Functor.RepresentableBy.isRepresentable (Y := Y')
    { homEquiv := fun {V} ↦
        ((ObjectProperty.fullyFaithfulι (IsNoetherianSeparated B X hX)).homEquiv
          (X := V) (Y := Y')).trans r.homEquiv
      homEquiv_comp := fun {V W} f g ↦ by
        exact r.homEquiv_comp f.hom g.hom }

end SmallEtale

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Representable presheaves on `Et(S)`.** A presheaf of sets `G` on the étale category
`Et(S)` is representable (Mathlib's `CategoryTheory.Functor.IsRepresentable`) if and only if
there are an object `Y` of `Et(S)` and an isomorphism `Ỹ ≅ G` from the Yoneda presheaf
`Ỹ = Hom(-, Y)` of `Et(S)`. -/
@[weil "def_fk103_representable_etale_sheaf"]
theorem isRepresentable_iff (G : EtalePresheaf B S hS (Type u)) :
    G.IsRepresentable ↔
      ∃ Y : SmallNoetherianSeparatedEtale B S hS, Nonempty (yoneda.obj Y ≅ G) :=
  ⟨fun _ ↦ ⟨G.reprX, ⟨G.reprW⟩⟩, fun ⟨_, ⟨e⟩⟩ ↦ Functor.IsRepresentable.mk' e⟩

/-- **Local representability on `Et(S)`.** For `U ∈ Et(S)`, the restriction `G|_U`, a presheaf
on `Et(U)`, is representable if and only if there are an object `Y` of `Et(U)` and an
isomorphism `Ỹ ≅ G|_U`. -/
@[weil "def_fk103_representable_etale_sheaf"]
theorem isRepresentable_restrict_iff (G : EtalePresheaf B S hS (Type u))
    (U : SmallNoetherianSeparatedEtale B S hS) :
    (restrict G U).IsRepresentable ↔
      ∃ Y : Over' U, Nonempty (yoneda.obj Y ≅ restrict G U) :=
  isRepresentable_iff _

/-- The sections over `V` of the Yoneda presheaf `Ỹ` of an object `Y` of `Et(S)` are the
morphisms of `S`-schemes `V ⟶ Y`. -/
def yonedaObjObjEquiv (Y V : SmallNoetherianSeparatedEtale B S hS) :
    (yoneda.obj Y).obj (op V) ≃ ((toOver B S hS).obj V ⟶ (toOver B S hS).obj Y) :=
  (fullyFaithfulToOver B S hS).homEquiv

end EtalePresheaf

end AlgebraicGeometry

end
