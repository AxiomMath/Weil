module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.BigEtale.EtaleFreeModuleToPushforwardMap

/-!
# Uniqueness of the diagonal map of an étale morphism

Let `f : U ⟶ V` be an étale morphism and `Λ` a commutative ring. There is exactly one
`Λ`-linear map `φ : (Ũ)^Λ ⟶ f_* Λ_U` sending the tautological section `ι(id_U)` of `(Ũ)^Λ`
over `U` to the diagonal section `s_f`, that is, exactly one diagonal map for `f`.

Composition with `ι` identifies `Λ`-linear maps out of the free sheaf `(Ũ)^Λ` with maps of
sheaves of sets out of the sheafified representable `h_U^#`, and by the Yoneda lemma these are
the sections over `U`; the composite is evaluation at `ι(id_U)`
(`CategoryTheory.Sheaf.freeSectionEquiv`).

## Main results

* `AlgebraicGeometry.BigEtaleSite.existsUnique_app_freeTautologicalSection_eq`: there is exactly
  one `Λ`-linear map `(Ũ)^Λ ⟶ f_* Λ_U` sending `ι(id_U)` to `s_f`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5, p. 59][FreitagKiehl]
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {U V : B.Scheme} (f : U ⟶ V) [Etale (B.inclusion.map f)]
  (Λ : Type (u + 1)) [CommRing Λ]
  [DiscreteTopology (_root_.ConnectedComponents
    ((SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))))]

/-- **Existence and uniqueness of the diagonal map.** For an étale morphism `f : U ⟶ V` there is
exactly one `Λ`-linear map `φ : (Ũ)^Λ ⟶ f_* Λ_U` with `φ_U(ι(id_U)) = s_f`; it is
`AlgebraicGeometry.BigEtaleSite.diagonalMap`. -/
@[weil "lem_fk105_diagonal_map_exists_unique"]
theorem existsUnique_app_freeTautologicalSection_eq :
    ∃! φ : freeModuleSheafOfEtale B f Λ ⟶ pushforwardConstantModuleSheaf B f Λ,
      φ.hom.app (op (SmallEtale.ofEtaleHom B f))
          (Sheaf.freeTautologicalSection (SmallEtale.topology B V.obj V.property) Λ _) =
        diagonalSectionModule B f Λ :=
  existsUnique_isDiagonalMap B f Λ

end AlgebraicGeometry.BigEtaleSite
