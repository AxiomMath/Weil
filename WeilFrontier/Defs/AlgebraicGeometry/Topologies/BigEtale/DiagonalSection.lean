module

public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.ConstantSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# The diagonal section of the direct image of a constant sheaf

Let `f : U ⟶ V` be an étale morphism and `Λ` an abelian group with a distinguished element `1`
(for instance a ring). Regard `U` as an object of the small étale site of `V` through `f`. The
direct image `f_* Λ_U` of the sheaf `Λ_U` of locally constant `Λ`-valued maps on the small étale
site of `U` has as sections over `U` the locally constant maps `U ×_V U → Λ`. The **diagonal
section** `s_f` is the locally constant map equal to `1` on the connected components of
`U ×_V U` meeting the diagonal `Δ(U)`, and to `0` on the others.

This requires the connected components of `U ×_V U` to be open (equivalently, its space of
connected components to be discrete), which holds for instance when `U ×_V U` is noetherian, the
situation of étale morphisms of noetherian schemes.

## Main definitions

* `LocallyConstant.connectedComponentsIndicator`: on a space with open connected components, the
  locally constant map equal to `1` on the connected components meeting a set `s` and to `0` on
  the others.
* `AlgebraicGeometry.BigEtaleSite.smallEtaleDiagonal`: the diagonal `U ⟶ U ×_V U` of an étale
  morphism `f : U ⟶ V` of a big étale site, as a morphism of the small étale site of `U`.
* `AlgebraicGeometry.BigEtaleSite.diagonalSection`: the diagonal section
  `s_f ∈ (f_* Λ_U)(U)`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.diagonalSection_apply`: the value of `s_f` at a point `z`
  is `1` if the connected component of `z` meets the diagonal, and `0` otherwise.
* `AlgebraicGeometry.BigEtaleSite.diagonalSection_apply_diagonal`: `s_f` is `1` on the diagonal.

## Implementation notes

The fibre product `U ×_V U` is the base change of the étale `V`-scheme `U` along `f`, an object
of the small étale site of `U` (`AlgebraicGeometry.smallEtaleBaseChange`), so that `s_f` is by
definition a section of the direct image sheaf `AlgebraicGeometry.BigEtaleSite.smallPushforward`
of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale`. The
diagonal is the morphism to this base change with both components the identity.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.5.3 c),
  p. 59][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace LocallyConstant

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology (ConnectedComponents X)]

open Classical in
/-- On a space whose connected components are open, the locally constant map equal to `1` on
the connected components meeting `s` and to `0` on the others. -/
def connectedComponentsIndicator (s : Set X) (Λ : Type*) [Zero Λ] [One Λ] :
    LocallyConstant X Λ :=
  equivConnectedComponents.symm fun c => if c ∈ ConnectedComponents.mk '' s then 1 else 0

open Classical in
lemma connectedComponentsIndicator_apply (s : Set X) (Λ : Type*) [Zero Λ] [One Λ] (x : X) :
    connectedComponentsIndicator s Λ x =
      if (connectedComponent x ∩ s).Nonempty then 1 else 0 := by
  simp only [connectedComponentsIndicator, equivConnectedComponents_symm_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, ConnectedComponents.coe_eq_coe'.1 hxy, hy⟩
  · rintro ⟨y, hxy, hy⟩
    exact ⟨y, hy, ConnectedComponents.coe_eq_coe'.2 hxy⟩

lemma connectedComponentsIndicator_apply_of_mem {s : Set X} (Λ : Type*) [Zero Λ] [One Λ]
    {x : X} (hx : x ∈ s) : connectedComponentsIndicator s Λ x = 1 := by
  have h : (connectedComponent x ∩ s).Nonempty := ⟨x, mem_connectedComponent, hx⟩
  simp [connectedComponentsIndicator_apply, h]

lemma connectedComponentsIndicator_apply_of_disjoint {s : Set X} (Λ : Type*) [Zero Λ] [One Λ]
    {x : X} (hx : Disjoint (connectedComponent x) s) : connectedComponentsIndicator s Λ x = 0 := by
  have h : ¬ (connectedComponent x ∩ s).Nonempty :=
    Set.not_nonempty_iff_eq_empty.2 (Set.disjoint_iff_inter_eq_empty.1 hx)
  simp [connectedComponentsIndicator_apply, h]

end LocallyConstant

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {U V : B.Scheme} (f : U ⟶ V) [Etale (B.inclusion.map f)]

/-- **The diagonal** `Δ : U ⟶ U ×_V U` of an étale morphism `f : U ⟶ V` of a big étale site, as
a morphism of the small étale site of `U`, from `U` (over itself by the identity) to the base
change `U ×_V U` of the étale `V`-scheme `U` along `f`: both of its components are the
identity of `U`. -/
def smallEtaleDiagonal :
    SmallEtale.ofEtaleHom B (𝟙 U) ⟶ (smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f) :=
  smallEtaleBaseChangeLift B f (SmallEtale.ofEtaleHom B f) (SmallEtale.ofEtaleHom B (𝟙 U)) (𝟙 _)
    (by simp)

variable (Λ : Type w) [AddCommGroup Λ] [One Λ]
  [DiscreteTopology (_root_.ConnectedComponents
    ((SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))))]

/-- **The diagonal section** `s_f ∈ (f_* Λ_U)(U) = Λ_U(U ×_V U)` of an étale morphism
`f : U ⟶ V`: the locally constant map on `U ×_V U` equal to `1` on the connected components
meeting the diagonal `Δ(U)` and to `0` on the others. -/
@[weil "def_fk105_diagonal_section"]
def diagonalSection :
    ((B.smallPushforward f AddCommGrpCat.{max u w}).obj
      (SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B U.obj U.property Λ)).obj.obj
        (op (SmallEtale.ofEtaleHom B f)) :=
  show LocallyConstant _ Λ from LocallyConstant.connectedComponentsIndicator
    (Set.range ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)).base) Λ

open Classical in
/-- The value of the diagonal section at a point `z` of `U ×_V U` is `1` if the connected
component of `z` meets the diagonal, and `0` otherwise. -/
lemma diagonalSection_apply
    (z : (SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))) :
    (show LocallyConstant _ Λ from diagonalSection B f Λ) z =
      if (connectedComponent z ∩
        Set.range ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)).base
          ).Nonempty then 1 else 0 :=
  LocallyConstant.connectedComponentsIndicator_apply
    (X := (SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))) _ Λ z

/-- The diagonal section is `1` on the diagonal. -/
lemma diagonalSection_apply_diagonal
    (x : (SmallEtale.toScheme B U.obj U.property).obj (SmallEtale.ofEtaleHom B (𝟙 U))) :
    (show LocallyConstant _ Λ from diagonalSection B f Λ)
      (((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)).base x) = 1 :=
  LocallyConstant.connectedComponentsIndicator_apply_of_mem
    (X := (SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))) Λ ⟨x, rfl⟩

/-- The diagonal section is `0` on a connected component disjoint from the diagonal. -/
lemma diagonalSection_apply_of_disjoint
    (z : (SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f)))
    (hz : Disjoint (connectedComponent z)
      (Set.range ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)).base)) :
    (show LocallyConstant _ Λ from diagonalSection B f Λ) z = 0 :=
  LocallyConstant.connectedComponentsIndicator_apply_of_disjoint
    (X := (SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))) Λ hz

end AlgebraicGeometry.BigEtaleSite
