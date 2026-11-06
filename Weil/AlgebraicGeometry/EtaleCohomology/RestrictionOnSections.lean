module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.RestrictionOnSections
public import Weil.Attr

/-!
# Naturality of the restriction of sections

Let `h : T ⟶ S` be a morphism of schemes of a big étale site, `G` a sheaf on the small étale
site of `S` and `V` an étale `S`-scheme. The restriction of sections
`r^h_{G,V} : G(V) ⟶ (h^* G)(T ×_S V)` (`AlgebraicGeometry.smallEtaleRestrictionOnSections`) is
natural in `V` and in `G`: for a morphism `e : V' ⟶ V` of étale `S`-schemes,
`(h^* G)(e_T) ∘ r^h_{G,V} = r^h_{G,V'} ∘ G(e)` with `e_T = T ×_S e`, and for a morphism of sheaves
`φ : G ⟶ G'`, `(h^* φ)_{V_T} ∘ r^h_{G,V} = r^h_{G',V} ∘ φ_V`. For sheaves of abelian groups it is
a group homomorphism.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionOnSections_naturality` — naturality in `V`.
* `AlgebraicGeometry.smallEtaleRestrictionOnSections_naturality_sheaf` — naturality in `G`.
* `AlgebraicGeometry.smallEtaleRestrictionOnSections_add` — additivity for sheaves of abelian
  groups.

## Implementation notes

Since `r^h_{G,V}` is the component at `V` of the unit `G ⟶ h_* h^* G` of the adjunction
`h^* ⊣ h_*`, and `(h_* F)(V) = F(T ×_S V)`, the two naturalities are the naturality of that unit
as a morphism of presheaves and as a natural transformation of functors on sheaves. Additivity
holds because a morphism in `AddCommGrpCat` is an additive map.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (h : T ⟶ S)

section General

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **Naturality of the restriction of sections in the étale scheme.** For a morphism
`e : V' ⟶ V` of étale `S`-schemes, `(h^* G)(e_T) ∘ r^h_{G,V} = r^h_{G,V'} ∘ G(e)`. -/
@[weil "lem_fk106_restriction_on_sections_natural", reassoc]
theorem smallEtaleRestrictionOnSections_naturality
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    {V' V : SmallEtale B S.obj S.property} (e : V' ⟶ V) :
    smallEtaleRestrictionOnSections B h A G V ≫
        ((smallEtaleInverseImage B h A).obj G).obj.map ((smallEtaleBaseChange B h).map e).op =
      G.obj.map e.op ≫ smallEtaleRestrictionOnSections B h A G V' :=
  (((smallEtaleInverseImageAdjunction B h A).unit.app G).hom.naturality e.op).symm

/-- **Naturality of the restriction of sections in the sheaf.** For a morphism of sheaves
`φ : G ⟶ G'`, `(h^* φ)_{V_T} ∘ r^h_{G,V} = r^h_{G',V} ∘ φ_V`. -/
@[weil "lem_fk106_restriction_on_sections_natural", reassoc]
theorem smallEtaleRestrictionOnSections_naturality_sheaf
    {G G' : Sheaf (SmallEtale.topology B S.obj S.property) A} (φ : G ⟶ G')
    (V : SmallEtale B S.obj S.property) :
    smallEtaleRestrictionOnSections B h A G V ≫
        ((smallEtaleInverseImage B h A).map φ).hom.app (op ((smallEtaleBaseChange B h).obj V)) =
      φ.hom.app (op V) ≫ smallEtaleRestrictionOnSections B h A G' V :=
  congrArg (fun ψ => ψ.hom.app (op V))
    ((smallEtaleInverseImageAdjunction B h A).unit.naturality φ).symm

end General

section Abelian

variable [HasColimitsOfSize.{u, u + 1} AddCommGrpCat.{w}]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{w}]

/-- **The restriction of sections is a group homomorphism** for sheaves of abelian groups. -/
@[weil "lem_fk106_restriction_on_sections_natural"]
theorem smallEtaleRestrictionOnSections_add
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{w})
    (V : SmallEtale B S.obj S.property) (s t : G.obj.obj (op V)) :
    (smallEtaleRestrictionOnSections B h AddCommGrpCat.{w} G V).hom (s + t) =
      (smallEtaleRestrictionOnSections B h AddCommGrpCat.{w} G V).hom s +
        (smallEtaleRestrictionOnSections B h AddCommGrpCat.{w} G V).hom t :=
  map_add _ s t

end Abelian

end AlgebraicGeometry

end
