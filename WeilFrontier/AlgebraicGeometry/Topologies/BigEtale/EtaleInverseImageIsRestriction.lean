module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardStages
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# The inverse image along an étale morphism is restriction

Let `f : T ⟶ S` be an étale morphism of schemes of a big étale site `B`, so that `T`, with `f`,
is an object of the small étale site of `S`. For a sheaf `G` on the small étale site of `S`, with
values in any category `A` (sets, abelian groups, `Λ`-modules, ...), the *restriction* `G|_T` is
the sheaf on the small étale site of `T` with
`(G|_T)(V ⟶ T) = G(V ⟶ T ⟶ S)`,
that is, `G` precomposed with the functor `V ↦ (V, f ∘ π_V)` from the small étale site of `T` to
that of `S`. The inverse image `f^* G` is canonically isomorphic to `G|_T`, naturally in `G`.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageIsoRestriction` — the natural isomorphism
  `f^* ≅ (-)|_T`.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionAlong_obj_obj` — `(G|_T)(V) = G(V, f ∘ π_V)`.
* `AlgebraicGeometry.smallEtaleInverseImageIsoRestriction_hom_naturality` — naturality in `G`.

## Implementation notes

The restriction `G|_T` is `AlgebraicGeometry.smallEtaleRestrictionAlong`, the direct image along
composition with `f`.

Composition with `f` is left adjoint to base change along `f` on the small étale sites, so
restriction is left adjoint to the direct image `f_*`; the isomorphism is the uniqueness of left
adjoints, as in [Stacks, Tag 03S3]. This replaces the computation of the colimit defining the
inverse image presheaf by its initial object `(V, (π_V, id_V))` and the stalkwise comparison with
the sheafification.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) [Etale (B.inclusion.map f)]
variable (A : Type w) [Category.{v} A]

/-- The sections of `G|_T` over an étale `T`-scheme `V` are the sections of `G` over `V`, viewed
as an étale `S`-scheme through `f`. -/
lemma smallEtaleRestrictionAlong_obj_obj (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (V : SmallEtale B T.obj T.property) :
    ((smallEtaleRestrictionAlong B f A).obj G).obj.obj (op V) =
      G.obj.obj (op ((smallEtalePostcompose B S.obj S.property
        (SmallEtale.ofEtaleHom B f)).obj V)) :=
  rfl

/-- The étale `S`-scheme underlying `V ⟶ T`, viewed through `f`, is `V` with structure morphism
`f ∘ π_V`. -/
lemma smallEtalePostcompose_ofEtaleHom_obj_hom (V : SmallEtale B T.obj T.property) :
    ((smallEtalePostcompose B S.obj S.property (SmallEtale.ofEtaleHom B f)).obj V).obj.hom =
      V.obj.hom ≫ f :=
  rfl

variable [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **The inverse image along an étale morphism is restriction.** For an étale morphism
`f : T ⟶ S` and sheaves `G` on the small étale site of `S` with values in `A`, there is an
isomorphism `f^* G ≅ G|_T`, natural in `G`. -/
@[weil "lem_fk108_etale_inverse_image_is_restriction"]
def smallEtaleInverseImageIsoRestriction :
    smallEtaleInverseImage B f A ≅ smallEtaleRestrictionAlong B f A :=
  smallInverseImageIsoPostcomposePushforward B f A

/-- The isomorphism `f^* G ≅ G|_T` is natural in `G`. -/
@[reassoc]
lemma smallEtaleInverseImageIsoRestriction_hom_naturality
    {G G' : Sheaf (SmallEtale.topology B S.obj S.property) A} (φ : G ⟶ G') :
    (smallEtaleInverseImage B f A).map φ ≫
        (smallEtaleInverseImageIsoRestriction B f A).hom.app G' =
      (smallEtaleInverseImageIsoRestriction B f A).hom.app G ≫
        (smallEtaleRestrictionAlong B f A).map φ :=
  (smallEtaleInverseImageIsoRestriction B f A).hom.naturality φ

end AlgebraicGeometry

end
