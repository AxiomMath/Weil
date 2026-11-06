module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StructureAndBaseChangeMapping
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import Weil.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import Weil.Attr

/-!
# The base change homomorphism at a geometric point

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, `X_T = X ×_S T` with projections
`g' : X_T ⟶ X` and `f' : X_T ⟶ T`, `I` a complex of abelian sheaves on the small étale site of
`X` and `q : g'^* I ⟶ J` a morphism of complexes on `X_T`. The base change homomorphism
`β^i : H^i(g^* f_* I) ⟶ H^i(f'_* J)` is `H^i` of the base change morphism
`γ = f'_*(q) ∘ β_I : g^* f_* I ⟶ f'_* J`.

Let `t : Spec Ω ⟶ T` be a geometric point and `s = t ≫ g`. An étale neighbourhood `(U, u)` of `s`
gives the étale neighbourhood `(U_T, u_T) = (U ×_S T, (u, t))` of `t`. The stalk of
`H^i(g^* f_* I)` at `t` receives the coprojection of `H^i(I^•(X ×_S U)) = H^i((f_* I)(U))`: the
unit `f_* I ⟶ g_* g^* f_* I` on sections over `U`, followed by the germs at `(U_T, u_T)`; it is the
germ at `(U, u)` read through the identification `(g^* G)_t ≅ G_s` of the stalks of an inverse
image. Likewise `(H^i(f'_* J))_t` receives the coprojection of `H^i(J^•(X_T ×_T V))` at every
étale neighbourhood `(V, v)` of `t`. We show that the stalk at `t` of `β^i` is the map whose
composite with the coprojection at `(U, u)` is `H^i` of the map of complexes of sections
`I^•(X ×_S U) ⟶ J^•(X_T ×_T U_T)` induced by the adjoint `f_* I ⟶ g_* f'_* J` of `γ`,
followed by the coprojection at `(U_T, u_T)`. In degree `j` that adjoint is
`g_* f'_*(q^j) ∘ c ∘ f_*(η^{g'}_{I^j})`, where `c` identifies `X_T ×_X (X ×_S U)` with
`X_T ×_T U_T`.

The key step is the description of `(g^* G)_t ≅ G_s` on germs: the germ of `a ∈ G(U)` at `(U, u)`
corresponds to the germ at `(U_T, u_T)` of the image of `a` under the unit `G ⟶ g_* g^* G`.

## Main definitions

* `Stacks.EtaleCohomology.pointSmallEtaleBaseChangeLift` — the étale neighbourhood `(U_T, u_T)`.
* `Stacks.EtaleCohomology.etaleAbelianSectionsHomologyToSheafFiber` — the coprojection
  `H^i(L(V)) ⟶ (H^i L)_y` at an étale neighbourhood `(V, y)`.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageSectionsHomologyToSheafFiber` — the coprojection
  `H^i(K(U)) ⟶ (H^i(g^* K))_t` at an étale neighbourhood `(U, u)` of `t ≫ g`.
* `Stacks.EtaleCohomology.etaleAbelianPullbackResolutionBaseChangeAdjoint` — the adjoint
  `f_* I ⟶ g_* f'_* J` of the base change morphism.

## Main results

* `Stacks.EtaleCohomology.toPresheafFiber_etaleAbelianInverseImageSheafFiberIso_inv_app` — the
  identification `G_s ≅ (g^* G)_t` on germs.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageSectionsHomologyToSheafFiber_eq` — the
  coprojection is the germ at `(U, u)` read through `(g^* K)_t ≅ K_s`.
* `Stacks.EtaleCohomology.etaleAbelianPullbackResolutionBaseChangeAdjoint_f`,
  `Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj_homEquiv_baseChange_comp` — the
  adjoint of the base change morphism in each degree.
* `etaleAbelianInverseImageSectionsHomologyToSheafFiber_sheafFiber_map_higherBaseChange`
  — the stalk at `t` of the base change homomorphism on coprojections.

## Implementation notes

Sheaves are abelian sheaves with coefficients in `AddCommGrpCat.{max (u + 1) v}` on Mathlib's
small étale sites, the setting of
`Stacks.EtaleCohomology.etaleAbelianPullbackResolutionHigherBaseChange`;
stalks are taken at the universe lift `(pointSmallEtale t).ulift` of Mathlib's point of the small
étale site at a geometric point over a separably closed field, as in
`Stacks.EtaleCohomology.etaleAbelianInverseImageSheafFiberIso`. The complexes `I` and `J` and the
morphism `q` are arbitrary: no resolution hypothesis is needed. When `I` and `J` restrict to
injective resolutions, `H^i(I^•(X ×_S U))` and `H^i(J^•(X_T ×_T U_T))` are the étale cohomology
groups `H^i(X ×_S U, F)` and `H^i(X_T ×_T U_T, g'^* F)`, and the map between them is the
inverse-image map on cohomology given by its cocycle formula.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
-/

/- Stated on Mathlib's small étale site (where `etaleAbelianPullbackResolutionHigherBaseChange`
lives), geometric points over separably closed fields. FK's groups `H^i(X ×_S U, F|)`
are presented as `H^i(I^•(X ×_S U))` (the identification of
`directImageCohomologyPresheafObjIso`), and `h_U^*` by the chain map of sections; their
transport to `Sheaf.H` / `Ext` (`extConstantAddEquivH`, `etaleModuleExtInverseImage`, stated for
other coefficient categories) is not formalized here. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

namespace CategoryTheory.GrothendieckTopology.Point

universe w v

section Comap

variable {C D : Type*} [Category* C] [Category* D]
  {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F] {J : GrothendieckTopology C}
  (hF : CoverPreserving J K F)
  [InitiallySmall (F ⋙ Φ.fiber).Elements]
  (A : Type*) [Category.{v} A] [HasProducts.{w} A]
  [Functor.IsContinuous F J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasColimitsOfSize.{w, w} A]

/-- The comparison `(Φ.comap F hF).sheafFiber ≅ F.sheafPullback ⋙ Φ.sheafFiber` sends the germ
of a section `a` of `X` at `(U, x)` to the germ at `(F U, x)` of the image of `a` under the unit
`X ⟶ F_* F^* X`. -/
@[reassoc]
private theorem toPresheafFiber_sheafFiberComapIso_hom_app (X : Sheaf J A) (U : C)
    (x : (Φ.comap F hF).fiber.obj U) :
    (Φ.comap F hF).toPresheafFiber U x X.obj ≫ (Φ.sheafFiberComapIso F hF A).hom.app X =
      ((F.sheafAdjunctionContinuous A J K).unit.app X).hom.app (op U) ≫
        Φ.toPresheafFiber (F.obj U) x ((F.sheafPullback A J K).obj X).obj := by
  rw [sheafFiberComapIso_hom_app]
  dsimp only [sheafFiber, Functor.comp_map]
  erw [(Φ.comap F hF).toPresheafFiber_naturality_assoc,
    (Φ.comap F hF).toPresheafFiber_naturality_assoc,
    (Φ.comap F hF).toPresheafFiber_naturality_assoc]
  congr 1
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_symm_id]
  erw [skyscraperSheafAdjunction_homEquiv_symm_apply,
    toPresheafFiber_skyscraperPresheafHomEquiv_symm]
  simp only [skyscraperSheafFunctorCompSheafPushforwardContinuous, Iso.refl_hom, NatTrans.id_app]
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.id_comp]
  refine Eq.trans ?_ ((skyscraperPresheafHomEquiv_app_π Φ
    (𝟙 (Φ.presheafFiber.obj ((F.sheafPullback A J K).obj X).obj)) (F.obj U) x).trans
      (Category.comp_id _))
  congr 1
  exact congr_arg (fun f => NatTrans.app f (op (F.obj U)))
    (skyscraperSheafAdjunction_homEquiv_apply_hom Φ (𝟙 _))

end Comap

/-- A morphism of points `f : Φ₁ ⟶ Φ₂` sends, on stalks of presheaves, the germ at `(X, x)` for
`Φ₂` to the germ at `(X, f x)` for `Φ₁`. -/
@[reassoc]
private theorem toPresheafFiber_hom_presheafFiber_app {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Type*} [Category.{v} A] [HasColimitsOfSize.{w, w} A]
    {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (X : C)
    (x : Φ₂.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₂.toPresheafFiber X x P ≫ f.presheafFiber.app P = Φ₁.toPresheafFiber X (f.hom.app X x) P := by
  simp [Hom.presheafFiber]

section Sections

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category.{v} A]
  [HasColimitsOfSize.{w, w} A] (Φ : Point.{w} J)

/-- The germ maps at `(U, x)`, `F(U) ⟶ F_Φ`, as a natural transformation from the sections over
`U` to the stalk functor of the point `Φ`. -/
@[simps]
def sheafSectionsToSheafFiber (U : C) (x : Φ.fiber.obj U) :
    (sheafSections J A).obj (op U) ⟶ Φ.sheafFiber where
  app F := Φ.toPresheafFiber U x F.obj
  naturality _ _ φ := (Φ.toPresheafFiber_naturality φ.hom U x).symm

end Sections

end CategoryTheory.GrothendieckTopology.Point

universe u v

namespace Stacks.EtaleCohomology

/-- The stalk functor of a point of a small étale site, on abelian sheaves with coefficients in
`AddCommGrpCat.{max (u + 1) v}`, is additive: it preserves finite colimits. -/
local instance additive_sheafFiber_smallEtale_of_point {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) v} Z.smallEtaleTopology) :
    (Φ.sheafFiber (A := AddCommGrpCat.{max (u + 1) v})).Additive :=
  Functor.additive_of_preserves_binary_products _

section InverseImageStalk

variable {S T : Scheme.{u}} (g : T ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (.of Ω) ⟶ T)

/-- The étale neighbourhood `(U ×_S T, (u, t))` of the geometric point `t` of `T` obtained from an
étale neighbourhood `(U, u)` of `t ≫ g` by base change along `g : T ⟶ S`, as an element of the
fibre of the universe-lifted point `(pointSmallEtale t).ulift`. -/
def pointSmallEtaleBaseChangeLift (U : S.Etale)
    (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) :
    ((pointSmallEtale t).ulift.{max (u + 1) v}).fiber.obj ((smallEtaleBaseChange g).obj U) :=
  ULift.up ((pointSmallEtaleBaseChangeFiberIso g t).hom.app U x.down)

/-- **The identification `G_{t ≫ g} ≅ (g^* G)_t` on germs.** The inverse of
`etaleAbelianInverseImageSheafFiberIso` sends the germ of a section `a ∈ G(U)` at an étale
neighbourhood `(U, u)` of `t ≫ g` to the germ at `(U ×_S T, (u, t))` of the image of `a` under the
unit `G ⟶ g_* g^* G`, a section of `g^* G` over `U ×_S T`. -/
@[reassoc]
theorem toPresheafFiber_etaleAbelianInverseImageSheafFiberIso_inv_app
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (U : S.Etale)
    (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) :
    ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).toPresheafFiber U x G.obj ≫
      ((etaleAbelianInverseImageSheafFiberIso.{u, v} g t).app G).inv =
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app G).hom.app (op U) ≫
      ((pointSmallEtale t).ulift.{max (u + 1) v}).toPresheafFiber ((smallEtaleBaseChange g).obj U)
        (pointSmallEtaleBaseChangeLift.{u, v} g t U x)
        ((etaleAbelianInverseImage.{u, v} g).obj G).obj := by
  unfold etaleAbelianInverseImageSheafFiberIso
  simp only [Iso.app_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv,
    GrothendieckTopology.Point.sheafFiberIso, Functor.whiskerRight_app]
  simp only [Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_hom_presheafFiber_app_assoc]
  let _ : InitiallySmall.{max (u + 1) v}
      (smallEtaleBaseChange g ⋙ ((pointSmallEtale t).ulift.{max (u + 1) v}).fiber).Elements :=
    initiallySmall_of_essentiallySmall _
  have h := GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app
    (pointSmallEtale t).ulift.{max (u + 1) v} (smallEtaleBaseChange g)
    (CoverPreserving.of_isContinuous _ _ _) AddCommGrpCat.{max (u + 1) v} G U
    (pointSmallEtaleBaseChangeLift.{u, v} g t U x)
  erw [reassoc_of% h]
  dsimp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_map]
  refine (Category.assoc _ _ _).trans ?_
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  refine (Category.assoc _ _ _).symm.trans ?_
  congr 1
  have := Adjunction.unit_leftAdjointUniq_hom_app
    ((smallEtaleBaseChange g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      S.smallEtaleTopology T.smallEtaleTopology)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
      AddCommGrpCat.{max (u + 1) v} S.smallEtaleTopology T.smallEtaleTopology) G
  exact congr_arg (fun f => NatTrans.app (InducedCategory.Hom.hom f) (op U)) this

/-- **The stalk at `t` of a morphism out of an inverse image, on germs.** For `φ : g^* G ⟶ H`, the
germ of `a ∈ G(U)` at an étale neighbourhood `(U, u)` of `t ≫ g`, read in `(g^* G)_t`, is sent by
`φ_t` to the germ at `(U ×_S T, (u, t))` of the adjoint `φ^♭(a) ∈ (g_* H)(U) = H(U ×_S T)`. -/
@[reassoc]
theorem toPresheafFiber_etaleAbelianInverseImageSheafFiberIso_inv_app_sheafFiber_map
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (H : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (φ : (etaleAbelianInverseImage.{u, v} g).obj G ⟶ H) (U : S.Etale)
    (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) :
    ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).toPresheafFiber U x G.obj ≫
      ((etaleAbelianInverseImageSheafFiberIso.{u, v} g t).app G).inv ≫
        ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber.map φ =
    (((etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv G H) φ).hom.app (op U) ≫
      ((pointSmallEtale t).ulift.{max (u + 1) v}).toPresheafFiber ((smallEtaleBaseChange g).obj U)
        (pointSmallEtaleBaseChangeLift.{u, v} g t U x) H.obj := by
  have h := toPresheafFiber_etaleAbelianInverseImageSheafFiberIso_inv_app.{u, v} g t G U x
  erw [reassoc_of% h]
  rw [Adjunction.homEquiv_unit]
  refine (Category.assoc _ _ _).trans ?_
  dsimp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_map]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  exact (Category.assoc _ _ _).symm

end InverseImageStalk

section Homology


/-- **The germ map on cohomology.** For a point `Φ` of the small étale site of `Z`, an étale
`Z`-scheme `V` with `y ∈ Φ(V)`, a complex `L` of abelian sheaves and `i : ℤ`, the map
`H^i(L(V)) ⟶ H^i(L_Φ) ≅ (H^i L)_Φ` induced by the germs at `(V, y)`, followed by the exactness
of the stalk functor. -/
def etaleAbelianSectionsHomologyToSheafFiber {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) v} Z.smallEtaleTopology) (V : Z.Etale)
    (y : Φ.fiber.obj V)
    (L : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) (i : ℤ) :
    ((((sheafSections Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (op V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology i ⟶
      Φ.sheafFiber.obj (L.homology i) :=
  HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
      (Φ.sheafSectionsToSheafFiber V y) (ComplexShape.up ℤ)).app L) i ≫
    (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso Φ.sheafFiber
      (ComplexShape.up ℤ) i).hom.app L

/-- The germ map on cohomology is natural in the complex. -/
@[reassoc]
theorem etaleAbelianSectionsHomologyToSheafFiber_naturality {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) v} Z.smallEtaleTopology) (V : Z.Etale)
    (y : Φ.fiber.obj V)
    {L L' : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (φ : L ⟶ L') (i : ℤ) :
    etaleAbelianSectionsHomologyToSheafFiber.{u, v} Φ V y L i ≫
        Φ.sheafFiber.map (HomologicalComplex.homologyMap φ i) =
      HomologicalComplex.homologyMap ((((sheafSections Z.smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) i ≫
        etaleAbelianSectionsHomologyToSheafFiber.{u, v} Φ V y L' i := by
  have h := (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso Φ.sheafFiber
    (ComplexShape.up ℤ) i).hom.naturality φ
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h
  rw [etaleAbelianSectionsHomologyToSheafFiber, etaleAbelianSectionsHomologyToSheafFiber]
  refine (Category.assoc _ _ _).trans ?_
  erw [← h]
  rw [HomologicalComplex.homologyFunctor_map]
  erw [← HomologicalComplex.homologyMap_comp_assoc, ← HomologicalComplex.homologyMap_comp_assoc]
  congr 2
  exact ((NatTrans.mapHomologicalComplex (Φ.sheafSectionsToSheafFiber V y)
    (ComplexShape.up ℤ)).naturality φ).symm

variable {S T : Scheme.{u}} (g : T ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (.of Ω) ⟶ T)

/-- **The coprojection of `H^i(K(U))` into the stalk of `H^i(g^* K)` at `t`.** For a complex `K` of
abelian sheaves on `S`, an étale neighbourhood `(U, u)` of `t ≫ g` and `i : ℤ`, the map
`H^i(K(U)) ⟶ H^i((g^* K)(U ×_S T)) ⟶ (H^i(g^* K))_t` given by the unit `K ⟶ g_* g^* K` and the
germs at the étale neighbourhood `(U ×_S T, (u, t))` of `t`. -/
def etaleAbelianInverseImageSectionsHomologyToSheafFiber
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (U : S.Etale) (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) (i : ℤ) :
    ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (op U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ⟶
      ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber.obj
        ((((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology i) :=
  HomologicalComplex.homologyMap ((((sheafSections S.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit
          (ComplexShape.up ℤ)).app K)) i ≫
    etaleAbelianSectionsHomologyToSheafFiber.{u, v} ((pointSmallEtale t).ulift.{max (u + 1) v})
      ((smallEtaleBaseChange g).obj U) (pointSmallEtaleBaseChangeLift.{u, v} g t U x)
      (((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) i

/-- **The coprojection is the germ at `(U, u)` read through `(g^* K)_t ≅ K_{t ≫ g}`.** The map
`etaleAbelianInverseImageSectionsHomologyToSheafFiber` is `H^i` of the germs at the étale
neighbourhood `(U, u)` of `t ≫ g`, followed by the identification of the stalks of an inverse
image `K_{t ≫ g} ≅ (g^* K)_t` (`etaleAbelianInverseImageSheafFiberIso`) and the exactness of the
stalk functor at `t`. -/
@[weil "lem_fk106_base_change_at_geometric_point_stalk"]
theorem etaleAbelianInverseImageSectionsHomologyToSheafFiber_eq
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (U : S.Etale) (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) (i : ℤ) :
    etaleAbelianInverseImageSectionsHomologyToSheafFiber.{u, v} g t K U x i =
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
          (((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).sheafSectionsToSheafFiber U x)
            (ComplexShape.up ℤ)).app K) i ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
          (etaleAbelianInverseImageSheafFiberIso.{u, v} g t).inv (ComplexShape.up ℤ)).app K) i ≫
        (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
          ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber (ComplexShape.up ℤ) i).hom.app
            (((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) := by
  rw [etaleAbelianInverseImageSectionsHomologyToSheafFiber,
    etaleAbelianSectionsHomologyToSheafFiber]
  erw [← HomologicalComplex.homologyMap_comp_assoc, ← HomologicalComplex.homologyMap_comp_assoc]
  congr 2
  ext j : 1
  exact (toPresheafFiber_etaleAbelianInverseImageSheafFiberIso_inv_app.{u, v} g t (K.X j) U x).symm

/-- The adjoint `φ^♭ = g_*(φ) ∘ η_K : K ⟶ g_* L` of a morphism of complexes `φ : g^* K ⟶ L`, for
the adjunction `g^* ⊣ g_*` applied degreewise. -/
def etaleAbelianInverseImageComplexAdjoint
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {L : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (φ : ((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      L) :
    K ⟶ ((etaleAbelianDirectImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  (NatTrans.mapHomologicalComplex (etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit
      (ComplexShape.up ℤ)).app K ≫
    ((etaleAbelianDirectImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).map φ

/-- In degree `j`, the adjoint of `φ` is the adjoint `g_*(φ^j) ∘ η_{K^j}` of `φ^j`. -/
theorem etaleAbelianInverseImageComplexAdjoint_f
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {L : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (φ : ((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (j : ℤ) :
    (etaleAbelianInverseImageComplexAdjoint.{u, v} g K φ).f j =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _ (φ.f j) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **The stalk at `t` of `H^i` of a morphism out of an inverse image, on coprojections.** For a
morphism of complexes `φ : g^* K ⟶ L`, the stalk at `t` of `H^i(φ)`, composed with the coprojection
of `H^i(K(U))` at an étale neighbourhood `(U, u)` of `t ≫ g`, is `H^i` of the adjoint
`φ^♭ : K ⟶ g_* L` on sections over `U`, followed by the coprojection of
`H^i(L(U ×_S T))` at `(U ×_S T, (u, t))`. -/
theorem etaleAbelianInverseImageSectionsHomologyToSheafFiber_sheafFiber_map
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {L : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (φ : ((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (U : S.Etale) (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) (i : ℤ) :
    etaleAbelianInverseImageSectionsHomologyToSheafFiber.{u, v} g t K U x i ≫
      ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber.map
        (HomologicalComplex.homologyMap φ i) =
    HomologicalComplex.homologyMap ((((sheafSections S.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaleAbelianInverseImageComplexAdjoint.{u, v} g K φ)) i ≫
      etaleAbelianSectionsHomologyToSheafFiber.{u, v} ((pointSmallEtale t).ulift.{max (u + 1) v})
        ((smallEtaleBaseChange g).obj U) (pointSmallEtaleBaseChangeLift.{u, v} g t U x) L i := by
  rw [etaleAbelianInverseImageSectionsHomologyToSheafFiber]
  refine (Category.assoc _ _ _).trans ?_
  erw [etaleAbelianSectionsHomologyToSheafFiber_naturality.{u, v}]
  erw [← HomologicalComplex.homologyMap_comp_assoc]
  rw [etaleAbelianInverseImageComplexAdjoint, Functor.map_comp]
  rfl

end Homology

section BaseChange

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (.of Ω) ⟶ T)

/-- **The base change morphism on sections.** For a complex `I` of abelian sheaves on `X` and a
morphism of complexes `q : g'^* I ⟶ J` on `X_T = X ×_S T`, the adjoint
`f_* I ⟶ g_* f'_* J` of the base change morphism `γ : g^* f_* I ⟶ f'_* J` for `(f, g)`. On
sections over an étale `U ⟶ S` it is a morphism of complexes
`I^•(X ×_S U) ⟶ J^•(X_T ×_T (U ×_S T))`. -/
def etaleAbelianPullbackResolutionBaseChangeAdjoint
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    ((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      ((etaleAbelianDirectImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleAbelianDirectImage.{u, v} (pullback.snd f g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) :=
  etaleAbelianInverseImageComplexAdjoint.{u, v} g
    (((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q)

/-- **The adjoint of the base change map followed by a morphism.** For an abelian sheaf `F` on `X`
and `φ : g'^* F ⟶ H`, the adjoint of `f'_*(φ) ∘ β_F : g^* f_* F ⟶ f'_* H` for `g^* ⊣ g_*` is
`g_* f'_*(φ) ∘ c ∘ f_*(η^{g'}_F)`: on sections over an étale `U ⟶ S`, the map
`F(X ×_S U) ⟶ (g'^* F)(X ×_S U_T)` underlying the unit of `g'^* ⊣ g'_*` for the étale `X`-scheme
`X ×_S U`, read through the identification `c` of `X_T ×_X (X ×_S U)` with `X_T ×_T U_T`,
followed by `φ`. -/
@[weil "lem_fk106_base_change_at_geometric_point_stalk"]
theorem etaleAbelianInverseImageDirectImageAdj_homEquiv_baseChange_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    {H : Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (φ : (etaleAbelianInverseImage.{u, v} (pullback.fst f g)).obj F ⟶ H) :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _
        ((etaleAbelianBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
          pullback.condition).app F ≫ (etaleAbelianDirectImage.{u, v} (pullback.snd f g)).map φ) =
      (etaleAbelianDirectImage.{u, v} f).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, v} (pullback.fst f g)).unit.app F) ≫
        (etaleAbelianDirectImageSquareIso.{u, v} f g (pullback.fst f g) (pullback.snd f g)
          pullback.condition).hom.app ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).obj F) ≫
        (etaleAbelianDirectImage.{u, v} g).map
          ((etaleAbelianDirectImage.{u, v} (pullback.snd f g)).map φ) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, etaleAbelianBaseChange_unit_assoc]

/-- **The base change morphism on sections, degreewise.** In degree `j`, the adjoint of the base
change morphism `γ` for `(f, g)` is the adjoint of `γ^j = f'_*(q^j) ∘ β_{I^j}`
(`etaleAbelianResolutionBaseChange_f`), which is `g_* f'_*(q^j) ∘ c ∘ f_*(η^{g'}_{I^j})` by
`etaleAbelianInverseImageDirectImageAdj_homEquiv_baseChange_comp`. -/
@[weil "lem_fk106_base_change_at_geometric_point_stalk"]
theorem etaleAbelianPullbackResolutionBaseChangeAdjoint_f
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) (j : ℤ) :
    (etaleAbelianPullbackResolutionBaseChangeAdjoint.{u, v} f g I q).f j =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv
        ((((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).X j)
        _
        ((etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q).f j) := by
  have h₂ : etaleAbelianPullbackResolutionBaseChangeAdjoint.{u, v} f g I q =
      etaleAbelianInverseImageComplexAdjoint.{u, v} g
        (((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q) := rfl
  rw [h₂, etaleAbelianInverseImageComplexAdjoint_f]

/-- **The stalk at a geometric point of the base change homomorphism** (Freitag–Kiehl I.6). Let
`t : Spec Ω ⟶ T` be a geometric point, `(U, u)` an étale neighbourhood of `s = t ≫ g` and
`(U_T, u_T) = (U ×_S T, (u, t))` the induced étale neighbourhood of `t`. Then the stalk at `t` of
the base change homomorphism `β^i : H^i(g^* f_* I) ⟶ H^i(f'_* J)` for `(f, g)`, composed with the
coprojection `H^i(I^•(X ×_S U)) ⟶ (H^i(g^* f_* I))_t` at `(U, u)`, is the map
`h_U : H^i(I^•(X ×_S U)) ⟶ H^i(J^•(X_T ×_T U_T))` induced by the base change morphism on
sections (`etaleAbelianPullbackResolutionBaseChangeAdjoint_f`), followed by the coprojection
`H^i(J^•(X_T ×_T U_T)) ⟶ (H^i(f'_* J))_t` at `(U_T, u_T)`. -/
@[weil "lem_fk106_base_change_at_geometric_point_stalk"]
theorem etaleAbelianInverseImageSectionsHomologyToSheafFiber_sheafFiber_map_higherBaseChange
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (U : S.Etale) (x : ((pointSmallEtale (t ≫ g)).ulift.{max (u + 1) v}).fiber.obj U) (i : ℤ) :
    etaleAbelianInverseImageSectionsHomologyToSheafFiber.{u, v} g t
        (((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        U x i ≫
      ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber.map
        (etaleAbelianPullbackResolutionHigherBaseChange.{u, v} f g I q i) =
    HomologicalComplex.homologyMap ((((sheafSections S.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaleAbelianPullbackResolutionBaseChangeAdjoint.{u, v} f g I q)) i ≫
      etaleAbelianSectionsHomologyToSheafFiber.{u, v} ((pointSmallEtale t).ulift.{max (u + 1) v})
        ((smallEtaleBaseChange g).obj U) (pointSmallEtaleBaseChangeLift.{u, v} g t U x)
        (((etaleAbelianDirectImage.{u, v} (pullback.snd f g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) i := by
  have h₁ : ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber.map
      (etaleAbelianPullbackResolutionHigherBaseChange.{u, v} f g I q i) =
      ((pointSmallEtale t).ulift.{max (u + 1) v}).sheafFiber.map
        (HomologicalComplex.homologyMap
          (K := ((etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
          (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q) i) := rfl
  have h₂ : etaleAbelianPullbackResolutionBaseChangeAdjoint.{u, v} f g I q =
      etaleAbelianInverseImageComplexAdjoint.{u, v} g
        (((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q) := rfl
  rw [h₁, h₂]
  exact etaleAbelianInverseImageSectionsHomologyToSheafFiber_sheafFiber_map.{u, v} g t
    (((etaleAbelianDirectImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q) U x i

end BaseChange

end Stacks.EtaleCohomology
