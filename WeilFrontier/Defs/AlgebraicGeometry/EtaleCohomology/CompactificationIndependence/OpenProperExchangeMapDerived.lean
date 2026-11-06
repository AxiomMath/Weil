module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import Mathlib.Algebra.Homology.Additive
public import Weil.Attr

/-!
# The exchange chain map `j_! f_* (J|_X) ⟶ f'_* J`

Consider a commutative square of schemes
```
  X --i--> X'
  |        |
  f        f'
  v        v
  Y --j--> Y'
```
with `i` and `j` open immersions and `f` proper. For a sheaf `G` of `Λ`-modules on the small étale
site of `X`, an exchange morphism `α_G : j_! f_* G ⟶ f'_* i_! G` is defined in
`AlgebraicGeometry.IsOpenProperExchangeMorphism`. For a sheaf `G` on the small étale site of `X'`
let `ε_G : i_! (G|_X) ⟶ G` be the morphism whose composite with the canonical map
`c : P_i (G|_X) ⟶ i_! (G|_X)` from the direct-sum presheaf is, on the summand indexed by
`φ : W ⟶ X`, the identity of `(G|_X)(W, φ) = G(W)`; it is the counit of the adjunction
`i_! ⊣ (-)|_X`.

For a complex `J` of sheaves of `Λ`-modules on the small étale site of `X'` (in the source, a
bounded-below injective resolution of `i_! F`), the *exchange chain map* is
`θ_J = (f'_*(ε^n) ∘ α^n)_n : j_! f_* (J|_X) ⟶ f'_* J`, with `α^n = α_{J^n|_X}` and
`ε^n = ε_{J^n}`. It represents the morphism `j_! Rf_* F ⟶ Rf'_* i_! F` of derived categories.

## Main definitions

* `AlgebraicGeometry.exchangeCounitTransformation`: the transformation
  `θ_G = f'_*(ε_G) ∘ α_{G|_X} : j_! f_* (G|_X) ⟶ f'_* G`, natural in `G`.
* `AlgebraicGeometry.exchangeChainMap`: the exchange chain map `θ_J`.

## Main results

* `AlgebraicGeometry.etaleModuleExtensionByZeroAdj_counit_app_apply`: the counit `ε_G` sends the
  section `[φ, s]` of the direct-sum presheaf to `s`.
* `AlgebraicGeometry.exchangeChainMap_f`: in degree `n`, `θ_J` is `f'_*(ε^n) ∘ α^n`.
* `AlgebraicGeometry.exchangeChainMap_naturality`: `θ_J` is natural in `J`.

## Implementation notes

The objects live on Mathlib's small étale site `X.Etale`, where the extension by zero
`Stacks.EtaleCohomology.etaleModuleExtensionByZero`, the restriction
`Stacks.EtaleCohomology.etaleModuleRestriction` and the direct image
`Stacks.EtaleCohomology.etaleModuleDirectImage` are defined, as for
`AlgebraicGeometry.IsOpenProperExchangeMorphism`; the source's abelian sheaves are the case
`Λ = ℤ`.

The exchange morphisms enter as a natural transformation `α : j_! f_* ⟶ f'_* i_!`: in the
situation of the source the exchange morphisms exist, are unique and are natural in the sheaf, and
the exchange chain map is the case where every component of `α` is an exchange morphism. The
construction uses neither this property nor the hypotheses on the square, so it is stated for an
arbitrary natural transformation `α`, étale `i`, `j` and arbitrary `f`, `f'`. The naturality of
`α` makes `θ_J` a chain map. The complex `J` is arbitrary, of any shape; the resolution
`i_! F ⟶ J` the source fixes does not enter the definition of `θ_J`, only its interpretation in
the derived category.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.5, p. 88.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology

universe r u

namespace AlgebraicGeometry

section Counit

variable (Λ : Type r) [Ring Λ] {X X' : Scheme.{u}} (i : X ⟶ X') [Etale i]

/-- The unit `M ⟶ (i_! M)|_X` of the adjunction `i_! ⊣ (-)|_X` is, over `U`, the unit of the
left Kan extension followed by the map to the sheafification. -/
theorem etaleModuleExtensionByZeroAdj_unit_app_hom_app (M : EtaleModules.{u, r} Λ X)
    (U : X.Etale) :
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app M).hom.app (op U) =
      ((smallEtaleCompose i).op.lanUnit.app M.obj).app (op U) ≫
        (toSheafify X'.smallEtaleTopology ((smallEtaleCompose i).op.lan.obj M.obj)).app
          (op ((smallEtaleCompose i).obj U)) := by
  have := congr_arg (fun g => g.app (op U))
    (Adjunction.map_restrictFullyFaithful_unit_app
      (((smallEtaleCompose i).op.lanAdjunction (ModuleCat.{max (u + 1) r} Λ)).comp
        (sheafificationAdjunction X'.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)))
      (fullyFaithfulSheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
      (Functor.FullyFaithful.id _) (L := etaleModuleExtensionByZero.{u, r} Λ i)
      (R := etaleModuleRestriction.{u, r} Λ i) (Iso.refl _) (Iso.refl _) M)
  simp only [etaleModuleExtensionByZeroAdj,
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  refine this.trans ?_
  congr 1

/-- The canonical map `c : P_i M ⟶ i_! M` on the summand indexed by `φ : W ⟶ X` is the unit of
`i_! ⊣ (-)|_X` over `(W, φ)`, transported to `W`. -/
theorem ι_comp_extensionByZeroPresheafToSheaf_app (M : EtaleModules.{u, r} Λ X) (W : X'.Etale)
    (φ : W ⟶ smallEtaleSource i) :
    (Sigma.ι (fun ψ : W ⟶ smallEtaleSource i => M.obj.obj (op (sourceDescend i ψ))) φ :
        M.obj.obj (op (sourceDescend i φ)) ⟶ (etaleExtensionByZeroPresheaf i M).obj (op W)) ≫
        (extensionByZeroPresheafToSheaf Λ i M).app (op W) =
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app M).hom.app (op (sourceDescend i φ)) ≫
        ((etaleModuleExtensionByZero.{u, r} Λ i).obj M).obj.map (sourceDescendIso i φ).inv.op := by
  rw [etaleModuleExtensionByZeroAdj_unit_app_hom_app]
  erw [Category.assoc]
  have hn := (toSheafify X'.smallEtaleTopology ((smallEtaleCompose i).op.lan.obj M.obj)).naturality
    (sourceDescendIso i φ).inv.op
  erw [← hn]
  have hV : Sigma.ι (fun ψ : W ⟶ smallEtaleSource i => M.obj.obj (op (sourceDescend i ψ))) φ ≫
      (extensionByZeroPresheafSectionIso i M.obj W).hom =
        extensionByZeroSummandInclusion i M.obj φ :=
    Sigma.ι_desc (fun ψ => extensionByZeroSummandInclusion i M.obj ψ) φ
  have hS : extensionByZeroSummandInclusion i M.obj φ =
      ((smallEtaleCompose i).op.lanUnit.app M.obj).app (op (sourceDescend i φ)) ≫
        ((smallEtaleCompose i).op.lan.obj M.obj).map (sourceDescendIso i φ).inv.op := rfl
  erw [← reassoc_of% hS, ← reassoc_of% hV]
  simp only [extensionByZeroPresheafToSheaf, etaleModuleExtensionByZeroObjIso,
    etaleModuleExtensionByZeroIsoSheafifyDirectSum]
  have key : toSheafify X'.smallEtaleTopology (etaleExtensionByZeroPresheaf i M) ≫
      (((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).isoWhiskerLeft
        (Functor.isoWhiskerRight (lanIsoExtensionByZeroDirectSum i)
          (presheafToSheaf X'.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)))).app M).inv.hom =
      (lanIsoExtensionByZeroDirectSum i).inv.app M.obj ≫
        toSheafify X'.smallEtaleTopology ((smallEtaleCompose i).op.lan.obj M.obj) :=
    (toSheafify_naturality _ _).symm
  erw [key]
  rfl

/-- The composite of the canonical map `c : P_i (G|_X) ⟶ i_! (G|_X)` with the counit
`ε : i_! (G|_X) ⟶ G`, on the summand indexed by `φ : W ⟶ X`, is the identification
`(G|_X)(W, φ) = G(W)`. -/
theorem ι_comp_extensionByZeroPresheafToSheaf_app_comp_counit (G : EtaleModules.{u, r} Λ X')
    (W : X'.Etale) (φ : W ⟶ smallEtaleSource i) :
    Sigma.ι (fun ψ : W ⟶ smallEtaleSource i =>
        ((etaleModuleRestriction.{u, r} Λ i).obj G).obj.obj (op (sourceDescend i ψ))) φ ≫
      (extensionByZeroPresheafToSheaf Λ i ((etaleModuleRestriction.{u, r} Λ i).obj G)).app (op W) ≫
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.app (op W) =
      G.obj.map (sourceDescendIso i φ).inv.op := by
  erw [← Category.assoc, ι_comp_extensionByZeroPresheafToSheaf_app, Category.assoc]
  erw [((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.naturality]
  erw [← Category.assoc]
  have ht := congr_arg (fun g => g.hom.app (op (sourceDescend i φ)))
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).right_triangle_components G)
  refine Eq.trans (congr_arg (· ≫ G.obj.map (sourceDescendIso i φ).inv.op) ht) ?_
  exact Category.id_comp _

/-- The counit `ε : i_! (G|_X) ⟶ G` sends the section `[φ, s]` of the direct-sum presheaf, for
`s ∈ (G|_X)(W, φ) = G(W)`, to `s` itself. -/
@[weil "def_fk108_open_proper_exchange_map_derived"]
theorem etaleModuleExtensionByZeroAdj_counit_app_apply (G : EtaleModules.{u, r} Λ X')
    (W : X'.Etale) (φ : W ⟶ smallEtaleSource i)
    (s : ((etaleModuleRestriction.{u, r} Λ i).obj G).obj.obj (op (sourceDescend i φ))) :
    (((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.app (op W)).hom
        (((extensionByZeroPresheafToSheaf Λ i ((etaleModuleRestriction.{u, r} Λ i).obj G)).app
          (op W)).hom ((Sigma.ι (fun ψ : W ⟶ smallEtaleSource i =>
            ((etaleModuleRestriction.{u, r} Λ i).obj G).obj.obj (op (sourceDescend i ψ))) φ).hom
              s)) =
      (G.obj.map (sourceDescendIso i φ).inv.op).hom s :=
  congr_arg (fun g => g.hom s) (ι_comp_extensionByZeroPresheafToSheaf_app_comp_counit Λ i G W φ)

end Counit

section ExchangeChainMap

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') [Etale i]
  (j : Y ⟶ Y') [Etale j] {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The transformation `θ : j_! f_* (G|_X) ⟶ f'_* G`, natural in the sheaf `G` of `Λ`-modules on
the small étale site of `X'`, attached to a natural transformation `α : j_! f_* ⟶ f'_* i_!`: the
component of `α` at `G|_X` followed by `f'_*` of the counit `ε : i_! (G|_X) ⟶ G`. -/
def exchangeCounitTransformation
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f') :
    etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f ⋙
        etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleDirectImage.{u, r} Λ f' :=
  Functor.whiskerLeft (etaleModuleRestriction.{u, r} Λ i) α ≫
    Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit
      (etaleModuleDirectImage.{u, r} Λ f') ≫ (Functor.leftUnitor _).hom

/-- The component of `θ` at `G` is `f'_*(ε_G) ∘ α_{G|_X}`. -/
theorem exchangeCounitTransformation_app
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (G : EtaleModules.{u, r} Λ X') :
    (exchangeCounitTransformation Λ i j α).app G =
      α.app ((etaleModuleRestriction.{u, r} Λ i).obj G) ≫
        (etaleModuleDirectImage.{u, r} Λ f').map
          ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G) := by
  simp [exchangeCounitTransformation]

/-- The *exchange chain map* `θ_J : j_! f_* (J|_X) ⟶ f'_* J` of a complex `J` of sheaves of
`Λ`-modules on the small étale site of `X'`, attached to a natural transformation
`α : j_! f_* ⟶ f'_* i_!`: in degree `n` it is `f'_*(ε^n) ∘ α^n`, where
`α^n : j_! f_* (J^n|_X) ⟶ f'_* i_! (J^n|_X)` is the component of `α` and
`ε^n : i_! (J^n|_X) ⟶ J^n` is the counit of `i_! ⊣ (-)|_X`
(`AlgebraicGeometry.etaleModuleExtensionByZeroAdj_counit_app_apply`). For `α` the exchange morphisms
(`AlgebraicGeometry.IsOpenProperExchangeMorphism`) and `J` an injective resolution of `i_! F`
this is the exchange chain map of the source. -/
@[weil "def_fk108_open_proper_exchange_map_derived"]
def exchangeChainMap
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {ι : Type*} {c : ComplexShape ι} (J : HomologicalComplex (EtaleModules.{u, r} Λ X') c) :
    ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f ⋙
        etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex c).obj J ⟶
      ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex c).obj J :=
  (NatTrans.mapHomologicalComplex (exchangeCounitTransformation Λ i j α) c).app J

/-- In degree `n` the exchange chain map is `f'_*(ε^n) ∘ α^n`. -/
@[weil "def_fk108_open_proper_exchange_map_derived"]
theorem exchangeChainMap_f
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {ι : Type*} {c : ComplexShape ι} (J : HomologicalComplex (EtaleModules.{u, r} Λ X') c)
    (n : ι) :
    (exchangeChainMap Λ i j α J).f n =
      α.app ((etaleModuleRestriction.{u, r} Λ i).obj (J.X n)) ≫
        (etaleModuleDirectImage.{u, r} Λ f').map
          ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app (J.X n)) :=
  exchangeCounitTransformation_app Λ i j α (J.X n)

/-- The exchange chain map is natural in the complex `J`. -/
theorem exchangeChainMap_naturality
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {ι : Type*} {c : ComplexShape ι} {J J' : HomologicalComplex (EtaleModules.{u, r} Λ X') c}
    (h : J ⟶ J') :
    ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f ⋙
        etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex c).map h ≫
        exchangeChainMap Λ i j α J' =
      exchangeChainMap Λ i j α J ≫
        ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex c).map h :=
  NatTrans.mapHomologicalComplex_naturality _ h

end ExchangeChainMap

end AlgebraicGeometry
