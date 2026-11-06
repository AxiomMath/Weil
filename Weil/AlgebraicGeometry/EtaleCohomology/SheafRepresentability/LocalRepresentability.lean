module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import Weil.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SectionsMorphismSurjectiveGeneric
public import Weil.AlgebraicGeometry.EtaleCohomology.SectionsMorphismInjectiveNearPoint
public import Weil.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Étale-local representability of étale sheaves

Let `X` be a noetherian separated scheme and `G` an étale sheaf of sets on `X`. Then `G` is
representable by a noetherian separated étale `X`-scheme if and only if every geometric point
`x` of `X` has an étale neighbourhood `(U, u)`, with `U` noetherian and separated, such that the
restriction `G|_U` is representable in the étale category of `U`.

The "only if" direction takes `(U, u) = (X, x)`. For the "if" direction, the local representing
objects `Y_x ⟶ U_x` are étale and separated morphisms with noetherian source, hence quasi-affine
(Stacks 02LR). Since a map into a representable sheaf is determined by the section it pulls back,
the local representatives come with canonical transition isomorphisms over the overlaps
`U_x × U_y`, satisfying the cocycle condition, i.e. a descent datum relative to the étale covering
`{U_x ⟶ X}`. This datum is effective by descent of quasi-affine morphisms along fpqc coverings
(Stacks 0247), and the descended scheme `W ⟶ X` is étale, quasi-compact and separated because these
properties are fpqc local on the target; as `X` is noetherian and separated, `W` is noetherian and
separated. The local isomorphisms `G|_{U_x} ≅ W̃|_{U_x}` agree on overlaps and glue to `G ≅ W̃`.

## Main results

* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_forall_exists_restrictIsRepresentableInEt`:
  the "if" direction.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_iff_forall_exists_restrictIsRepresentableInEt`:
  a sheaf of sets on the small étale site of a noetherian separated scheme is representable if
  and only if it is so étale-locally around every geometric point.

## Implementation notes

The statement is on the small étale site `SmallEtale B X hX` of a big étale site, with geometric
points over algebraically closed fields; an étale neighbourhood `(U, u)` of a geometric point
`x : Spec k ⟶ X` is an object `U` together with a lift `u : Spec k ⟶ U` of `x`. The restriction
`G|_U` is restriction along composition with `U ⟶ X`.

The descent argument is the one of Stacks 03RV for finite étale representing objects, whose
construction of the descent datum, of its chart and of the glued isomorphism is reused verbatim;
what changes is the effectivity theorem (Stacks 0247 for quasi-affine morphisms in place of 0245
for affine ones) and the properties read off the descended morphism. The construction works with
sheaves valued in `Type (u + 1)`, so the sheaf is first composed with `uliftFunctor`.

The proof does not choose finitely many neighbourhoods, as the source does: the family of all
neighbourhoods is an étale covering of `X`, and the descent theorem applies to coverings indexed by
any type.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.18
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- A morphism property which is fpqc local on the target and holds for every component of a
descent datum holds for the structure morphism of any scheme whose canonical descent datum is
isomorphic to it. -/
theorem DescentData.prop_hom_of_iso_canonical {S : Scheme.{u}} {I : Type v}
    {Z : I → Scheme.{u}} (f : ∀ i, Z i ⟶ S)
    (hf : Presieve.ofArrows Z f ∈ Scheme.fpqcPrecoverage S)
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    {D : DescentData f} (U : Over S) (e : (canonicalFamilyDescentFunctor f).functor.obj U ≅ D)
    (hD : ∀ i, P (D.obj i).hom) : P U.hom := by
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hf
  intro V g _ hmem
  obtain ⟨j⟩ := hmem
  have : IsIso (e.hom.hom j) := (DescentData.evaluation j).map_isIso e.hom
  have : IsIso (e.hom.hom j).left := (Over.forget (Z j)).map_isIso (e.hom.hom j)
  change P ((Over.pullback (f j)).obj U).hom
  rw [← (canonicalFamilyDescentFunctor f).obj U j, ← Over.w (e.hom.hom j)]
  exact MorphismProperty.RespectsIso.precomp P _ _ (hD j)

/-- The source of a separated morphism into a separated scheme is separated. -/
theorem Scheme.isSeparated_of_isSeparated_hom {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Z.IsSeparated]
    [IsSeparated f] : Y.IsSeparated :=
  ⟨by rw [show terminal.from Y = f ≫ terminal.from Z from terminal.hom_ext _ _]; infer_instance⟩

/-- The source of a morphism of finite type into a noetherian scheme is noetherian. -/
theorem Scheme.isNoetherian_of_locallyOfFiniteType_of_quasiCompact {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsNoetherian Z] [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian Y :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A scheme étale and quasi-compact over `X` is an object of the small étale site of `X`. -/
theorem exists_iso_smallEtaleToOver (U : Over X) [Etale U.hom] [QuasiCompact U.hom] :
    ∃ W : SmallEtale B X hX, Nonempty ((smallEtaleToOver B (B.obj X hX)).obj W ≅ U) := by
  let U' : B.Scheme :=
    B.obj U.left (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact U.hom hX)
  let g : U' ⟶ B.obj X hX := B.inclusion.preimage (U.hom : B.inclusion.obj U' ⟶ _)
  have hg : B.inclusion.map g = U.hom := B.inclusion.map_preimage _
  refine ⟨⟨Over.mk g, ?_⟩, ⟨Over.isoMk (Iso.refl _) ?_⟩⟩
  · change Etale (B.inclusion.map g)
    rw [hg]
    infer_instance
  · change 𝟙 _ ≫ U.hom = B.inclusion.map g
    rw [hg, Category.id_comp]

/-- A family of objects of the small étale site of `X` whose images cover `X` covers the final
object. -/
theorem ofArrows_mem_topology_final {I : Type*} (V : I → SmallEtale B X hX)
    (h : ∀ x : X, ∃ i, x ∈ Set.range (B.inclusion.map (V i).obj.hom)) :
    Sieve.ofArrows V (fun i ↦ (finalIsTerminal B X hX).from (V i)) ∈
      SmallEtale.topology B X hX (SmallEtale.final B X hX) := by
  apply mem_topology_of_jointlySurjective
  intro x
  obtain ⟨i, hi⟩ := h x
  refine ⟨V i, _, Sieve.ofArrows_mk _ _ i, ?_⟩
  have : (SmallEtale.toScheme B X hX).map ((finalIsTerminal B X hX).from (V i)) =
      B.inclusion.map (V i).obj.hom := by
    have := Over.w ((finalIsTerminal B X hX).from (V i)).hom
    simpa [SmallEtale.final] using congrArg B.inclusion.map this
  rw [this]
  exact hi

/-- **A local representative in the slice.** If the restriction of a sheaf `F` to the small étale
site of an object `V` is represented by `Y`, then the restriction of `F` (composed with
`uliftFunctor`) to the localized site at `V` is represented by the image of `Y` in the slice
`Over V`. -/
theorem nonempty_over_iso_uliftYoneda_of_restrict
    (F : Sheaf (SmallEtale.topology B X hX) (Type u)) (V : SmallEtale B X hX)
    (Y : SmallEtale B V.obj.left.1 V.obj.left.property)
    (eY : (representedSheaf Y).obj ≅ (smallEtalePostcompose B X hX V).op ⋙ F.obj) :
    Nonempty (((sheafCompose (SmallEtale.topology B X hX) uliftFunctor.{u + 1, u}).obj F).over V ≅
      ((SmallEtale.topology B X hX).over V).uliftYoneda.{u + 1}.obj
        ((smallEtaleEquivalenceOver B X hX V).functor.obj Y)) := by
  let e := smallEtaleEquivalenceOver B X hX V
  let JV := SmallEtale.topology B V.obj.left.1 V.obj.left.property
  let K := (SmallEtale.topology B X hX).over V
  let cg := e.sheafCongr JV K (Type (u + 1))
  have hrestr : cg.inverse.obj
      (((sheafCompose (SmallEtale.topology B X hX) uliftFunctor.{u + 1, u}).obj F).over V) ≅
      JV.uliftYoneda.{u + 1}.obj Y :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (Functor.isoWhiskerRight eY.symm uliftFunctor)
  have hy : cg.inverse.obj (K.uliftYoneda.{u + 1}.obj (e.functor.obj Y)) ≅
      JV.uliftYoneda.{u + 1}.obj Y :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Stacks.EtaleCohomology.restrictedUliftYonedaIso e.functor Y)
  exact ⟨cg.inverse.preimageIso (hrestr ≪≫ hy.symm)⟩

/-- An étale separated morphism with noetherian source is quasi-affine (Stacks 02LR). -/
theorem isQuasiAffineHom_of_etale_of_isNoetherian {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Etale f]
    [IsNoetherian Y] [Y.IsSeparated] : IsQuasiAffineHom f := by
  have := (locallyQuasiFinite_of_etale f).2
  exact isQuasiAffineHom_of_locallyQuasiFinite f

attribute [local implicit_reducible] Stacks.EtaleCohomology.descentDataOfTransitions
  Stacks.EtaleCohomology.localRepresentativesDescentData

/-- **Étale-local representability implies representability.** Let `X` be noetherian and
separated, and `F` a sheaf of sets on the small étale site of `X`. If every geometric point of `X`
has an étale neighbourhood `(U, u)` such that `F|_U` is representable in the étale category of
`U`, then `F` is representable. -/
theorem isRepresentableInEt_of_forall_exists_restrictIsRepresentableInEt
    [IsNoetherian X] [X.IsSeparated] (F : Sheaf (SmallEtale.topology B X hX) (Type u))
    (h : ∀ x : GeometricPoint X, ∃ (U : SmallEtale B X hX)
      (u : x.source ⟶ (SmallEtale.toScheme B X hX).obj U),
      u ≫ B.inclusion.map U.obj.hom = x.hom ∧ RestrictIsRepresentableInEt F.obj U) :
    IsRepresentableInEt F.obj := by
  classical
  let XB : B.Scheme := B.obj X hX
  let J := SmallEtale.topology B X hX
  let F' := (sheafCompose J uliftFunctor.{u + 1, u}).obj F
  choose V p hp hrep using h
  choose Y hY eY using hrep
  let A : ∀ x, Over (V x) := fun x ↦ (smallEtaleEquivalenceOver B X hX (V x)).functor.obj (Y x)
  let e : ∀ x, F'.over (V x) ≅ (J.over (V x)).uliftYoneda.{u + 1}.obj (A x) := fun x ↦
    (nonempty_over_iso_uliftYoneda_of_restrict F (V x) (Y x) (eY x).some).some
  have hcov := ofArrows_mem_topology_final V (fun x₀ ↦
    ⟨X.algClosedPoint x₀, p _ default, by
      rw [← Scheme.Hom.comp_apply, hp]
      exact Scheme.algClosedPointHom_apply X x₀ _⟩)
  have hfpqc := Stacks.EtaleCohomology.smallEtale_cover_isFpqc B XB V _ hcov
  let D := Stacks.EtaleCohomology.localRepresentativesDescentData B XB F' V A e
  have hYn : ∀ x, IsNoetherian (B.inclusion.obj (Y x).obj.left) := fun x ↦ (hY x).1
  have hYs : ∀ x, (B.inclusion.obj (Y x).obj.left).IsSeparated := fun x ↦ (hY x).2
  have hDet : ∀ x, Etale (D.obj x).hom := fun x ↦ (Y x).property
  have hDqa : ∀ x, IsQuasiAffineHom (D.obj x).hom := fun x ↦
    have := hYn x
    have := hYs x
    have : Etale (B.inclusion.map (Y x).obj.hom) := (Y x).property
    isQuasiAffineHom_of_etale_of_isNoetherian (B.inclusion.map (Y x).obj.hom)
  have hDqc : ∀ x, QuasiCompact (D.obj x).hom := fun x ↦
    have := hYn x
    inferInstanceAs (QuasiCompact (B.inclusion.map (Y x).obj.hom))
  have hDsep : ∀ x, IsSeparated (D.obj x).hom := fun x ↦
    have := hYs x
    inferInstanceAs (IsSeparated (B.inclusion.map (Y x).obj.hom))
  obtain ⟨U, ⟨d⟩⟩ := DescentData.isFamilyEffective_of_isQuasiAffineHom _ hfpqc D hDqa
  have hUet : Etale U.hom := DescentData.prop_hom_of_iso_canonical _ hfpqc @Etale U d hDet
  have hUqc : QuasiCompact U.hom :=
    DescentData.prop_hom_of_iso_canonical _ hfpqc @QuasiCompact U d hDqc
  have hUsep : IsSeparated U.hom :=
    DescentData.prop_hom_of_iso_canonical _ hfpqc @IsSeparated U d hDsep
  obtain ⟨W, ⟨w⟩⟩ := exists_iso_smallEtaleToOver (B := B) (hX := hX) U
  have hW : B.inclusion.map W.obj.hom = w.hom.left ≫ U.hom := (Over.w w.hom).symm
  have : IsIso w.hom.left := (Over.forget X).map_isIso w.hom
  have : IsNoetherian (B.inclusion.obj (B.obj X hX)) := ‹IsNoetherian X›
  have : (B.inclusion.obj (B.obj X hX)).IsSeparated := ‹X.IsSeparated›
  have hWqc : QuasiCompact (B.inclusion.map W.obj.hom) := by
    rw [hW]
    have : QuasiCompact w.hom.left := inferInstance
    exact MorphismProperty.comp_mem @QuasiCompact _ _ this hUqc
  have hWsep : IsSeparated (B.inclusion.map W.obj.hom) := by
    rw [hW]
    have : IsSeparated w.hom.left := inferInstance
    exact MorphismProperty.comp_mem @IsSeparated _ _ this hUsep
  have hWlft : LocallyOfFiniteType (B.inclusion.map W.obj.hom) := by
    have : Etale (B.inclusion.map W.obj.hom) := W.property
    infer_instance
  refine ⟨W, ⟨Scheme.isNoetherian_of_locallyOfFiniteType_of_quasiCompact
      (B.inclusion.map W.obj.hom), Scheme.isSeparated_of_isSeparated_hom
      (B.inclusion.map W.obj.hom)⟩, ⟨?_⟩⟩
  let iso : F' ≅ J.uliftYoneda.{u + 1}.obj W :=
    Stacks.EtaleCohomology.sheafIsoUliftYonedaOfChart B XB F' V A e
      (DescentData.Chart.ofIsoCanonicalDatum U d.symm) W w
      (Stacks.EtaleCohomology.coversTop_of_cover_final B XB V _ hcov)
  exact ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
    _).preimageIso ((sheafToPresheaf J _).mapIso iso.symm)

instance : Mono (SmallEtale.final B X hX).obj.hom :=
  inferInstanceAs (Mono (𝟙 _))

/-- **Representability implies étale-local representability**, with the neighbourhood `(X, x)`:
the restriction of a presheaf to the small étale site of the final object is the presheaf
itself. -/
theorem restrictIsRepresentableInEt_final {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (hF : IsRepresentableInEt F) : RestrictIsRepresentableInEt F (SmallEtale.final B X hX) := by
  obtain ⟨Y, hY, ⟨eY⟩⟩ := hF
  let G := smallEtalePostcompose B X hX (SmallEtale.final B X hX)
  let hG : G.FullyFaithful := .ofFullyFaithful G
  let eGY : G.obj Y ≅ Y :=
    ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Y.obj.hom = Y.obj.hom ≫ 𝟙 _
      simp))
  refine ⟨Y, hY, ⟨?_⟩⟩
  exact (uliftYonedaIsoYoneda.{u}.app Y).symm ≪≫ (hG.homNatIso Y).symm ≪≫
    Functor.isoWhiskerLeft G.op (uliftYonedaIsoYoneda.{u}.app (G.obj Y)) ≪≫
    Functor.isoWhiskerLeft G.op (yoneda.mapIso eGY) ≪≫ Functor.isoWhiskerLeft G.op eY

/-- **Representability is étale local** (FK I.3.18). Let `X` be a noetherian separated scheme and
`F` a sheaf of sets on the small étale site of `X`. Then `F` is representable by a noetherian
separated étale `X`-scheme if and only if every geometric point `x` of `X` has an étale
neighbourhood `(U, u)`, with `U` noetherian and separated, such that the restriction `F|_U` is
representable in the étale category of `U`. -/
@[weil "lem_fk103_representable_iff_locally_representable"]
theorem isRepresentableInEt_iff_forall_exists_restrictIsRepresentableInEt
    [IsNoetherian X] [X.IsSeparated] (F : Sheaf (SmallEtale.topology B X hX) (Type u)) :
    IsRepresentableInEt F.obj ↔
      ∀ x : GeometricPoint X, ∃ (U : SmallEtale B X hX)
        (u : x.source ⟶ (SmallEtale.toScheme B X hX).obj U),
        u ≫ B.inclusion.map U.obj.hom = x.hom ∧ IsNoetherianSeparated B X hX U ∧
          RestrictIsRepresentableInEt F.obj U := by
  refine ⟨fun hF x ↦ ⟨SmallEtale.final B X hX, x.hom, ?_, ⟨?_, ?_⟩,
    restrictIsRepresentableInEt_final hF⟩, fun h ↦
    isRepresentableInEt_of_forall_exists_restrictIsRepresentableInEt F fun x ↦ ?_⟩
  · change x.hom ≫ B.inclusion.map (𝟙 (B.obj X hX)) = x.hom
    simp
  · exact inferInstanceAs (IsNoetherian X)
  · exact inferInstanceAs X.IsSeparated
  · obtain ⟨U, u, hu, -, hU⟩ := h x
    exact ⟨U, u, hu, hU⟩

end SmallEtale

end AlgebraicGeometry

end

/-! ### Sheaves with finite stalks are representable near a generic point -/

/-!
# Sheaves with finite stalks are representable near a generic point

Let `X` be a locally noetherian scheme and `G` an étale sheaf of sets on `X` with finite stalks
and open difference loci. Let `x̄` be a geometric point of `X` over the generic point `η` of an
irreducible component of `X`, and let `m = |G_x̄|`. Then there is an étale neighbourhood
`(Y, ȳ)` of `x̄` with `Y` irreducible (and affine) such that the restriction `G|_Y` is isomorphic
to the sheaf `Ỹ^{⊔ m}` represented by the disjoint union of `m` copies of `Y` on the small étale
site of `Y`; in particular `G|_Y` is representable in `Et(Y)`.

The `m` elements of `G_x̄` are germs of sections `t_1, …, t_m` over one étale neighbourhood
`(V, v̄)`, as the neighbourhoods of `x̄` form a cofiltered category. The image `v₀` of `v̄` lies
over `η`, so a connected open neighbourhood of `v₀` in `V` has generic point `v₀`; an affine
open `Y` inside it containing `v₀` is irreducible with generic point `v₀`. The restrictions
`s_i = t_i|_Y` have pairwise distinct germs at the lift `ȳ` of `x̄`, and since the stalk of `G|_Y`
at `ȳ` is in bijection with `G_x̄`, they exhaust it. The morphism `Φ_s : Ỹ^{⊔ m} ⟶ G|_Y` defined
by `s` is then injective on sections because `Y` is connected, and surjective because `ȳ` lies
over the generic point of `Y`, hence an isomorphism.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.exists_toPresheafFiber_eq_of_finite`: finitely many
  elements of the fiber of a presheaf of sets at a point of a site come from sections over one
  object.
* `AlgebraicGeometry.SmallEtale.exists_restrict_iso_representedSheaf_disjointCopies`: the
  isomorphism `G|_Y ≅ Ỹ^{⊔ m}` on an irreducible affine étale neighbourhood `(Y, ȳ)` of `x̄`.
* `AlgebraicGeometry.SmallEtale.exists_restrictIsRepresentableInEt_of_hasFiniteStalks`: in
  particular `G|_Y` is representable in `Et(Y)`.

## Implementation notes

The statements are on the small étale site `AlgebraicGeometry.SmallEtale` of `X`, with
geometric points over algebraically closed fields; an étale neighbourhood of `x̄` is an object
`Y` with a lift `ȳ ∈ (geometricPointFiber B X hX x).obj Y`. The restriction `G|_Y` is the
direct image along `AlgebraicGeometry.smallEtalePostcompose`. The source assumes `X` noetherian;
local noetherianity is what the choice of the irreducible neighbourhood uses. The neighbourhood
is moreover chosen affine, so that it and the disjoint union `Y^{⊔ m}` are noetherian and
separated, as representability in `Et(Y)` requires. The number of copies is `Nat.card` of the
stalk.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.20
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  [LocallySmall.{w} C]

/-- Finitely many elements of the fiber of a presheaf of sets at a point of a site are the
images of sections over one common object. -/
theorem exists_toPresheafFiber_eq_of_finite (P : Cᵒᵖ ⥤ Type w) {ι : Type*} [Finite ι]
    (p : ι → Φ.presheafFiber.obj P) :
    ∃ (U : C) (u : Φ.fiber.obj U) (z : ι → P.obj (op U)),
      ∀ i, Φ.toPresheafFiber U u P (z i) = p i := by
  choose U u z hz using fun i ↦ Φ.toPresheafFiber_jointly_surjective (P := P) (p i)
  have := Fintype.ofFinite ι
  let c := IsCofiltered.cone (Discrete.functor fun i ↦ Φ.fiber.elementsMk (U i) (u i))
  refine ⟨c.pt.1, c.pt.2, fun i ↦ P.map (c.π.app ⟨i⟩).1.op (z i), fun i ↦ ?_⟩
  have hf : Φ.fiber.map (c.π.app ⟨i⟩).1 c.pt.2 = u i := (c.π.app ⟨i⟩).2
  rw [Φ.toPresheafFiber_w_apply]
  change Φ.toPresheafFiber (U i) (Φ.fiber.map (c.π.app ⟨i⟩).1 c.pt.2) P (z i) = p i
  rw [hf]
  exact hz i

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Sheaves with finite stalks near a generic point.** Let `X` be locally noetherian, `G` an
étale sheaf of sets on `X` with finite stalks and open difference loci, and `x̄` a geometric
point of `X` over the generic point of an irreducible component of `X`. Then there is an étale
neighbourhood `(Y, ȳ)` of `x̄` with `Y` irreducible and affine such that the restriction `G|_Y`
is isomorphic to the sheaf represented by the disjoint union `Y^{⊔ m}` of `m = |G_x̄|` copies of
`Y` on the small étale site of `Y`. -/
@[weil "lem_fk103_finite_stalks_open_difference_representable_near_generic_point"]
theorem exists_restrict_iso_representedSheaf_disjointCopies [IsLocallyNoetherian X]
    (G : smallEtaleTopos.{u, u} B X hX) (hfin : HasFiniteStalks G)
    (hG : HasOpenDifferenceLoci G.obj) (x : GeometricPoint X) {η : X}
    (hη : closure {η} ∈ irreducibleComponents X) (hx : x.LiesOver η) :
    ∃ (Y : SmallEtale B X hX) (_ : (geometricPointFiber B X hX x).obj Y),
      IrreducibleSpace ((SmallEtale.toScheme B X hX).obj Y) ∧
      _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B X hX).obj Y) ∧
      Nonempty (((smallEtalePostcompose B X hX Y).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B _ Y.obj.left.property) (SmallEtale.topology B X hX)).obj G ≅
        representedSheaf (Stacks.EtaleCohomology.disjointCopies B Y.obj.left.property
          (SmallEtale.final B _ Y.obj.left.property)
          (Nat.card ((geometricPointSitePoint B X hX x).sheafFiber.obj G)))) := by
  classical
  let T := SmallEtale.toScheme B X hX
  let Φ := geometricPointSitePoint B X hX x
  have := hfin x
  set m := Nat.card (Φ.sheafFiber.obj G) with hm
  let en : Fin m ≃ Φ.sheafFiber.obj G := (Finite.equivFin _).symm
  -- Step 1: the elements of the stalk are germs of sections over one neighbourhood `(V, v)`.
  obtain ⟨V, v, t, ht⟩ := Φ.exists_toPresheafFiber_eq_of_finite G.obj (fun i ↦ en i)
  let π : T.obj V ⟶ X := B.inclusion.map V.obj.hom
  have : Etale π := V.property
  have : IsLocallyNoetherian (T.obj V) := LocallyOfFiniteType.isLocallyNoetherian π
  let v₀ : T.obj V := v.1 default
  have hv₀ : π v₀ = η := by
    rw [← hx, ← v.2]
    rfl
  -- Step 2: a connected open neighbourhood of `v₀` with generic point `v₀`.
  have hα : Maximal (fun Z : Set X ↦ IsIrreducible Z ∧ Z ⊆ Set.univ) (closure {η}) :=
    ⟨⟨hη.prop, Set.subset_univ _⟩, fun Z hZ hle ↦ hη.2 hZ.1 hle⟩
  obtain ⟨V', hv₀V', -, hgen⟩ :=
    exists_isConnected_isGenericPoint_preimage π isClosed_univ hα hv₀
  have hspec : ∀ z ∈ (V' : Set (T.obj V)), v₀ ⤳ z := by
    intro z hz
    have : (⟨v₀, hv₀V'⟩ : V') ⤳ ⟨z, hz⟩ :=
      (isGenericPoint_iff_specializes.1 hgen _).2 (Set.mem_univ _)
    exact this.map continuous_subtype_val
  -- Step 3: an affine open `W ⊆ V'` containing `v₀`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hv₀W, hWV'⟩ :=
    (T.obj V).isBasis_affineOpens.exists_subset_of_mem_open hv₀V' V'.isOpen
  let Y := openObject B X hX V W
  let ι : Y ⟶ V := openObjectι B X hX V W
  have hrange : Set.range (T.map ι) = W := openObjectι_range B X hX V W
  -- Step 4: the neighbourhood `(Y, y)` and its generic point.
  have hvW : Set.range v.1 ⊆ Set.range (T.map ι) := by
    rintro _ ⟨z, rfl⟩
    rw [hrange, Subsingleton.elim z default]
    exact hv₀W
  let l : x.source ⟶ T.obj Y := IsOpenImmersion.lift (T.map ι) v.1 hvW
  have hl : l ≫ T.map ι = v.1 := IsOpenImmersion.lift_fac _ _ _
  have hy : l ≫ B.inclusion.map Y.obj.hom = x.hom := by
    rw [← SmallEtale.toScheme_map_comp B X hX ι, ← Category.assoc, hl]
    exact v.2
  let y : (geometricPointFiber B X hX x).obj Y := ⟨l, hy⟩
  let w₀ : T.obj Y := l default
  have hw₀ : T.map ι w₀ = v₀ := by
    change (l ≫ T.map ι) default = _
    rw [hl]
  have hgenY : IsGenericPoint w₀ (Set.univ : Set (T.obj Y)) := by
    rw [isGenericPoint_iff_specializes]
    intro w
    simp only [Set.mem_univ, iff_true]
    rw [← (T.map ι).isOpenEmbedding.isInducing.specializes_iff, hw₀]
    exact hspec _ (hWV' (hrange ▸ ⟨w, rfl⟩))
  have hirr : IrreducibleSpace (T.obj Y) := (irreducibleSpace_def _).2 hgenY.isIrreducible
  refine ⟨Y, y, hirr, hW, ?_⟩
  -- Step 5: the restricted sheaf `H = G|_Y` and the sections `s_i = t_i|_Y`.
  let P := smallEtalePostcompose B X hX Y
  let F₀ := SmallEtale.final B _ Y.obj.left.property
  let e : P.obj F₀ ≅ Y := (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
    (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Y.obj.hom = 𝟙 _ ≫ Y.obj.hom
      rfl))
  have hTe : T.map e.hom = 𝟙 _ := by
    simp [T, e, SmallEtale.toScheme]
    rfl
  let g : P.obj F₀ ⟶ V := e.hom ≫ ι
  have : (smallEtalePostcompose B X hX Y).IsContinuous
      (SmallEtale.topology B _ Y.obj.left.property) (SmallEtale.topology B X hX) :=
    smallEtalePostcompose_isContinuous B X hX Y
  let H := ((smallEtalePostcompose B X hX Y).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B _ Y.obj.left.property) (SmallEtale.topology B X hX)).obj G
  let s : Fin m → H.obj.obj (op F₀) := fun i ↦ G.obj.map g.op (t i)
  let y' : GeometricPoint Y.obj.left.1 := { residueField := x.residueField, hom := l }
  let q : (geometricPointFiber B X hX x).obj (P.obj F₀) := ⟨l, by
    change l ≫ B.inclusion.map (𝟙 _ ≫ Y.obj.hom) = _
    rw [Category.id_comp]
    exact hy⟩
  have hfib : (geometricPointFiber B X hX x).map g q = v := by
    apply Subtype.ext
    change l ≫ T.map (e.hom ≫ ι) = v.1
    erw [Functor.map_comp, hTe, Category.id_comp, hl]
  have hgerm : ∀ i j, germ H.obj (s i) y' = germ H.obj (s j) y' ↔ i = j := by
    intro i j
    change germ (P.op ⋙ G.obj) (s i) y' = germ (P.op ⋙ G.obj) (s j) y' ↔ _
    refine (germ_smallEtalePostcompose_eq_iff G.obj Y (s i) (s j) y').trans
      ((germ_eq_germ_iff_toPresheafFiber_eq G.obj (s i) (s j) x q).trans ?_)
    change Φ.toPresheafFiber _ q G.obj (G.obj.map g.op (t i)) =
      Φ.toPresheafFiber _ q G.obj (G.obj.map g.op (t j)) ↔ _
    have h1 : ∀ k, Φ.toPresheafFiber _ q G.obj (G.obj.map g.op (t k)) = en k := fun k ↦
      (Φ.toPresheafFiber_w_apply g q G.obj (t k)).trans 
        ((congrArg (fun z ↦ Φ.toPresheafFiber V z G.obj (t k)) hfib).trans (ht k))
    exact ⟨fun h ↦ en.injective ((h1 i).symm.trans (h.trans (h1 j))), fun h ↦ h ▸ rfl⟩
  -- Step 6: the stalk of `H` at `y'` has `m` elements, so the germs of the `s_i` exhaust it.
  let Ψ := geometricPointSitePoint B _ Y.obj.left.property y'
  have hx' : y'.map (B.inclusion.map Y.obj.hom) = x := by
    change ({ residueField := x.residueField, hom := l ≫ B.inclusion.map Y.obj.hom } :
      GeometricPoint X) = x
    rw [hy]
  have hcard : Nat.card (Ψ.presheafFiber.obj H.obj) = m :=
    (Nat.card_congr (Equiv.ofBijective _
      (bijective_etaleStalkRestrictionMap B X hX Y y' G.obj))).trans
      (congrArg (fun z ↦ Nat.card ((geometricPointSitePoint B X hX z).presheafFiber.obj G.obj))
        hx')
  have : Finite (Ψ.presheafFiber.obj H.obj) := by
    exact @Finite.of_equiv _ _ (hfin (y'.map (B.inclusion.map Y.obj.hom))) (Equiv.ofBijective _
      (bijective_etaleStalkRestrictionMap B X hX Y y' G.obj)).symm
  let φ : Fin m → Ψ.presheafFiber.obj H.obj := fun i ↦
    Ψ.toPresheafFiber F₀ (SmallEtale.finalLift B _ _ y') H.obj (s i)
  have hφ : Function.Injective φ := fun i j hij ↦
    (hgerm i j).1 ((germ_eq_germ_iff_toPresheafFiber_eq H.obj (s i) (s j) y'
      (SmallEtale.finalLift B _ _ y')).2 hij)
  have hs : Set.range φ = Set.univ :=
    Set.range_eq_univ.2 (hφ.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])).2
  -- Step 7: `y'` lies over the generic point of `Y`.
  have : IrreducibleSpace Y.obj.left.1 := hirr
  have hy'gen : y'.LiesOver (genericPoint Y.obj.left.1) :=
    hgenY.eq (genericPoint_spec (T.obj Y))
  -- Step 8: `Φ_s` is bijective on sections, hence an isomorphism.
  have hHG : HasOpenDifferenceLoci H.obj := hG.smallEtalePostcompose Y
  let Φs := Stacks.EtaleCohomology.morphismFromCopies H F₀ s
  have hbij : ∀ U, Function.Bijective (Φs.hom.app (op U)) := fun U ↦
    ⟨Stacks.EtaleCohomology.injective_morphismFromCopies_app_of_connectedSpace H hHG s y'
        (fun i j hij ↦ hij ∘ (hgerm i j).1) U,
      Stacks.EtaleCohomology.surjective_morphismFromCopies_app_of_irreducibleSpace H hHG y'
        hy'gen s hs U⟩
  have : IsIso Φs.hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨U⟩
    exact (isIso_iff_bijective _).2 (hbij U)
  have : IsIso ((sheafToPresheaf _ _).map Φs) := this
  have : IsIso Φs := (fullyFaithfulSheafToPresheaf _ _).isIso_of_isIso_map Φs
  exact ⟨(asIso Φs).symm⟩

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Sheaves with finite stalks are representable near a generic point.** Under the
hypotheses of `exists_restrict_iso_representedSheaf_disjointCopies`, there is an étale
neighbourhood `(Y, ȳ)` of `x̄` with `Y` irreducible such that the restriction `G|_Y` is
representable in `Et(Y)`. -/
@[weil "lem_fk103_finite_stalks_open_difference_representable_near_generic_point"]
theorem exists_restrictIsRepresentableInEt_of_hasFiniteStalks [IsLocallyNoetherian X]
    (G : smallEtaleTopos.{u, u} B X hX) (hfin : HasFiniteStalks G)
    (hG : HasOpenDifferenceLoci G.obj) (x : GeometricPoint X) {η : X}
    (hη : closure {η} ∈ irreducibleComponents X) (hx : x.LiesOver η) :
    ∃ (Y : SmallEtale B X hX) (_ : (geometricPointFiber B X hX x).obj Y),
      IrreducibleSpace ((SmallEtale.toScheme B X hX).obj Y) ∧
      RestrictIsRepresentableInEt G.obj Y := by
  obtain ⟨Y, y, hirr, haff, ⟨e⟩⟩ :=
    exists_restrict_iso_representedSheaf_disjointCopies G hfin hG x hη hx
  refine ⟨Y, y, hirr, _, ⟨?_, ?_⟩, ⟨(sheafToPresheaf _ _).mapIso e.symm⟩⟩
  · change IsNoetherian (∐ fun _ : Fin (Nat.card
      ((geometricPointSitePoint B X hX x).sheafFiber.obj G)) ↦ (SmallEtale.toScheme B X hX).obj Y)
    let π : (SmallEtale.toScheme B X hX).obj Y ⟶ X := B.inclusion.map Y.obj.hom
    have : Etale π := Y.property
    have : IsLocallyNoetherian ((SmallEtale.toScheme B X hX).obj Y) :=
      LocallyOfFiniteType.isLocallyNoetherian π
    have : IsNoetherian ((SmallEtale.toScheme B X hX).obj Y) :=
      (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
    have : IsLocallyNoetherian
        (∐ fun _ : Fin (Nat.card ((geometricPointSitePoint B X hX x).sheafFiber.obj G)) ↦
          (SmallEtale.toScheme B X hX).obj Y) :=
      (isLocallyNoetherian_iff_openCover (sigmaOpenCover _)).2 fun _ ↦
        inferInstanceAs (IsLocallyNoetherian ((SmallEtale.toScheme B X hX).obj Y))
    exact (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  · change (∐ fun _ : Fin (Nat.card ((geometricPointSitePoint B X hX x).sheafFiber.obj G)) ↦
      (SmallEtale.toScheme B X hX).obj Y).IsSeparated
    infer_instance

end AlgebraicGeometry.SmallEtale
