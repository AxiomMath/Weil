module

public import Weil.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.QuotientOfRepresentableImpliesCokernelEquivalenceRelation
public import Weil.AlgebraicGeometry.Topologies.Etale.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import Weil.Attr

/-!
# Constructible sheaves of sets are the cokernels of étale equivalence relations

Let `X` be a Noetherian scheme. A sheaf of sets `F` on the small étale site of `X` is
constructible if and only if there are Noetherian étale `X`-schemes `R` and `Y` and an
equivalence relation `u, v : R ⇉ Y` in the étale category of `X` such that `F` is the cokernel
(coequalizer) of the induced pair `h_u, h_v : h_R ⇉ h_Y` of representable sheaves.

If `F` is constructible, there is an epimorphism `h_Y ⟶ F` from the sheaf represented by a
finite disjoint union `Y` of quasi-compact étale `X`-schemes. Its kernel pair is a subsheaf of
`h_{Y ×_X Y}`, hence represented by an open subscheme `R` of `Y ×_X Y`: the union of the images
of the morphisms `U ⟶ Y ×_X Y` whose two components have the same image in `F`. Its two
projections form an equivalence relation, and an epimorphism of sheaves of sets is the
coequalizer of its kernel pair. Conversely the cokernel of `h_R ⇉ h_Y` is a finite colimit of
constructible sheaves, hence constructible.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_of_isColimit_cofork`: on a quasi-compact
  quasi-separated scheme, a cokernel of a pair `h_R ⇉ h_Y` with `R`, `Y` quasi-compact and
  quasi-separated is constructible.
* `AlgebraicGeometry.exists_isEquivalenceRelation_isColimit_cofork_of_epi`: on a Noetherian
  scheme, an epimorphism `h_Y ⟶ F` with `Y` Noetherian is the cokernel of an equivalence
  relation `R ⇉ Y` with `R` Noetherian.
* `AlgebraicGeometry.isConstructibleSetSheaf_iff_exists_isEquivalenceRelation_iso_coequalizer`:
  `F` is constructible if and only if `F ≅ Coker(h_u, h_v)` for an equivalence relation
  `u, v : R ⇉ Y` of Noetherian étale `X`-schemes.

## Implementation notes

The étale category `Et(X)` of Noetherian schemes étale over `X` is represented by the objects
`U` of the small étale site whose underlying scheme is Noetherian; the representable sheaf of
`U` is `Sheaf.sheafifiedYoneda` of the small étale topology, with values in `Type (u + 1)`, the
universe in which constructible sheaves of sets are defined. Inside the proofs the representable
sheaf is replaced by `GrothendieckTopology.uliftYoneda`, whose sections are literally the
morphisms into the representing object, through `Sheaf.uliftYonedaIsoSheafifiedYoneda`.
The converse direction does not use that `u, v` is an equivalence relation.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)


/-- **The cokernel of a pair of representable sheaves is constructible.** On a quasi-compact
quasi-separated scheme `X`, if `R` and `Y` are quasi-compact quasi-separated étale `X`-schemes
and `π : h_Y ⟶ F` is a cokernel of `h_u, h_v : h_R ⇉ h_Y`, then `F` is constructible. -/
theorem isConstructibleSetSheaf_of_isColimit_cofork [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj] {R Y : SmallEtale B X.obj X.property}
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj R)]
    [QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj R)]
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj Y)]
    [QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj Y)] (u v : R ⟶ Y)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (π : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶ F)
    (w : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map u ≫ π =
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map v ≫ π)
    (hc : IsColimit (Cofork.ofπ π w)) : IsConstructibleSetSheaf B X F := by
  refine isConstructibleSetSheaf_congr B X
    ((colimit.isColimit _).coconePointUniqueUpToIso hc) ?_
  refine isConstructibleSetSheaf_colimit B X _ fun i => ?_
  have : CompactSpace R.obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj R))
  have : QuasiSeparatedSpace R.obj.left.obj :=
    inferInstanceAs (QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj R))
  have : CompactSpace Y.obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj Y))
  have : QuasiSeparatedSpace Y.obj.left.obj :=
    inferInstanceAs (QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj Y))
  cases i
  · exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X R
  · exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X Y

section Representability

variable {B X}

/-- Every étale scheme over a locally Noetherian scheme is locally Noetherian. -/
lemma SmallEtale.isLocallyNoetherian_toScheme_obj [IsLocallyNoetherian X.obj]
    (V : SmallEtale B X.obj X.property) :
    IsLocallyNoetherian ((SmallEtale.toScheme B X.obj X.property).obj V) := by
  have : Etale (B.inclusion.map V.obj.hom) := V.property
  exact @LocallyOfFiniteType.isLocallyNoetherian _ _ (B.inclusion.map V.obj.hom) _
    (inferInstanceAs (IsLocallyNoetherian X.obj))

/-- Over a locally Noetherian scheme, the product in the small étale site of two quasi-compact
étale schemes is quasi-compact. -/
lemma SmallEtale.compactSpace_toScheme_obj_prod [IsLocallyNoetherian X.obj]
    (Y₁ Y₂ : SmallEtale B X.obj X.property)
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj Y₁)]
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj Y₂)] :
    CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (Y₁ ⨯ Y₂)) := by
  let e := (SmallEtale.toScheme B X.obj X.property).mapIso (prodIsoPullback Y₁ Y₂) ≪≫
    PreservesPullback.iso (SmallEtale.toScheme B X.obj X.property) (terminal.from Y₁)
      (terminal.from Y₂)
  have := SmallEtale.isLocallyNoetherian_toScheme_obj (⊤_ SmallEtale B X.obj X.property)
  have : CompactSpace (pullback (C := Scheme.{u}) ((SmallEtale.toScheme B X.obj X.property).map
      (terminal.from Y₁)) ((SmallEtale.toScheme B X.obj X.property).map (terminal.from Y₂))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
  exact QuasiCompact.compactSpace_of_compactSpace e.hom

variable {Y : SmallEtale B X.obj X.property} {F : Sheaf (SmallEtale.topology B X.obj X.property)
  (Type (u + 1))}

lemma uliftYoneda_app_up_comp
    (q : (GrothendieckTopology.uliftYoneda.{u + 1} (SmallEtale.topology B X.obj X.property)).obj Y ⟶
      F)
    {U V : SmallEtale B X.obj X.property} (g : V ⟶ U) (a : U ⟶ Y) :
    q.hom.app (op V) (ULift.up (g ≫ a) : ULift.{u + 1} (V ⟶ Y)) =
      F.obj.map g.op (q.hom.app (op U) (ULift.up a : ULift.{u + 1} (U ⟶ Y))) :=
  NatTrans.naturality_apply q.hom g.op (ULift.up a : ULift.{u + 1} (U ⟶ Y))

/-- The open subscheme of `Y ×_X Y` covered by the images of the morphisms `U ⟶ Y ×_X Y` whose
two components have the same image under `q : h_Y ⟶ F`. -/
noncomputable def kernelPairSupport
    (q : (GrothendieckTopology.uliftYoneda.{u + 1} (SmallEtale.topology B X.obj X.property)).obj Y ⟶
      F) :
    ((SmallEtale.toScheme B X.obj X.property).obj (Y ⨯ Y)).Opens :=
  ⨆ p : Σ U : SmallEtale B X.obj X.property, {f : U ⟶ Y ⨯ Y //
      q.hom.app (op U) (ULift.up (f ≫ prod.fst)) = q.hom.app (op U) (ULift.up (f ≫ prod.snd))},
    ⟨Set.range ((SmallEtale.toScheme B X.obj X.property).map p.2.1).base,
      ((SmallEtale.toScheme B X.obj X.property).map p.2.1).isOpenMap.isOpen_range⟩

/-- A morphism `f : U ⟶ Y ×_X Y` factors through `kernelPairSupport q` exactly when its two
components have the same image under `q`. -/
lemma exists_comp_ofOpensι_kernelPairSupport_iff
    (q : (GrothendieckTopology.uliftYoneda.{u + 1} (SmallEtale.topology B X.obj X.property)).obj Y ⟶
      F)
    {U : SmallEtale B X.obj X.property} (f : U ⟶ Y ⨯ Y) :
    (∃ g : U ⟶ SmallEtale.ofOpens (Y ⨯ Y) (kernelPairSupport q),
        g ≫ SmallEtale.ofOpensι (Y ⨯ Y) (kernelPairSupport q) = f) ↔
      q.hom.app (op U) (ULift.up (f ≫ prod.fst)) = q.hom.app (op U) (ULift.up (f ≫ prod.snd)) := by
  rw [SmallEtale.exists_comp_ofOpensι_eq_iff]
  refine ⟨fun ht => ?_, fun h => fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, f, h⟩, hx⟩⟩
  have hstab : ∀ {V W : SmallEtale B X.obj X.property} (g : W ⟶ V) (f' : V ⟶ Y ⨯ Y),
      q.hom.app (op V) (ULift.up (f' ≫ prod.fst)) = q.hom.app (op V) (ULift.up (f' ≫ prod.snd)) →
      q.hom.app (op W) (ULift.up ((g ≫ f') ≫ prod.fst)) =
        q.hom.app (op W) (ULift.up ((g ≫ f') ≫ prod.snd)) := by
    intro V W g f' h
    rw [Category.assoc, Category.assoc, uliftYoneda_app_up_comp q g (f' ≫ prod.fst),
      uliftYoneda_app_up_comp q g (f' ≫ prod.snd), h]
  let S : Sieve U :=
    { arrows := fun V g => q.hom.app (op V) (ULift.up ((g ≫ f) ≫ prod.fst)) =
        q.hom.app (op V) (ULift.up ((g ≫ f) ≫ prod.snd))
      downward_closed := by
        intro V V' g hg g'
        rw [Category.assoc]
        exact hstab g' (g ≫ f) hg }
  have hS : S ∈ SmallEtale.topology B X.obj X.property U := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    obtain ⟨⟨V, f', hf'⟩, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp (ht ⟨x, rfl⟩)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨pullback f f', pullback.fst _ _, ?_,
      ⟨(PreservesPullback.iso (SmallEtale.toScheme B X.obj X.property) f f').inv z, ?_⟩⟩
    · have h := hstab (pullback.snd f f') f' hf'
      rw [← pullback.condition] at h
      exact h
    · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst, hz]
  have hF : Presieve.IsSheaf (SmallEtale.topology B X.obj X.property) F.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
  rw [← uliftYoneda_app_up_comp q g (f ≫ prod.fst), ← uliftYoneda_app_up_comp q g (f ≫ prod.snd)]
  have hg' : q.hom.app (op V) (ULift.up ((g ≫ f) ≫ prod.fst)) =
      q.hom.app (op V) (ULift.up ((g ≫ f) ≫ prod.snd)) := hg
  simpa only [Category.assoc] using hg'

/-- **A quotient of a representable sheaf is the cokernel of an equivalence relation**, for the
Yoneda sheaf `GrothendieckTopology.uliftYoneda` with values in `Type (u + 1)`. On a Noetherian
scheme, an epimorphism `q : h_Y ⟶ F` with `Y` Noetherian is a cokernel of `h_u, h_v` for an
equivalence relation `u, v : R ⇉ Y` with `R` Noetherian. -/
theorem exists_isEquivalenceRelation_isColimit_cofork_of_epi_uliftYoneda [IsNoetherian X.obj]
    [IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y)]
    (q : (GrothendieckTopology.uliftYoneda.{u + 1} (SmallEtale.topology B X.obj X.property)).obj Y ⟶
      F)
    [Epi q] :
    ∃ (R : SmallEtale B X.obj X.property) (_ : IsNoetherian
        ((SmallEtale.toScheme B X.obj X.property).obj R)) (u v : R ⟶ Y)
      (w : (GrothendieckTopology.uliftYoneda.{u + 1}
          (SmallEtale.topology B X.obj X.property)).map u ≫ q =
        (GrothendieckTopology.uliftYoneda.{u + 1}
          (SmallEtale.topology B X.obj X.property)).map v ≫ q),
      IsEquivalenceRelation u v ∧ Nonempty (IsColimit (Cofork.ofπ q w)) := by
  let W := kernelPairSupport q
  let j := SmallEtale.ofOpensι (Y ⨯ Y) W
  have hrel : ∀ (U : SmallEtale B X.obj X.property) (a b : U ⟶ Y),
      (∃ r : U ⟶ SmallEtale.ofOpens (Y ⨯ Y) W, r ≫ j ≫ prod.fst = a ∧ r ≫ j ≫ prod.snd = b) ↔
        q.hom.app (op U) (ULift.up a) = q.hom.app (op U) (ULift.up b) := by
    intro U a b
    constructor
    · rintro ⟨r, rfl, rfl⟩
      have := (exists_comp_ofOpensι_kernelPairSupport_iff q (r ≫ j)).1 ⟨r, rfl⟩
      simpa only [Category.assoc] using this
    · intro h
      obtain ⟨g, hg⟩ := (exists_comp_ofOpensι_kernelPairSupport_iff q (prod.lift a b)).2
        (by simpa only [prod.lift_fst, prod.lift_snd] using h)
      refine ⟨g, ?_, ?_⟩
      · rw [← Category.assoc, hg, prod.lift_fst]
      · rw [← Category.assoc, hg, prod.lift_snd]
  -- Noetherianity of `R`.
  have := SmallEtale.isLocallyNoetherian_toScheme_obj (Y ⨯ Y)
  have := SmallEtale.compactSpace_toScheme_obj_prod Y Y
  have := SmallEtale.isLocallyNoetherian_toScheme_obj (SmallEtale.ofOpens (Y ⨯ Y) W)
  have : CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj
      (SmallEtale.ofOpens (Y ⨯ Y) W)) :=
    QuasiCompact.compactSpace_of_compactSpace ((SmallEtale.toScheme B X.obj X.property).map j)
  have hR : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj
      (SmallEtale.ofOpens (Y ⨯ Y) W)) := ⟨⟩
  have w : (GrothendieckTopology.uliftYoneda.{u + 1}
        (SmallEtale.topology B X.obj X.property)).map (j ≫ prod.fst) ≫ q =
      (GrothendieckTopology.uliftYoneda.{u + 1}
        (SmallEtale.topology B X.obj X.property)).map (j ≫ prod.snd) ≫ q := by
    apply Sheaf.hom_ext
    ext U r
    exact (hrel U.unop _ _).1 ⟨r.down, rfl, rfl⟩
  refine ⟨SmallEtale.ofOpens (Y ⨯ Y) W, hR, j ≫ prod.fst, j ≫ prod.snd, w, ?_, ?_⟩
  · rw [SmallEtale.isEquivalenceRelation_iff_forall_injective_and_equivalence]
    intro U
    refine ⟨fun r r' h => ?_, ?_⟩
    · simp only [Prod.mk.injEq] at h
      apply (cancel_mono j).1
      apply prod.hom_ext
      · simpa only [Category.assoc] using h.1
      · simpa only [Category.assoc] using h.2
    · have : (fun a b : U ⟶ Y => ∃ r : U ⟶ SmallEtale.ofOpens (Y ⨯ Y) W,
          r ≫ j ≫ prod.fst = a ∧ r ≫ j ≫ prod.snd = b) =
          fun a b => q.hom.app (op U) (ULift.up a) = q.hom.app (op U) (ULift.up b) := by
        ext a b
        exact hrel U a b
      rw [this]
      exact ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  · -- An epimorphism of sheaves of sets is the coequalizer of its kernel pair.
    have : IsRegularEpi q := IsRegularEpiCategory.regularEpiOfEpi q
    let hc := isColimitCoforkOfEffectiveEpi q (Sheaf.sectionwisePullbackCone q q)
      (Sheaf.isLimitSectionwisePullbackCone q q)
    refine ⟨Cofork.IsColimit.mk' _ fun t => ?_⟩
    have ht : (Sheaf.sectionwisePullbackCone q q).fst ≫ t.π =
        (Sheaf.sectionwisePullbackCone q q).snd ≫ t.π := by
      apply Sheaf.hom_ext
      ext U p
      obtain ⟨r, h₁, h₂⟩ := (hrel U.unop p.1.1.down p.1.2.down).2 p.2
      have hcond := congrArg (fun k => k.hom.app U (ULift.up r)) t.condition
      change t.π.hom.app U p.1.1 = t.π.hom.app U p.1.2
      rw [← ULift.up_down p.1.1, ← ULift.up_down p.1.2, ← h₁, ← h₂]
      exact hcond
    refine ⟨hc.desc (Cofork.ofπ t.π ht), hc.fac _ WalkingParallelPair.one, fun {k} hk => ?_⟩
    apply (cancel_epi q).1
    exact hk.trans (hc.fac (Cofork.ofπ t.π ht) WalkingParallelPair.one).symm

/-- **A quotient of a representable sheaf is the cokernel of an equivalence relation.** On a
Noetherian scheme `X`, let `Y` be a Noetherian étale `X`-scheme and `p : h_Y ⟶ F` an
epimorphism of étale sheaves of sets. Then there are a Noetherian étale `X`-scheme `R` and an
equivalence relation `u, v : R ⇉ Y` in the étale category of `X` such that `p` is a cokernel of
`h_u, h_v : h_R ⇉ h_Y`. -/
theorem exists_isEquivalenceRelation_isColimit_cofork_of_epi [IsNoetherian X.obj]
    [IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y)]
    (p : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶ F) [Epi p] :
    ∃ (R : SmallEtale B X.obj X.property) (_ : IsNoetherian
        ((SmallEtale.toScheme B X.obj X.property).obj R)) (u v : R ⟶ Y)
      (w : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map u ≫ p =
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map v ≫ p),
      IsEquivalenceRelation u v ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  let N := Sheaf.uliftYonedaIsoSheafifiedYoneda (SmallEtale.topology B X.obj X.property)
  obtain ⟨R, hR, u, v, w, he, ⟨hc⟩⟩ :=
    exists_isEquivalenceRelation_isColimit_cofork_of_epi_uliftYoneda (N.hom.app Y ≫ p)
  have hnat : ∀ (g : R ⟶ Y) {Z}
      (k : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶ Z),
      N.hom.app R ≫ (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map g ≫ k =
        (GrothendieckTopology.uliftYoneda.{u + 1} (SmallEtale.topology B X.obj X.property)).map g ≫
          N.hom.app Y ≫ k := by
    intro g Z k
    rw [← Category.assoc, ← N.hom.naturality, Category.assoc]
  have w' : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map u ≫ p =
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map v ≫ p := by
    rw [← cancel_epi (N.hom.app R), hnat, hnat]
    exact w
  refine ⟨R, hR, u, v, w', he, ⟨Cofork.IsColimit.mk' _ fun t => ?_⟩⟩
  have ht : (GrothendieckTopology.uliftYoneda.{u + 1}
        (SmallEtale.topology B X.obj X.property)).map u ≫ N.hom.app Y ≫ t.π =
      (GrothendieckTopology.uliftYoneda.{u + 1}
        (SmallEtale.topology B X.obj X.property)).map v ≫ N.hom.app Y ≫ t.π := by
    rw [← hnat, ← hnat, t.condition]
  refine ⟨hc.desc (Cofork.ofπ _ ht), ?_, fun {k} hk => ?_⟩
  · apply (cancel_epi (N.hom.app Y)).1
    rw [← Category.assoc]
    exact hc.fac (Cofork.ofπ _ ht) WalkingParallelPair.one
  · apply (cancel_epi (N.hom.app Y ≫ p)).1
    have hk' : p ≫ k = t.π := hk
    rw [Category.assoc, hk']
    exact (hc.fac (Cofork.ofπ _ ht) WalkingParallelPair.one).symm

end Representability

/-- **Constructible sheaves of sets are the cokernels of étale equivalence relations**, in the
form of a universal property. On a Noetherian scheme `X`, a sheaf of sets `F` on the small étale
site is constructible if and only if there are Noetherian étale `X`-schemes `R`, `Y`, an
equivalence relation `u, v : R ⇉ Y` in the étale category of `X` and a morphism
`π : h_Y ⟶ F` exhibiting `F` as the cokernel of `h_u, h_v : h_R ⇉ h_Y`. -/
theorem isConstructibleSetSheaf_iff_exists_isEquivalenceRelation_isColimit_cofork
    [IsNoetherian X.obj] (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∃ (R Y : SmallEtale B X.obj X.property)
        (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj R))
        (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y)) (u v : R ⟶ Y)
        (π : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶ F)
        (w : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map u ≫ π =
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map v ≫ π),
        IsEquivalenceRelation u v ∧ Nonempty (IsColimit (Cofork.ofπ π w)) := by
  constructor
  · intro hF
    obtain ⟨n, U, hU, p, hp⟩ := exists_finite_representable_epi_of_isConstructibleSetSheaf B X F hF
    let _ : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
      CategoryTheory.Sheaf.instHasFiniteColimits
    let _ : HasColimitsOfShape (Discrete (Fin n))
        (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
      HasFiniteColimits.out _
    let Y := Stacks.EtaleCohomology.disjointUnionObj B X.property U
    have : CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj Y) := by
      rw [Stacks.EtaleCohomology.toScheme_obj_disjointUnionObj]
      have : Finite (sigmaOpenCover fun k : Fin n =>
          (SmallEtale.toScheme B X.obj X.property).obj (U k)).I₀ := inferInstanceAs (Finite (Fin n))
      exact @Scheme.OpenCover.compactSpace _
        (sigmaOpenCover fun k : Fin n => (SmallEtale.toScheme B X.obj X.property).obj (U k)) _
        fun k => (hU k).1
    have := SmallEtale.isLocallyNoetherian_toScheme_obj Y
    have hY : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y) := ⟨⟩
    let π := (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B X.property U).inv ≫ p
    have : Epi π := epi_comp _ _
    obtain ⟨R, hR, u, v, w, he, hc⟩ := exists_isEquivalenceRelation_isColimit_cofork_of_epi π
    exact ⟨R, Y, hR, hY, u, v, π, w, he, hc⟩
  · rintro ⟨R, Y, _, _, u, v, π, w, -, ⟨hc⟩⟩
    exact isConstructibleSetSheaf_of_isColimit_cofork B X u v π w hc

/-- **Constructible sheaves of sets are the cokernels of étale equivalence relations.** On a
Noetherian scheme `X`, a sheaf of sets `F` on the small étale site is constructible if and only if
there is an equivalence relation `u, v : R ⇉ Y` in the étale category of `X`, with `R` and `Y`
Noetherian, such that `F ≅ Coker(h_u, h_v)` is the cokernel of the induced pair of
representable sheaves. -/
@[weil "prop_fk104_constructible_iff_cokernel_representable_equivalence_relation"]
theorem isConstructibleSetSheaf_iff_exists_isEquivalenceRelation_iso_coequalizer
    [IsNoetherian X.obj] (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∃ (R Y : SmallEtale B X.obj X.property)
        (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj R))
        (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y)) (u v : R ⟶ Y),
        IsEquivalenceRelation u v ∧
          Nonempty (F ≅ coequalizer
            ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map u)
            ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map v)) := by
  rw [isConstructibleSetSheaf_iff_exists_isEquivalenceRelation_isColimit_cofork]
  constructor
  · rintro ⟨R, Y, hR, hY, u, v, π, w, he, ⟨hc⟩⟩
    exact ⟨R, Y, hR, hY, u, v, he,
      ⟨hc.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩
  · rintro ⟨R, Y, hR, hY, u, v, he, ⟨e⟩⟩
    refine ⟨R, Y, hR, hY, u, v, coequalizer.π _ _ ≫ e.inv, ?_, he, ⟨?_⟩⟩
    · rw [← Category.assoc, coequalizer.condition, Category.assoc]
    · exact IsColimit.ofIsoColimit (coequalizerIsCoequalizer
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map u)
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).map v))
        (Cofork.ext e.symm rfl)

end AlgebraicGeometry
