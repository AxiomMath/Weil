module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafCoincidenceLocusOpen
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering

/-!
# Coincidence of two sections near a geometric point

Let `F` be a presheaf of sets on the small étale site of a scheme `X`, let `U` be an object of
that site, `α β ∈ F(U)`, `u ∈ U` and `ū` a geometric point of `U` lying over `u` with
`α_ū = β_ū`. Then there is an open neighbourhood `W` of `u` in `U` contained in the coincidence
set `C(α, β)`. In particular `C(α, β)` is open.

The germs agree, so `α` and `β` agree on an étale neighbourhood `f : V ⟶ U` of `ū`. The image
`W = f(V)` is open, as étale morphisms are open, and contains `u`. Every geometric point `w̄`
of `U` over a point of `W` lifts along `f`, since `f` is étale and the residue field of `w̄` is
algebraically closed; hence `α_w̄ = β_w̄`, both being germs of the equal restrictions to `V`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isOpen_mem_subset_germCoincidenceSet`: the coincidence
  set contains an open neighbourhood of every point over which some geometric point sees equal
  germs.

## Implementation notes

The statement holds for every presheaf, not only for sheaves: only the description of equality
in a stalk as equality on some étale neighbourhood is used. The open neighbourhood is the image
of such an étale neighbourhood rather than a Zariski open on which the sections agree.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Coincidence from one geometric point.** If the germs of two sections `α β ∈ F(U)` of a
presheaf on the small étale site agree at one geometric point `ū` of `U` lying over `u`, then
an open neighbourhood of `u` in `U` lies in the coincidence set `C(α, β)`. -/
@[weil "lem_fk103_coincidence_from_one_geometric_point"]
theorem exists_isOpen_mem_subset_germCoincidenceSet (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    [UnivLE.{u, v}] {U : SmallEtale B X hX} (α β : F.obj (op U))
    {u : (SmallEtale.toScheme B X hX).obj U}
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) (hū : ū.LiesOver u)
    (h : germ F α ū = germ F β ū) :
    ∃ W : Set ((SmallEtale.toScheme B X hX).obj U), IsOpen W ∧ u ∈ W ∧
      W ⊆ germCoincidenceSet F α β := by
  obtain ⟨V, f, y, hy, hf⟩ :=
    ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_eq_iff'
      U (geometricPointLift U ū) (P := F) α β).1 h
  let g := (SmallEtale.toScheme B X hX).map f
  have : Etale g := _root_.AlgebraicGeometry.SmallEtale.etale_toScheme_map f
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  refine ⟨Set.range g, g.isOpenMap.isOpen_range, ⟨y.1 default, ?_⟩, ?_⟩
  · have hy' : y.1 ≫ g = ū.hom := congrArg Subtype.val hy
    rw [← hū, ← hy']
    rfl
  · rintro w ⟨v, hv⟩ wb hwb
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g wb.hom v (hv.trans hwb.symm)
    let y₁ : (geometricPointFiber B X hX (toBaseGeometricPoint U wb)).obj V :=
      ⟨l, by
        change l ≫ B.inclusion.map V.obj.hom = wb.hom ≫ B.inclusion.map U.obj.hom
        rw [← SmallEtale.toScheme_map_comp B X hX f, ← Category.assoc]
        exact congrArg (· ≫ B.inclusion.map U.obj.hom) hl⟩
    have hy₁ : (geometricPointFiber B X hX (toBaseGeometricPoint U wb)).map f y₁ =
        geometricPointLift U wb := Subtype.ext hl
    let Φ := geometricPointSitePoint B X hX (toBaseGeometricPoint U wb)
    change Φ.toPresheafFiber U (geometricPointLift U wb) F α =
      Φ.toPresheafFiber U (geometricPointLift U wb) F β
    rw [← hy₁]
    change Φ.toPresheafFiber U (Φ.fiber.map f y₁) F α = Φ.toPresheafFiber U (Φ.fiber.map f y₁) F β
    refine (GrothendieckTopology.Point.toPresheafFiber_w_apply Φ f y₁ F α).symm.trans ?_
    rw [hf]
    exact GrothendieckTopology.Point.toPresheafFiber_w_apply Φ f y₁ F β

end AlgebraicGeometry.SmallEtale

end

/-! ### Sections of a sheaf with open difference loci over a connected object -/

/-!
# Sections of a sheaf with open difference loci over a connected object

Let `F` be a presheaf of sets on the small étale site of a scheme `X`, `U` an object of the site
and `α β ∈ F(U)`. If the germs of `α` and `β` agree at one geometric point `ū` of `U`, they agree
on an étale neighbourhood `V → U` of `ū`; the image of `V` is an open neighbourhood of the point
under `ū`, and every geometric point of `U` lying over a point of that image lifts to `V`, so the
image lies in the coincidence set `C(α, β)`. Hence `C(α, β)` is open. For a sheaf `F`, the
coincidence set is all of `U` exactly when `α = β`: the étale neighbourhoods on which `α` and `β`
agree then cover `U`, and a sheaf is separated.

If moreover `F` has open difference loci, `C(α, β)` is also closed, so on a connected `U` it is
either empty or everything: two sections whose germs agree at one geometric point are equal.

## Main results

* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_eq_univ_iff`: for a sheaf, `C(α, β) = U` iff
  `α = β`.
* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.eq_of_germ_eq`: on a connected `U`, two
  sections of a sheaf with open difference loci whose germs agree at one geometric point are
  equal.

## Implementation notes

The source takes the cover of `U` by Zariski opens on which the sections agree and extracts a
finite subcover using that `U` is noetherian. Here the cover is by the étale neighbourhoods on
which the sections agree, which is a covering of the small étale site without any finiteness, so
no noetherian hypothesis on `U` is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.15
-/

public section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/- the three private lemmas below duplicate
`AlgebraicGeometry.SmallEtale.exists_isOpen_mem_subset_germCoincidenceSet` (above),
`AlgebraicGeometry.SmallEtale.isOpen_germCoincidenceSet` (in
`WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafCoincidenceLocusOpen`) and
`HasOpenDifferenceLoci.isClopen_germCoincidenceSet` (in
`WeilFrontier.AlgebraicGeometry.Sites.OpenDifferenceLociClopen`). They are private to avoid a name
clash. -/

/-- If the germs of two sections agree at a geometric point `ū` of `U`, there is an open
neighbourhood of the point under `ū` contained in the coincidence set `C(α, β)`. -/
private theorem exists_isOpen_subset_germCoincidenceSet' (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    [UnivLE.{u, v}] {U : SmallEtale B X hX} {α β : F.obj (op U)}
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) (h : germ F α ū = germ F β ū) :
    ∃ O : Set ((SmallEtale.toScheme B X hX).obj U), IsOpen O ∧ ū.hom default ∈ O ∧
      O ⊆ germCoincidenceSet F α β := by
  obtain ⟨V, f, y, hy, hf⟩ :=
    ((geometricPointSitePoint B X hX _).toPresheafFiber_eq_iff' (P := F) U
      (geometricPointLift U ū) α β).1 h
  have : Flat ((SmallEtale.toScheme B X hX).map f) := inferInstance
  have : LocallyOfFinitePresentation ((SmallEtale.toScheme B X hX).map f) := inferInstance
  have : UniversallyOpen ((SmallEtale.toScheme B X hX).map f) := UniversallyOpen.of_flat _
  refine ⟨Set.range ((SmallEtale.toScheme B X hX).map f),
    ((SmallEtale.toScheme B X hX).map f).isOpenMap.isOpen_range, ⟨y.1 default, ?_⟩, ?_⟩
  · have h1 : y.1 ≫ (SmallEtale.toScheme B X hX).map f = ū.hom := congrArg Subtype.val hy
    rw [← h1]
    rfl
  · rintro _ ⟨v, rfl⟩ w' hw'
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      ((SmallEtale.toScheme B X hX).map f) w'.hom v hw'.symm
    let y₁ : (geometricPointFiber B X hX (toBaseGeometricPoint U w')).obj V :=
      ⟨l, by
        change l ≫ B.inclusion.map V.obj.hom = w'.hom ≫ B.inclusion.map U.obj.hom
        rw [← hl, Category.assoc, ← SmallEtale.toScheme_map_comp]⟩
    have hy₁ : (geometricPointFiber B X hX (toBaseGeometricPoint U w')).map f y₁ =
        geometricPointLift U w' := Subtype.ext hl
    let Φ := geometricPointSitePoint B X hX (toBaseGeometricPoint U w')
    change Φ.toPresheafFiber U (geometricPointLift U w') F α =
      Φ.toPresheafFiber U (geometricPointLift U w') F β
    rw [← hy₁]
    exact ((Φ.toPresheafFiber_w_apply f y₁ F α).symm.trans
      (congrArg (Φ.toPresheafFiber V y₁ F) hf)).trans (Φ.toPresheafFiber_w_apply f y₁ F β)

/-- The coincidence set `C(α, β)` of two sections of a presheaf of sets is open. -/
private theorem isOpen_germCoincidenceSet' (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    [UnivLE.{u, v}] {U : SmallEtale B X hX} (α β : F.obj (op U)) :
    IsOpen (germCoincidenceSet F α β) := by
  rw [isOpen_iff_forall_mem_open]
  intro u hu
  obtain ⟨O, hO, huO, hOC⟩ := exists_isOpen_subset_germCoincidenceSet' F
    (GeometricPoint.ofPoint _ u) (hu _ (GeometricPoint.ofPoint_liesOver _ u))
  refine ⟨O, hOC, hO, ?_⟩
  rwa [GeometricPoint.ofPoint_liesOver _ u] at huO

/-- For a presheaf with open difference loci, the coincidence set `C(α, β)` is open and
closed. -/
private theorem HasOpenDifferenceLoci.isClopen' {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v}
    {hv : UnivLE.{u, v}} (hF : HasOpenDifferenceLoci F) {U : SmallEtale B X hX}
    (α β : F.obj (op U)) :
    IsClopen (germCoincidenceSet F α β) :=
  ⟨hF.isClosed α β, isOpen_germCoincidenceSet' F α β⟩

/-- Two sections of a sheaf of sets coincide everywhere if and only if they are equal. -/
theorem germCoincidenceSet_eq_univ_iff (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    [UnivLE.{u, v}] {U : SmallEtale B X hX} (α β : F.obj.obj (op U)) :
    germCoincidenceSet F.obj α β = Set.univ ↔ α = β := by
  refine ⟨fun h ↦ ?_, germCoincidenceSet_eq_univ_of_eq F.obj⟩
  have hcov : Presheaf.equalizerSieve (F := F.obj) (X := op U) α β ∈
      SmallEtale.topology B X hX U := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    have hx : x ∈ germCoincidenceSet F.obj α β := h ▸ Set.mem_univ x
    obtain ⟨V, f, y, hy, hf⟩ := ((geometricPointSitePoint B X hX _).toPresheafFiber_eq_iff'
      (P := F.obj) U
      (geometricPointLift U (GeometricPoint.ofPoint _ x)) α β).1
      (hx _ (GeometricPoint.ofPoint_liesOver _ x))
    refine ⟨V, f, hf, ⟨y.1 default, ?_⟩⟩
    have h1 : y.1 ≫ (SmallEtale.toScheme B X hX).map f = (GeometricPoint.ofPoint _ x).hom :=
      congrArg Subtype.val hy
    exact (congrArg (fun g ↦ g default) h1).trans (GeometricPoint.ofPoint_liesOver _ x)
  exact F.property.isSeparated _ _ hcov _ _ fun _ _ hf ↦ hf

/-- **Sections over a connected object agreeing at one geometric point are equal.** Let `F` be
an étale sheaf of sets on `X` with open difference loci, `U` a connected object of the small
étale site of `X`, `α β ∈ F(U)` and `ū` a geometric point of `U` with `α_ū = β_ū`. Then
`α = β`. -/
@[weil "lem_fk103_open_difference_loci_connected_sections_equal"]
theorem HasOpenDifferenceLoci.eq_of_germ_eq {F : Sheaf (SmallEtale.topology B X hX) (Type v)}
    {hv : UnivLE.{u, v}} (hF : HasOpenDifferenceLoci F.obj) {U : SmallEtale B X hX}
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] {α β : F.obj.obj (op U)}
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U))
    (h : germ F.obj α ū = germ F.obj β ū) : α = β := by
  obtain ⟨O, -, huO, hOC⟩ := exists_isOpen_subset_germCoincidenceSet' F.obj ū h
  exact (germCoincidenceSet_eq_univ_iff F α β).1
    ((hF.isClopen' α β).eq_univ ⟨_, hOC huO⟩)

end AlgebraicGeometry.SmallEtale

end
