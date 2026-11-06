module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.MorphismFromCopiesDefinedBySections
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian

/-!
# Surjectivity of the morphism from copies over an irreducible scheme

Let `X` be an irreducible scheme with generic point `η`, `G` an étale sheaf of sets on `X` with
open difference loci, `x` a geometric point of `X` over `η` and `s = (s_0, …, s_{m-1})` global
sections of `G` whose germs at `x` exhaust the stalk `G_x`. Then for every object `U` of the
small étale site of `X` the map `Φ_{s,U} : Hom_X(U, X^{⊔ m}) → G(U)` defined by `s` is
surjective.

Given `t ∈ G(U)`, every point `u ∈ U` has a generalization `u'` over `η`, as the structure
morphism `π : U → X` is flat. The geometric point `x` lifts along the étale morphism `π` to a
geometric point over `u'`, at which the germ of `t` is the germ of some `s_i`; hence `u'`, and
with it `u`, lies in the coincidence set `C(t, s_i|_U)`, which is open and closed. Making the
coincidence sets disjoint gives a decomposition of `U` into open and closed pieces `D_i` with
`t|_{D_i} = s_i|_{D_i}`; the morphism `U → X^{⊔ m}` sending `D_i` into the `i`-th copy is then
glued from the pieces, and it is sent to `t` by `Φ_{s,U}`.

## Main results

* `AlgebraicGeometry.SmallEtale.germ_eq_germ_iff_toPresheafFiber_eq`: equality of germs at a
  geometric point of `U` is equality in the stalk at a geometric point `x` of `X` along a lift
  of `x` to `U`.
* `AlgebraicGeometry.SmallEtale.mem_germCoincidenceSet_iff_forall_toPresheafFiber_eq`: the
  coincidence set in terms of lifts of geometric points of `X`.
* `AlgebraicGeometry.SmallEtale.mem_germCoincidenceSet_map`: coincidence sets pull back along
  morphisms of the small étale site.
* `Stacks.EtaleCohomology.surjective_morphismFromCopies_app_of_irreducibleSpace`: the map
  `Φ_{s,U}` is surjective.

## Implementation notes

The source decomposes `U` into its finitely many connected components, using that the objects
of its étale site are noetherian. On the small étale site the objects need not be noetherian,
so here `U` is decomposed instead into the open and closed pieces `D_i` cut out by the
coincidence sets; points of `U` reach the generic fibre by lifting generalizations along the
flat morphism `π`, rather than through the image of a connected component.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

private theorem germ_eq_germ_iff_toPresheafFiber_eq_aux (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    [UnivLE.{u, v}] {U : SmallEtale B X hX} (α β : F.obj (op U)) (k : Type u) [Field k]
    [IsAlgClosed k] (h : Spec (.of k) ⟶ X) (p : Spec (.of k) ⟶ (SmallEtale.toScheme B X hX).obj U)
    (hp : p ≫ B.inclusion.map U.obj.hom = h) :
    germ F α { residueField := k, hom := p } = germ F β { residueField := k, hom := p } ↔
      (geometricPointSitePoint B X hX { residueField := k, hom := h }).toPresheafFiber U
          ⟨p, hp⟩ F α =
        (geometricPointSitePoint B X hX { residueField := k, hom := h }).toPresheafFiber U
          ⟨p, hp⟩ F β := by
  subst hp
  exact Iff.rfl

/-- Equality of the germs of two sections at the geometric point `ū = p` of `U` defined by a
lift `p` of a geometric point `y` of `X` is equality in the stalk at `y`. -/
theorem germ_eq_germ_iff_toPresheafFiber_eq (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    [UnivLE.{u, v}] {U : SmallEtale B X hX} (α β : F.obj (op U)) (y : GeometricPoint X)
    (p : (geometricPointFiber B X hX y).obj U) :
    germ F α { residueField := y.residueField, hom := p.1 } =
        germ F β { residueField := y.residueField, hom := p.1 } ↔
      (geometricPointSitePoint B X hX y).toPresheafFiber U p F α =
        (geometricPointSitePoint B X hX y).toPresheafFiber U p F β := by
  cases y
  exact germ_eq_germ_iff_toPresheafFiber_eq_aux F α β _ _ p.1 p.2

/-- A point `u` of `U` lies in the coincidence set `C(α, β)` if and only if the germs of `α`
and `β` agree along every lift to `U`, over `u`, of a geometric point of `X`. -/
theorem mem_germCoincidenceSet_iff_forall_toPresheafFiber_eq
    (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}] {U : SmallEtale B X hX}
    (α β : F.obj (op U)) (u : (SmallEtale.toScheme B X hX).obj U) :
    u ∈ germCoincidenceSet F α β ↔
      ∀ (y : GeometricPoint X) (p : (geometricPointFiber B X hX y).obj U), p.1 default = u →
        (geometricPointSitePoint B X hX y).toPresheafFiber U p F α =
          (geometricPointSitePoint B X hX y).toPresheafFiber U p F β := by
  refine ⟨fun h y p hp ↦ ?_, fun h ū hū ↦ h _ (geometricPointLift U ū) hū⟩
  exact (germ_eq_germ_iff_toPresheafFiber_eq F α β y p).1
    (h { residueField := y.residueField, hom := p.1 } hp)

/-- Coincidence sets pull back along morphisms `g : V ⟶ U` of the small étale site: if `g v`
lies in `C(α, β)`, then `v` lies in `C(g^* α, g^* β)`. -/
theorem mem_germCoincidenceSet_map (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]
    {U V : SmallEtale B X hX} (g : V ⟶ U) {α β : F.obj (op U)}
    {v : (SmallEtale.toScheme B X hX).obj V}
    (hv : (SmallEtale.toScheme B X hX).map g v ∈ germCoincidenceSet F α β) :
    v ∈ germCoincidenceSet F (F.map g.op α) (F.map g.op β) := by
  rw [mem_germCoincidenceSet_iff_forall_toPresheafFiber_eq] at hv ⊢
  intro y p hp
  let Φ := geometricPointSitePoint B X hX y
  change Φ.toPresheafFiber V p F (F.map g.op α) = Φ.toPresheafFiber V p F (F.map g.op β)
  rw [Φ.toPresheafFiber_w_apply g p F α, Φ.toPresheafFiber_w_apply g p F β]
  exact hv y (Φ.fiber.map g p) (by
    change (p.1 ≫ (SmallEtale.toScheme B X hX).map g) default = _
    rw [← hp]
    rfl)

end AlgebraicGeometry.SmallEtale

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

variable {B : AlgebraicGeometry.BigEtaleSite.{u}} {X : AlgebraicGeometry.Scheme.{u}}
  {hX : B.Contains X}

/-- **The morphism from copies is surjective over an irreducible scheme.** Let `X` be
irreducible, `G` an étale sheaf of sets on `X` with open difference loci, `x` a geometric point
of `X` over the generic point, and `s_0, …, s_{m-1}` global sections of `G` whose germs at `x`
make up the whole stalk `G_x`. Then for every object `U` of the small étale site of `X`, the
map `Φ_{s,U} : Hom_X(U, X^{⊔ m}) → G(U)` defined by `s` is surjective. -/
@[weil "lem_fk103_sections_morphism_surjective_generic"]
theorem surjective_morphismFromCopies_app_of_irreducibleSpace [IrreducibleSpace X]
    (G : smallEtaleTopos.{u, u} B X hX) (hG : HasOpenDifferenceLoci G.obj)
    (x : GeometricPoint X) (hx : x.LiesOver (genericPoint X)) {m : ℕ}
    (s : Fin m → G.obj.obj (op (SmallEtale.final B X hX)))
    (hs : Set.range (fun i ↦ (geometricPointSitePoint B X hX x).toPresheafFiber
      (SmallEtale.final B X hX) (SmallEtale.finalLift B X hX x) G.obj (s i)) = Set.univ)
    (U : SmallEtale B X hX) :
    Function.Surjective
      ((morphismFromCopies G (SmallEtale.final B X hX) s).hom.app (op U)) := by
  classical
  intro t
  let Xf := SmallEtale.final B X hX
  let hY : IsTerminal Xf := SmallEtale.finalIsTerminal B X hX
  let T := SmallEtale.toScheme B X hX
  let π : T.obj U ⟶ X := B.inclusion.map U.obj.hom
  have : Etale π := U.property
  let r : U ⟶ Xf := hY.from U
  let σ : Fin m → G.obj.obj (op U) := fun i ↦ G.obj.map r.op (s i)
  let C : Fin m → Set (T.obj U) := fun i ↦ germCoincidenceSet G.obj t (σ i)
  have hCopen : ∀ i, IsOpen (C i) := fun i ↦ isOpen_germCoincidenceSet G.obj t (σ i)
  have hCclosed : ∀ i, IsClosed (C i) := fun i ↦ hG.isClosed t (σ i)
  -- Every point of `U` lies in some coincidence set `C(t, s_i|_U)`.
  have hcover : ∀ u : T.obj U, ∃ i, u ∈ C i := by
    intro u
    obtain ⟨u', hu'u, hu'⟩ := Flat.generalizingMap π (genericPoint_specializes (π u))
    obtain ⟨l, hl, hlu⟩ := Scheme.exists_fac_of_etale_of_isSepClosed π x.hom u'
      (hu'.trans hx.symm)
    let p : (geometricPointFiber B X hX x).obj U := ⟨l, hl⟩
    let Φ := geometricPointSitePoint B X hX x
    obtain ⟨i, hi⟩ : Φ.toPresheafFiber U p G.obj t ∈ Set.range (fun i ↦
        Φ.toPresheafFiber Xf (SmallEtale.finalLift B X hX x) G.obj (s i)) :=
      hs ▸ Set.mem_univ _
    have hgerm : Φ.toPresheafFiber U p G.obj t = Φ.toPresheafFiber U p G.obj (σ i) := by
      refine hi.symm.trans ?_
      change _ = Φ.toPresheafFiber U p G.obj (G.obj.map r.op (s i))
      rw [Φ.toPresheafFiber_w_apply r p G.obj (s i),
        geometricPointFiber_final_eq B X hX x (Φ.fiber.map r p)]
    obtain ⟨W, -, hu'W, hWC⟩ := exists_isOpen_mem_subset_germCoincidenceSet G.obj t (σ i)
      { residueField := x.residueField, hom := l } hlu
      ((germ_eq_germ_iff_toPresheafFiber_eq G.obj t (σ i) x p).2 hgerm)
    exact ⟨i, hu'u.mem_closed (hCclosed i) (hWC hu'W)⟩
  -- The disjoint open and closed pieces `D_i = C_i \ ⋃_{j < i} C_j`.
  let D : Fin m → Set (T.obj U) := fun i ↦ C i ∩ ⋂ (j : Fin m) (_ : j < i), (C j)ᶜ
  have hDopen : ∀ i, IsOpen (D i) := fun i ↦ (hCopen i).inter
    (isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦ (hCclosed j).isOpen_compl)
  have hDC : ∀ i, D i ⊆ C i := fun i _ h ↦ h.1
  have hDdisj : ∀ i j (u : T.obj U), u ∈ D i → u ∈ D j → i = j := by
    intro i j u hi hj
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.mem_iInter₂.1 hj.2 i h hi.1
    · exact Set.mem_iInter₂.1 hi.2 j h hj.1
  have hDcover : ∀ u : T.obj U, ∃ i, u ∈ D i := by
    intro u
    have hne : {i | u ∈ C i}.Nonempty := hcover u
    have hwf : WellFounded (α := Fin m) (· < ·) := wellFounded_lt
    refine ⟨hwf.min _ hne, hwf.min_mem _ hne, ?_⟩
    exact Set.mem_iInter₂.2 fun j hj hjC ↦ hwf.not_lt_min {i | u ∈ C i} hjC hj
  -- The covering of `U` by the pieces.
  let W : Fin m → SmallEtale B X hX := fun i ↦ openObject B X hX U ⟨D i, hDopen i⟩
  let ι : ∀ i, W i ⟶ U := fun i ↦ openObjectι B X hX U ⟨D i, hDopen i⟩
  have hι : ∀ i (w : T.obj (W i)), T.map (ι i) w ∈ D i := by
    intro i w
    have : T.map (ι i) w ∈ Set.range (T.map (ι i)).base := ⟨w, rfl⟩
    rwa [openObjectι_range] at this
  have hcov : Sieve.ofArrows W ι ∈ SmallEtale.topology B X hX U :=
    ofArrows_mem_topology B hX W ι fun u ↦ by
      obtain ⟨i, hi⟩ := hDcover u
      exact ⟨i, by rw [openObjectι_range]; exact hi⟩
  have hsheafFor : ∀ P : smallEtaleTopos.{u, u} B X hX,
      Presieve.IsSheafFor P.obj (Presieve.ofArrows W ι) := fun P ↦
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B X hX) P.obj).1 P.property _ hcov)
  -- Glue the morphism `a : U ⟶ X^{⊔ m}` sending `D_i` into the `i`-th copy.
  let Z := disjointCopies B hX Xf m
  let aᵢ : ∀ i, (representedSheaf Z).obj.obj (op (W i)) := fun i ↦
    (hY.from (W i) ≫ disjointCopiesι B hX Xf m i : W i ⟶ Z)
  have hcomp : Presieve.Arrows.Compatible (representedSheaf Z).obj ι aᵢ := by
    intro i j V gi gj hij
    by_cases h : i = j
    · subst h
      change gi ≫ hY.from (W i) ≫ _ = gj ≫ hY.from (W i) ≫ _
      rw [← Category.assoc, ← Category.assoc, hY.hom_ext (gi ≫ _) (gj ≫ _)]
    · have hV : IsEmpty (T.obj V) := ⟨fun v ↦ h (hDdisj i j _ (by
          have := hι i (T.map gi v)
          rwa [← Scheme.Hom.comp_apply, ← T.map_comp] at this) (by
          have := hι j (T.map gj v)
          rwa [← Scheme.Hom.comp_apply, ← T.map_comp, ← hij] at this))⟩
      have := subsingleton_sheaf_obj_of_isEmpty_toScheme (representedSheaf Z) V hV
      exact Subsingleton.elim _ _
  obtain ⟨a, ha, -⟩ := (Presieve.isSheafFor_arrows_iff _ ι).1 (hsheafFor _) aᵢ hcomp
  refine ⟨a, (morphismFromCopies_app G Xf s U a).trans ?_⟩
  -- `Φ_{s,U}(a)` and `t` agree on every piece.
  refine (hsheafFor G).isSeparatedFor.ext ?_
  rintro _ _ ⟨i⟩
  let a' : U ⟶ Z := a
  have hai : ι i ≫ a' = hY.from (W i) ≫ disjointCopiesι B hX Xf m i := ha i
  have ht : G.obj.map (ι i).op t = G.obj.map (ι i).op (σ i) := by
    refine (germCoincidenceSet_eq_univ_iff G _ _).1 (Set.eq_univ_of_forall fun w ↦ ?_)
    exact mem_germCoincidenceSet_map G.obj (ι i) (hDC i (hι i w))
  calc G.obj.map (ι i).op (G.obj.map a'.op (disjointCopiesSection G Xf s))
      = G.obj.map (ι i ≫ a').op (disjointCopiesSection G Xf s) :=
        (G.obj.map_comp_apply _ _ _).symm
    _ = G.obj.map (hY.from (W i)).op
          (G.obj.map (disjointCopiesι B hX Xf m i).op (disjointCopiesSection G Xf s)) := by
        rw [hai]
        exact G.obj.map_comp_apply _ _ _
    _ = G.obj.map (hY.from (W i)).op (s i) := by
        rw [map_disjointCopiesι_disjointCopiesSection]
    _ = G.obj.map (ι i ≫ r).op (s i) := by
        rw [hY.hom_ext (ι i ≫ r) (hY.from (W i))]
    _ = G.obj.map (ι i).op (σ i) := G.obj.map_comp_apply _ _ _
    _ = G.obj.map (ι i).op t := ht.symm

end Stacks.EtaleCohomology

end
