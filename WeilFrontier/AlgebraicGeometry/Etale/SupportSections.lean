module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.SupportSections
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import Weil.Attr

/-!
# Sections of a sheaf with open difference loci over a connected scheme

Let `X` be a connected scheme and `F` an étale sheaf of sets on `X` with open difference loci.
Two sections of `F` over a connected object `U` of the small étale site whose germs agree at
one geometric point are equal: their coincidence set is open, closed and nonempty, hence all
of `U`, and a sheaf is separated by its germs at the geometric points.

Consequently, for pairwise distinct global sections `sᵢ` of `F` and a connected nonempty object
`U`, the restrictions `sᵢ|_U` are pairwise distinct, and `F(U)` is the disjoint union of the
`sᵢ|_U` and of the set `F°_E(U)` of sections avoiding `E = {sᵢ}`.

## Main results

* `AlgebraicGeometry.SmallEtale.eq_of_germCoincidenceSet_eq_univ`: sections of a sheaf whose
  germs agree at every geometric point are equal.
* `AlgebraicGeometry.SmallEtale.eq_of_germ_eq_of_connectedSpace`: over a connected object,
  for a sheaf with open difference loci, sections whose germs agree at one geometric point are
  equal.
* `AlgebraicGeometry.SmallEtale.globalRestrict_injective`: restriction of global sections to a
  nonempty object is injective when `X` is connected.
* `AlgebraicGeometry.SmallEtale.sumElim_globalRestrict_sectionsAvoiding_bijective`: the map
  `ι ⊕ F°_E(U) → F(U)`, `i ↦ sᵢ|_U`, `σ ↦ σ`, is bijective for connected `U`.

## Implementation notes

The family of global sections is indexed by an arbitrary type `ι` rather than by
`{1, …, m}`; finiteness is not used. The restriction is injective as soon as `U` is nonempty.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A sheaf of sets on the small étale site is separated by its germs: two sections whose
coincidence set is everything are equal. -/
theorem eq_of_germCoincidenceSet_eq_univ (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    [UnivLE.{u, v}] {U : SmallEtale B X hX} {α β : F.obj.obj (op U)}
    (h : germCoincidenceSet F.obj α β = Set.univ) : α = β := by
  let S : Sieve U :=
    { arrows := fun V f ↦ F.obj.map f.op α = F.obj.map f.op β
      downward_closed := by
        intro V W f hf g
        simp only [op_comp, Functor.map_comp, types_comp_apply, hf] }
  have hS : S ∈ SmallEtale.topology B X hX U := by
    refine mem_topology_of_jointlySurjective fun t ↦ ?_
    have ht : t ∈ germCoincidenceSet F.obj α β := h ▸ Set.mem_univ t
    obtain ⟨V, f, y, hy, hf⟩ :=
      ((geometricPointSitePoint B X hX
        (toBaseGeometricPoint U (GeometricPoint.ofPoint _ t))).toPresheafFiber_eq_iff'
        U (geometricPointLift U _) (P := F.obj) α β).1
        (ht _ (GeometricPoint.ofPoint_liesOver _ t))
    refine ⟨V, f, hf, y.1 default, ?_⟩
    have hy' : y.1 ≫ (SmallEtale.toScheme B X hX).map f = (GeometricPoint.ofPoint _ t).hom :=
      congrArg Subtype.val hy
    calc _ = (y.1 ≫ (SmallEtale.toScheme B X hX).map f) default := rfl
      _ = t := by rw [hy']; exact GeometricPoint.ofPoint_liesOver _ t
  exact ((isSheaf_iff_isSheaf_of_type _ F.obj).1 F.property S hS).isSeparatedFor.ext
    fun _ _ hf ↦ hf

/-- **Sections over a connected object agreeing at one geometric point are equal.** Let `F` be
an étale sheaf of sets with open difference loci, `U` a connected object of the small étale
site and `α β ∈ F(U)`. If the germs of `α` and `β` agree at one geometric point of `U`, then
`α = β`. -/
theorem eq_of_germ_eq_of_connectedSpace (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    [UnivLE.{u, v}] (hF : HasOpenDifferenceLoci F.obj) {U : SmallEtale B X hX}
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] {α β : F.obj.obj (op U)}
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U))
    (h : germ F.obj α ū = germ F.obj β ū) : α = β := by
  refine eq_of_germCoincidenceSet_eq_univ F ?_
  obtain ⟨W, -, huW, hWC⟩ :=
    exists_isOpen_mem_subset_germCoincidenceSet F.obj α β (u := ū.hom default) ū rfl h
  exact IsClopen.eq_univ ⟨hF.isClosed α β, isOpen_germCoincidenceSet F.obj α β⟩ ⟨_, hWC huW⟩

/-- The same statement with the germ taken at an arbitrary lift `z` to `U` of a geometric
point `x̄` of `X`. -/
theorem eq_of_toPresheafFiber_eq_of_connectedSpace
    (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    [UnivLE.{u, v}] (hF : HasOpenDifferenceLoci F.obj) {U : SmallEtale B X hX}
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] {α β : F.obj.obj (op U)}
    (x : GeometricPoint X) (z : (geometricPointFiber B X hX x).obj U)
    (h : (geometricPointSitePoint B X hX x).toPresheafFiber U z F.obj α =
      (geometricPointSitePoint B X hX x).toPresheafFiber U z F.obj β) : α = β := by
  cases x with | mk K xhom => ?_
  revert h
  change {p // p ≫ B.inclusion.map U.obj.hom = xhom} at z
  cases z with | mk z hz => ?_
  subst hz
  intro h
  exact eq_of_germ_eq_of_connectedSpace F hF ⟨K, z⟩ h

/-- **Restriction of global sections is injective.** For a connected scheme `X`, an étale
sheaf of sets `F` with open difference loci and a nonempty object `U` of the small étale site,
restriction `F(X) → F(U)` is injective. -/
theorem globalRestrict_injective [ConnectedSpace X]
    (F : Sheaf (SmallEtale.topology B X hX) (Type v)) [UnivLE.{u, v}]
    (hF : HasOpenDifferenceLoci F.obj)
    (U : SmallEtale B X hX) [Nonempty ((SmallEtale.toScheme B X hX).obj U)] :
    Function.Injective (globalRestrict F.obj U) := by
  intro e₁ e₂ he
  obtain ⟨u⟩ := (inferInstance : Nonempty ((SmallEtale.toScheme B X hX).obj U))
  let ū := GeometricPoint.ofPoint _ u
  let Φ := geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)
  let f := (SmallEtale.finalIsTerminal B X hX).from U
  have : ConnectedSpace ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX)) :=
    inferInstanceAs (ConnectedSpace X)
  refine eq_of_toPresheafFiber_eq_of_connectedSpace F hF _
    (Φ.fiber.map f (geometricPointLift U ū)) ?_
  exact (GrothendieckTopology.Point.toPresheafFiber_w_apply Φ f _ F.obj e₁).symm.trans
    ((congrArg (Φ.toPresheafFiber U (geometricPointLift U ū) F.obj) he).trans
      (GrothendieckTopology.Point.toPresheafFiber_w_apply Φ f _ F.obj e₂))

/-- **Decomposition of the sections over a connected object.** Let `X` be connected, `F` an
étale sheaf of sets on `X` with open difference loci and `s : ι → F(X)` an injective family of
global sections. For every connected nonempty object `U` of the small étale site, the
restrictions `sᵢ|_U` are pairwise distinct. -/
@[weil "lem_fk103_sheaf_decomposes_sections_plus_rest"]
theorem globalRestrict_comp_injective [ConnectedSpace X]
    (F : Sheaf (SmallEtale.topology B X hX) (Type v)) [UnivLE.{u, v}]
    (hF : HasOpenDifferenceLoci F.obj)
    {ι : Type*} {s : ι → F.obj.obj (op (SmallEtale.final B X hX))}
    (hs : Function.Injective s) (U : SmallEtale B X hX)
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] :
    Function.Injective fun i ↦ globalRestrict F.obj U (s i) :=
  (globalRestrict_injective F hF U).comp hs

/-- **Decomposition of the sections over a connected object.** Let `X` be connected, `F` an
étale sheaf of sets on `X` with open difference loci, `s : ι → F(X)` an injective family of
global sections and `E` its range. For every connected nonempty object `U` of the small étale
site, the map `ι ⊕ F°_E(U) → F(U)`, `i ↦ sᵢ|_U`, `σ ↦ σ`, is bijective. -/
@[weil "lem_fk103_sheaf_decomposes_sections_plus_rest"]
theorem sumElim_globalRestrict_sectionsAvoiding_bijective [ConnectedSpace X]
    (F : Sheaf (SmallEtale.topology B X hX) (Type v)) [UnivLE.{u, v}]
    (hF : HasOpenDifferenceLoci F.obj)
    {ι : Type*} {s : ι → F.obj.obj (op (SmallEtale.final B X hX))}
    (hs : Function.Injective s) (U : SmallEtale B X hX)
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] :
    Function.Bijective (Sum.elim (fun i ↦ globalRestrict F.obj U (s i))
      (fun σ : sectionsAvoiding F.obj (Set.range s) U ↦ (σ : F.obj.obj (op U)))) := by
  refine ⟨(globalRestrict_comp_injective F hF hs U).sumElim Subtype.val_injective ?_, ?_⟩
  · rintro i ⟨σ, hσ⟩ h
    exact (mem_sectionsAvoiding_iff_of_connectedSpace F.obj _ σ).1 hσ (s i) ⟨i, rfl⟩ h.symm
  · intro τ
    by_cases hτ : ∃ i, globalRestrict F.obj U (s i) = τ
    · obtain ⟨i, hi⟩ := hτ
      exact ⟨Sum.inl i, hi⟩
    · refine ⟨Sum.inr ⟨τ, (mem_sectionsAvoiding_iff_of_connectedSpace F.obj _ τ).2 ?_⟩, rfl⟩
      rintro _ ⟨i, rfl⟩ h
      exact hτ ⟨i, h.symm⟩

end AlgebraicGeometry.SmallEtale

end
