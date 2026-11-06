module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite

/-!
# Quasi-finite morphisms

A morphism of schemes `f : X ⟶ Y` is *quasi-finite* (in the sense of Freitag–Kiehl, EGA II 6.2.2)
if it is locally of finite type and every fibre `f ⁻¹' {y}` is a finite set.

In the Stacks project (Tag 01TJ) a quasi-finite morphism is one that is of finite type and
quasi-finite at every point. In Mathlib's language this is `LocallyOfFiniteType f`,
`LocallyQuasiFinite f` and `QuasiCompact f` (Mathlib's `LocallyQuasiFinite` does not include
finite type). No bundled predicate is introduced: statements about quasi-finite morphisms carry
the instance hypotheses `[LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f]`, and
the finite fibres are `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`. This file
identifies that notion with the fibrewise one.

## Main results

- `AlgebraicGeometry.locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact_iff`: `f` is
  locally of finite type, locally quasi-finite and quasi-compact if and only if it is locally of
  finite type, quasi-compact, and has finite fibres.
- `AlgebraicGeometry.locallyOfFiniteType_and_locallyQuasiFinite_iff_of_quasiCompact`: for a
  quasi-compact `f`, `f` is locally of finite type and locally quasi-finite if and only if it is
  locally of finite type and has finite fibres.
- `AlgebraicGeometry.locallyOfFiniteType_and_locallyQuasiFinite_iff_of_noetherianSpace`: the
  same for a noetherian source; the right side is the definition of Freitag–Kiehl, all of whose
  schemes are noetherian.

## Implementation notes

Freitag–Kiehl's "finitely generated" morphism is `AlgebraicGeometry.LocallyOfFiniteType`. Their
definition does not require quasi-compactness, which is automatic for their (noetherian) schemes;
for an arbitrary source the standard notion includes it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2, p. 18][FK88]
-/

@[expose] public section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is locally of finite type, locally quasi-finite and quasi-compact if and only if
it is locally of finite type, quasi-compact, and has finite fibres. -/
@[weil "def_fk102_quasi_finite_morphism"]
theorem locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact_iff :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ∧ QuasiCompact f ↔
      LocallyOfFiniteType f ∧ QuasiCompact f ∧ ∀ y, (f ⁻¹' {y}).Finite := by
  constructor
  · rintro ⟨_, _, _⟩
    exact ⟨inferInstance, inferInstance, f.finite_preimage_singleton⟩
  · rintro ⟨_, _, h⟩
    exact ⟨inferInstance, .of_finite_preimage_singleton f h, inferInstance⟩

/-- A quasi-compact morphism is locally of finite type and locally quasi-finite if and only if it
is locally of finite type and has finite fibres. -/
@[weil "def_fk102_quasi_finite_morphism"]
theorem locallyOfFiniteType_and_locallyQuasiFinite_iff_of_quasiCompact [QuasiCompact f] :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      LocallyOfFiniteType f ∧ ∀ y, (f ⁻¹' {y}).Finite := by
  constructor
  · rintro ⟨_, _⟩
    exact ⟨inferInstance, f.finite_preimage_singleton⟩
  · rintro ⟨_, h⟩
    exact ⟨inferInstance, .of_finite_preimage_singleton f h⟩

/-- For a morphism with noetherian source, being locally of finite type and locally quasi-finite
is being locally of finite type with finite fibres. -/
theorem locallyOfFiniteType_and_locallyQuasiFinite_iff_of_noetherianSpace [NoetherianSpace X] :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      LocallyOfFiniteType f ∧ ∀ y, (f ⁻¹' {y}).Finite :=
  locallyOfFiniteType_and_locallyQuasiFinite_iff_of_quasiCompact f

end AlgebraicGeometry

end

/-! ### Irreducible preimages near a point over the generic point of a component -/

/-!
# Irreducible preimages near a point over the generic point of a component

Let `π : V ⟶ X` be an étale morphism, `A ⊆ X` a closed subset, `α₀` the generic point of an
irreducible component of `A`, and `v₀ ∈ V` a point with `π v₀ = α₀`. Then `v₀` has a connected
open neighbourhood `V'` such that `π⁻¹(A) ∩ V'` is irreducible with generic point `v₀`.

The proof has two steps. First, `v₀` has no proper generization in `π⁻¹(A)`: a generization
`v₁` maps to a generization of `α₀` inside `A`, which is `α₀` itself since `closure {α₀}` is
maximal among the irreducible subsets of `A`; so `v₁` and `v₀` lie in the fibre over `α₀`,
which is discrete, and `v₁ = v₀`. Second, in a noetherian open neighbourhood of `v₀`, one removes
the finitely many irreducible pieces of `π⁻¹(A)`, and of the neighbourhood itself, that do not
contain `v₀`. What remains is a union of irreducible sets through `v₀`, hence connected, and
its intersection with `π⁻¹(A)` consists of specializations of `v₀`.

## Main results

* `exists_isOpen_isPreconnected_inter_subset_closure_singleton`: in a noetherian quasi-sober
  space, a point `y` of a closed set `B` with no proper generization in `B` has a preconnected
  open neighbourhood `W` with `B ∩ W ⊆ closure {y}`.
* `AlgebraicGeometry.exists_isConnected_isGenericPoint_preimage_of_locallyQuasiFinite`: the
  statement for a locally quasi-finite morphism with locally noetherian source.
* `AlgebraicGeometry.exists_isConnected_isGenericPoint_preimage`: the statement for an étale
  morphism with locally noetherian source.

## Implementation notes

The source works with noetherian schemes throughout; here only the source `V` is assumed
locally noetherian, and of étaleness only local quasi-finiteness (discreteness of the fibres)
is used. That `closure {α₀}` is an irreducible component of `A` is expressed as maximality
of `closure {α₀}` among the irreducible subsets of `A`. That `π⁻¹(A) ∩ V'` is irreducible with
generic point `v₀` is expressed in the subspace `V'`, as `IsGenericPoint`, which implies
irreducibility (`IsGenericPoint.isIrreducible`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
-/

public section

open CategoryTheory TopologicalSpace Topology

/-- The intersection of a preirreducible set with an open set is preirreducible. -/
theorem IsPreirreducible.inter_isOpen {X : Type*} [TopologicalSpace X] {t W : Set X}
    (ht : IsPreirreducible t) (hW : IsOpen W) : IsPreirreducible (t ∩ W) := by
  intro u v hu hv ⟨x, hx, hxu⟩ ⟨y, hy, hyv⟩
  obtain ⟨z, hzt, hzu, hzv⟩ := ht (u ∩ W) (v ∩ W) (hu.inter hW) (hv.inter hW)
    ⟨x, hx.1, hxu, hx.2⟩ ⟨y, hy.1, hyv, hy.2⟩
  exact ⟨z, ⟨hzt, hzu.2⟩, hzu.1, hzv.1⟩

/-- In a noetherian quasi-sober space, a point `y` of a closed set `B` which has no proper
generization inside `B` has a preconnected open neighbourhood `W` such that every point of
`B ∩ W` is a specialization of `y`. -/
theorem exists_isOpen_isPreconnected_inter_subset_closure_singleton {Y : Type*}
    [TopologicalSpace Y] [NoetherianSpace Y] [QuasiSober Y] {B : Set Y} (hB : IsClosed B)
    {y : Y} (hgen : ∀ z ∈ B, z ⤳ y → z = y) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ IsPreconnected W ∧ B ∩ W ⊆ closure {y} := by
  classical
  obtain ⟨S, hSirr, hSeq⟩ := NoetherianSpace.exists_finset_irreducible ⟨B, hB⟩
  obtain ⟨T, hTirr, hTeq⟩ := NoetherianSpace.exists_finset_irreducible (⊤ : Closeds Y)
  have hmemS : ∀ x, x ∈ B → ∃ k ∈ S, x ∈ (k : Set Y) := by
    intro x hx
    have : x ∈ ((S.sup id : Closeds Y) : Set Y) := by rw [← hSeq]; exact hx
    rw [Closeds.coe_finset_sup] at this
    simpa using this
  have hmemT : ∀ x, ∃ k ∈ T, x ∈ (k : Set Y) := by
    intro x
    have : x ∈ ((T.sup id : Closeds Y) : Set Y) := by rw [← hTeq]; trivial
    rw [Closeds.coe_finset_sup] at this
    simpa using this
  set W : Set Y := (⋂ k ∈ S.filter (fun k : Closeds Y => y ∉ k), (k : Set Y)ᶜ) ∩
    (⋂ k ∈ T.filter (fun k : Closeds Y => y ∉ k), (k : Set Y)ᶜ) with hW
  have hWS : ∀ x ∈ W, ∀ k ∈ S, x ∈ (k : Set Y) → y ∈ k := by
    intro x hx k hk hxk
    by_contra hyk
    have := hx.1
    simp only [Set.mem_iInter] at this
    exact this k (Finset.mem_filter.mpr ⟨hk, hyk⟩) hxk
  have hWT : ∀ x ∈ W, ∀ k ∈ T, x ∈ (k : Set Y) → y ∈ k := by
    intro x hx k hk hxk
    by_contra hyk
    have := hx.2
    simp only [Set.mem_iInter] at this
    exact this k (Finset.mem_filter.mpr ⟨hk, hyk⟩) hxk
  have hWopen : IsOpen W :=
    (isOpen_biInter_finset fun k _ => k.isClosed.isOpen_compl).inter
      (isOpen_biInter_finset fun k _ => k.isClosed.isOpen_compl)
  have hyW : y ∈ W := by
    refine ⟨?_, ?_⟩ <;>
    · simp only [Set.mem_iInter]
      intro k hk hyk
      exact (Finset.mem_filter.mp hk).2 hyk
  refine ⟨W, hWopen, hyW, ?_, ?_⟩
  · -- `W` is the union of the preirreducible sets `k ∩ W`, `k ∈ T`, `y ∈ k`.
    have hcover : W = ⋃₀ ((fun k : Closeds Y => (k : Set Y) ∩ W) ''
        {k | k ∈ T ∧ y ∈ k}) := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk, hxk⟩ := hmemT x
        exact ⟨(k : Set Y) ∩ W, ⟨k, ⟨hk, hWT x hx k hk hxk⟩, rfl⟩, hxk, hx⟩
      · rintro ⟨_, ⟨k, _, rfl⟩, hx⟩
        exact hx.2
    rw [hcover]
    refine isPreconnected_sUnion y _ ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨hk.2, hyW⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact ((hTirr ⟨k, hk.1⟩).2.inter_isOpen hWopen).isPreconnected
  · rintro x ⟨hxB, hxW⟩
    obtain ⟨k, hk, hxk⟩ := hmemS x hxB
    have hyk : y ∈ k := hWS x hxW k hk hxk
    have hkirr : IsIrreducible (k : Set Y) := hSirr ⟨k, hk⟩
    have hgp : IsGenericPoint hkirr.genericPoint (k : Set Y) := by
      simpa [k.isClosed.closure_eq] using hkirr.isGenericPoint_genericPoint_closure
    have hkB : (k : Set Y) ⊆ B := by
      intro z hz
      have : z ∈ ((S.sup id : Closeds Y) : Set Y) := by
        rw [Closeds.coe_finset_sup]
        simp only [Finset.sup_eq_iSup, Set.iSup_eq_iUnion, Set.mem_iUnion]
        exact ⟨k, hk, hz⟩
      rw [← hSeq] at this
      exact this
    have hgy : hkirr.genericPoint = y :=
      hgen _ (hkB hgp.mem) (hgp.specializes hyk)
    rw [← hgp.def, hgy] at hxk
    exact hxk

universe u

namespace AlgebraicGeometry

/-- Let `π : V ⟶ X` be a locally quasi-finite morphism with locally noetherian source,
`A ⊆ X` closed, `α₀` the generic point of an irreducible component of `A`, and `π v₀ = α₀`.
Then `v₀` has a connected open neighbourhood `V'` on which `π⁻¹(A) ∩ V'` is irreducible with
generic point `v₀`. -/
theorem exists_isConnected_isGenericPoint_preimage_of_locallyQuasiFinite {V X : Scheme.{u}}
    (π : V ⟶ X) [LocallyQuasiFinite π] [IsLocallyNoetherian V] {A : Set X} (hA : IsClosed A)
    {α₀ : X} (hα₀ : Maximal (fun Z : Set X => IsIrreducible Z ∧ Z ⊆ A) (closure {α₀}))
    {v₀ : V} (hv₀ : π v₀ = α₀) :
    ∃ (V' : V.Opens) (hv : v₀ ∈ V'), _root_.IsConnected (V' : Set V) ∧
      IsGenericPoint (⟨v₀, hv⟩ : V') {x : V' | π x.1 ∈ A} := by
  -- Step 1: `v₀` has no proper generization in `π⁻¹(A)`.
  have hgen : ∀ v, π v ∈ A → v ⤳ v₀ → v = v₀ := by
    intro v hv hsp
    have h1 : π v ⤳ α₀ := hv₀ ▸ hsp.map π.continuous
    have hsub : closure {π v} ⊆ A :=
      hA.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hv)
    have hle : closure {α₀} ⊆ closure {π v} := specializes_iff_closure_subset.mp h1
    have heq : closure {α₀} = closure {π v} :=
      hα₀.eq_of_subset ⟨isIrreducible_singleton.closure, hsub⟩ hle
    have hπv : π v = α₀ := (inseparable_iff_closure_eq.mpr heq.symm).eq
    have hdisc : DiscreteTopology (π ⁻¹' {α₀}) :=
      (π.isDiscrete_preimage_singleton α₀).to_subtype
    have hsp' : (⟨v, hπv⟩ : π ⁻¹' {α₀}) ⤳ ⟨v₀, hv₀⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hsp
    exact congrArg Subtype.val (specializes_iff_eq.mp hsp')
  -- Step 2: work in a noetherian affine open neighbourhood `U` of `v₀`.
  obtain ⟨_, ⟨U, hU, rfl⟩, hv₀U, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v₀) isOpen_univ
  have hUaff : IsAffine (Scheme.Opens.toScheme (X := V) U) := hU
  have hUnoeth : IsNoetherian (Scheme.Opens.toScheme (X := V) U) :=
    (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  have hN : NoetherianSpace U :=
    inferInstanceAs (NoetherianSpace (Scheme.Opens.toScheme (X := V) U))
  have hB : IsClosed {x : U | π x.1 ∈ A} :=
    hA.preimage (π.continuous.comp continuous_subtype_val)
  obtain ⟨W, hWo, hvW, hWc, hWB⟩ :=
    @exists_isOpen_isPreconnected_inter_subset_closure_singleton U _ hN inferInstance _ hB
      ⟨v₀, hv₀U⟩ (fun z hz hsp => Subtype.ext (hgen z.1 hz (hsp.map continuous_subtype_val)))
  let V' : V.Opens := ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hWo⟩
  have hv : v₀ ∈ V' := ⟨⟨v₀, hv₀U⟩, hvW, rfl⟩
  refine ⟨V', hv, ⟨⟨v₀, hv⟩, hWc.image _ continuous_subtype_val.continuousOn⟩, ?_⟩
  apply subset_antisymm
  · exact (hA.preimage (π.continuous.comp continuous_subtype_val)).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (by simpa [hv₀] using hα₀.prop.2 (subset_closure rfl)))
  · rintro ⟨x, hxV'⟩ hx
    obtain ⟨w, hwW, rfl⟩ := hxV'
    have hw : (⟨v₀, hv₀U⟩ : U) ⤳ w := specializes_iff_mem_closure.mpr (hWB ⟨hx, hwW⟩)
    apply specializes_iff_mem_closure.mp
    exact Topology.IsInducing.subtypeVal.specializes_iff.mp (hw.map continuous_subtype_val)

/-- Let `π : V ⟶ X` be an étale morphism with locally noetherian source, `A ⊆ X` a closed
subset, `α₀` the generic point of an irreducible component of `A` (that is, `closure {α₀}` is
maximal among the irreducible subsets of `A`), and `v₀ ∈ V` with `π v₀ = α₀`. Then there is a
connected open neighbourhood `V'` of `v₀` such that `π⁻¹(A) ∩ V'` is irreducible with generic
point `v₀`. -/
@[weil "lem_fk103_etale_neighbourhood_irreducible_preimage"]
theorem exists_isConnected_isGenericPoint_preimage {V X : Scheme.{u}} (π : V ⟶ X) [Etale π]
    [IsLocallyNoetherian V] {A : Set X} (hA : IsClosed A) {α₀ : X}
    (hα₀ : Maximal (fun Z : Set X => IsIrreducible Z ∧ Z ⊆ A) (closure {α₀}))
    {v₀ : V} (hv₀ : π v₀ = α₀) :
    ∃ (V' : V.Opens) (hv : v₀ ∈ V'), _root_.IsConnected (V' : Set V) ∧
      IsGenericPoint (⟨v₀, hv⟩ : V') {x : V' | π x.1 ∈ A} := by
  have : LocallyQuasiFinite π := (locallyQuasiFinite_of_etale π).2
  exact exists_isConnected_isGenericPoint_preimage_of_locallyQuasiFinite π hA hα₀ hv₀

end AlgebraicGeometry
