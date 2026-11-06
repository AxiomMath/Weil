module

public import Weil.Attr
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Continuity of a linear group action on an adic module

Let `R` be a commutative ring, `I` an ideal of `R` and `M` a finitely generated `R`-module with
its `I`-adic topology, in which the submodules `I ^ n M` form a basis of neighbourhoods of `0`.
Let a topological group `π` act `R`-linearly on `M`. For `n ≥ 0` let `Kₙ ⊆ π` be the subgroup of
elements acting trivially on `M / I ^ (n + 1) M`. The action map `π × M → M` is continuous if
and only if every `Kₙ` is open in `π`.

For `R = ℤ_l` and `I = (l)` this is the description of continuous `l`-adic representations of a
profinite group by their finite quotients `M / l ^ (n + 1) M`.

## Main results

* `Ideal.hasBasis_nhds_adicModuleTopology`: the cosets `x + I ^ n M` form a basis of
  neighbourhoods of `x` in the `I`-adic topology.
* `continuous_smul_iff_isOpen_setOf_smul_sub_mem_pow_smul_top`: the action map is continuous if
  and only if all the subgroups `Kₙ` are open.

## Implementation notes

The statement is made for an arbitrary commutative ring `R` with an ideal `I` and an arbitrary
topological group `π`; profiniteness of `π` and `R = ℤ_l`, `I = (l)` are not needed. The
topology of `M` is an instance argument together with a hypothesis identifying it with
`I.adicModuleTopology M`, and `Kₙ` is written as the set of `g` with `g • m - m ∈ I ^ (n + 1) M`
for all `m`. Finite generation of `M` is used only for the direction continuity ⇒ openness.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], Appendix A I
-/

@[expose] public section

open Filter Topology

variable {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]

/-- In the `I`-adic topology of an `R`-module `M`, the cosets `x + I ^ n M` form a basis of
neighbourhoods of `x`. -/
theorem Ideal.hasBasis_nhds_adicModuleTopology (x : M) :
    HasBasis (@nhds M (I.adicModuleTopology M) x) (fun _ : ℕ => True)
    fun n => {y | y - x ∈ I ^ n • (⊤ : Submodule R M)} := by
  let := I.adicModuleTopology M
  let := I.adicTopology
  have h := (AddGroupFilterBasis.nhds_hasBasis
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis x)
  refine ⟨fun s => ?_⟩
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, ⟨n, rfl⟩, hV⟩
    refine ⟨n, trivial, fun y hy => hV ⟨y - x, hy, by simp⟩⟩
  · rintro ⟨n, -, hn⟩
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hn (by simpa using hz)

/-- In the `I`-adic topology of an `R`-module `M`, every coset `x + I ^ n M` is open. -/
theorem Ideal.isOpen_setOf_sub_mem_pow_smul_top (n : ℕ) (x : M) :
    IsOpen[I.adicModuleTopology M] {y | y - x ∈ I ^ n • (⊤ : Submodule R M)} := by
  let := I.adicModuleTopology M
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [(I.hasBasis_nhds_adicModuleTopology y).mem_iff]
  refine ⟨n, trivial, fun z hz => ?_⟩
  have := add_mem (show z - y ∈ I ^ n • (⊤ : Submodule R M) from hz)
    (show y - x ∈ I ^ n • (⊤ : Submodule R M) from hy)
  simpa using this

variable {π : Type*} [Group π] [DistribMulAction π M] [SMulCommClass π R M]

/-- A group acting `R`-linearly on `M` preserves each submodule `I ^ n M`. -/
theorem Ideal.smul_mem_pow_smul_top (n : ℕ) (g : π) {x : M} (hx : x ∈ I ^ n • (⊤ : Submodule R M)) :
    g • x ∈ I ^ n • (⊤ : Submodule R M) := by
  have : (I ^ n • (⊤ : Submodule R M)).map (DistribSMul.toLinearMap R M g) ≤
      I ^ n • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨x, hx, rfl⟩

/-- Let `π` be a topological group acting `R`-linearly on a finitely generated `R`-module `M`
carrying its `I`-adic topology. The action map `π × M → M` is continuous if and only if, for
every `n`, the subgroup `Kₙ` of elements acting trivially on `M / I ^ (n + 1) M` is open. -/
@[weil "lem_fka1_continuous_action_iff_finite_quotients"]
theorem continuous_smul_iff_isOpen_setOf_smul_sub_mem_pow_smul_top
    [TopologicalSpace π] [IsTopologicalGroup π] [TopologicalSpace M]
    (hM : ‹TopologicalSpace M› = I.adicModuleTopology M) [Module.Finite R M] :
    Continuous (fun p : π × M => p.1 • p.2) ↔
      ∀ n : ℕ, IsOpen {g : π | ∀ m : M, g • m - m ∈ I ^ (n + 1) • (⊤ : Submodule R M)} := by
  subst hM
  let := I.adicModuleTopology M
  constructor
  · intro hc n
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
    have heq : {g : π | ∀ m : M, g • m - m ∈ I ^ (n + 1) • (⊤ : Submodule R M)} =
        ⋂ m ∈ (s : Set M), {g : π | g • m - m ∈ I ^ (n + 1) • (⊤ : Submodule R M)} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      refine ⟨fun h m _ => h m, fun h m => ?_⟩
      have hm : m ∈ Submodule.span R (s : Set M) := hs ▸ Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x y _ _ hx hy =>
        rw [smul_add, add_sub_add_comm]
        exact add_mem hx hy
      | smul r x _ hx =>
        rw [smul_comm, ← smul_sub]
        exact Submodule.smul_mem _ r hx
    rw [heq]
    refine isOpen_biInter_finset fun m _ => ?_
    exact (I.isOpen_setOf_sub_mem_pow_smul_top (n + 1) m).preimage
      (hc.comp (Continuous.prodMk_left m))
  · intro hK
    refine continuous_iff_continuousAt.2 fun ⟨g, m⟩ => ?_
    rw [ContinuousAt, (I.hasBasis_nhds_adicModuleTopology (g • m)).tendsto_right_iff]
    intro n _
    have hle : I ^ (n + 1) • (⊤ : Submodule R M) ≤ I ^ n • (⊤ : Submodule R M) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
    have hU : {h : π | g⁻¹ * h ∈ {g : π | ∀ m : M, g • m - m ∈ I ^ (n + 1) • (⊤ : Submodule R M)}}
        ∈ 𝓝 g :=
      ((hK n).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
    have hV := (I.hasBasis_nhds_adicModuleTopology m).mem_of_mem (i := n + 1) trivial
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod hU hV] with ⟨h, m'⟩ ⟨hh, hm'⟩
    simp only [Set.mem_ofPred_eq] at hh hm' ⊢
    have key : h • m' - g • m = h • (m' - m) + g • ((g⁻¹ * h) • m - m) := by
      rw [smul_sub, smul_sub, ← mul_smul, mul_inv_cancel_left]
      abel
    rw [key]
    exact hle (add_mem (I.smul_mem_pow_smul_top _ h hm') (I.smul_mem_pow_smul_top _ g (hh m)))

end
