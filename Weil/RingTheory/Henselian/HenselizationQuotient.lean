module

public import Weil.Attr
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.Henselian.Quotient
public import Weil.Defs.RingTheory.Henselian.Henselization.Defs

/-!
# The Henselization modulo an ideal with henselian quotient

Let `R` be a local ring, `R → R^h` its Henselization, and `I ⊆ 𝔪_R` an ideal such that `R/I` is
henselian. Then the canonical map `R/I → R^h/I R^h` is an isomorphism.

The proof uses the universal property of the Henselization twice. Since `R/I` is henselian and
`R → R/I` is local, there is a local `R`-algebra map `π : R^h → R/I`; it kills `I R^h` and so
induces `π̄ : R^h/I R^h → R/I`. The composite `π̄ ∘ c` with the canonical map `c` is an
`R`-algebra endomorphism of `R/I`, hence the identity. The ring `R^h/I R^h` is a quotient of the
henselian local ring `R^h` by a proper ideal, hence henselian, and `c ∘ π` and the projection
`R^h → R^h/I R^h` are two local `R`-algebra maps into it, so they agree by uniqueness; hence
`c ∘ π̄` is the identity.

## Main results

* `IsLocalRing.IsHenselization.quotientMap_bijective_of_henselianLocalRing`: the canonical map
  `R/I → R^h/I R^h` is bijective.
* `IsLocalRing.IsHenselizationAlong.quotientMap_bijective_of_henselianLocalRing`: the same for
  a Henselization `(R^h, ψ)` of `R` with respect to the residue map.

## Implementation notes

The source assumes `R` noetherian; the proof does not need it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open IsLocalRing

namespace IsLocalRing

/-- **The Henselization modulo an ideal with henselian quotient.** Let `R` be a local ring, `R^h`
its Henselization and `I ⊆ 𝔪_R` an ideal with `R/I` henselian. Then the canonical map
`R/I → R^h/I R^h` is bijective. -/
@[weil "lem_fk107_henselization_modulo_henselian_quotient"]
theorem IsHenselization.quotientMap_bijective_of_henselianLocalRing
    {R : Type*} [CommRing R] [IsLocalRing R] {Rh : Type*} [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh] [IsHenselization R (ResidueField R) Rh]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) [HenselianLocalRing (R ⧸ I)] :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R Rh)) (algebraMap R Rh) Ideal.le_comap_map) := by
  have hloc : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  have hRh : HenselianLocalRing Rh := IsHenselization.henselian (R := R) (L := ResidueField R)
  set J := I.map (algebraMap R Rh) with hJ
  have hJne : J ≠ ⊤ := by
    refine ne_top_of_le_ne_top (maximalIdeal.isMaximal Rh).ne_top ?_
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro x hx
    exact (mem_maximalIdeal _).2 fun hu =>
      (mem_maximalIdeal x).1 (hI hx) (isUnit_of_map_unit _ x hu)
  have hQ : HenselianLocalRing (Rh ⧸ J) := Stacks.Henselian.henselianLocalRing_quotient hJne
  let c : R ⧸ I →ₐ[R] Rh ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R Rh) Ideal.le_comap_map
  have hc : ∀ x, Ideal.quotientMap J (algebraMap R Rh) Ideal.le_comap_map x = c x := fun _ => rfl
  -- the local map `R → R/I`
  have hmk : IsLocalHom (algebraMap R (R ⧸ I)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨π, hπ, -, -⟩ := StacksDraft.existsUnique_henselization_map (R := R) (A := R)
    (Ah := Rh) (B := R ⧸ I)
  -- `π` kills `I R^h`
  have hπJ : J ≤ RingHom.ker π.toRingHom := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro x hx
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  let πbar : Rh ⧸ J →ₐ[R] R ⧸ I := Ideal.Quotient.liftₐ J π hπJ
  have h1 : πbar.comp c = AlgHom.id R (R ⧸ I) := Ideal.Quotient.algHom_ext R (AlgHom.ext fun _ =>
    by simp [c, πbar, Ideal.quotientMapₐ, Ideal.quotientMap_mk])
  -- the local map `R → R^h/I R^h`
  have hmkJ : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hRQ : IsLocalHom (algebraMap R (Rh ⧸ J)) := by
    rw [IsScalarTower.algebraMap_eq R Rh (Rh ⧸ J), Ideal.Quotient.algebraMap_eq]
    exact RingHom.isLocalHom_comp _ _
  have hcloc : IsLocalHom c := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have : IsUnit (algebraMap R (Rh ⧸ J) r) := by
      simpa [c, Ideal.quotientMapₐ, Ideal.quotientMap_mk] using hx
    exact (isUnit_of_map_unit _ r this).map (Ideal.Quotient.mk I)
  obtain ⟨g, -, -, hg⟩ := StacksDraft.existsUnique_henselization_map (R := R) (A := R)
    (Ah := Rh) (B := Rh ⧸ J)
  have hcπ : c.comp π = g := hg _ (by
    have : IsLocalHom (c.toRingHom.comp π.toRingHom) := @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
      ⟨hcloc.map_nonunit⟩ ⟨hπ.map_nonunit⟩
    exact ⟨this.map_nonunit⟩) (RingHom.ext fun r => (c.comp π).commutes r)
  have hmkg : Ideal.Quotient.mkₐ R J = g := hg _ ⟨hmkJ.map_nonunit⟩
    (RingHom.ext fun r => (Ideal.Quotient.mkₐ R J).commutes r)
  have h2 : c.comp πbar = AlgHom.id R (Rh ⧸ J) := by
    refine Ideal.Quotient.algHom_ext R (AlgHom.ext fun x => ?_)
    have := AlgHom.congr_fun (hcπ.trans hmkg.symm) x
    have hl : πbar (Ideal.Quotient.mk J x) = π x := Ideal.Quotient.liftₐ_apply J π hπJ _
    simpa [hl] using this
  have hfun : Ideal.quotientMap J (algebraMap R Rh) Ideal.le_comap_map = c.toRingHom :=
    RingHom.ext hc
  rw [hfun]
  exact Function.bijective_iff_has_inverse.mpr ⟨πbar, fun x => AlgHom.congr_fun h1 x,
    fun x => AlgHom.congr_fun h2 x⟩

/-- **The Henselization modulo an ideal with henselian quotient**, for a Henselization `(R^h, ψ)`
of `R` with respect to the residue map `R → κ`: for `I ⊆ 𝔪_R` with `R/I` henselian, the canonical
map `R/I → R^h/I R^h` is bijective. -/
@[weil "lem_fk107_henselization_modulo_henselian_quotient"]
theorem IsHenselizationAlong.quotientMap_bijective_of_henselianLocalRing
    {R : Type*} [CommRing R] [IsLocalRing R] {Rh : Type*} [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh] {ψ : Rh →+* ResidueField R} (h : IsHenselizationAlong (residue R) Rh ψ)
    (I : Ideal R) (hI : I ≤ maximalIdeal R) [HenselianLocalRing (R ⧸ I)] :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R Rh)) (algebraMap R Rh) Ideal.le_comap_map) :=
  have := (isHenselizationAlong_residue_iff.mp h).1
  IsHenselization.quotientMap_bijective_of_henselianLocalRing I hI

end IsLocalRing
