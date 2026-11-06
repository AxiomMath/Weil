module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings

/-!
# Torsion orders of sections of a filtered colimit of étale sheaves

Let `N` be a set of natural numbers, `S` a scheme and `(G_ν)_{ν ∈ I}` a filtered diagram of
sheaves of abelian groups on the small étale site of `S` such that each `G_ν` is annihilated by
some element of `N`. Then for every object `U` of the site whose underlying scheme is
quasi-compact and quasi-separated, every section of `colim_ν G_ν` over `U` is annihilated by an
element of `N`. Indeed, sections over such a `U` commute with filtered colimits, so a section
comes from a section of some `G_ν`, which is killed by the order of `G_ν`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_mem_nsmul_eq_zero_colimit_sheafSections` — every section
  over a quasi-compact quasi-separated object of a filtered colimit of abelian étale sheaves,
  each annihilated by an element of `N`, is annihilated by an element of `N`.

## Implementation notes

Freitag–Kiehl take `N` a set of positive integers closed under products; neither condition is
used, so the statement is for an arbitrary `N : Set ℕ`. The objects of their étale category are
étale `S`-schemes with noetherian separated source, which are quasi-compact and
quasi-separated, so the hypotheses on `U` cover their case.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Torsion orders of sections of a filtered colimit.** Let `F` be a filtered diagram of
abelian sheaves on the small étale site of `S` such that each `F ν` is annihilated by some
element of `N`. Then every section of `colim F` over an object `U` with quasi-compact
quasi-separated underlying scheme is annihilated by an element of `N`. -/
@[weil "lem_fk108_torsion_orders_in_set_colimit"]
theorem exists_mem_nsmul_eq_zero_colimit_sheafSections (N : Set ℕ) {I : Type (u + 1)}
    [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1})
    (hF : ∀ ν, ∃ n ∈ N, ∀ (V : (SmallEtale B S hS)ᵒᵖ) (x : (F.obj ν).obj.obj V), n • x = 0)
    (U : SmallEtale B S hS)
    (hU : CompactSpace ((SmallEtale.toScheme B S hS).obj U))
    (hQS : QuasiSeparatedSpace ((SmallEtale.toScheme B S hS).obj U))
    (x : (colimit F).obj.obj (op U)) :
    ∃ n ∈ N, n • x = 0 := by
  let Sec := (sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}).obj (op U)
  obtain ⟨y, rfl⟩ := (bijective_colimit_post_sheafSections_addCommGrp B S hS F U hU hQS).2 x
  obtain ⟨ν, τ, rfl⟩ := Concrete.colimit_exists_rep (F ⋙ Sec) y
  obtain ⟨n, hn, hτ⟩ := hF ν
  refine ⟨n, hn, ?_⟩
  rw [← map_nsmul, ← map_nsmul, hτ (op U) τ, map_zero, map_zero]

end AlgebraicGeometry.SmallEtale

end
