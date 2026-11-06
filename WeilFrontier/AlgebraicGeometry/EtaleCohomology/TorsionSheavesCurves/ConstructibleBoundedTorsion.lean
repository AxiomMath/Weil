module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles

/-!
# Constructible sheaves of prime-to-the-characteristic torsion are killed by an invertible integer

Let `X` be a quasi-compact quasi-separated scheme, `k` a nontrivial commutative ring and `F` a
constructible abelian sheaf on the small étale site of `X` every section of which has an additive
order invertible in `k`. Then some positive integer `n`, invertible in `k`, satisfies
`n • 𝟙 F = 0`. For `k` a field and `X` of finite type over `k`, this says that a constructible
sheaf whose sections have order prime to `char k` is killed by an integer prime to `char k`.

## Main results

* `AlgebraicGeometry.exists_nsmul_id_eq_zero_isUnit_of_isConstructibleAbelianSheaf`: the
  statement for a quasi-compact quasi-separated scheme.
* `AlgebraicGeometry.exists_nsmul_id_eq_zero_isUnit_of_isConstructibleAbelianSheaf_of_finiteType`:
  the statement for a scheme of finite type over a field `k`.

## Implementation notes

A constructible abelian sheaf on a quasi-compact quasi-separated scheme is a finitely presentable
object of the category of abelian sheaves, and a torsion sheaf is the union of its subsheaves
`F[N!]`; so the identity of `F` factors through one of them and `F` is killed by some `N > 0`.
Every section then has order dividing `N` and invertible in `k`; the product of the divisors of
`N` that are invertible in `k` is invertible in `k` and kills every section. This replaces the
stalkwise argument of [FK] (finitely many finite stalk groups, the least common multiple of
their exponents) by the finite presentability of constructible sheaves (Stacks, Tag 09Z4).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The value of a multiple of a morphism of abelian sheaves on a section. -/
private lemma nsmul_hom_val_app_apply {F G : Sheaf (SmallEtale.topology B X.obj X.property)
      AddCommGrpCat.{u + 1}} (n : ℕ) (f : F ⟶ G) (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (x : F.obj.obj U) : (n • f).hom.app U x = n • f.hom.app U x := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

/-- A constructible torsion abelian sheaf on a quasi-compact quasi-separated scheme is killed by a
positive integer (on the small étale site cut out of a big étale site). -/
private lemma exists_nsmul_id_eq_zero_of_torsion [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hc : IsConstructibleAbelianSheaf B X F)
    (ht : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  let := SmallEtale.isGrothendieckAbelian_sheaf_succ B X.obj X.property
  let : ∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
    fun S T g => Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence
      (smallEtaleBaseChange B g) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
    fun T V => Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ
      (SmallEtale.topology B T.obj T.property) V
  have := isFinitelyPresentable_of_isConstructibleAbelianSheaf B X
    (hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B X) F hc
  have hcol : IsColimit (Cocone.mk F
      (Stacks.Torsion.torsionFiltrationι (SmallEtale.topology B X.obj X.property) F)) := by
    have : IsIso (Stacks.Torsion.torsionFiltrationDesc
        (SmallEtale.topology B X.obj X.property) F) :=
      Stacks.Torsion.isIso_torsionFiltrationDesc _ F ht
    exact IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (Stacks.Torsion.torsionFiltrationDesc
        (SmallEtale.topology B X.obj X.property) F))
        (fun j => Stacks.Torsion.ι_torsionFiltrationDesc _ F j))
  obtain ⟨j, r, hr⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcol (𝟙 F)
  refine ⟨Nat.factorial j.down, Nat.factorial_pos _, ?_⟩
  calc (Nat.factorial j.down) • 𝟙 F
        = r ≫ ((Stacks.Torsion.torsionFiltrationι
            (SmallEtale.topology B X.obj X.property) F).app j ≫
          ((Nat.factorial j.down) • 𝟙 F)) := by rw [← Category.assoc, hr, Category.id_comp]
    _ = r ≫ 0 := congrArg (r ≫ ·) (kernel.condition _)
    _ = 0 := comp_zero

/-- **A constructible sheaf with sections of invertible order is killed by an invertible
integer.** Let `X` be a quasi-compact quasi-separated scheme, `k` a nontrivial commutative ring and
`F` a constructible abelian sheaf on the small étale site of `X` each section of which has an
additive order invertible in `k`. Then there is an integer `n ≥ 1`, invertible in `k`, with
`n • 𝟙 F = 0`. -/
theorem exists_nsmul_id_eq_zero_isUnit_of_isConstructibleAbelianSheaf [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj] (k : Type v) [CommRing k] [Nontrivial k]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hc : IsConstructibleAbelianSheaf B X F)
    (hord : ∀ (U : (SmallEtale B X.obj X.property)ᵒᵖ) (s : F.obj.obj U),
      IsUnit ((addOrderOf s : ℕ) : k)) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : k) ∧ n • 𝟙 F = 0 := by
  classical
  have hpos : ∀ (U : (SmallEtale B X.obj X.property)ᵒᵖ) (s : F.obj.obj U),
      0 < addOrderOf s := fun U s => by
    refine Nat.pos_of_ne_zero fun h => ?_
    have := hord U s
    rw [h, Nat.cast_zero] at this
    exact not_isUnit_zero this
  have ht : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F :=
    fun U x => ⟨⊤, (SmallEtale.topology B X.obj X.property).top_mem U, fun V f _ =>
      ⟨addOrderOf (F.obj.map f.op x), hpos _ _, addOrderOf_nsmul_eq_zero _⟩⟩
  obtain ⟨N, hN, hNF⟩ := exists_nsmul_id_eq_zero_of_torsion B X F hc ht
  have hdvd : ∀ (U : (SmallEtale B X.obj X.property)ᵒᵖ) (s : F.obj.obj U),
      addOrderOf s ∣ N := fun U s => by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    have := congrArg (fun φ : F ⟶ F => φ.hom.app U s) hNF
    simpa [nsmul_hom_val_app_apply] using this
  let S := N.divisors.filter fun d : ℕ => IsUnit ((d : ℕ) : k)
  refine ⟨∏ d ∈ S, d, Finset.prod_pos fun d hd => ?_, ?_, ?_⟩
  · exact Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  · rw [Nat.cast_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one
      fun d hd => (Finset.mem_filter.mp hd).2
  · ext U s
    rw [nsmul_hom_val_app_apply]
    have h0 : (0 : F ⟶ F).hom.app U s = 0 := rfl
    have h1 : (𝟙 F : F ⟶ F).hom.app U s = s := rfl
    rw [h0, h1]
    exact (addOrderOf_dvd_iff_nsmul_eq_zero).mp (Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd U s, hN.ne'⟩, hord U s⟩))

/-- **A constructible sheaf with sections of order prime to `char k` is killed by an integer
prime to `char k`.** Let `k` be a field, `X` a `k`-scheme of finite type and `F` a constructible
abelian sheaf on the small étale site of `X` whose sections have order invertible in `k`. Then
there is an integer `n ≥ 1`, invertible in `k`, with `n • 𝟙 F = 0`. -/
@[weil "lem_fk105_constructible_prime_to_char_killed_by_n"]
theorem exists_nsmul_id_eq_zero_isUnit_of_isConstructibleAbelianSheaf_of_finiteType
    (k : Type u) [Field k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hc : IsConstructibleAbelianSheaf B X F)
    (hord : ∀ (U : (SmallEtale B X.obj X.property)ᵒᵖ) (s : F.obj.obj U),
      IsUnit ((addOrderOf s : ℕ) : k)) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : k) ∧ n • 𝟙 F = 0 := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X.obj := ⟨⟩
  exact exists_nsmul_id_eq_zero_isUnit_of_isConstructibleAbelianSheaf B X k F hc hord

end AlgebraicGeometry

end
