module

public import Weil.CategoryTheory.Sites.Cohomology.Torsion.ArCategorySheaves
public import Weil.Attr

/-!
# Kernels and cokernels in the Artin–Rees category of `l`-torsion sheaves

Let `P_S` be the category of projective systems of `l`-torsion sheaves on the small étale site
of a scheme `S`, and `AR_S` its Artin–Rees category. Let `φ = [r, f] : F ⟶ G` be the A–R morphism
represented by `f : F[r] ⟶ G`, and let `k : K ⟶ F[r]` be a kernel and `c : G ⟶ C` a cokernel of
`f` in `P_S`. Then `[ε_r] ∘ [k] : K ⟶ F` is a kernel and `[c] : G ⟶ C` is a cokernel of `φ` in
`AR_S`, where `[-]` is the canonical functor `P_S ⥤ AR_S` and `ε_r : F[r] ⟶ F` the natural
morphism.

The proof writes `φ = [ε_r]⁻¹ ∘ [f]`, which reduces the statement to the case `r = 0`. An A–R
morphism `[s, g]` vanishes if and only if `g ∘ (F[t] ⟶ F[s]) = 0` for some `t ≥ s`; a
representative of a morphism into `F` killed by `[f]` therefore factors through `k` after
restriction to a deeper level, and a representative of a morphism out of `G` killing `[f]`
factors through `c[t]`, which is a cokernel of `f[t]` since the shift `[t]` is an
autoequivalence of `P_S`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftEquiv t`: the shift `[t]` as an
  autoequivalence of `P_S`, with inverse `[-t]`.

## Main results

* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.homMk_eq_zero_iff`: `[r, f] = 0` if
  and only if `f ∘ (F[t] ⟶ F[r]) = 0` for some `t ≥ r`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.isLimitKernelForkHomMk`: the A–R
  morphism `[ε_r] ∘ [k]` is a kernel of `[r, f]`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.isColimitCokernelCoforkHomMk`: the
  A–R morphism `[c]` is a cokernel of `[r, f]`.

## Implementation notes

The kernel and cokernel of `f` are arbitrary limit and colimit (co)forks in `P_S`; no
description of them by components is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

namespace LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

variable (B S hS l) in
/-- The shift `[t]` is an autoequivalence of the category of projective systems of `l`-torsion
sheaves, with inverse the shift `[-t]`. -/
def shiftEquiv (t : ℤ) :
    LTorsionProjectiveSystem.{w} B S hS l ≌ LTorsionProjectiveSystem.{w} B S hS l :=
  CategoryTheory.Equivalence.mk (shift B S hS l t) (shift B S hS l (-t))
    (shiftZeroIso.symm ≪≫ eqToIso (congrArg (shift B S hS l) (add_neg_cancel t).symm) ≪≫
      (shiftAddIso t (-t)).symm)
    (shiftAddIso (-t) t ≪≫ eqToIso (congrArg (shift B S hS l) (neg_add_cancel t)) ≪≫
      shiftZeroIso)

/-- The shift of a cokernel is a cokernel of the shifted morphism. -/
def isColimitCokernelCoforkShiftMap {X Y Q : LTorsionProjectiveSystem.{w} B S hS l} {f : X ⟶ Y}
    {c : Y ⟶ Q} {hc : f ≫ c = 0} (h : IsColimit (CokernelCofork.ofπ c hc)) (t : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := (shift B S hS l t).map f) ((shift B S hS l t).map c)
      (by rw [← Functor.map_comp, hc, Functor.map_zero])) :=
  have : PreservesColimit (parallelPair f 0) (shiftEquiv.{w} B S hS l t).functor :=
    ((shiftEquiv.{w} B S hS l t).toAdjunction.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape (J := WalkingParallelPair)).preservesColimit
  CokernelCofork.mapIsColimit _ h (shiftEquiv.{w} B S hS l t).functor

end LTorsionProjectiveSystem

namespace ArLTorsionProjectiveSystem

open LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

/-- An A–R morphism `[r, f]` vanishes if and only if `f ∘ (F[t] ⟶ F[r]) = 0` for some `t ≥ r`. -/
lemma homMk_eq_zero_iff {F G : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    homMk r f = 0 ↔ ∃ (t : ℕ) (h : r ≤ t), shiftMap F h ≫ f = 0 := by
  rw [← homMk_zero (F := F) (G := G) 0, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨t, hr, _, e⟩
    exact ⟨t, hr, by rw [e, Limits.comp_zero]⟩
  · rintro ⟨t, hr, e⟩
    exact ⟨t, hr, Nat.zero_le t, by rw [e, Limits.comp_zero]⟩

/-- `[s, g] ∘ [0, k ∘ ε_0] = [s, k ∘ g]`: postcomposition with the image of a morphism `k` of
`P_S` (`toAr_map`). -/
lemma homMk_comp_homMk_shiftι_zero {F G H : LTorsionProjectiveSystem.{w} B S hS l} {s : ℕ}
    (g : (shift B S hS l (s : ℤ)).obj F ⟶ G) (k : G ⟶ H) :
    homMk s g ≫ homMk 0 ((shiftι B S hS l 0).app G ≫ k) = homMk s (g ≫ k) := by
  rw [homMk_comp_homMk, shiftι_naturality_assoc, shiftShift_comp_shiftι_zero_assoc,
    homMk_shiftMap_comp]

/-- `[0, c ∘ ε_0] ∘ [s, g] = [s, g ∘ c[s]]`: precomposition with the image of a morphism `c` of
`P_S` (`toAr_map`). -/
lemma homMk_shiftι_zero_comp_homMk {F G H : LTorsionProjectiveSystem.{w} B S hS l} {s : ℕ}
    (c : F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj G ⟶ H) :
    homMk 0 ((shiftι B S hS l 0).app F ≫ c) ≫ homMk s g =
      homMk s ((shift B S hS l (s : ℤ)).map c ≫ g) := by
  rw [homMk_comp_homMk, Functor.map_comp, Category.assoc,
    shiftShift_comp_shift_map_shiftι_zero_assoc, homMk_shiftMap_comp]

/-- `[r, f] = [r, id] ∘ [0, f ∘ ε_0]`, that is `[r, f] = [ε_r]⁻¹ ∘ [f]` (`shiftιIso_inv`). -/
lemma homMk_eq_homMk_id_comp {F G : LTorsionProjectiveSystem.{w} B S hS l} (r : ℕ)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    homMk r f = homMk r (𝟙 _) ≫ homMk 0 ((shiftι B S hS l 0).app _ ≫ f) := by
  rw [homMk_comp_homMk_shiftι_zero, Category.id_comp]

/-- The image `[0, k ∘ ε_0]` of a monomorphism `k` of `P_S` is a monomorphism. -/
lemma mono_homMk_shiftι_zero {K F : LTorsionProjectiveSystem.{w} B S hS l} (k : K ⟶ F)
    [Mono k] : Mono (homMk 0 ((shiftι B S hS l 0).app K ≫ k)) := by
  refine Preadditive.mono_of_cancel_zero _ fun {P} θ hθ => ?_
  induction θ using hom_induction with
  | h s h' =>
    obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff (h' ≫ k)).mp
      ((homMk_comp_homMk_shiftι_zero h' k).symm.trans hθ)
    rw [← Category.assoc, ← Limits.zero_comp (f := k)] at e
    exact (homMk_eq_zero_iff h').mpr ⟨t, hst, cancel_mono k |>.mp e⟩

/-- The image `[0, c ∘ ε_0]` of a cokernel morphism `c` of `P_S` is an epimorphism. -/
lemma epi_homMk_shiftι_zero {X Y Q : LTorsionProjectiveSystem.{w} B S hS l} {f : X ⟶ Y}
    {c : Y ⟶ Q} {hc : f ≫ c = 0} (h : IsColimit (CokernelCofork.ofπ c hc)) :
    Epi (homMk 0 ((shiftι B S hS l 0).app Y ≫ c)) := by
  refine Preadditive.epi_of_cancel_zero _ fun {R} θ hθ => ?_
  induction θ using hom_induction with
  | h s h' =>
    obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff _).mp
      ((homMk_shiftι_zero_comp_homMk c h').symm.trans hθ)
    rw [← Category.assoc, ← shiftMap_naturality, Category.assoc] at e
    have : Epi ((shift B S hS l (t : ℤ)).map c) :=
      Cofork.IsColimit.epi (isColimitCokernelCoforkShiftMap h (t : ℤ))
    rw [← Limits.comp_zero (f := (shift B S hS l (t : ℤ)).map c)] at e
    exact (homMk_eq_zero_iff h').mpr ⟨t, hst, cancel_epi _ |>.mp e⟩

/-- A morphism of the A–R category into `X` killed by the image of `f` factors through the image
of `k`, for `k` a kernel of `f` in `P_S`. -/
lemma exists_comp_homMk_shiftι_zero_eq {X Y K : LTorsionProjectiveSystem.{w} B S hS l}
    {f : X ⟶ Y} {k : K ⟶ X} {hk : k ≫ f = 0} (h : IsLimit (KernelFork.ofι k hk))
    {A : ArLTorsionProjectiveSystem.{w} B S hS l} (ψ : A ⟶ of X)
    (hψ : ψ ≫ homMk 0 ((shiftι B S hS l 0).app X ≫ f) = 0) :
    ∃ m : A ⟶ of K, m ≫ homMk 0 ((shiftι B S hS l 0).app K ≫ k) = ψ := by
  induction ψ using hom_induction with
  | h s g =>
    obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff _).mp
      ((homMk_comp_homMk_shiftι_zero g f).symm.trans hψ)
    obtain ⟨m, hm⟩ := KernelFork.IsLimit.lift' h (shiftMap A.obj hst ≫ g)
      (by rw [Category.assoc, e])
    refine ⟨homMk t m, (homMk_comp_homMk_shiftι_zero m k).trans ?_⟩
    have hm' : m ≫ k = shiftMap A.obj hst ≫ g := hm
    rw [hm', homMk_shiftMap_comp]

/-- A morphism of the A–R category out of `Y` killing the image of `f` factors through the image
of `c`, for `c` a cokernel of `f` in `P_S`. -/
lemma exists_homMk_shiftι_zero_comp_eq {X Y Q : LTorsionProjectiveSystem.{w} B S hS l}
    {f : X ⟶ Y} {c : Y ⟶ Q} {hc : f ≫ c = 0} (h : IsColimit (CokernelCofork.ofπ c hc))
    {A : ArLTorsionProjectiveSystem.{w} B S hS l} (ψ : of Y ⟶ A)
    (hψ : homMk 0 ((shiftι B S hS l 0).app X ≫ f) ≫ ψ = 0) :
    ∃ m : of Q ⟶ A, homMk 0 ((shiftι B S hS l 0).app Y ≫ c) ≫ m = ψ := by
  induction ψ using hom_induction with
  | h s g =>
    obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff _).mp
      ((homMk_shiftι_zero_comp_homMk f g).symm.trans hψ)
    rw [← Category.assoc, ← shiftMap_naturality, Category.assoc] at e
    obtain ⟨m, hm⟩ := CokernelCofork.IsColimit.desc' (isColimitCokernelCoforkShiftMap h (t : ℤ))
      (shiftMap Y hst ≫ g) e
    refine ⟨homMk t m, (homMk_shiftι_zero_comp_homMk c m).trans ?_⟩
    have hm' : (shift B S hS l (t : ℤ)).map c ≫ m = shiftMap Y hst ≫ g := hm
    rw [hm', homMk_shiftMap_comp]

/-- **Kernels in the A–R category, from a representative.** Let `φ = [r, f] : F ⟶ G` be the
A–R morphism represented by `f : F[r] ⟶ G`, and `k : K ⟶ F[r]` a kernel of `f` in `P_S`. Then
`[ε_r] ∘ [k] : K ⟶ F` is a kernel of `φ` in the A–R category, where `[-]` is the canonical
functor `toAr` and `[ε_r]` the isomorphism `shiftιIso F r`. -/
@[weil "lem_fk112_ar_sheaves_kernel_cokernel_representative"]
def isLimitKernelForkHomMk {F G K : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ}
    {f : (shift B S hS l (r : ℤ)).obj F ⟶ G} {k : K ⟶ (shift B S hS l (r : ℤ)).obj F}
    {hk : k ≫ f = 0} (h : IsLimit (KernelFork.ofι k hk)) :
    IsLimit (KernelFork.ofι (f := homMk r f)
      ((toAr B S hS l).map k ≫ (shiftιIso F r).hom)
      (by
        change (homMk 0 ((shiftι B S hS l 0).app K ≫ k) ≫ (shiftιIso F r).hom) ≫ homMk r f = 0
        rw [Category.assoc, homMk_eq_homMk_id_comp r f, ← shiftιIso_inv, Iso.hom_inv_id_assoc,
          homMk_comp_homMk_shiftι_zero, Category.assoc, hk, Limits.comp_zero, homMk_zero])) :=
  have : Mono k := Fork.IsLimit.mono h
  have : Mono (homMk 0 ((shiftι B S hS l 0).app K ≫ k)) := mono_homMk_shiftι_zero k
  have : Mono ((toAr B S hS l).map k ≫ (shiftιIso F r).hom) :=
    mono_comp (homMk 0 ((shiftι B S hS l 0).app K ≫ k)) (shiftιIso F r).hom
  KernelFork.IsLimit.ofι' _ _ fun {A} ψ hψ =>
    have hex := exists_comp_homMk_shiftι_zero_eq h (ψ ≫ (shiftιIso F r).inv)
      (by rw [Category.assoc, shiftιIso_inv, ← homMk_eq_homMk_id_comp, hψ])
    ⟨hex.choose, by
      change hex.choose ≫ homMk 0 ((shiftι B S hS l 0).app K ≫ k) ≫ (shiftιIso F r).hom = ψ
      rw [← Category.assoc, hex.choose_spec, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]⟩

/-- **Cokernels in the A–R category, from a representative.** Let `φ = [r, f] : F ⟶ G` be the
A–R morphism represented by `f : F[r] ⟶ G`, and `c : G ⟶ C` a cokernel of `f` in `P_S`. Then
`[c] : G ⟶ C` is a cokernel of `φ` in the A–R category, where `[-]` is the canonical functor
`toAr`. -/
@[weil "lem_fk112_ar_sheaves_kernel_cokernel_representative"]
def isColimitCokernelCoforkHomMk {F G Q : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ}
    {f : (shift B S hS l (r : ℤ)).obj F ⟶ G} {c : G ⟶ Q} {hc : f ≫ c = 0}
    (h : IsColimit (CokernelCofork.ofπ c hc)) :
    IsColimit (CokernelCofork.ofπ (f := homMk r f) ((toAr B S hS l).map c)
      (by
        change homMk r f ≫ homMk 0 ((shiftι B S hS l 0).app G ≫ c) = 0
        rw [homMk_comp_homMk_shiftι_zero, hc, homMk_zero])) :=
  have : Epi (homMk 0 ((shiftι B S hS l 0).app G ≫ c)) := epi_homMk_shiftι_zero h
  CokernelCofork.IsColimit.ofπ' (hp := this) _ _ fun {A} ψ hψ =>
    have hex := exists_homMk_shiftι_zero_comp_eq h ψ
      (by
        rw [← cancel_epi (shiftιIso F r).inv, ← Category.assoc, shiftιIso_inv,
          ← homMk_eq_homMk_id_comp, Limits.comp_zero]
        exact hψ)
    ⟨hex.choose, hex.choose_spec⟩

end ArLTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
