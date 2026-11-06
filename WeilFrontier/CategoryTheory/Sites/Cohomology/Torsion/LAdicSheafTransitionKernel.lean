module

public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.LAdicSheaves
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ShiftMorphismSheaves
public import Weil.Attr

/-!
# The composite transition maps of an `l`-adic sheaf

Let `F = (F_n, u_n)_{n ∈ ℤ}` be an `l`-adic sheaf on the small étale site of a scheme `X`, and
`r, n ≥ 0`. The natural morphism `ε_{r,n} = u_{n+1} ∘ ⋯ ∘ u_{n+r} : F_{n+r} ⟶ F_n` is an
epimorphism with kernel `l^{n+1} F_{n+r}`: it exhibits `F_n` as the cokernel of multiplication by
`l^{n+1}` on `F_{n+r}`.

The proof is an induction on `r`: each `u_{m+1}` is a cokernel of `l^{m+1}`, and a cokernel of
`b` followed by a cokernel of `a`, where `a` divides `b`, is a cokernel of `a`.

## Main results

* `AlgebraicGeometry.SmallEtale.IsLAdicSheaf.nonempty_isColimit_shiftι`: `ε_{r,n}` is a cokernel
  of `l^{n+1}` on `F_{n+r}` (with the chosen colimit datum `IsLAdicSheaf.isColimitShiftι`).
* `AlgebraicGeometry.SmallEtale.IsLAdicSheaf.epi_shiftι`: `ε_{r,n}` is an epimorphism.
* `AlgebraicGeometry.SmallEtale.IsLAdicSheaf.exact_shiftι`: the sequence
  `F_{n+r} --l^{n+1}--> F_{n+r} --ε_{r,n}--> F_n` is exact, i.e. the kernel of `ε_{r,n}` is
  `l^{n+1} F_{n+r}`.

## Implementation notes

The kernel `l^{n+1} F_{n+r}` is the image of multiplication by `l^{n+1}`; the statement that
`ε_{r,n}` is an epimorphism with this kernel is stated as `ε_{r,n}` being a cokernel of
`l^{n+1}`, which needs no abelian structure, and, when sheafification exists (so that sheaves
form an abelian category), as exactness of `F_{n+r} → F_{n+r} → F_n`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

section Preadditive

variable {C : Type*} [Category C] [Preadditive C]

/-- A cokernel of `b` followed by a cokernel of `a`, where `a ∣ b`, is a cokernel of `a`. -/
private noncomputable def isColimitCokernelCoforkNsmulComp {A B Q : C} {π₁ : A ⟶ B} {π₂ : B ⟶ Q}
    {a b : ℕ} (hab : a ∣ b) {w₁ : (b • 𝟙 A) ≫ π₁ = 0} {w₂ : (a • 𝟙 B) ≫ π₂ = 0}
    (h₁ : IsColimit (CokernelCofork.ofπ π₁ w₁)) (h₂ : IsColimit (CokernelCofork.ofπ π₂ w₂))
    (w : (a • 𝟙 A) ≫ π₁ ≫ π₂ = 0) :
    IsColimit (CokernelCofork.ofπ (π₁ ≫ π₂) w) := by
  have hb : ∀ {Z : C} (g : A ⟶ Z), (a • 𝟙 A) ≫ g = 0 → (b • 𝟙 A) ≫ g = 0 := by
    intro Z g hg
    obtain ⟨c, rfl⟩ := hab
    rw [Preadditive.nsmul_comp, Category.id_comp] at hg ⊢
    rw [mul_comm, mul_smul, hg, smul_zero]
  have epi₁ : Epi π₁ := Cofork.IsColimit.epi h₁
  have epi₂ : Epi π₂ := Cofork.IsColimit.epi h₂
  let d₁ {Z : C} (g : A ⟶ Z) (hg : (a • 𝟙 A) ≫ g = 0) : B ⟶ Z :=
    (CokernelCofork.IsColimit.desc' h₁ g (hb g hg)).1
  have d₁_spec {Z : C} (g : A ⟶ Z) (hg : (a • 𝟙 A) ≫ g = 0) : π₁ ≫ d₁ g hg = g :=
    (CokernelCofork.IsColimit.desc' h₁ g (hb g hg)).2
  have h₂' {Z : C} (g : A ⟶ Z) (hg : (a • 𝟙 A) ≫ g = 0) : (a • 𝟙 B) ≫ d₁ g hg = 0 := by
    rw [← cancel_epi π₁, comp_zero, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, d₁_spec g hg]
    rwa [Preadditive.nsmul_comp, Category.id_comp] at hg
  let d₂ {Z : C} (g : A ⟶ Z) (hg : (a • 𝟙 A) ≫ g = 0) : Q ⟶ Z :=
    (CokernelCofork.IsColimit.desc' h₂ _ (h₂' g hg)).1
  have d₂_spec {Z : C} (g : A ⟶ Z) (hg : (a • 𝟙 A) ≫ g = 0) : π₂ ≫ d₂ g hg = d₁ g hg :=
    (CokernelCofork.IsColimit.desc' h₂ _ (h₂' g hg)).2
  refine CokernelCofork.IsColimit.ofπ _ _ d₂ (fun g hg ↦ ?_) (fun g hg m hm ↦ ?_)
  · rw [Category.assoc, d₂_spec g hg, d₁_spec g hg]
  · rw [← cancel_epi (π₁ ≫ π₂), hm, Category.assoc, d₂_spec g hg, d₁_spec g hg]

/-- Transport of a cokernel property along an equality of morphisms. -/
private theorem nonempty_isColimit_of_eq {A Q : C}
    {f : A ⟶ A} {π π' : A ⟶ Q} (e : π = π') (w : f ≫ π = 0) (w' : f ≫ π' = 0)
    (H : Nonempty (IsColimit (CokernelCofork.ofπ π w))) :
    Nonempty (IsColimit (CokernelCofork.ofπ π' w')) := by
  subst e
  exact H

/-- Transport of the cokernel property of `F_b ⟶ F_a` along equalities of the indices. -/
private theorem nonempty_isColimit_congr {F : ℤᵒᵖ ⥤ C} {a b a' b' : ℤ} (ha : a = a') (hb : b = b')
    (h : a ≤ b) (h' : a' ≤ b') (j : ℕ)
    (w : ((j • 𝟙 (F.obj (op b))) ≫ F.map (homOfLE h).op) = 0)
    (w' : ((j • 𝟙 (F.obj (op b'))) ≫ F.map (homOfLE h').op) = 0)
    (H : Nonempty (IsColimit (CokernelCofork.ofπ _ w))) :
    Nonempty (IsColimit (CokernelCofork.ofπ _ w')) := by
  subst ha hb
  exact H

end Preadditive

namespace IsLAdicSheaf

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {l : ℕ}
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{w}]
  {F : LTorsionProjectiveSystem.{w} B X.obj X.property l}

/-- For `n ≤ m`, `l^{n+1}` kills every map `F_m ⟶ F_n` of an `l`-adic sheaf. -/
theorem nsmul_id_comp_map_eq_zero (hF : IsLAdicSheaf B X l F) (n : ℕ) {m : ℤ} (h : (n : ℤ) ≤ m) :
    ((l ^ (n + 1)) • 𝟙 (F.obj.obj (op m))) ≫ F.obj.map (homOfLE h).op = 0 :=
  nsmul_id_comp_eq_zero _ _ (hF.nsmul_id_eq_zero n)

/-- For `k ≥ 0`, the map `F_{n+k} ⟶ F_n` of an `l`-adic sheaf is a cokernel of `l^{n+1}`. -/
private theorem nonempty_isColimit_map_add (hF : IsLAdicSheaf B X l F) (n k : ℕ) :
    Nonempty (IsColimit (CokernelCofork.ofπ _
      (hF.nsmul_id_comp_map_eq_zero n (show (n : ℤ) ≤ n + k by omega)))) := by
  induction k with
  | zero =>
    refine nonempty_isColimit_congr rfl (by simp) le_rfl _ _
      (nsmul_id_comp_map_eq_zero hF n le_rfl) _ ?_
    · refine ⟨CokernelCofork.IsColimit.ofπ _ _ (fun g _ ↦ g) (fun g _ ↦ by simp)
        (fun g _ m hm ↦ by simpa using hm)⟩
  | succ k ih =>
    obtain ⟨ih⟩ := ih
    obtain ⟨hstep⟩ := nonempty_isColimit_congr (b' := (n : ℤ) + (k + 1 : ℕ))
      (by push_cast; ring) (by push_cast; ring)
      _ (show (n : ℤ) + k ≤ n + (k + 1 : ℕ) by omega) _ _
      (nsmul_id_comp_eq_zero _ _ (by
        have := hF.nsmul_id_eq_zero (n + k)
        rwa [show ((n + k : ℕ) : ℤ) = n + k by push_cast; ring] at this)) (hF.isColimit (n + k))
    have hcomp : F.obj.map (homOfLE (show (n : ℤ) + k ≤ n + (k + 1 : ℕ) by omega)).op ≫
          F.obj.map (homOfLE (show (n : ℤ) ≤ n + k by omega)).op =
        F.obj.map (homOfLE (show (n : ℤ) ≤ n + (k + 1 : ℕ) by omega)).op := by
      rw [← F.obj.map_comp]; rfl
    exact nonempty_isColimit_of_eq hcomp _ _ ⟨isColimitCokernelCoforkNsmulComp
      (show l ^ (n + 1) ∣ l ^ (n + k + 1) from pow_dvd_pow l (by omega)) hstep ih
      (by rw [hcomp]; exact hF.nsmul_id_comp_map_eq_zero n _)⟩

/-- **The composite transition maps of an `l`-adic sheaf.** For `r, n ≥ 0`, the natural morphism
`ε_{r,n} : F_{n+r} ⟶ F_n` exhibits `F_n` as the cokernel of multiplication by `l^{n+1}` on
`F_{n+r}`: it is an epimorphism with kernel `l^{n+1} F_{n+r}`. -/
@[weil "lem_fk112_l_adic_sheaf_transition_kernel"]
theorem nonempty_isColimit_shiftι (hF : IsLAdicSheaf B X l F) (r n : ℕ) :
    Nonempty (IsColimit (CokernelCofork.ofπ
      (((LTorsionProjectiveSystem.shiftι B X.obj X.property l r).app F).hom.app (op (n : ℤ)))
      (hF.nsmul_id_comp_map_eq_zero n (show (n : ℤ) ≤ n + r by omega)))) :=
  hF.nonempty_isColimit_map_add n r

/-- The natural morphism `ε_{r,n} : F_{n+r} ⟶ F_n` of an `l`-adic sheaf is a cokernel of
multiplication by `l^{n+1}` on `F_{n+r}`. -/
noncomputable def isColimitShiftι (hF : IsLAdicSheaf B X l F) (r n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (((LTorsionProjectiveSystem.shiftι B X.obj X.property l r).app F).hom.app (op (n : ℤ)))
      (hF.nsmul_id_comp_map_eq_zero n (show (n : ℤ) ≤ n + r by omega))) :=
  Classical.choice (hF.nonempty_isColimit_shiftι r n)

/-- The natural morphism `ε_{r,n} : F_{n+r} ⟶ F_n` of an `l`-adic sheaf is an epimorphism. -/
@[weil "lem_fk112_l_adic_sheaf_transition_kernel"]
theorem epi_shiftι (hF : IsLAdicSheaf B X l F) (r n : ℕ) :
    Epi (((LTorsionProjectiveSystem.shiftι B X.obj X.property l r).app F).hom.app (op (n : ℤ))) :=
  Cofork.IsColimit.epi (hF.isColimitShiftι r n)

/-- The kernel of `ε_{r,n} : F_{n+r} ⟶ F_n` is `l^{n+1} F_{n+r}`: the sequence
`F_{n+r} --l^{n+1}--> F_{n+r} --ε_{r,n}--> F_n` is exact. -/
@[weil "lem_fk112_l_adic_sheaf_transition_kernel"]
theorem exact_shiftι [HasSheafify (topology B X.obj X.property) AddCommGrpCat.{w}]
    (hF : IsLAdicSheaf B X l F) (r n : ℕ) :
    (ShortComplex.mk ((l ^ (n + 1)) • 𝟙 (F.obj.obj (op ((n : ℤ) + r))))
      (((LTorsionProjectiveSystem.shiftι B X.obj X.property l r).app F).hom.app (op (n : ℤ)))
      (hF.nsmul_id_comp_map_eq_zero n (show (n : ℤ) ≤ n + r by omega))).Exact := by
  exact ShortComplex.exact_of_g_is_cokernel _ (hF.isColimitShiftι r n)

end IsLAdicSheaf

end AlgebraicGeometry.SmallEtale

end
