module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArIsomorphism
public import WeilFrontier.CategoryTheory.Preadditive.ArZeroMorphismCriterion

/-!
# Kernels in the Artin–Rees category

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules, `AR` its
Artin–Rees category and `q : 𝒫 ⥤ AR` the canonical functor. Let `φ = [r, f] : F ⟶ G` be an
A–R morphism with representative `f : F[r] ⟶ G`, and let `i : K ⟶ F[r]` be a kernel of `f` in
the abelian category `𝒫`. Then `q(ε^r_F) ∘ q(i) : K ⟶ F` is a kernel of `φ` in `AR`.

The proof goes through two facts. First, `q(ε^r_F) : F[r] ⟶ F` is an isomorphism of `AR`, with
inverse `[r, id_{F[r]}]`, and `φ = q(f) ∘ [r, id_{F[r]}]`. Second, `q` sends kernels of `𝒫` to
kernels of `AR`: if `ψ = [s, h] : T ⟶ F[r]` satisfies `q(f) ∘ ψ = 0`, then `f ∘ h` vanishes after
precomposition with some `T[t] ⟶ T[s]`, so `h ∘ (T[t] ⟶ T[s])` factors through `i`; and `q(i)` is
a monomorphism by the same argument.

## Main definitions

* `CategoryTheory.ProjectiveSystem.ArCategory.shiftIso F r`: the isomorphism `q(ε^r_F) : F[r] ≅ F`
  of the A–R category, with inverse `[r, id_{F[r]}]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.isLimitMapKernelFork`: `q` sends a kernel of a
  morphism `f` of `𝒫` to a kernel of `q(f)`.
* `CategoryTheory.ProjectiveSystem.ArCategory.isLimitKernelForkHomMk`: for a kernel
  `i : K ⟶ F[r]` of `f : F[r] ⟶ G`, the morphism `q(ε^r_F) ∘ q(i)` is a kernel of `[r, f]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.isLimitKernelForkHomMkKernelι`: the same for the
  chosen kernel `kernel.ι f`.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_comp_toArCategory_map`:
  `q(g) ∘ [s, h] = [s, g ∘ h]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.toArCategory_map_comp_homMk`:
  `[s, h] ∘ q(g) = [s, h ∘ g[s]]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_eq_shiftIso_inv_comp`:
  `[r, f] = q(f) ∘ q(ε^r_F)⁻¹`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

namespace ArCategory

/-- `q(g) ∘ [s, h] = [s, g ∘ h]`. -/
lemma homMk_comp_toArCategory_map {T F G : ProjectiveSystem.{v} Λ l} {s : ℕ}
    (h : (shift (s : ℤ)).obj T ⟶ F) (g : F ⟶ G) :
    homMk s h ≫ (toArCategory Λ l).map g = homMk s (h ≫ g) := by
  change homMk (s + 0) (shiftShift T s 0 ≫ (shift ((0 : ℕ) : ℤ)).map h ≫ natMap F 0 ≫ g) = _
  rw [natMap_naturality_assoc,
    shiftShift_comp_natMap_zero_assoc, homMk_shiftMap_comp]

/-- `[s, h] ∘ q(g) = [s, h ∘ g[s]]`. -/
lemma toArCategory_map_comp_homMk {F G H : ProjectiveSystem.{v} Λ l} {s : ℕ} (g : F ⟶ G)
    (h : (shift (s : ℤ)).obj G ⟶ H) :
    (toArCategory Λ l).map g ≫ homMk s h = homMk s ((shift (s : ℤ)).map g ≫ h) := by
  change homMk (0 + s) (shiftShift F 0 s ≫ (shift (s : ℤ)).map (natMap F 0 ≫ g) ≫ h) = _
  rw [Functor.map_comp, Category.assoc,
    shiftShift_comp_shift_map_natMap_zero_assoc, homMk_shiftMap_comp]

/-- The shift of the natural map `ε^r_F` is the natural map of the shifted system:
`(ε^r_F)[r] = ε^r_{F[r]}`. -/
lemma shift_map_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (shift (r : ℤ)).map (natMap F r) = natMap ((shift (r : ℤ)).obj F) r :=
  hom_ext fun _ => congrArg F.obj.map (Subsingleton.elim _ _)

/-- The natural map `ε^r_F : F[r] ⟶ F` becomes an isomorphism `q(ε^r_F)` of the A–R category,
with inverse the A–R morphism `[r, id_{F[r]}] : F ⟶ F[r]`. -/
def shiftIso (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    of ((shift (r : ℤ)).obj F) ≅ of F where
  hom := (toArCategory Λ l).map (natMap F r)
  inv := homMk r (𝟙 _)
  hom_inv_id := by
    erw [toArCategory_map_comp_homMk, Category.comp_id, shift_map_natMap, homMk_natMap]
  inv_hom_id := by
    erw [homMk_comp_toArCategory_map, Category.id_comp, homMk_natMap]

@[simp]
lemma shiftIso_hom (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (shiftIso F r).hom = (toArCategory Λ l).map (natMap F r) := rfl

@[simp]
lemma shiftIso_inv (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (shiftIso F r).inv = homMk r (𝟙 _) := rfl

/-- Every A–R morphism factors as `[r, f] = q(f) ∘ q(ε^r_F)⁻¹`. -/
lemma homMk_eq_shiftIso_inv_comp {F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    homMk r f = (shiftIso F r).inv ≫ (toArCategory Λ l).map f := by
  rw [shiftIso_inv, homMk_comp_toArCategory_map, Category.id_comp]

/-- The canonical functor `q` sends a kernel `i : K ⟶ F` of a morphism `f : F ⟶ G` of projective
systems to a kernel `q(i)` of `q(f)` in the A–R category. -/
noncomputable def isLimitMapKernelFork {K F G : ProjectiveSystem.{v} Λ l} {f : F ⟶ G} {i : K ⟶ F}
    {w : i ≫ f = 0} (hi : IsLimit (KernelFork.ofι i w)) :
    IsLimit (KernelFork.ofι (f := (toArCategory Λ l).map f) ((toArCategory Λ l).map i)
      (by rw [← Functor.map_comp, w, Functor.map_zero])) := by
  -- `q(i)` is a monomorphism of the A–R category.
  have hmono : ∀ {W : ArCategory.{v} Λ l} (χ : W ⟶ (toArCategory Λ l).obj K),
      χ ≫ (toArCategory Λ l).map i = 0 → χ = 0 := by
    intro W χ hχ
    induction χ using hom_induction with
    | h s c =>
      obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff (c ≫ i)).1
        ((homMk_comp_toArCategory_map c i).symm.trans hχ)
      exact (homMk_eq_zero_iff c).2 ⟨t, hst, Fork.IsLimit.hom_ext hi
        ((Category.assoc _ _ _).trans (e.trans Limits.zero_comp.symm))⟩
  -- Every morphism killed by `q(f)` factors through `q(i)`.
  have hlift : ∀ {W : ArCategory.{v} Λ l} (ψ : W ⟶ (toArCategory Λ l).obj F),
      ψ ≫ (toArCategory Λ l).map f = 0 →
        ∃ χ : W ⟶ (toArCategory Λ l).obj K, χ ≫ (toArCategory Λ l).map i = ψ := by
    intro W ψ hψ
    induction ψ using hom_induction with
    | h s h =>
      obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff (h ≫ f)).1
        ((homMk_comp_toArCategory_map h f).symm.trans hψ)
      replace e := (Category.assoc _ _ _).trans e
      exact ⟨homMk t (KernelFork.IsLimit.lift' hi _ e).1,
        (homMk_comp_toArCategory_map _ i).trans
          ((congrArg (homMk t) (KernelFork.IsLimit.lift' hi _ e).2).trans
            (homMk_shiftMap_comp hst h))⟩
  exact KernelFork.IsLimit.ofι _ _ (fun ψ hψ => (hlift ψ hψ).choose)
    (fun ψ hψ => (hlift ψ hψ).choose_spec)
    (fun ψ hψ m hm => sub_eq_zero.1 (hmono _ (by
      rw [Preadditive.sub_comp, hm, (hlift ψ hψ).choose_spec, sub_self])))

/-- Let `e : Y ≅ X` be an isomorphism and `φ = e⁻¹ ≫ g : X ⟶ Z`. If `ι : K ⟶ Y` is a kernel of
`g`, then `ι ≫ e : K ⟶ X` is a kernel of `φ`. -/
noncomputable def isLimitKernelForkOfιCompIso {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z K : C} (e : Y ≅ X) {g : Y ⟶ Z} {φ : X ⟶ Z} (hφ : φ = e.inv ≫ g) {ι : K ⟶ Y}
    {w : ι ≫ g = 0} (h : IsLimit (KernelFork.ofι ι w)) :
    IsLimit (KernelFork.ofι (f := φ) (ι ≫ e.hom) (by simp [hφ, w])) := by
  let L : ∀ {W : C} (ψ : W ⟶ X), ψ ≫ φ = 0 → {u : W ⟶ K // u ≫ ι = ψ ≫ e.inv} :=
    fun ψ hψ => KernelFork.IsLimit.lift' h (ψ ≫ e.inv) (by rw [Category.assoc, ← hφ, hψ])
  refine KernelFork.IsLimit.ofι _ _ (fun ψ hψ => (L ψ hψ).1) (fun ψ hψ => ?_)
    (fun ψ hψ m hm => Fork.IsLimit.hom_ext h ?_)
  · rw [← Category.assoc, (L ψ hψ).2, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change m ≫ ι = (L ψ hψ).1 ≫ ι
    rw [(L ψ hψ).2, ← hm, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma toArCategory_map_comp_natMap_comp_homMk {K F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    {f : (shift (r : ℤ)).obj F ⟶ G} {i : K ⟶ (shift (r : ℤ)).obj F} (w : i ≫ f = 0) :
    ((toArCategory Λ l).map i ≫ (toArCategory Λ l).map (natMap F r)) ≫ homMk r f = 0 := by
  erw [homMk_eq_shiftIso_inv_comp, ← shiftIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, w, Functor.map_zero]
  rfl

/-- **The kernel of an A–R morphism, from a representative.** Let `φ = [r, f] : F ⟶ G` be an A–R
morphism with representative `f : F[r] ⟶ G`, and let `i : K ⟶ F[r]` be a kernel of `f` in the
category of projective systems. Then `q(ε^r_F) ∘ q(i) : K ⟶ F` is a kernel of `φ` in the A–R
category. -/
@[weil "lem_fk112_ar_kernel_of_representative"]
noncomputable def isLimitKernelForkHomMk {K F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    {f : (shift (r : ℤ)).obj F ⟶ G} {i : K ⟶ (shift (r : ℤ)).obj F} {w : i ≫ f = 0}
    (hi : IsLimit (KernelFork.ofι i w)) :
    IsLimit (KernelFork.ofι (f := homMk r f)
      ((toArCategory Λ l).map i ≫ (toArCategory Λ l).map (natMap F r))
      (toArCategory_map_comp_natMap_comp_homMk w)) :=
  isLimitKernelForkOfιCompIso (shiftIso F r) (homMk_eq_shiftIso_inv_comp f)
    (isLimitMapKernelFork hi)

/-- **The kernel of an A–R morphism, from a representative**, for the chosen kernel
`kernel.ι f : ker f ⟶ F[r]` of `f` in the category of projective systems:
`q(ε^r_F) ∘ q(kernel.ι f)` is a kernel of `[r, f]`. -/
@[weil "lem_fk112_ar_kernel_of_representative"]
noncomputable def isLimitKernelForkHomMkKernelι {F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    IsLimit (KernelFork.ofι (f := homMk r f)
      ((toArCategory Λ l).map (kernel.ι f) ≫ (toArCategory Λ l).map (natMap F r))
      (toArCategory_map_comp_natMap_comp_homMk (kernel.condition f))) :=
  isLimitKernelForkHomMk (w := kernel.condition f) (kernelIsKernel f)

end ArCategory

end ProjectiveSystem

end CategoryTheory
