module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import Weil.Attr

/-!
# The sheaf `μ_n` of `n`-th roots of unity on the étale site

For a scheme `X` and an integer `n`, the sheaf `μ_n = (μ_n)_X` of `n`-th roots of unity is the
kernel of the `n`-th power map `f ↦ fⁿ` on the multiplicative sheaf `𝒪^*_{X,et} = 𝐆_m`. Its
sections over an étale `X`-scheme `U` are the invertible global functions `ζ ∈ Γ(U, 𝒪_U)ˣ`
with `ζⁿ = 1`, it is a subsheaf of `𝒪^*_{X,et}`, and its restriction maps are those of
`𝒪^*_{X,et}`.

The sheaf itself is `Stacks.Kummer.rootsOfUnitySheaf`, defined as a kernel in the category of
abelian sheaves on the small étale site; this file proves that this kernel is computed
objectwise, so that its sections are exactly the `n`-th roots of unity.

## Main definitions

* `AlgebraicGeometry.rootsOfUnitySheafObjIsoKer`: the sections of `μ_n` over `U` are the kernel
  of the `n`-th power map on `𝒪^*(U)`.
* `AlgebraicGeometry.rootsOfUnitySheafAddEquiv`: the sections of `μ_n` over `U` are the group
  `rootsOfUnity n Γ(U, 𝒪_U)` of `n`-th roots of unity (written additively).

## Main results

* `AlgebraicGeometry.injective_rootsOfUnityι_app`: `μ_n(U)` is a subgroup of `𝒪^*(U)`.
* `AlgebraicGeometry.range_rootsOfUnityι_app_eq_ker`: `μ_n(U)` is the kernel of the `n`-th
  power map `𝒪^*(U) → 𝒪^*(U)`; i.e. `μ_n` is the objectwise kernel of `n : 𝒪^* → 𝒪^*`.
* `AlgebraicGeometry.exists_rootsOfUnityι_app_eq_ofUnit_iff`: a unit `ζ ∈ Γ(U, 𝒪_U)ˣ` is a
  section of `μ_n` if and only if `ζⁿ = 1`.
* `AlgebraicGeometry.rootsOfUnitySheafAddEquiv_map`: restriction in `μ_n` is restriction of
  functions.

## Implementation notes

The integer `n` is an arbitrary natural number: neither `n ≥ 1` nor the invertibility of `n`
on `X` is needed to define `μ_n` or to describe its sections; these hypotheses enter only in
the exactness of the Kummer sequence. The site is the small étale site `X.Etale` and the
coefficients are `AddCommGrpCat.{max (u + 1) v}`, as for `Stacks.Kummer.multiplicativeSheaf`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

open Stacks.Kummer

variable (X : Scheme.{u}) (n : ℕ)

/-- The sections of `μ_n` over `U` are the kernel of the `n`-th power map on `𝒪^*(U)`. -/
def rootsOfUnitySheafObjIsoKer (U : X.Etale) :
    (rootsOfUnitySheaf.{u, v} X n).obj.obj (op U) ≅
      AddCommGrpCat.of ((powMap.{u, v} X n).hom.app (op U)).hom.ker :=
  PreservesKernel.iso (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
    (evaluation _ _).obj (op U)) (powMap.{u, v} X n) ≪≫
    AddCommGrpCat.kernelIsoKer _

lemma rootsOfUnitySheafObjIsoKer_hom_subtype (U : X.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U))) :
    (((rootsOfUnitySheafObjIsoKer.{u, v} X n U).hom s : _) :
      ToType ((multiplicativeSheaf.{u, v} X).obj.obj (op U))) =
      (rootsOfUnityι.{u, v} X n).hom.app (op U) s := by
  let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
    (evaluation _ _).obj (op U)
  have h : (PreservesKernel.iso G (powMap.{u, v} X n)).hom ≫
      (AddCommGrpCat.kernelIsoKer (G.map (powMap.{u, v} X n))).hom ≫
      AddCommGrpCat.ofHom (AddSubgroup.subtype (G.map (powMap.{u, v} X n)).hom.ker) =
      G.map (kernel.ι (powMap.{u, v} X n)) := by
    rw [AddCommGrpCat.kernelIsoKer_hom_comp_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  exact congrArg (fun φ => φ s) (congrArg AddCommGrpCat.Hom.hom h)

/-- **`μ_n(U)` is a subgroup of `𝒪^*(U)`**: the inclusion `μ_n ⟶ 𝐆_m` is injective on
sections over every étale `X`-scheme `U`. -/
@[weil "def_fk102_roots_of_unity_sheaf"]
theorem injective_rootsOfUnityι_app (U : X.Etale) :
    Function.Injective ((rootsOfUnityι.{u, v} X n).hom.app (op U)) := by
  intro s t hst
  have h : (rootsOfUnitySheafObjIsoKer.{u, v} X n U).hom s =
      (rootsOfUnitySheafObjIsoKer.{u, v} X n U).hom t := by
    apply Subtype.ext
    rw [rootsOfUnitySheafObjIsoKer_hom_subtype, rootsOfUnitySheafObjIsoKer_hom_subtype, hst]
  simpa only [Iso.hom_inv_id_apply] using
    congrArg (rootsOfUnitySheafObjIsoKer.{u, v} X n U).inv h

/-- **`μ_n` is the objectwise kernel of `n : 𝒪^* → 𝒪^*`**: the image of `μ_n(U)` in `𝒪^*(U)`
is the kernel of the `n`-th power map on `𝒪^*(U)`. -/
@[weil "def_fk102_roots_of_unity_sheaf"]
theorem range_rootsOfUnityι_app_eq_ker (U : X.Etale) :
    ((rootsOfUnityι.{u, v} X n).hom.app (op U)).hom.range =
      ((powMap.{u, v} X n).hom.app (op U)).hom.ker := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    rw [← rootsOfUnitySheafObjIsoKer_hom_subtype]
    exact ((rootsOfUnitySheafObjIsoKer.{u, v} X n U).hom s).2
  · intro hx
    refine ⟨(rootsOfUnitySheafObjIsoKer.{u, v} X n U).inv ⟨x, hx⟩, ?_⟩
    change _ = ((⟨x, hx⟩ : ((powMap.{u, v} X n).hom.app (op U)).hom.ker) :
      ToType ((multiplicativeSheaf.{u, v} X).obj.obj (op U)))
    rw [← rootsOfUnitySheafObjIsoKer_hom_subtype, Iso.inv_hom_id_apply]

/-- **The sections of `μ_n` over `U` are the `n`-th roots of unity in `Γ(U, 𝒪_U)ˣ`**: a unit
`ζ` is (the image of) a section of `μ_n` over `U` if and only if `ζⁿ = 1`. -/
@[weil "def_fk102_roots_of_unity_sheaf"]
theorem exists_rootsOfUnityι_app_eq_ofUnit_iff (U : X.Etale) (ζ : (Γ(U.left, ⊤))ˣ) :
    (∃ s, (rootsOfUnityι.{u, v} X n).hom.app (op U) s = ofUnit ζ) ↔ ζ ^ n = 1 := by
  have h := SetLike.ext_iff.mp (range_rootsOfUnityι_app_eq_ker.{u, v} X n U) (ofUnit ζ)
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker] at h
  rw [h]
  change (powMap.{u, v} X n).hom.app (op U) (ofUnit ζ) = ofUnit 1 ↔ _
  rw [powMap_app_ofUnit]
  exact ofUnit_injective.eq_iff

/-- The image of a section of `μ_n` in `𝒪^*(U)`, as an `n`-th root of unity of `Γ(U, 𝒪_U)`. -/
def rootsOfUnitySheafToRootsOfUnity (U : X.Etale) :
    ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U)) →+
      Additive (rootsOfUnity n Γ(U.left, ⊤)) where
  toFun s := Additive.ofMul
    ⟨(Additive.toMul ((rootsOfUnityι.{u, v} X n).hom.app (op U) s).down : (Γ(U.left, ⊤))ˣ),
      (mem_rootsOfUnity _ _).2 ((exists_rootsOfUnityι_app_eq_ofUnit_iff.{u, v} X n U _).1
        ⟨s, rfl⟩)⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (Additive.toMul ((rootsOfUnityι.{u, v} X n).hom.app (op U) 0).down :
      (Γ(U.left, ⊤))ˣ) = 1
    rw [map_zero]
    rfl
  map_add' s t := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (Additive.toMul ((rootsOfUnityι.{u, v} X n).hom.app (op U) (s + t)).down :
      (Γ(U.left, ⊤))ˣ) =
      (Additive.toMul ((rootsOfUnityι.{u, v} X n).hom.app (op U) s).down : (Γ(U.left, ⊤))ˣ) *
        (Additive.toMul ((rootsOfUnityι.{u, v} X n).hom.app (op U) t).down : (Γ(U.left, ⊤))ˣ)
    rw [map_add]
    rfl

lemma ofUnit_rootsOfUnitySheafToRootsOfUnity (U : X.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U))) :
    ofUnit (((Additive.toMul (rootsOfUnitySheafToRootsOfUnity.{u, v} X n U s) :
      rootsOfUnity n Γ(U.left, ⊤)) : (Γ(U.left, ⊤))ˣ)) =
      (rootsOfUnityι.{u, v} X n).hom.app (op U) s :=
  rfl

lemma bijective_rootsOfUnitySheafToRootsOfUnity (U : X.Etale) :
    Function.Bijective (rootsOfUnitySheafToRootsOfUnity.{u, v} X n U) := by
  refine ⟨fun s t hst => injective_rootsOfUnityι_app.{u, v} X n U ?_, fun ζ => ?_⟩
  · rw [← ofUnit_rootsOfUnitySheafToRootsOfUnity, ← ofUnit_rootsOfUnitySheafToRootsOfUnity, hst]
  · obtain ⟨s, hs⟩ := (exists_rootsOfUnityι_app_eq_ofUnit_iff.{u, v} X n U
      (Additive.toMul ζ : rootsOfUnity n Γ(U.left, ⊤))).2
      ((mem_rootsOfUnity _ _).1 (Additive.toMul ζ).2)
    refine ⟨s, Additive.toMul.injective (Subtype.ext (ofUnit_injective.{u, v} ?_))⟩
    rw [ofUnit_rootsOfUnitySheafToRootsOfUnity, hs]

/-- **The sections of `μ_n` over `U` are the group of `n`-th roots of unity of `Γ(U, 𝒪_U)`**,
written additively. -/
def rootsOfUnitySheafAddEquiv (U : X.Etale) :
    ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U)) ≃+
      Additive (rootsOfUnity n Γ(U.left, ⊤)) :=
  AddEquiv.ofBijective _ (bijective_rootsOfUnitySheafToRootsOfUnity.{u, v} X n U)

/-- The root of unity attached to a section `s` of `μ_n` is the image of `s` in `𝒪^*(U)`. -/
lemma ofUnit_rootsOfUnitySheafAddEquiv (U : X.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U))) :
    ofUnit (((Additive.toMul (rootsOfUnitySheafAddEquiv.{u, v} X n U s) :
      rootsOfUnity n Γ(U.left, ⊤)) : (Γ(U.left, ⊤))ˣ)) =
      (rootsOfUnityι.{u, v} X n).hom.app (op U) s :=
  ofUnit_rootsOfUnitySheafToRootsOfUnity.{u, v} X n U s

/-- **Restriction in `μ_n` is restriction of functions**: the restriction maps of `μ_n` are
those of `𝒪^*`. -/
lemma rootsOfUnitySheafAddEquiv_map {U V : X.Etale} (f : V ⟶ U)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U))) :
    (((Additive.toMul (rootsOfUnitySheafAddEquiv.{u, v} X n V
        ((rootsOfUnitySheaf.{u, v} X n).obj.map f.op s)) : rootsOfUnity n Γ(V.left, ⊤)) :
        (Γ(V.left, ⊤))ˣ)) =
      Units.map f.left.appTop.hom
        ((Additive.toMul (rootsOfUnitySheafAddEquiv.{u, v} X n U s) :
          rootsOfUnity n Γ(U.left, ⊤)) : (Γ(U.left, ⊤))ˣ) := by
  apply ofUnit_injective.{u, v}
  rw [ofUnit_rootsOfUnitySheafAddEquiv, ← map_ofUnit, ofUnit_rootsOfUnitySheafAddEquiv,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, NatTrans.naturality]

end AlgebraicGeometry

end
