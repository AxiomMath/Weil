module

public import Weil.Attr
public import Weil.Defs.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Étale line bundles

Let `S` be a scheme and `L` an `𝒪_{S,et}`-module, i.e. a sheaf of modules over the structure
sheaf `(U ⟶ S) ↦ Γ(U, 𝒪_U)` of the small étale site of `S`. A section `e ∈ L(U)` is a
*generator of `L` over `U`* if for every arrow `f : V ⟶ U` of the site the map
`Γ(V, 𝒪_V) → L(V)`, `a ↦ a • e|_V`, is bijective; equivalently, the morphism
`𝒪_{U,et} ⟶ L|_U`, `a ↦ a • e`, is an isomorphism of `𝒪_{U,et}`-modules. The module `L` is an
*étale line bundle* if there are an étale covering `(Uᵢ ⟶ S)ᵢ` and generators `eᵢ` of `L` over
`Uᵢ`; such a family is a *trivialization* of `L`.

An étale line bundle is the same thing as an `𝒪_{S,et}`-module which is finite locally free of
rank one on the ringed site `AlgebraicGeometry.smallEtaleRingedSite`, in the sense of Stacks
0409; that is how it is defined here.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsGenerator`: a section generating an `𝒪_{S,et}`-module over an
  object of the site.
* `AlgebraicGeometry.SmallEtale.IsEtaleLineBundle`: an `𝒪_{S,et}`-module locally free of rank
  one.
* `AlgebraicGeometry.SmallEtale.LineBundleTrivialization`: a covering of `S` in the small étale
  site together with generators over its members.
* `AlgebraicGeometry.SmallEtale.unitHomOfSection`: the morphism `𝒪_{U,et} ⟶ L|_U`,
  `a ↦ a • e`, of a section `e` over `U`.

## Main results

* `AlgebraicGeometry.SmallEtale.isGenerator_iff_isIso_unitHomOfSection`: `e` generates `L` over
  `U` exactly when `a ↦ a • e` is an isomorphism `𝒪_{U,et} ≅ L|_U`.
* `AlgebraicGeometry.SmallEtale.isEtaleLineBundle_iff_forall_exists_isGenerator`: `L` is an
  étale line bundle exactly when every object of the site is covered by objects over which `L`
  has a generator.
* `AlgebraicGeometry.SmallEtale.isEtaleLineBundle_iff_nonempty_trivialization`: `L` is an
  étale line bundle exactly when it has a trivialization over a covering of `S`.

## Implementation notes

The étale site is StacksFrontier's small étale site `AlgebraicGeometry.SmallEtale B S hS` inside
a big étale site `B`, whose final object `AlgebraicGeometry.SmallEtale.final` is `S` itself. A
covering of `S` is a family of arrows to the final object generating a covering sieve; by
`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective` and
`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range` these are exactly the jointly
surjective families of étale `S`-schemes of the site. The covering families are not required to
be finite: over a quasi-compact scheme every covering is refined by a finite one, and the
condition is unchanged.

`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` asks for a trivializing covering of
every object of the site rather than of the final object only; the two agree because a covering
of the final object pulls back to a covering of every object, and a generator restricts to a
generator.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits.Cofan

/-- A cofan of a single morphism is a colimit cofan exactly when that morphism is an
isomorphism. -/
lemma nonempty_isColimit_mk_fin_one_iff {C : Type*} [Category C] {X Y : C}
    (ι : Fin 1 → (X ⟶ Y)) : Nonempty (IsColimit (Cofan.mk Y ι)) ↔ IsIso (ι 0) := by
  constructor
  · rintro ⟨hc⟩
    let h0 : IsColimit (Cofan.mk X fun _ : Fin 1 => 𝟙 X) :=
      Cofan.IsColimit.mk _ (fun s => s.inj 0) (by intro s j; fin_cases j; simp)
        (by intro s m hm; simpa using hm 0)
    have := IsColimit.comp_coconePointUniqueUpToIso_hom h0 hc ⟨0⟩
    simp only [Cofan.mk_ι_app] at this
    rw [← this]
    infer_instance
  · intro h
    refine ⟨Cofan.IsColimit.mk _ (fun s => inv (ι 0) ≫ s.inj 0) ?_ ?_⟩
    · intro s j
      fin_cases j
      simp
    · intro s m hm
      simp [← hm 0]

end CategoryTheory.Limits.Cofan

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Generators of an `𝒪_{S,et}`-module.** A section `e ∈ L(U)` generates `L` over `U` if for
every arrow `f : V ⟶ U` of the small étale site the map `Γ(V, 𝒪_V) → L(V)`, `a ↦ a • e|_V`, is
bijective. -/
@[weil "def_fk102_etale_line_bundle"]
def IsGenerator (L : OxetModule B S hS) (U : SmallEtale B S hS) (e : L.val.obj (op U)) : Prop :=
  ∀ ⦃V : SmallEtale B S hS⦄ (f : V ⟶ U),
    Function.Bijective (fun a : (structureSheaf B S hS).obj.obj (op V) => a • L.val.map f.op e)

variable (B S hS) in
/-- **Étale line bundles.** An `𝒪_{S,et}`-module is an étale line bundle if it is finite
locally free of rank one on the small étale ringed site: every object of the site has a
covering on whose members the module is isomorphic to the structure sheaf. By
`AlgebraicGeometry.SmallEtale.isEtaleLineBundle_iff_nonempty_trivialization` this is the
existence of a covering of `S` with generators over its members. -/
@[weil "def_fk102_etale_line_bundle"]
abbrev IsEtaleLineBundle (L : OxetModule B S hS) : Prop :=
  RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS) L 1

namespace IsGenerator

variable {L : OxetModule B S hS} {U : SmallEtale B S hS} {e : L.val.obj (op U)}

/-- The restriction of a generator over `U` along `g : V ⟶ U` is a generator over `V`. -/
lemma restrict (he : IsGenerator L U e) {V : SmallEtale B S hS} (g : V ⟶ U) :
    IsGenerator L V (L.val.map g.op e) := by
  intro W f
  have h := he (f ≫ g)
  rw [op_comp, PresheafOfModules.map_comp] at h
  exact h

end IsGenerator

/-- The section of `L` over `U` given by a morphism `𝒪_{U,et} ⟶ L|_U`: the image of `1`. -/
abbrev sectionOfUnitHom (L : OxetModule B S hS) (U : SmallEtale B S hS)
    (φ : SheafOfModules.unit ((structureSheaf B S hS).over U) ⟶ L.over U) : L.val.obj (op U) :=
  ((L.over U).unitHomEquiv φ).val (op (Over.mk (𝟙 U)))

/-- A morphism `φ : 𝒪_{U,et} ⟶ L|_U` is multiplication by the section `φ(1)`: over
`f : V ⟶ U` it is `a ↦ a • φ(1)|_V`. -/
lemma unitHom_app_eq_smul (L : OxetModule B S hS) (U : SmallEtale B S hS)
    (φ : SheafOfModules.unit ((structureSheaf B S hS).over U) ⟶ L.over U)
    {V : SmallEtale B S hS} (f : V ⟶ U) (a : (structureSheaf B S hS).obj.obj (op V)) :
    @id (L.val.obj (op V)) (φ.val.app (op (Over.mk f)) a) =
      a • L.val.map f.op (sectionOfUnitHom L U φ) := by
  have h1 : @id (L.val.obj (op V)) (φ.val.app (op (Over.mk f)) a) =
      a • @id (L.val.obj (op V))
        (φ.val.app (op (Over.mk f)) (1 : (structureSheaf B S hS).obj.obj (op V))) := by
    have := (φ.val.app (op (Over.mk f))).hom.map_smul a
      (1 : (structureSheaf B S hS).obj.obj (op V))
    exact (congrArg (fun x => (φ.val.app (op (Over.mk f))).hom x) (mul_one a).symm).trans this
  rw [h1]
  congr 1
  exact (((L.over U).unitHomEquiv φ).property
    (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)).op).symm

/-- If `φ : 𝒪_{U,et} ⟶ L|_U` is an isomorphism, then `φ(1)` generates `L` over `U`. -/
lemma isGenerator_sectionOfUnitHom (L : OxetModule B S hS) (U : SmallEtale B S hS)
    (φ : SheafOfModules.unit ((structureSheaf B S hS).over U) ⟶ L.over U) [IsIso φ] :
    IsGenerator L U (sectionOfUnitHom L U φ) := by
  intro V f
  have hφ : IsIso (φ.val.app (op (Over.mk f))) := by
    have : IsIso φ.val := Functor.map_isIso (SheafOfModules.forget _) φ
    exact Functor.map_isIso (PresheafOfModules.evaluation _ (op (Over.mk f))) φ.val
  have hb := (ConcreteCategory.isIso_iff_bijective (φ.val.app (op (Over.mk f)))).mp hφ
  have heq : (fun a : (structureSheaf B S hS).obj.obj (op V) =>
      a • L.val.map f.op (sectionOfUnitHom L U φ)) =
      fun a => @id (L.val.obj (op V)) (φ.val.app (op (Over.mk f)) a) :=
    funext fun a => (unitHom_app_eq_smul L U φ f a).symm
  rw [heq]
  exact hb

/-- The morphism `𝒪_{U,et} ⟶ L|_U`, `a ↦ a • e|_V` over `V ⟶ U`, given by a section `e` of `L`
over `U`. -/
def unitHomOfSection (L : OxetModule B S hS) (U : SmallEtale B S hS) (e : L.val.obj (op U)) :
    SheafOfModules.unit ((structureSheaf B S hS).over U) ⟶ L.over U :=
  (L.over U).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun W => L.val.map W.unop.hom.op e) (by
      intro W W' f
      change L.val.map f.unop.left.op (L.val.map W.unop.hom.op e) = _
      rw [← PresheafOfModules.map_comp_apply]
      change L.val.map (f.unop.left ≫ W.unop.hom).op e = _
      rw [Over.w f.unop]))

/-- The morphism `a ↦ a • e` sends `1` to `e`. -/
@[simp]
lemma sectionOfUnitHom_unitHomOfSection (L : OxetModule B S hS) (U : SmallEtale B S hS)
    (e : L.val.obj (op U)) : sectionOfUnitHom L U (unitHomOfSection L U e) = e := by
  simp only [sectionOfUnitHom, unitHomOfSection, Equiv.apply_symm_apply]
  change L.val.map (𝟙 U).op e = e
  rw [op_id, PresheafOfModules.map_id]
  rfl

/-- If `e` generates `L` over `U`, then `a ↦ a • e` is an isomorphism `𝒪_{U,et} ≅ L|_U`. -/
lemma isIso_unitHomOfSection {L : OxetModule B S hS} {U : SmallEtale B S hS}
    {e : L.val.obj (op U)} (he : IsGenerator L U e) : IsIso (unitHomOfSection L U e) := by
  let φ := unitHomOfSection L U e
  have hφ (W : (Over U)ᵒᵖ) : IsIso (φ.val.app W) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (he W.unop.hom)
  let ψ : (SheafOfModules.unit ((structureSheaf B S hS).over U)).val ≅ (L.over U).val :=
    PresheafOfModules.isoMk (fun W => @asIso _ _ _ _ (φ.val.app W) (hφ W))
      (by intro W W' f; exact φ.val.naturality f)
  have : IsIso φ.val := by
    have hψ : ψ.hom = φ.val := by ext W; rfl
    rw [← hψ]
    infer_instance
  have : IsIso ((SheafOfModules.forget ((structureSheaf B S hS).over U)).map φ) := this
  exact isIso_of_fully_faithful (SheafOfModules.forget _) φ

/-- **Generators as trivializations.** A section `e` generates `L` over `U` exactly when
`a ↦ a • e` is an isomorphism `𝒪_{U,et} ≅ L|_U` of `𝒪_{U,et}`-modules. -/
@[weil "def_fk102_etale_line_bundle"]
theorem isGenerator_iff_isIso_unitHomOfSection (L : OxetModule B S hS)
    (U : SmallEtale B S hS) (e : L.val.obj (op U)) :
    IsGenerator L U e ↔ IsIso (unitHomOfSection L U e) := by
  refine ⟨isIso_unitHomOfSection, fun h => ?_⟩
  have := isGenerator_sectionOfUnitHom L U (unitHomOfSection L U e)
  rwa [sectionOfUnitHom_unitHomOfSection] at this

/-- `L` has a generator over `V` exactly when `L|_V` is a coproduct of one copy of
`𝒪_{V,et}`. -/
lemma exists_isGenerator_iff (L : OxetModule B S hS) (V : SmallEtale B S hS) :
    (∃ e, IsGenerator L V e) ↔
      ∃ ι : Fin 1 → (SheafOfModules.unit ((structureSheaf B S hS).over V) ⟶ L.over V),
        Nonempty (IsColimit (Cofan.mk (L.over V) ι)) := by
  constructor
  · rintro ⟨e, he⟩
    have := isIso_unitHomOfSection he
    exact ⟨fun _ => unitHomOfSection L V e,
      (Cofan.nonempty_isColimit_mk_fin_one_iff _).mpr inferInstance⟩
  · rintro ⟨ι, hι⟩
    have := (Cofan.nonempty_isColimit_mk_fin_one_iff ι).mp hι
    exact ⟨_, isGenerator_sectionOfUnitHom L V (ι 0)⟩

/-- An `𝒪_{S,et}`-module is an étale line bundle exactly when every object `U` of the small
étale site has a covering `(Vᵢ ⟶ U)ᵢ` such that `L` has a generator over each `Vᵢ`. -/
theorem isEtaleLineBundle_iff_forall_exists_isGenerator (L : OxetModule B S hS) :
    IsEtaleLineBundle B S hS L ↔
      ∀ U : SmallEtale B S hS, ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS)
        (f : ∀ i, V i ⟶ U), Sieve.ofArrows V f ∈ topology B S hS U ∧
          ∀ i, ∃ e, IsGenerator L (V i) e := by
  constructor
  · intro h U
    obtain ⟨I, V, f, hf, hV⟩ := h U
    exact ⟨I, V, f, hf, fun i => (exists_isGenerator_iff L (V i)).mpr (hV i)⟩
  · intro h U
    obtain ⟨I, V, f, hf, hV⟩ := h U
    exact ⟨I, V, f, hf, fun i => (exists_isGenerator_iff L (V i)).mp (hV i)⟩

variable (L : OxetModule B S hS) in
/-- **Trivializations of an `𝒪_{S,et}`-module.** A covering `(Uᵢ ⟶ S)ᵢ` of `S` in its small
étale site, i.e. a family of arrows to the final object generating a covering sieve, together
with a generator `eᵢ` of `L` over each `Uᵢ`. -/
@[weil "def_fk102_etale_line_bundle"]
structure LineBundleTrivialization where
  /-- The index type of the covering. -/
  ι : Type (u + 1)
  /-- The members `Uᵢ` of the covering. -/
  obj : ι → SmallEtale B S hS
  /-- The arrows `Uᵢ ⟶ S` of the covering. -/
  hom : ∀ i, obj i ⟶ final B S hS
  /-- The family covers `S`. -/
  ofArrows_mem_topology : Sieve.ofArrows obj hom ∈ topology B S hS (final B S hS)
  /-- The generator `eᵢ ∈ L(Uᵢ)`. -/
  generator : ∀ i, L.val.obj (op (obj i))
  /-- Each `eᵢ` generates `L` over `Uᵢ`. -/
  isGenerator : ∀ i, IsGenerator L (obj i) (generator i)

/-- **An étale line bundle is an `𝒪_{S,et}`-module with a trivialization**: there are a
covering `(Uᵢ ⟶ S)ᵢ` of `S` in the small étale site and generators of `L` over the `Uᵢ`. -/
@[weil "def_fk102_etale_line_bundle"]
theorem isEtaleLineBundle_iff_nonempty_trivialization (L : OxetModule B S hS) :
    IsEtaleLineBundle B S hS L ↔ Nonempty (LineBundleTrivialization L) := by
  rw [isEtaleLineBundle_iff_forall_exists_isGenerator]
  constructor
  · intro h
    obtain ⟨I, V, f, hf, hV⟩ := h (final B S hS)
    choose e he using hV
    exact ⟨⟨I, V, f, hf, e, he⟩⟩
  · rintro ⟨T⟩ U
    let R := Sieve.pullback ((finalIsTerminal B S hS).from U) (Sieve.ofArrows T.obj T.hom)
    have hR : R ∈ topology B S hS U :=
      (topology B S hS).pullback_stable _ T.ofArrows_mem_topology
    refine ⟨R.arrows.category, fun g => g.obj.left, fun g => g.obj.hom, ?_, fun g => ?_⟩
    · rw [Sieve.ofArrows_category]
      exact hR
    · obtain ⟨i, h, -⟩ := Sieve.ofArrows.exists g.property
      exact ⟨_, (T.isGenerator i).restrict h⟩

/-- A chosen trivialization of an étale line bundle. -/
def IsEtaleLineBundle.trivialization {L : OxetModule B S hS}
    (hL : IsEtaleLineBundle B S hS L) : LineBundleTrivialization L :=
  ((isEtaleLineBundle_iff_nonempty_trivialization L).mp hL).some

end AlgebraicGeometry.SmallEtale
