module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable
public import Weil.Attr

/-!
# The sheaf represented by disjoint copies of the base is constant

Let `V` be a scheme and `σ` a set, and let `V^(σ) = ∐_{i ∈ σ} V` be the disjoint union of copies
of `V`, a `V`-scheme through the codiagonal `V^(σ) ⟶ V`. For a `V`-scheme `T`, a `V`-morphism
`g : T ⟶ V^(σ)` determines the locally constant map `c_g : |T| → σ` sending `t` to the index of
the copy containing `g(t)`. Conversely a locally constant map `c : |T| → σ` partitions `T` into
the open and closed subschemes `T_i = c⁻¹(i)`, and there is exactly one `V`-morphism `T ⟶ V^(σ)`
sending each `T_i` into the `i`-th copy, namely the structure morphism `T_i ⟶ V` followed by the
inclusion of that copy. These maps are inverse to each other and compatible with pullback along
`T' ⟶ T`. Hence the sheaf `Hom_V(-, V^(σ))` represented by `V^(σ)` on the étale site of `V` is
the constant sheaf `σ_V` of locally constant `σ`-valued maps; for `σ = {1, …, m}` this is the
statement that the sheaf represented by `V ⊔ ⋯ ⊔ V` (`m` copies) is `{1, …, m}_V`.

## Main definitions

* `AlgebraicGeometry.Scheme.sigmaIndex`: the locally constant map `∐ Y ⟶ σ` sending a point to
  the index of the component containing it.
* `AlgebraicGeometry.Scheme.disjointCopies`: the `V`-scheme `V^(σ) = ∐_{i ∈ σ} V`.
* `AlgebraicGeometry.Scheme.homDisjointCopiesEquiv`: for a `V`-scheme `T`, the bijection
  `Hom_V(T, V^(σ)) ≃ LocallyConstant |T| σ`.

## Main results

* `AlgebraicGeometry.SmallEtale.representablePresheafDisjointCopiesIso`: on the small étale site
  of `V`, the presheaf `h_{V^(σ)}` is isomorphic to the presheaf of locally constant
  `σ`-valued maps.
* `AlgebraicGeometry.SmallEtale.representableSheafDisjointCopiesIso`: the same for the sheaf
  represented by the object `V^(m)` of the small étale site, and
  `AlgebraicGeometry.SmallEtale.isSheaf_locallyConstantMapsType_fin`: hence `{1, …, m}_V` is an
  étale sheaf.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.representablePresheafDisjointCopiesIso`: on
  `Et(V)`, the presheaf `h_{V^(σ)}` is isomorphic to the constant presheaf `σ_V`.

## Implementation notes

The bijection `Hom_V(T, V^(σ)) ≃ LocallyConstant |T| σ` holds for every `V`-scheme `T` and every
`σ` small for the universe of schemes. The isomorphisms of presheaves are stated for `σ : Type`,
so that both sides take values in `Type u`; this contains the finite sets `Fin m` of the source.
The scheme `V^(σ)` is a `V`-scheme, not required to lie in the chosen big étale site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme

variable {σ : Type v} [Small.{u} σ]

/-! ### The index of the component of a point of a coproduct -/

lemma exists_sigmaι_apply_eq (Y : σ → Scheme.{u}) (x : (∐ Y :)) :
    ∃ i, x ∈ Set.range (Sigma.ι Y i) := by
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover Y).exists_eq x
  exact ⟨i, y, hy⟩

/-- The index of the component of `∐ Y` containing a point. -/
noncomputable def sigmaIndexFun (Y : σ → Scheme.{u}) (x : (∐ Y :)) : σ :=
  (exists_sigmaι_apply_eq Y x).choose

lemma sigmaIndexFun_eq_iff (Y : σ → Scheme.{u}) (x : (∐ Y :)) (i : σ) :
    sigmaIndexFun Y x = i ↔ x ∈ Set.range (Sigma.ι Y i) := by
  constructor
  · rintro rfl
    exact (exists_sigmaι_apply_eq Y x).choose_spec
  · rintro ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := (exists_sigmaι_apply_eq Y (Sigma.ι Y i y)).choose_spec
    exact congrArg Sigma.fst ((sigmaι_eq_iff Y _ _ _ _).1 hy')

@[simp]
lemma sigmaIndexFun_sigmaι_apply (Y : σ → Scheme.{u}) (i : σ) (y : Y i) :
    sigmaIndexFun Y (Sigma.ι Y i y) = i :=
  (sigmaIndexFun_eq_iff Y _ i).2 ⟨y, rfl⟩

lemma isOpen_sigmaIndexFun_fiber (Y : σ → Scheme.{u}) (i : σ) :
    IsOpen (sigmaIndexFun Y ⁻¹' {i}) := by
  have : sigmaIndexFun Y ⁻¹' {i} = ((Sigma.ι Y i).opensRange : Set (∐ Y :)) := by
    ext x
    exact sigmaIndexFun_eq_iff Y x i
  rw [this]
  exact (Sigma.ι Y i).opensRange.isOpen

/-- **The index of the component**: the locally constant map `∐ Y ⟶ σ` sending a point to the
index of the component of the coproduct containing it. -/
noncomputable def sigmaIndex (Y : σ → Scheme.{u}) : LocallyConstant (∐ Y :) σ where
  toFun := sigmaIndexFun Y
  isLocallyConstant := (IsLocallyConstant.iff_isOpen_fiber).2 (isOpen_sigmaIndexFun_fiber Y)

lemma sigmaIndex_eq_iff (Y : σ → Scheme.{u}) (x : (∐ Y :)) (i : σ) :
    sigmaIndex Y x = i ↔ x ∈ Set.range (Sigma.ι Y i) :=
  sigmaIndexFun_eq_iff Y x i

@[simp]
lemma sigmaIndex_sigmaι_apply (Y : σ → Scheme.{u}) (i : σ) (y : Y i) :
    sigmaIndex Y (Sigma.ι Y i y) = i :=
  sigmaIndexFun_sigmaι_apply Y i y

/-! ### The clopen decomposition defined by a locally constant map -/

/-- The open and closed subscheme `c⁻¹(i)` of a scheme `T`, for a locally constant map
`c : |T| → σ`. -/
def fiberOpens {T : Scheme.{u}} (c : LocallyConstant T σ) (i : σ) : T.Opens :=
  ⟨c ⁻¹' {i}, c.isLocallyConstant.isOpen_fiber i⟩

omit [Small.{u} σ] in
lemma mem_fiberOpens {T : Scheme.{u}} (c : LocallyConstant T σ) (i : σ) (t : T) :
    t ∈ fiberOpens c i ↔ c t = i :=
  Iff.rfl

/-- A scheme is the coproduct of the open and closed subschemes `c⁻¹(i)`, for a locally constant
map `c : |T| → σ`. -/
noncomputable def isColimitFiberOpens {T : Scheme.{u}} (c : LocallyConstant T σ) :
    IsColimit (Cofan.mk T fun i ↦ (fiberOpens c i).ι) :=
  (nonempty_isColimit_cofanMk_of (fun i ↦ (fiberOpens c i).ι)
    (by
      simp only [Scheme.Opens.opensRange_ι]
      rw [eq_top_iff]
      intro t _
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨c t, rfl⟩)
    (by
      intro i j hij
      simp only [Function.onFun, Scheme.Opens.opensRange_ι]
      rw [disjoint_iff, eq_bot_iff]
      rintro t ⟨hi, hj⟩
      exact hij (hi.symm.trans hj))).some

/-! ### Morphisms into disjoint copies of the base -/

variable (V : Scheme.{u}) (σ)

/-- **The disjoint union `V^(σ) = ∐_{i ∈ σ} V` of copies of `V`**, a `V`-scheme through the
codiagonal. -/
noncomputable abbrev disjointCopies : Over V :=
  Over.mk (Sigma.desc fun _ : σ ↦ 𝟙 V)

variable {V σ}

/-- The `V`-morphism `T ⟶ V^(σ)` attached to a locally constant map `c : |T| → σ`: on
`c⁻¹(i)` it is the structure morphism followed by the inclusion of the `i`-th copy. -/
noncomputable def homDisjointCopiesOfLocallyConstant (T : Over V) (c : LocallyConstant T.left σ) :
    T.left ⟶ ∐ fun _ : σ ↦ V :=
  Cofan.IsColimit.desc (isColimitFiberOpens c)
    fun i ↦ (fiberOpens c i).ι ≫ T.hom ≫ Sigma.ι (fun _ : σ ↦ V) i

@[reassoc (attr := simp)]
lemma ι_homDisjointCopiesOfLocallyConstant (T : Over V) (c : LocallyConstant T.left σ) (i : σ) :
    (fiberOpens c i).ι ≫ homDisjointCopiesOfLocallyConstant T c =
      (fiberOpens c i).ι ≫ T.hom ≫ Sigma.ι (fun _ : σ ↦ V) i :=
  Cofan.IsColimit.fac (isColimitFiberOpens c) _ i

lemma homDisjointCopiesOfLocallyConstant_comp (T : Over V) (c : LocallyConstant T.left σ) :
    homDisjointCopiesOfLocallyConstant T c ≫ (disjointCopies σ V).hom = T.hom :=
  Cofan.IsColimit.hom_ext (isColimitFiberOpens c) _ _ fun i ↦ by
    simp [disjointCopies]

/-- On a point `t` with `c t = i`, the `V`-morphism attached to `c` is the structure morphism
followed by the inclusion of the `i`-th copy. -/
lemma homDisjointCopiesOfLocallyConstant_apply (T : Over V) (c : LocallyConstant T.left σ)
    (t : T.left) (i : σ) (ht : c t = i) :
    homDisjointCopiesOfLocallyConstant T c t = Sigma.ι (fun _ : σ ↦ V) i (T.hom t) := by
  obtain ⟨x, rfl⟩ : t ∈ Set.range (fiberOpens c i).ι := by
    rw [Scheme.Opens.range_ι]
    exact ht
  rw [← Scheme.Hom.comp_apply, ι_homDisjointCopiesOfLocallyConstant, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply]

/-- **`Hom_V(T, V^(σ)) ≃ LocallyConstant |T| σ`.** A `V`-morphism `g : T ⟶ V^(σ)` corresponds
to the locally constant map sending `t` to the index of the copy containing `g(t)`. -/
noncomputable def homDisjointCopiesEquiv (T : Over V) :
    (T ⟶ disjointCopies σ V) ≃ LocallyConstant T.left σ where
  toFun g := (sigmaIndex fun _ : σ ↦ V).comap g.left.base.hom
  invFun c := Over.homMk (homDisjointCopiesOfLocallyConstant T c)
    (homDisjointCopiesOfLocallyConstant_comp T c)
  left_inv g := by
    ext1
    refine Cofan.IsColimit.hom_ext
      (isColimitFiberOpens ((sigmaIndex fun _ : σ ↦ V).comap g.left.base.hom)) _ _ fun i ↦ ?_
    simp only [cofan_mk_inj, Over.homMk_left, ι_homDisjointCopiesOfLocallyConstant]
    have hrange : Set.range ((fiberOpens ((sigmaIndex fun _ : σ ↦ V).comap g.left.base.hom) i).ι ≫
        g.left) ⊆ Set.range (Sigma.ι (fun _ : σ ↦ V) i) := by
      rintro _ ⟨t, rfl⟩
      rw [← sigmaIndex_eq_iff]
      exact t.2
    set a := IsOpenImmersion.lift (Sigma.ι (fun _ : σ ↦ V) i) _ hrange
    have ha : a ≫ Sigma.ι (fun _ : σ ↦ V) i = _ := IsOpenImmersion.lift_fac _ _ hrange
    have hw : g.left ≫ (disjointCopies σ V).hom = T.hom := Over.w g
    have : (fiberOpens ((sigmaIndex fun _ : σ ↦ V).comap g.left.base.hom) i).ι ≫ T.hom = a := by
      rw [← hw, ← Category.assoc, ← ha, Category.assoc]
      simp [disjointCopies]
    rw [← Category.assoc, this, ha]
  right_inv c := by
    ext t
    change sigmaIndex _ (homDisjointCopiesOfLocallyConstant T c t) = c t
    rw [homDisjointCopiesOfLocallyConstant_apply T c t (c t) rfl, sigmaIndex_sigmaι_apply]

/-- The bijection `Hom_V(T, V^(σ)) ≃ LocallyConstant |T| σ` is compatible with pullback along
`V`-morphisms `T' ⟶ T`. -/
lemma homDisjointCopiesEquiv_comp {T T' : Over V} (f : T' ⟶ T) (g : T ⟶ disjointCopies σ V) :
    homDisjointCopiesEquiv T' (f ≫ g) = (homDisjointCopiesEquiv T g).comap f.left.base.hom :=
  rfl

@[simp]
lemma homDisjointCopiesEquiv_apply (T : Over V) (g : T ⟶ disjointCopies σ V) (t : T.left) :
    homDisjointCopiesEquiv T g t = sigmaIndex (fun _ : σ ↦ V) (g.left t) :=
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (V : Scheme.{u}) (hV : B.Contains V) (σ : Type)

/-- **The sheaf represented by disjoint copies of the base is constant.** On the small étale
site of `V`, the sheaf `h_{V^(σ)} = Hom_V(-, V^(σ))` represented by `V^(σ) = ∐_{i ∈ σ} V` is
isomorphic to the presheaf `U ↦ LocallyConstant |U| σ` of locally constant `σ`-valued maps:
a `V`-morphism `g : U ⟶ V^(σ)` corresponds to the map sending `t` to the index of the copy
containing `g(t)`. For `σ = Fin m` this is `V ⊔ ⋯ ⊔ V` (`m` copies) and `{1, …, m}_V`. -/
@[weil "lem_fk104_representable_disjoint_copies_constant"]
noncomputable def representablePresheafDisjointCopiesIso :
    (representablePresheaf B V hV).obj (Scheme.disjointCopies σ V) ≅
      (toScheme B V hV).op ⋙ locallyConstantMapsType.{0, u} σ :=
  NatIso.ofComponents
    (fun U ↦ (Scheme.homDisjointCopiesEquiv ((toOver B V hV).obj U.unop)).toIso)
    (fun _ ↦ rfl)

variable {B V hV σ}

@[simp]
lemma representablePresheafDisjointCopiesIso_hom_app_apply (U : SmallEtale B V hV)
    (g : (toOver B V hV).obj U ⟶ Scheme.disjointCopies σ V) (t : (toScheme B V hV).obj U) :
    (show LocallyConstant ((toScheme B V hV).obj U) σ from
      (representablePresheafDisjointCopiesIso B V hV σ).hom.app (op U) g) t =
      Scheme.sigmaIndex (fun _ : σ ↦ V) (g.left t) :=
  rfl

variable (B V hV)

/-- The base `V` as an object of its small étale site, through the identity of `V`. -/
noncomputable abbrev baseObj : SmallEtale B V hV :=
  Stacks.EtaleCohomology.mkObj B hV V (𝟙 V) hV inferInstance

/-- The object `V^(m) = V ⊔ ⋯ ⊔ V` (`m` copies) of the small étale site of `V` is the
`V`-scheme `Scheme.disjointCopies (Fin m) V`. -/
lemma toOver_obj_disjointCopies_baseObj (m : ℕ) :
    (toOver B V hV).obj (Stacks.EtaleCohomology.disjointCopies B hV (baseObj B V hV) m) =
      Scheme.disjointCopies (Fin m) V :=
  rfl

/-- **The sheaf represented by `V^(m)` is `{1, …, m}_V`.** On the small étale site of `V`, the
sheaf represented by the object `V^(m) = V ⊔ ⋯ ⊔ V` (`m` copies) of the site is isomorphic to
the presheaf of locally constant `Fin m`-valued maps. -/
@[weil "lem_fk104_representable_disjoint_copies_constant"]
noncomputable def representableSheafDisjointCopiesIso (m : ℕ) :
    ((representableSheaf B V hV).obj
        (Stacks.EtaleCohomology.disjointCopies B hV (baseObj B V hV) m)).obj ≅
      (toScheme B V hV).op ⋙ locallyConstantMapsType.{0, u} (Fin m) :=
  representablePresheafDisjointCopiesIso B V hV (Fin m)

/-- The presheaf `{1, …, m}_V` of locally constant `Fin m`-valued maps is a sheaf on the small
étale site of `V`, being isomorphic to the sheaf represented by `V^(m)`. -/
theorem isSheaf_locallyConstantMapsType_fin (m : ℕ) :
    Presheaf.IsSheaf (topology B V hV)
      ((toScheme B V hV).op ⋙ locallyConstantMapsType.{0, u} (Fin m)) :=
  (Presheaf.isSheaf_of_iso_iff (representableSheafDisjointCopiesIso B V hV m)).1
    ((representableSheaf B V hV).obj
      (Stacks.EtaleCohomology.disjointCopies B hV (baseObj B V hV) m)).property

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (V : Scheme.{u}) (hV : B.Contains V) (σ : Type)

/-- **The sheaf represented by disjoint copies of the base is the constant sheaf on `Et(V)`.**
The restriction to `Et(V)` of the sheaf `h_{V^(σ)}` represented by `V^(σ) = ∐_{i ∈ σ} V` is
isomorphic to the constant presheaf `σ_V` of locally constant `σ`-valued maps. For
`σ = Fin m`, the sheaf represented by `V ⊔ ⋯ ⊔ V` (`m` copies) is `{1, …, m}_V`. -/
@[weil "lem_fk104_representable_disjoint_copies_constant"]
noncomputable def representablePresheafDisjointCopiesIso :
    (inclusion B V hV).op ⋙ (SmallEtale.representablePresheaf B V hV).obj
        (Scheme.disjointCopies σ V) ≅
      locallyConstantPresheaf B V hV σ :=
  Functor.isoWhiskerLeft (inclusion B V hV).op
    (SmallEtale.representablePresheafDisjointCopiesIso B V hV σ)

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
