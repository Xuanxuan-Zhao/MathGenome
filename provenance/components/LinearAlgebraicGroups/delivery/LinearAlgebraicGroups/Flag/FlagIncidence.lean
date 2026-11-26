import Specs.LinearAlgebraicGroups.Flag.FlagIncidence
import LinearAlgebraicGroups.Flag.GrassmannianCharts
import LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open TensorProduct AlgebraTensorModule

universe u

namespace LinearAlgebraicGroups.FlagIncidence

open Specs.GrassmannianCharts Specs.FlagIncidence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open private tensorExtensionOfHom planeMap_eq_span_of_hom coordinates_basis
  from LinearAlgebraicGroups.Flag.GrassmannianCharts

section AffineEquations

variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {d e m : ℕ} {R A : TestAlgebra k}

private theorem coordinates_tmul (r : R) (v : V) (j : idx) :
    coordinates b R (r ⊗ₜ[k] v) j = r * algebraMap k R (b.repr v j) := by
  change (b.baseChange R).repr (r ⊗ₜ[k] v) j = _
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

private theorem coordinates_extension (a : R ⟶ A) (v : R ⊗[k] V) (j : idx) :
    coordinates b A (tensorExtensionOfHom a v) j = a.hom (coordinates b R v j) := by
  induction v using TensorProduct.inductionOn with
  | tmul r v =>
    change coordinates b A (a.hom r ⊗ₜ[k] v) j = _
    rw [coordinates_tmul, coordinates_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp [hx, hy]

private def quotientSection (M : Plane k V e R) :
    ((R ⊗[k] V) ⧸ M.toSubmodule) →ₗ[R] R ⊗[k] V :=
  (Module.projective_lifting_property M.toSubmodule.mkQ LinearMap.id
    M.toSubmodule.mkQ_surjective).choose

private theorem mkQ_comp_quotientSection (M : Plane k V e R) :
    M.toSubmodule.mkQ.comp (quotientSection M) = LinearMap.id :=
  (Module.projective_lifting_property M.toSubmodule.mkQ LinearMap.id
    M.toSubmodule.mkQ_surjective).choose_spec

private def quotientProjection (M : Plane k V e R) :
    (R ⊗[k] V) →ₗ[R] (R ⊗[k] V) :=
  (quotientSection M).comp M.toSubmodule.mkQ

private theorem baseChange_quotientProjection_eq_zero_iff (a : R ⟶ A)
    (M : Plane k V e R) (v : R ⊗[k] V) :
    tensorExtensionOfHom a (quotientProjection M v) = 0 ↔
      tensorExtensionOfHom a v ∈ (Module.Grassmannian.map a.hom M).toSubmodule := by
  let : Algebra R A := a.hom.toAlgebra
  let : IsScalarTower k R A :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k R A)
  let c := cancelBaseChange k R A A V
  have hExt (x : R ⊗[k] V) : tensorExtensionOfHom a x = c (1 ⊗ₜ[R] x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      change a.hom r ⊗ₜ[k] x = c (1 ⊗ₜ[R] (r ⊗ₜ[k] x))
      simp [c, Algebra.smul_def, show algebraMap R A r = a.hom r from rfl]
    | add x y hx hy => simp [tmul_add, hx, hy]
  have hs : Function.Injective ((quotientSection M).baseChange A) := by
    apply Function.LeftInverse.injective (g := M.toSubmodule.mkQ.baseChange A)
    intro x
    exact DFunLike.congr_fun (show (M.toSubmodule.mkQ.baseChange A).comp
        ((quotientSection M).baseChange A) = LinearMap.id by
      rw [← LinearMap.baseChange_comp, mkQ_comp_quotientSection, LinearMap.baseChange_id]) x
  rw [hExt, hExt, Module.Grassmannian.map_toSubmodule]
  change c (1 ⊗ₜ[R] quotientProjection M v) = 0 ↔
    Module.Grassmannian.baseChangeMkQ A M.toSubmodule (c (1 ⊗ₜ[R] v)) = 0
  simp only [Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    map_eq_zero_iff _ c.injective]
  change _ = 0 ↔ (M.toSubmodule.mkQ.baseChange A) (c.symm (c (1 ⊗ₜ[R] v))) = 0
  rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  change (1 : A) ⊗ₜ[R] quotientSection M (M.toSubmodule.mkQ v) = 0 ↔ _
  rw [← LinearMap.baseChange_tmul, map_eq_zero_iff _ hs]

/-- Coefficients of the composite from the first plane to the quotient by
the second, computed using a split embedding of that quotient in the ambient module. -/
def incidenceIdeal (ranks : Fin m → ℕ)
    (L : ∀ i : Fin m, Plane k V (ranks i) R) : Ideal R :=
  Ideal.span { x | ∃ (i j : Fin m) (_ : i < j) (v : (L i).toSubmodule) (l : idx),
    coordinates b R (quotientProjection (L j) v) l = x }

theorem incidenceIdeal_property (ranks : Fin m → ℕ)
    (L : ∀ i : Fin m, Plane k V (ranks i) R) :
    IncidenceIdealProperty ranks L (incidenceIdeal b ranks L) := by
  intro A a
  rw [incidenceIdeal, Ideal.span_le]
  constructor
  · intro h i j hij
    rw [planeMap_eq_span_of_hom]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    apply (baseChange_quotientProjection_eq_zero_iff a (L j) v).mp
    apply (coordinates b A).injective
    ext l
    rw [coordinates_extension, map_zero]
    exact h ⟨i, j, hij, ⟨v, hv⟩, l, rfl⟩
  · rintro h _ ⟨i, j, hij, v, l, rfl⟩
    have hv : tensorExtensionOfHom a v.val ∈
        (Module.Grassmannian.map a.hom (L i)).toSubmodule := by
      rw [planeMap_eq_span_of_hom]
      exact Submodule.subset_span ⟨v, v.property, rfl⟩
    have hz := (baseChange_quotientProjection_eq_zero_iff a (L j) v).mpr (h hij hv)
    have hc := congrFun (congrArg (coordinates b A) hz) l
    rw [coordinates_extension, map_zero] at hc
    exact hc

private theorem incidenceIdeal_unique (ranks : Fin m → ℕ)
    (L : ∀ i : Fin m, Plane k V (ranks i) R) {I J : Ideal R}
    (hI : IncidenceIdealProperty ranks L I) (hJ : IncidenceIdealProperty ranks L J) :
    I = J := by
  have aux (I J : Ideal R) (hI : IncidenceIdealProperty ranks L I)
      (hJ : IncidenceIdealProperty ranks L J) : I ≤ J := by
    let a : R ⟶ CommAlgCat.of k (R ⧸ J) := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k J)
    have ha : RingHom.ker a.hom.toRingHom = J := Ideal.mk_ker
    rw [← ha, hI]
    exact (hJ (a := a)).mp (by rw [ha])
  exact (aux I J hI hJ).antisymm (aux J I hJ hI)

theorem affineIncidenceEquations : AffineIncidenceEquations.{u} := by
  intro k V idx _ _ _ _ _ b m ranks R L
  exact ⟨incidenceIdeal b ranks L, incidenceIdeal_property b ranks L,
    fun _ h ↦ incidenceIdeal_unique ranks L h (incidenceIdeal_property b ranks L)⟩

private theorem incidenceIdeal_map (ranks : Fin m → ℕ)
    (L : ∀ i : Fin m, Plane k V (ranks i) R) (a : R ⟶ A) :
    (incidenceIdeal b ranks L).map a.hom.toRingHom =
      incidenceIdeal b ranks (fun i ↦ Module.Grassmannian.map a.hom (L i)) := by
  apply incidenceIdeal_unique ranks _ _ (incidenceIdeal_property b ranks _)
  intro B c
  rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  have h := incidenceIdeal_property b ranks L (a := a ≫ c)
  change (incidenceIdeal b ranks L ≤ RingHom.ker (c.hom.comp a.hom).toRingHom ↔ _) at h
  change _ ≤ RingHom.ker (c.hom.comp a.hom).toRingHom ↔ _
  exact h.trans (by
    simp only [show (a ≫ c).hom = c.hom.comp a.hom from rfl, Module.Grassmannian.map_comp])

end AffineEquations

section IdealSheaf

variable {k : Type u} [Field k] {X Y : SchemeOver k}

private abbrev affineOpenAlgebra (U : X.left.affineOpens) : Algebra k Γ(X.left, U) :=
  (Spec.fullyFaithful.preimage (U.2.fromSpec ≫ X.hom)).unop.hom.toAlgebra

private def affineOpenRing (U : X.left.affineOpens) : TestAlgebra k :=
  letI := affineOpenAlgebra (k := k) U
  CommAlgCat.of k Γ(X.left, U)

private def affineOpenProbe (U : X.left.affineOpens) :
    Points X (affineOpenRing U) :=
  Over.homMk U.2.fromSpec (by
    change _ = Spec.map (Spec.fullyFaithful.preimage (U.2.fromSpec ≫ X.hom)).unop
    exact (Spec.fullyFaithful.map_preimage _).symm)

private def affineOpenMap (f : X ⟶ Y) (U : Y.left.affineOpens) (W : X.left.affineOpens)
    (h : W.1 ≤ f.left ⁻¹ᵁ U.1) : affineOpenRing U ⟶ affineOpenRing W := by
  let ψ := f.left.appLE U.1 W.1 h
  have hc : Spec.map ψ ≫ U.2.fromSpec = W.2.fromSpec ≫ f.left :=
    IsAffineOpen.SpecMap_appLE_fromSpec f.left U.2 W.2 h
  letI := affineOpenAlgebra U
  letI := affineOpenAlgebra W
  refine CommAlgCat.ofHom { toRingHom := ψ.hom, commutes' := fun r ↦ ?_ }
  have he : Spec.map ψ ≫ ((testSpec k).obj (op (affineOpenRing U))).hom =
      ((testSpec k).obj (op (affineOpenRing W))).hom := by
    rw [← Over.w (affineOpenProbe U), ← Over.w (affineOpenProbe W)]
    change Spec.map ψ ≫ (U.2.fromSpec ≫ Y.hom) = W.2.fromSpec ≫ X.hom
    rw [← Category.assoc, hc, Category.assoc, Over.w f]
  change Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y.left, U))) =
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, W))) at he
  rw [← Spec.map_comp] at he
  have he' := Spec.map_injective he
  exact congrArg (fun g : CommRingCat.of k ⟶ Γ(X.left, W) ↦ g r) he'

private theorem affineOpenMap_probe (f : X ⟶ Y) (U : Y.left.affineOpens)
    (W : X.left.affineOpens) (h : W.1 ≤ f.left ⁻¹ᵁ U.1) :
    (testSpec k).map (affineOpenMap f U W h).op ≫ affineOpenProbe U =
      affineOpenProbe W ≫ f := by
  apply Over.OverMorphism.ext
  change Spec.map (f.left.appLE U.1 W.1 h) ≫ U.2.fromSpec = W.2.fromSpec ≫ f.left
  exact IsAffineOpen.SpecMap_appLE_fromSpec f.left U.2 W.2 h

variable {V idx : Type u} [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {m : ℕ} (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

private theorem productPlanes_naturality {R A : TestAlgebra k} (a : R ⟶ A)
    (p : Points (GrassmannianProduct ranks b C) R) (i : Fin m) :
    productPlanes ranks b C (mapPoints a p) i =
      Module.Grassmannian.map a.hom (productPlanes ranks b C p i) := by
  have h := congrArg (fun f : Points (C i).scheme R ⟶ Plane k V (ranks i) A ↦
    f (p ≫ Pi.π _ i)) ((C i).affinePoints.hom.naturality a)
  change (C i).affinePoints.hom.app A ((testSpec k).map a.op ≫ (p ≫ Pi.π _ i)) =
    Module.Grassmannian.map a.hom ((C i).affinePoints.hom.app R (p ≫ Pi.π _ i)) at h
  simpa only [productPlanes, Category.assoc] using h

/-- The ideal of the incidence locus, computed on every affine open of the
product. The ideals agree under restriction by base change. -/
def incidenceIdealSheaf : (GrassmannianProduct ranks b C).left.IdealSheafData where
  ideal U := incidenceIdeal b ranks (productPlanes ranks b C (affineOpenProbe U))
  map_ideal_basicOpen U s := by
    let Z := GrassmannianProduct ranks b C
    let W := Z.left.affineBasicOpen s
    let h : W.1 ≤ (Over.Hom.left (𝟙 Z)) ⁻¹ᵁ U.1 := by
      change W.1 ≤ (𝟙 Z.left) ⁻¹ᵁ U.1
      simpa [W] using Z.left.basicOpen_le s
    let a := affineOpenMap (𝟙 Z) U W h
    have ha : a.hom.toRingHom =
        (Z.left.presheaf.map (homOfLE (Z.left.basicOpen_le s)).op).hom := by
      change (Scheme.Hom.appLE (𝟙 Z.left) _ _ h).hom = _
      simp [Scheme.Hom.appLE]
    rw [← ha]
    change (incidenceIdeal b ranks (productPlanes ranks b C (affineOpenProbe U))).map
      a.hom.toRingHom = incidenceIdeal b ranks (productPlanes ranks b C (affineOpenProbe W))
    rw [incidenceIdeal_map b ranks _ a]
    congr 1
    funext i
    rw [← productPlanes_naturality]
    congr 1
    exact (affineOpenMap_probe (𝟙 Z) U W h).trans (Category.comp_id _)

/-- The closed scheme defined by the incidence equations. -/
def flagScheme : SchemeOver k :=
  Over.mk ((incidenceIdealSheaf b ranks C).subschemeι ≫
    (GrassmannianProduct ranks b C).hom)

def flagInclusion : flagScheme b ranks C ⟶ GrassmannianProduct ranks b C :=
  Over.homMk (incidenceIdealSheaf b ranks C).subschemeι rfl

instance : IsClosedImmersion (flagInclusion b ranks C).left :=
  inferInstanceAs (IsClosedImmersion (incidenceIdealSheaf b ranks C).subschemeι)

private theorem incidenceIdealSheaf_le_ker {S : SchemeOver k}
    (p : S ⟶ GrassmannianProduct ranks b C)
    (hp : ∀ (R : TestAlgebra k) (a : Points S R) ⦃i j : Fin m⦄, i < j →
      (productPlanes ranks b C (a ≫ p) i).toSubmodule ≤
        (productPlanes ranks b C (a ≫ p) j).toSubmodule) :
    incidenceIdealSheaf b ranks C ≤ p.left.ker := by
  apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
  intro U x hx
  change p.left.app U.1 x = 0
  apply S.left.IsSheaf.section_ext
  intro y hy
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset hy
  let W' : S.left.affineOpens := ⟨W, hW⟩
  let a := affineOpenMap p U W' hWU
  have he (i : Fin m) :
      Module.Grassmannian.map a.hom (productPlanes ranks b C (affineOpenProbe U) i) =
        productPlanes ranks b C (affineOpenProbe W' ≫ p) i := by
    rw [← productPlanes_naturality, show mapPoints a (affineOpenProbe U) = _ from
      affineOpenMap_probe p U W' hWU]
  have hn : ∀ ⦃i j : Fin m⦄, i < j →
      (Module.Grassmannian.map a.hom (productPlanes ranks b C (affineOpenProbe U) i)).toSubmodule ≤
        (Module.Grassmannian.map a.hom (productPlanes ranks b C (affineOpenProbe U) j)).toSubmodule := by
    intro i j hij
    simpa only [he] using hp _ (affineOpenProbe W') hij
  have hh := ((incidenceIdeal_property b ranks (productPlanes ranks b C (affineOpenProbe U)))
      (a := a)).mpr hn hx
  refine ⟨W, hWU, hyW, ?_⟩
  change (p.left.appLE U.1 W hWU) x = 0 at hh
  simpa only [Scheme.Hom.appLE, CommRingCat.comp_apply, map_zero] using hh

private theorem baseChange_nested {R A : TestAlgebra k} (a : R ⟶ A)
    {d e : ℕ} (L : Plane k V d R) (M : Plane k V e R)
    (h : L.toSubmodule ≤ M.toSubmodule) :
    (Module.Grassmannian.map a.hom L).toSubmodule ≤
      (Module.Grassmannian.map a.hom M).toSubmodule := by
  rw [planeMap_eq_span_of_hom, planeMap_eq_span_of_hom]
  exact Submodule.span_mono (Set.image_mono h)

private theorem incidenceIdealSheaf_ker_le_iff {S : SchemeOver k}
    (p : S ⟶ GrassmannianProduct ranks b C) :
    incidenceIdealSheaf b ranks C ≤ p.left.ker ↔
      ∀ (R : TestAlgebra k) (a : Points S R) ⦃i j : Fin m⦄, i < j →
        (productPlanes ranks b C (a ≫ p) i).toSubmodule ≤
          (productPlanes ranks b C (a ≫ p) j).toSubmodule := by
  refine ⟨?_, incidenceIdealSheaf_le_ker b ranks C p⟩
  intro hp R q i j hij
  let T := (testSpec k).obj (op R)
  let f : T ⟶ GrassmannianProduct ranks b C := q ≫ p
  have hf : incidenceIdealSheaf b ranks C ≤ f.left.ker :=
    hp.trans (Scheme.Hom.le_ker_comp q.left p.left)
  let : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  let H : T.left.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let L := productPlanes ranks b C (affineOpenProbe H ≫ f)
  have hzero : incidenceIdeal b ranks L ≤ ⊥ := by
    intro t ht
    change t = 0
    apply T.left.IsSheaf.section_ext (U := op (⊤ : T.left.Opens))
    intro x _
    obtain ⟨U, hU, hfx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
      (show f.left x ∈ (⊤ : (GrassmannianProduct ranks b C).left.Opens) from trivial)
    let U' : (GrassmannianProduct ranks b C).left.affineOpens := ⟨U, hU⟩
    have hx : x ∈ f.left ⁻¹ᵁ U := hfx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    let W' : T.left.affineOpens := ⟨W, hW⟩
    let a := affineOpenMap f U' W' hWU
    have htop : W'.1 ≤ (Over.Hom.left (𝟙 T)) ⁻¹ᵁ H.1 := by
      change W ≤ (𝟙 T.left) ⁻¹ᵁ (⊤ : T.left.Opens)
      simp
    let c := affineOpenMap (𝟙 T) H W' htop
    have hc : mapPoints c (affineOpenProbe H) = affineOpenProbe W' :=
      (affineOpenMap_probe (𝟙 T) H W' htop).trans (Category.comp_id _)
    have ha : mapPoints a (affineOpenProbe U') = affineOpenProbe W' ≫ f :=
      affineOpenMap_probe f U' W' hWU
    have he : (incidenceIdeal b ranks L).map c.hom.toRingHom =
        ((incidenceIdealSheaf b ranks C).ideal U').map a.hom.toRingHom := by
      change _ = (incidenceIdeal b ranks (productPlanes ranks b C (affineOpenProbe U'))).map _
      rw [incidenceIdeal_map b ranks _ c, incidenceIdeal_map b ranks _ a]
      congr 1
      funext l
      rw [← productPlanes_naturality, ← productPlanes_naturality, ha]
      congr 1
      simpa only [Category.assoc] using congrArg (· ≫ f) hc
    have hkill : ((incidenceIdealSheaf b ranks C).ideal U').map a.hom.toRingHom = ⊥ := by
      apply (Ideal.map_eq_bot_iff_le_ker _).mpr
      exact (hf U').trans ((f.left.ideal_ker_le U').trans
        (fun t ht ↦ by
          change f.left.appLE U W hWU t = 0
          change f.left.app U t = 0 at ht
          simp [Scheme.Hom.appLE, ht]))
    have ht' := Ideal.mem_map_of_mem c.hom.toRingHom ht
    rw [he, hkill] at ht'
    change (Scheme.Hom.appLE (𝟙 T.left) ⊤ W htop) t = 0 at ht'
    exact ⟨W, le_top, hxW, by simpa [Scheme.Hom.appLE] using ht'⟩
  have hn := ((incidenceIdeal_property b ranks L) (a := 𝟙 (affineOpenRing H))).mp (by
    have hh : RingHom.ker (CommAlgCat.Hom.hom (𝟙 (affineOpenRing H))).toRingHom = ⊥ := by
      ext x
      exact RingHom.mem_ker.trans Ideal.mem_bot.symm
    rwa [hh])
  have hL : (L i).toSubmodule ≤ (L j).toSubmodule := by
    simpa only [CommAlgCat.hom_id, Module.Grassmannian.map_id] using hn hij
  have hIso : IsIso (affineOpenProbe H).left := by
    change IsIso H.2.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hIso' : IsIso (affineOpenProbe H) := by
    let : IsIso ((Over.forget _).map (affineOpenProbe H)) := hIso
    exact isIso_of_reflects_iso (affineOpenProbe H) (Over.forget _)
  let g := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (inv (affineOpenProbe H))
  have hg : (testSpec k).map g ≫ (affineOpenProbe H ≫ f) = f := by
    rw [(algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage, IsIso.inv_hom_id_assoc]
  have hg' : mapPoints g.unop (affineOpenProbe H ≫ f) = f := hg
  change (productPlanes ranks b C f i).toSubmodule ≤ (productPlanes ranks b C f j).toSubmodule
  rw [← hg', productPlanes_naturality, productPlanes_naturality]
  exact baseChange_nested g.unop (L i) (L j) hL

private theorem flagInclusion_mono : Mono (flagInclusion b ranks C) :=
  Over.mono_of_mono_left _

/-- A map factors through the incidence subscheme exactly when its pulled
back planes are nested on every affine probe. -/
theorem factorsThroughFlag_iff {S : SchemeOver k}
    (p : S ⟶ GrassmannianProduct ranks b C) :
    (∃ q : S ⟶ flagScheme b ranks C, q ≫ flagInclusion b ranks C = p) ↔
      ∀ (R : TestAlgebra k) (a : Points S R) ⦃i j : Fin m⦄, i < j →
        (productPlanes ranks b C (a ≫ p) i).toSubmodule ≤
          (productPlanes ranks b C (a ≫ p) j).toSubmodule := by
  rw [← incidenceIdealSheaf_ker_le_iff b ranks C p]
  let I := incidenceIdealSheaf b ranks C
  change _ ↔ I ≤ p.left.ker
  constructor
  · rintro ⟨q, rfl⟩
    rw [← I.ker_subschemeι]
    exact Scheme.Hom.le_ker_comp q.left I.subschemeι
  · intro h
    have hk : I.subschemeι.ker ≤ p.left.ker := by rwa [I.ker_subschemeι]
    let q := IsClosedImmersion.lift I.subschemeι p.left hk
    have hq : q ≫ I.subschemeι = p.left := IsClosedImmersion.lift_fac _ _ _
    exact ⟨Over.homMk q (by change q ≫ (I.subschemeι ≫ _) = _; rw [← Category.assoc, hq, Over.w]),
      Over.OverMorphism.ext hq⟩

end IdealSheaf


section SubbundleIncidence

open private openPullbackComparison openTest openTestInclusion
  from LinearAlgebraicGroups.Flag.GrassmannianCharts
open GrassmannianCharts (pullbackSubbundle pullbackSubbundle_spec pullbackSubbundle_comp
  pullbackSubbundle_unique moduleSheafRange moduleSheafRangeIso moduleSheafRangeIso_ι)
open Scheme.Modules

variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {d e : ℕ} {S T : SchemeOver k}

private theorem affineSubbundles_le_iff {R : TestAlgebra k}
    (L : Plane k V d R) (M : Plane k V e R)
    (P : Subbundles k V d ((testSpec k).obj (op R)))
    (Q : Subbundles k V e ((testSpec k).obj (op R)))
    (hP : IsTildePlane V b R L P) (hQ : IsTildePlane V b R M Q) :
    P.val ≤ Q.val ↔ L.toSubmodule ≤ M.toSubmodule := by
  obtain ⟨ep, hp⟩ := hP
  obtain ⟨eq, hq⟩ := hQ
  let F := tilde.functor (CommRingCat.of R)
  let E := affineAmbientOfBasis (k := k) (V := V) b R
  constructor
  · intro h
    let g := ep.hom ≫ Subobject.ofLE _ _ h ≫ eq.inv
    let s := (tilde.fullyFaithfulFunctor (R := CommRingCat.of R)).preimage g
    have hs : s ≫ ModuleCat.ofHom M.toSubmodule.subtype =
        ModuleCat.ofHom L.toSubmodule.subtype := by
      apply (tilde.fullyFaithfulFunctor (R := CommRingCat.of R)).map_injective
      change F.map _ = F.map _
      rw [Functor.map_comp, (tilde.fullyFaithfulFunctor (R := CommRingCat.of R)).map_preimage,
        ← hq, ← hp]
      simp only [g, Category.assoc, Iso.inv_hom_id_assoc, Subobject.ofLE_arrow_assoc]
    intro x hx
    have hval : (s ⟨x, hx⟩ : R ⊗[k] V) = x :=
      congrArg (fun f : ModuleCat.of R L.toSubmodule ⟶ _ ↦ f ⟨x, hx⟩) hs
    rw [← hval]
    exact (s ⟨x, hx⟩).property
  · intro h
    let s : ModuleCat.of R L.toSubmodule ⟶ ModuleCat.of R M.toSubmodule :=
      ModuleCat.ofHom (Submodule.inclusion h)
    have hs : s ≫ ModuleCat.ofHom M.toSubmodule.subtype =
        ModuleCat.ofHom L.toSubmodule.subtype := rfl
    apply Subobject.le_of_comm (ep.inv ≫ F.map s ≫ eq.hom)
    apply (cancel_mono E.hom).mp
    have he := congrArg F.map hs
    rw [Functor.map_comp, ← hq, ← hp] at he
    simp only [Category.assoc] at he ⊢
    rw [he, Iso.inv_hom_id_assoc]

private theorem pullbackSubbundle_le (a : T ⟶ S)
    {L : Subbundles k V d S} {M : Subbundles k V e S} (h : L.val ≤ M.val) :
    (pullbackSubbundle a L).val ≤ (pullbackSubbundle a M).val := by
  obtain ⟨eL, hL⟩ := pullbackSubbundle_spec a L
  obtain ⟨eM, hM⟩ := pullbackSubbundle_spec a M
  apply Subobject.le_of_comm (eL.inv ≫ (Scheme.Modules.pullback a.left).map
    (Subobject.ofLE L.val M.val h) ≫ eM.hom)
  simp only [Category.assoc, hM, ← Functor.map_comp_assoc, Subobject.ofLE_arrow,
    ← hL, Iso.inv_hom_id_assoc]

include b in
private theorem pullbackSubbundle_comp_eq {A : SchemeOver k} (f : T ⟶ A) (g : A ⟶ S)
    (a : T ⟶ S) (h : f ≫ g = a) (N : Subbundles k V d S) :
    pullbackSubbundle f (pullbackSubbundle g N) = pullbackSubbundle a N :=
  (pullbackSubbundle_comp b f g N).trans
    (congrArg (fun g : T ⟶ S ↦ pullbackSubbundle g N) h)

set_option maxHeartbeats 1200000 in
include b in
private theorem subbundles_le_of_affineOpens
    (L : Subbundles k V d S) (M : Subbundles k V e S)
    (h : ∀ U : S.left.affineOpens,
      (pullbackSubbundle (affineOpenProbe U) L).val ≤
        (pullbackSubbundle (affineOpenProbe U) M).val) :
    L.val ≤ M.val := by
  let Q := moduleSheafRange M.val.arrow
  let E := moduleSheafRangeIso M.val.arrow
  have hQ : L.val ≤ Subobject.mk Q.ι := by
    have hs : moduleSheafRange L.val.arrow ≤ Q := by
      intro W s hs
      apply Q.isSheaf s
      intro x hx
      obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
      let U' : S.left.affineOpens := ⟨U, hU⟩
      let O : SchemeOver k := openTest U
      let a : O ⟶ S := openTestInclusion U
      let g : (testSpec k).obj (op (affineOpenRing U')) ⟶ O :=
        Over.homMk hU.isoSpec.inv (by
          rw [← Over.w (affineOpenProbe U')]
          rfl)
      let g' : O ⟶ (testSpec k).obj (op (affineOpenRing U')) :=
        Over.homMk hU.isoSpec.hom (by
          rw [← Over.w (affineOpenProbe U')]
          change hU.isoSpec.hom ≫ (hU.fromSpec ≫ S.hom) = _
          rw [IsAffineOpen.isoSpec_hom_fromSpec_assoc]
          rfl)
      have hg : g ≫ a = affineOpenProbe U' := rfl
      have hgg : g' ≫ g = 𝟙 O := Over.OverMorphism.ext hU.isoSpec.hom_inv_id
      have hle := pullbackSubbundle_le g' (h U')
      have hcomp : g' ≫ affineOpenProbe U' = a :=
        (congrArg (g' ≫ ·) hg.symm).trans ((Category.assoc g' g a).symm.trans
          ((congrArg (· ≫ a) hgg).trans (Category.id_comp a)))
      have hle' : (pullbackSubbundle a L).val ≤ (pullbackSubbundle a M).val := by
        have hl := pullbackSubbundle_comp_eq b g' (affineOpenProbe U') a hcomp L
        have hm := pullbackSubbundle_comp_eq b g' (affineOpenProbe U') a hcomp M
        exact hl ▸ hm ▸ hle
      obtain ⟨eL, heL⟩ := pullbackSubbundle_spec a L
      obtain ⟨eM, heM⟩ := pullbackSubbundle_spec a M
      let F := (overEquiv U).functor
      let C := openPullbackComparison U
      let A := ambientPullback k V a
      let f := (C.app (L.val : S.left.Modules)).hom ≫ eL.hom ≫
        Subobject.ofLE _ _ hle' ≫ eM.inv ≫ (C.app (M.val : S.left.Modules)).inv
      have hf : f ≫ F.map (M.val.arrow.over U) = F.map (L.val.arrow.over U) := by
        apply (cancel_mono ((C.app (ambient k V S)).hom ≫ A.hom)).mp
        have hnat (N : S.left.Modules) (z : N ⟶ ambient k V S) :
            F.map (z.over U) ≫ (C.app (ambient k V S)).hom ≫ A.hom =
              (C.app N).hom ≫ (Scheme.Modules.pullback U.ι).map z ≫ A.hom :=
          C.hom.naturality_assoc z A.hom
        simp only [Category.assoc]
        rw [hnat _ L.val.arrow, hnat _ M.val.arrow]
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc]
        change (C.app (L.val : S.left.Modules)).hom ≫ eL.hom ≫
          Subobject.ofLE _ _ hle' ≫ eM.inv ≫
          (Scheme.Modules.pullback a.left).map M.val.arrow ≫ (ambientPullback k V a).hom =
          (C.app (L.val : S.left.Modules)).hom ≫
          (Scheme.Modules.pullback a.left).map L.val.arrow ≫ (ambientPullback k V a).hom
        rw [← heM, Iso.inv_hom_id_assoc, Subobject.ofLE_arrow, ← heL]
      let z := (overEquiv U).fullyFaithfulFunctor.preimage f
      have hz : z ≫ M.val.arrow.over U = L.val.arrow.over U := by
        apply (overEquiv U).fullyFaithfulFunctor.map_injective
        change F.map _ = F.map _
        rw [Functor.map_comp, (overEquiv U).fullyFaithfulFunctor.map_preimage]
        exact hf
      refine ⟨U, homOfLE hUW, ?_, hxU⟩
      have hs' := (moduleSheafRange L.val.arrow).toSubmodule.map_mem
        (homOfLE hUW).op hs
      change _ ∈ (L.val.arrow.val.app (op U)).hom.range at hs'
      obtain ⟨t, ht⟩ := hs'
      change _ ∈ (M.val.arrow.val.app (op U)).hom.range
      let Z : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
      refine ⟨z.val.app Z t, ?_⟩
      exact (congrArg (fun q ↦ q.val.app Z t) hz).trans ht
    let z : (moduleSheafRange L.val.arrow).toSheafOfModules ⟶ Q.toSheafOfModules :=
      ⟨PresheafOfModules.Submodule.homOfLE hs⟩
    apply Subobject.le_mk_of_comm ((moduleSheafRangeIso L.val.arrow).hom ≫ z)
    rw [Category.assoc, show z ≫ Q.ι = (moduleSheafRange L.val.arrow).ι from rfl,
      moduleSheafRangeIso_ι]
  have hM : M.val = Subobject.mk Q.ι := Subobject.eq_mk_of_comm Q.ι E
    (moduleSheafRangeIso_ι M.val.arrow)
  exact hM ▸ hQ

end SubbundleIncidence

section Representability

open GrassmannianCharts (pullbackSubbundle pullbackSubbundle_spec pullbackSubbundle_unique)
variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {m : ℕ} (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))
  (P : ∀ i : Fin m, SchemePoints (k := k) (V := V) (ranks i)
    (C i).scheme (C i).affinePoints)
  (hc : ∀ (i : Fin m) (R : TestAlgebra k) (p : Points (C i).scheme R),
    IsTildePlane V b R ((C i).affinePoints.hom.app R p)
      ((P i).subbundle _ ((P i).family _ p)))

include hc in
private theorem productSubbundles_nested_iff {S : SchemeOver k}
    (p : S ⟶ GrassmannianProduct ranks b C) :
    (∀ ⦃i j : Fin m⦄, i < j →
      (productSubbundles ranks b C P p i).val ≤ (productSubbundles ranks b C P p j).val) ↔
      ∀ (R : TestAlgebra k) (a : Points S R) ⦃i j : Fin m⦄, i < j →
        (productPlanes ranks b C (a ≫ p) i).toSubmodule ≤
          (productPlanes ranks b C (a ≫ p) j).toSubmodule := by
  have htilde (R : TestAlgebra k) (a : Points S R) (i : Fin m) :
      IsTildePlane V b R (productPlanes ranks b C (a ≫ p) i)
        (pullbackSubbundle a (productSubbundles ranks b C P p i)) := by
    have he := (P i).pullback a (p ≫ Pi.π _ i)
    have he' := pullbackSubbundle_unique a (productSubbundles ranks b C P p i) _ _
      (pullbackSubbundle_spec a _) he
    rw [he']
    exact hc i R ((a ≫ p) ≫ Pi.π _ i) |> (by
      simpa only [productPlanes, Category.assoc] using ·)
  constructor
  · intro hn R a i j hij
    exact (affineSubbundles_le_iff b _ _ _ _ (htilde R a i) (htilde R a j)).mp
      (pullbackSubbundle_le a (hn hij))
  · intro hn i j hij
    apply subbundles_le_of_affineOpens b
    intro U
    exact (affineSubbundles_le_iff b _ _ _ _ (htilde _ (affineOpenProbe U) i)
      (htilde _ (affineOpenProbe U) j)).mpr (hn _ (affineOpenProbe U) hij)

private theorem productSubbundles_injective (S : SchemeOver k) :
    Function.Injective (productSubbundles ranks b C P (S := S)) := by
  intro f g h
  apply Pi.hom_ext
  intro i
  apply (P i).family S |>.injective
  apply (P i).subbundle S |>.injective
  exact congrFun h i

private theorem subobject_le_iff_comp_cokernel_eq_zero {D : Type*} [Category D] [Abelian D]
    {M : D} (L N : Subobject M) : L ≤ N ↔ L.arrow ≫ cokernel.π N.arrow = 0 := by
  constructor
  · intro h
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  · intro h
    let isKernel := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel N.arrow)
    obtain ⟨f, hf⟩ := KernelFork.IsLimit.lift' isKernel L.arrow h
    exact Subobject.le_of_comm f hf

private theorem nested_iff_adjacent {α : Type*} [Preorder α] {n : ℕ} (L : Fin n → α) :
    (∀ ⦃i j⦄, i < j → L i ≤ L j) ↔
      (∀ ⦃i j⦄, i.val + 1 = j.val → L i ≤ L j) := by
  constructor
  · intro h i j hij
    exact h (show i.val < j.val by omega)
  · cases n with
    | zero => exact fun _ i ↦ Fin.elim0 i
    | succ n =>
      intro h i j hij
      exact (Fin.monotone_iff_le_succ.mpr (fun l ↦ h (i := l.castSucc) (j := l.succ) rfl))
        hij.le

/-- Points of the incidence scheme are exactly nested subbundles. -/
def flagPointsEquiv (S : SchemeOver k) :
    (S ⟶ flagScheme b ranks C) ≃ BundleFlag k V ranks S := by
  let I := flagInclusion b ranks C
  letI : Mono I := flagInclusion_mono b ranks C
  let F : (S ⟶ flagScheme b ranks C) → BundleFlag k V ranks S := fun f ↦
    ⟨productSubbundles ranks b C P (f ≫ I),
      (productSubbundles_nested_iff b ranks C P hc (f ≫ I)).mpr
        ((factorsThroughFlag_iff b ranks C (f ≫ I)).mp ⟨f, rfl⟩)⟩
  apply Equiv.ofBijective F
  constructor
  · intro f g he
    apply (cancel_mono I).mp
    exact productSubbundles_injective b ranks C P S (congrArg Subtype.val he)
  · intro L
    let f (i : Fin m) : S ⟶ (C i).scheme :=
      ((P i).family S).symm (((P i).subbundle S).symm (L.val i))
    let p := Pi.lift f
    have h (i : Fin m) : productSubbundles ranks b C P p i = L.val i := by
      dsimp only [productSubbundles, p]
      have hi : Pi.lift f ≫ Pi.π _ i = f i := by
        simpa only [Category.comp_id] using Pi.lift_comp_π_assoc f i (𝟙 ((C i).scheme))
      rw [hi]
      simp [f]
    have hn : ∀ ⦃i j : Fin m⦄, i < j →
        (productSubbundles ranks b C P p i).val ≤ (productSubbundles ranks b C P p j).val := by
      intro i j hij
      rw [h, h]
      exact L.property hij
    obtain ⟨q, hq⟩ := (factorsThroughFlag_iff b ranks C p).mpr
      ((productSubbundles_nested_iff b ranks C P hc p).mp hn)
    refine ⟨q, Subtype.ext (funext fun i ↦ ?_)⟩
    change productSubbundles ranks b C P (q ≫ I) i = L.val i
    rw [hq]
    exact h i

theorem flagPointsEquiv_apply {S : SchemeOver k} (p : S ⟶ flagScheme b ranks C)
    (i : Fin m) :
    (flagPointsEquiv b ranks C P hc S p).val i =
      productSubbundles ranks b C P (p ≫ flagInclusion b ranks C) i := rfl

theorem flagPointsEquiv_pullback {S T : SchemeOver k} (f : T ⟶ S)
    (p : S ⟶ flagScheme b ranks C) (i : Fin m) :
    IsPullbackSubbundle k V f (flagPointsEquiv b ranks C P hc S p |>.val i)
      (flagPointsEquiv b ranks C P hc T (f ≫ p) |>.val i) := by
  simp only [flagPointsEquiv_apply, productSubbundles, Category.assoc]
  exact (P i).pullback _ _

/-- The closed incidence locus and its point comparisons. -/
def flagPresentation : Presentation ranks b C P where
  scheme := flagScheme b ranks C
  inclusion := flagInclusion b ranks C
  closed := inferInstance
  affine_comparison R p i := hc i R (p ≫ Pi.π _ i)
  factor_affine R p := by
    rw [factorsThroughFlag_iff b ranks C p]
    constructor
    · intro h i j hij
      simpa only [Category.id_comp] using h R (𝟙 _) hij
    · intro h A a i j hij
      let f := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage a
      have he : (testSpec k).map f = a :=
        (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a
      rw [← he]
      change (productPlanes ranks b C (mapPoints f.unop p) i).toSubmodule ≤
        (productPlanes ranks b C (mapPoints f.unop p) j).toSubmodule
      rw [productPlanes_naturality, productPlanes_naturality]
      exact baseChange_nested f.unop _ _ (h hij)
  factor_iff_zero S p := by
    rw [factorsThroughFlag_iff b ranks C p, ← productSubbundles_nested_iff b ranks C P hc p]
    exact (nested_iff_adjacent (fun i ↦ (productSubbundles ranks b C P p i).val)).trans
      (by simp only [subobject_le_iff_comp_cokernel_eq_zero])
  families := flagPointsEquiv b ranks C P hc
  families_apply := fun _ p i ↦ flagPointsEquiv_apply b ranks C P hc p i
  pullback := fun f p i ↦ flagPointsEquiv_pullback b ranks C P hc f p i
  empty_terminal := by
    intro h
    subst m
    let L (S : SchemeOver k) : BundleFlag k V ranks S :=
      ⟨fun i ↦ Fin.elim0 i, fun {i} ↦ Fin.elim0 i⟩
    let ε := flagPointsEquiv b ranks C P hc
    refine ⟨IsTerminal.ofUniqueHom (fun S ↦ (ε S).symm (L S)) ?_⟩
    intro S f
    apply (ε S).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (funext fun i ↦ Fin.elim0 i)

theorem flagIncidenceConstruction : Specs.FlagIncidence.Construction.{u} := by
  intro k V idx _ _ _ _ _ b m ranks _ hr
  choose C P hP using fun i : Fin m ↦
    GrassmannianCharts.construction k V idx b (ranks i) (hr i)
  exact ⟨C, P, ⟨flagPresentation b ranks C P hP⟩⟩

end Representability


section Action

open Specs.StandardGroups
open StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
open GrassmannianCharts (affineProbesEquiv affineProbesEquiv_apply hom_ext_on_affines)

variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {R A : TestAlgebra k} {d m : ℕ}

private theorem coordinates_transport (g : Matrix.GeneralLinearGroup idx R) (v : R ⊗[k] V) :
    coordinates b R (matrixTransport b R g v) =
      (g : Matrix idx idx R).mulVec (coordinates b R v) := by
  simp [matrixTransport, ← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin]

private theorem matrixTransport_extension (a : R ⟶ A)
    (g : Matrix.GeneralLinearGroup idx R) (v : R ⊗[k] V) :
    tensorExtensionOfHom a (matrixTransport b R g v) =
      matrixTransport b A (Matrix.GeneralLinearGroup.map a.hom.toRingHom g)
        (tensorExtensionOfHom a v) := by
  apply (coordinates b A).injective
  funext j
  rw [coordinates_extension, coordinates_transport, coordinates_transport]
  have h := RingHom.map_mulVec a.hom.toRingHom (g : Matrix idx idx R) (coordinates b R v) j
  change _ = ((g : Matrix idx idx R).map a.hom.toRingHom).mulVec
    (coordinates b A (tensorExtensionOfHom a v)) j
  rw [show coordinates b A (tensorExtensionOfHom a v) = a.hom ∘ coordinates b R v from
    funext (coordinates_extension b a v)]
  exact h

private def linearTransportPlane (f : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V))
    (L : Plane k V d R) : Plane k V d R :=
  let Q := L.toSubmodule.map f.toLinearMap
  let e := Submodule.Quotient.equiv L.toSubmodule Q f rfl
  { toSubmodule := Q
    finite_quotient := Module.Finite.equiv e
    projective_quotient := Module.Projective.of_equiv e
    rankAtStalk_eq := fun p ↦
      (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans (L.rankAtStalk_eq p) }

private abbrev transportPlane (g : Matrix.GeneralLinearGroup idx R)
    (L : Plane k V d R) : Plane k V d R :=
  linearTransportPlane (matrixTransport b R g) L

private theorem transportPlane_naturality (a : R ⟶ A)
    (g : Matrix.GeneralLinearGroup idx R) (L : Plane k V d R) :
    Module.Grassmannian.map a.hom (transportPlane b g L) =
      transportPlane b (Matrix.GeneralLinearGroup.map a.hom.toRingHom g)
        (Module.Grassmannian.map a.hom L) := by
  apply Module.Grassmannian.ext
  rw [planeMap_eq_span_of_hom]
  change Submodule.span A (tensorExtensionOfHom a ''
      (L.toSubmodule.map (matrixTransport b R g).toLinearMap : Set (R ⊗[k] V))) =
    (Module.Grassmannian.map a.hom L).toSubmodule.map
      (matrixTransport b A (Matrix.GeneralLinearGroup.map a.hom.toRingHom g)).toLinearMap
  rw [planeMap_eq_span_of_hom, Submodule.map_span, Submodule.map_coe, Set.image_image,
    Set.image_image]
  congr 1
  exact congrArg (fun f : R ⊗[k] V → A ⊗[k] V ↦ f '' (L.toSubmodule : Set (R ⊗[k] V)))
    (funext (matrixTransport_extension b a g))

private abbrev glObject := (generalLinearGroup k idx).val
private abbrev matrixAt (p : Points (glObject (k := k) (idx := idx)).X R) :
    Matrix.GeneralLinearGroup idx R :=
  (generalLinearGroupPointsIso k idx).hom.app R p

private theorem matrixAt_naturality (a : R ⟶ A)
    (p : Points (glObject (k := k) (idx := idx)).X R) :
    matrixAt (mapPoints a p) = Matrix.GeneralLinearGroup.map a.hom.toRingHom (matrixAt p) := by
  exact congrArg (fun f : ((groupPointsFunctor k).obj (glObject (k := k) (idx := idx))).obj R ⟶
    (generalLinearPoints k idx).obj A ↦ f p)
    ((generalLinearGroupPointsIso k idx).hom.naturality a)

variable (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

private abbrev productActionSource := (glObject (k := k) (idx := idx)).X ⨯ GrassmannianProduct ranks b C

private def productActionPoints (R : TestAlgebra k)
    (p : Points (productActionSource b ranks C) R) :
    Points (GrassmannianProduct ranks b C) R :=
  Pi.lift fun i ↦ (C i).affinePoints.inv.app R
    (transportPlane b (matrixAt (p ≫ prod.fst)) (productPlanes ranks b C (p ≫ prod.snd) i))

private theorem productActionPoints_plane (R : TestAlgebra k)
    (p : Points (productActionSource b ranks C) R) (i : Fin m) :
    productPlanes ranks b C (productActionPoints b ranks C R p) i =
      transportPlane b (matrixAt (p ≫ prod.fst)) (productPlanes ranks b C (p ≫ prod.snd) i) := by
  let f (i : Fin m) :=
    (C i).affinePoints.inv.app R
      (transportPlane b (matrixAt (p ≫ prod.fst)) (productPlanes ranks b C (p ≫ prod.snd) i))
  have hi : Pi.lift f ≫ Pi.π _ i = f i := by
    simpa only [Category.comp_id] using Pi.lift_comp_π_assoc f i (𝟙 ((C i).scheme))
  change (C i).affinePoints.hom.app R (Pi.lift f ≫ Pi.π _ i) = _
  rw [hi]
  exact congrArg (fun h : Plane k V (ranks i) R ⟶ Plane k V (ranks i) R ↦
    h (transportPlane b (matrixAt (p ≫ prod.fst))
      (productPlanes ranks b C (p ≫ prod.snd) i))) ((C i).affinePoints.inv_hom_id_app R)

private theorem productPlanes_injective (R : TestAlgebra k) :
    Function.Injective (productPlanes ranks b C (R := R)) := by
  intro f g h
  apply Pi.hom_ext
  intro i
  apply (ConcreteCategory.bijective_of_isIso ((C i).affinePoints.hom.app R)).1
  exact congrFun h i

private def productActionTransformation :
    pointsFunctor (productActionSource b ranks C) ⟶ pointsFunctor (GrassmannianProduct ranks b C) where
  app R := ↾productActionPoints b ranks C R
  naturality {R A} a := by
    apply ConcreteCategory.hom_ext
    intro p
    change productActionPoints b ranks C A (mapPoints a p) =
      mapPoints a (productActionPoints b ranks C R p)
    apply productPlanes_injective b ranks C
    funext i
    rw [productPlanes_naturality, productActionPoints_plane, productActionPoints_plane,
      transportPlane_naturality]
    simp only [show mapPoints a p ≫ prod.fst = mapPoints a (p ≫ prod.fst)
      from Category.assoc _ _ _, show mapPoints a p ≫ prod.snd = mapPoints a (p ≫ prod.snd)
      from Category.assoc _ _ _, matrixAt_naturality, productPlanes_naturality]

/-- The action on the Grassmannian product by transport of every ambient submodule. -/
def productAction : productActionSource b ranks C ⟶ GrassmannianProduct ranks b C :=
  (affineProbesEquiv _ _).symm (productActionTransformation b ranks C)

theorem productAction_plane (R : TestAlgebra k)
    (p : Points (productActionSource b ranks C) R) (i : Fin m) :
    (productPlanes ranks b C (p ≫ productAction b ranks C) i).toSubmodule =
      (productPlanes ranks b C (p ≫ prod.snd) i).toSubmodule.map
        (matrixTransport b R (matrixAt (p ≫ prod.fst))).toLinearMap := by
  have h := congrArg (fun α : pointsFunctor (productActionSource b ranks C) ⟶
    pointsFunctor (GrassmannianProduct ranks b C) ↦ α.app R p)
    ((affineProbesEquiv _ _).apply_symm_apply (productActionTransformation b ranks C))
  change p ≫ productAction b ranks C = productActionPoints b ranks C R p at h
  rw [h, productActionPoints_plane]
  rfl

private abbrev flagActionSource := (glObject (k := k) (idx := idx)).X ⨯ flagScheme b ranks C

private theorem productAction_preserves_flag :
    ∃ q : flagActionSource b ranks C ⟶ flagScheme b ranks C,
      q ≫ flagInclusion b ranks C =
        prod.map (𝟙 (glObject (k := k) (idx := idx)).X) (flagInclusion b ranks C) ≫
          productAction b ranks C := by
  apply (factorsThroughFlag_iff b ranks C _).mpr
  intro R a i j hij
  have h := (factorsThroughFlag_iff b ranks C (flagInclusion b ranks C)).mp ⟨𝟙 _, by simp⟩
    R (a ≫ prod.snd) hij
  rw [← Category.assoc, productAction_plane, productAction_plane]
  simp only [Category.assoc, prod.map_snd] at h ⊢
  exact Submodule.map_mono h

/-- The restriction of the product action to the closed incidence locus. -/
def flagAction : flagActionSource b ranks C ⟶ flagScheme b ranks C :=
  (productAction_preserves_flag b ranks C).choose

theorem flagAction_restricts :
    flagAction b ranks C ≫ flagInclusion b ranks C =
      prod.map (𝟙 (glObject (k := k) (idx := idx)).X) (flagInclusion b ranks C) ≫
        productAction b ranks C :=
  (productAction_preserves_flag b ranks C).choose_spec

end Action

section BasisPoint

open GrassmannianCharts (graphPlane graphPlane_toSubmodule)
variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {m : ℕ} (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

private theorem graphZero_eq_span {j : Type u} [Fintype j] [DecidableEq j]
    (β : Module.Basis j k V) {d : ℕ} (I : Pivot j d) (R : TestAlgebra k) :
    (graphPlane β I R 0).toSubmodule = Submodule.span R
      ((β.baseChange R) '' (I.val : Set j)) := by
  rw [graphPlane_toSubmodule]
  let g := graphInclusion β I R 0
  have col (l : Inside I) : g (Pi.single l 1) = (β.baseChange R) l.val := by
    apply (coordinates β R).injective
    funext i
    have hg : coordinates β R (g (Pi.single l 1)) = graphColumns I R 0 (Pi.single l 1) :=
      (coordinates β R).apply_symm_apply _
    rw [hg]
    rw [Module.Basis.baseChange_apply, coordinates_basis]
    by_cases h : i ∈ I.val
    · simp only [graphColumns, LinearMap.pi_apply, dite_eq_left h, LinearMap.proj_apply]
      by_cases e : l.val = i
      · have el : l = ⟨i, h⟩ := Subtype.ext e
        simp [el]
      · have el : (⟨i, h⟩ : Inside I) ≠ l := fun hh ↦ e (congrArg Subtype.val hh.symm)
        simp [e, Pi.single_eq_of_ne el]
    · have he : l.val ≠ i := fun he ↦ h (he ▸ l.property)
      simp [graphColumns, h, he]
  have hg : g.range = (Submodule.span R (Set.range (Pi.basisFun R (Inside I)))).map g := by
    rw [(Pi.basisFun R (Inside I)).span_eq, Submodule.map_top]
  change g.range = _
  rw [hg, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.val, l.property, by simpa [Pi.basisFun_apply] using (col l).symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, by simpa [Pi.basisFun_apply] using col ⟨l, hl⟩⟩

private def prefixPlane {n d : ℕ} (β : Module.Basis (Fin n) k V) (hd : d ≤ n) (R : TestAlgebra k) :
    Plane k V d R :=
  let I : Pivot (ULift.{u} (Fin n)) d :=
    ⟨Finset.univ.map ((Fin.castLEEmb hd).trans Equiv.ulift.symm.toEmbedding), by simp⟩
  graphPlane (β.reindex Equiv.ulift.symm) I R 0

private theorem prefixPlane_submodule {n d : ℕ} (β : Module.Basis (Fin n) k V)
    (hd : d ≤ n) (R : TestAlgebra k) :
    (prefixPlane β hd R).toSubmodule = prefixSubmodule β R d := by
  let I : Pivot (ULift.{u} (Fin n)) d :=
    ⟨Finset.univ.map ((Fin.castLEEmb hd).trans Equiv.ulift.symm.toEmbedding), by simp⟩
  change (graphPlane (β.reindex Equiv.ulift.symm) I R 0).toSubmodule = _
  rw [graphZero_eq_span, prefixSubmodule]
  congr 1
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hld : l.down.val < d := by
      change l ∈ Finset.univ.map ((Fin.castLEEmb hd).trans Equiv.ulift.symm.toEmbedding) at hl
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hl
      rw [← hj]
      exact j.isLt
    refine ⟨l.down, hld, ?_⟩
    simp [Module.Basis.baseChange_apply]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨ULift.up l, ?_, by simp [Module.Basis.baseChange_apply]⟩
    exact Finset.mem_map.mpr ⟨⟨l.val, hl⟩, Finset.mem_univ _, rfl⟩

private theorem map_span_basis_subset {R M J : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (B B' : Module.Basis J R M) (s : Set J) :
    (Submodule.span R (B '' s)).map (B.equiv B' (Equiv.refl J)).toLinearMap =
      Submodule.span R (B' '' s) := by
  rw [Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span R)
  apply Set.image_congr'
  intro i
  change B.equiv B' (Equiv.refl J) (B i) = B' i
  rw [Module.Basis.equiv_apply, Equiv.refl_apply]

/-- Every ordered basis determines a rational point of this flag scheme. -/
theorem flagBasisPoints (hn : Monotone ranks) (hr : ∀ i, ranks i ≤ Module.finrank k V) :
    HasBasisPoints ranks b C (flagInclusion b ranks C) := by
  intro n β
  let R := CommAlgCat.of k k
  have hdim : Module.finrank k V = n := by simp [Module.finrank_eq_card_basis β]
  let L (i : Fin m) := prefixPlane β ((hr i).trans_eq hdim) R
  have hL (i : Fin m) : (L i).toSubmodule = prefixSubmodule β R (ranks i) :=
    prefixPlane_submodule β _ R
  let f (i : Fin m) := (C i).affinePoints.inv.app R (L i)
  let p := Pi.lift f
  have hp (i : Fin m) : productPlanes ranks b C p i = L i := by
    have hi : Pi.lift f ≫ Pi.π _ i = f i := Pi.lift_comp_π f i
    change (C i).affinePoints.hom.app R (Pi.lift f ≫ Pi.π _ i) = L i
    rw [hi]
    exact congrArg (fun h : Plane k V (ranks i) R ⟶ Plane k V (ranks i) R ↦ h (L i))
      ((C i).affinePoints.inv_hom_id_app R)
  obtain ⟨q, hq⟩ := (factorsThroughFlag_iff b ranks C p).mpr (by
    intro A a i j hij
    let φ := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage a
    have he : (testSpec k).map φ = a :=
      (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a
    rw [← he]
    change (productPlanes ranks b C (mapPoints φ.unop p) i).toSubmodule ≤
      (productPlanes ranks b C (mapPoints φ.unop p) j).toSubmodule
    rw [productPlanes_naturality, productPlanes_naturality, hp, hp]
    apply baseChange_nested
    rw [hL, hL]
    exact Submodule.span_mono (Set.image_mono (fun x hx ↦ Nat.lt_of_lt_of_le hx (hn hij.le))))
  exact ⟨q, fun i ↦ by rw [hq, hp, hL]⟩

end BasisPoint

section ActionLaws

open Specs.StandardGroups
open StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
open GrassmannianCharts (hom_ext_on_affines)
open scoped CategoryTheory.MonObj

variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {m : ℕ} (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

private theorem productAction_lift_plane {R : TestAlgebra k}
    (g : Points (glObject (k := k) (idx := idx)).X R)
    (q : Points (GrassmannianProduct ranks b C) R) (i : Fin m) :
    (productPlanes ranks b C (prod.lift g q ≫ productAction b ranks C) i).toSubmodule =
      (productPlanes ranks b C q i).toSubmodule.map (matrixTransport b R (matrixAt g)).toLinearMap :=
  by rw [productAction_plane, prod.lift_snd, prod.lift_fst]

private theorem flagAction_plane {R : TestAlgebra k} (g : Points (glObject (k := k) (idx := idx)).X R)
    (q : Points (flagScheme b ranks C) R) (i : Fin m) :
    (productPlanes ranks b C ((prod.lift g q ≫ flagAction b ranks C) ≫ flagInclusion b ranks C)
      i).toSubmodule =
      (productPlanes ranks b C (q ≫ flagInclusion b ranks C) i).toSubmodule.map
        (matrixTransport b R (matrixAt g)).toLinearMap := by
  rw [Category.assoc, flagAction_restricts, prod.lift_map_assoc, Category.comp_id,
    productAction_lift_plane]

private theorem flags_eq_of_planes {R : TestAlgebra k} {p q : Points (flagScheme b ranks C) R}
    (h : ∀ i, (productPlanes ranks b C (p ≫ flagInclusion b ranks C) i).toSubmodule =
      (productPlanes ranks b C (q ≫ flagInclusion b ranks C) i).toSubmodule) : p = q := by
  let := flagInclusion_mono b ranks C
  apply (cancel_mono (flagInclusion b ranks C)).mp
  apply productPlanes_injective b ranks C
  exact funext fun i ↦ Module.Grassmannian.ext (h i)

private theorem matrixTransport_identity (R : TestAlgebra k) :
    matrixTransport b R (1 : Matrix.GeneralLinearGroup idx R) = LinearEquiv.refl R _ := by
  ext v
  change (coordinates b R).symm
    ((Matrix.GeneralLinearGroup.toLin (1 : Matrix.GeneralLinearGroup idx R)).toLinearEquiv
      (coordinates b R v)) = v
  rw [map_one]
  exact (coordinates b R).symm_apply_apply _

private theorem matrixTransport_comp {R : TestAlgebra k} (g h : Matrix.GeneralLinearGroup idx R) :
    (matrixTransport b R h).trans (matrixTransport b R g) = matrixTransport b R (g * h) := by
  ext v
  simp only [matrixTransport, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
  rfl

private theorem productAction_one (S : SchemeOver k) (p : S ⟶ GrassmannianProduct ranks b C) :
    prod.lift (1 : S ⟶ (glObject (k := k) (idx := idx)).X) p ≫ productAction b ranks C = p := by
  apply hom_ext_on_affines
  intro R a
  rw [← Category.assoc, prod.comp_lift, MonObj.comp_one]
  apply productPlanes_injective b ranks C
  funext i
  apply Module.Grassmannian.ext
  have h : matrixAt (1 : Points (glObject (k := k) (idx := idx)).X R) = 1 :=
    (GrpCat.Hom.hom ((generalLinearGroupPointsIso k idx).hom.app R)).map_one
  rw [productAction_lift_plane, h, matrixTransport_identity, LinearEquiv.refl_toLinearMap,
    Submodule.map_id]

private theorem productAction_mul (S : SchemeOver k)
    (g h : S ⟶ (glObject (k := k) (idx := idx)).X) (p : S ⟶ GrassmannianProduct ranks b C) :
    prod.lift (g * h) p ≫ productAction b ranks C =
      prod.lift g (prod.lift h p ≫ productAction b ranks C) ≫ productAction b ranks C := by
  apply hom_ext_on_affines
  intro R a
  simp only [← Category.assoc, prod.comp_lift, MonObj.comp_mul]
  apply productPlanes_injective b ranks C
  funext i
  apply Module.Grassmannian.ext
  rw [productAction_lift_plane, productAction_lift_plane, productAction_lift_plane]
  have he : matrixAt ((a ≫ g) * (a ≫ h)) = matrixAt (a ≫ g) * matrixAt (a ≫ h) :=
    (GrpCat.Hom.hom ((generalLinearGroupPointsIso k idx).hom.app R)).map_mul _ _
  rw [he, ← Submodule.map_comp]
  change _ = Submodule.map ((matrixTransport b R (matrixAt (a ≫ h))).trans
    (matrixTransport b R (matrixAt (a ≫ g)))).toLinearMap _
  rw [matrixTransport_comp]

private theorem flagAction_one (S : SchemeOver k) (p : S ⟶ flagScheme b ranks C) :
    prod.lift (1 : S ⟶ (glObject (k := k) (idx := idx)).X) p ≫ flagAction b ranks C = p := by
  let := flagInclusion_mono b ranks C
  apply (cancel_mono (flagInclusion b ranks C)).mp
  rw [Category.assoc, flagAction_restricts, prod.lift_map_assoc, Category.comp_id]
  exact productAction_one b ranks C S _

private theorem flagAction_mul (S : SchemeOver k) (g h : S ⟶ (glObject (k := k) (idx := idx)).X)
    (p : S ⟶ flagScheme b ranks C) :
    prod.lift (g * h) p ≫ flagAction b ranks C =
      prod.lift g (prod.lift h p ≫ flagAction b ranks C) ≫ flagAction b ranks C := by
  let := flagInclusion_mono b ranks C
  apply (cancel_mono (flagInclusion b ranks C)).mp
  simp only [Category.assoc, flagAction_restricts, prod.lift_map_assoc, Category.comp_id]
  exact productAction_mul b ranks C S g h _

/-- Linear transport of the ambient bundle defines the scheme action on flags. -/
def intrinsicFlagAction :
    Specs.FlagIncidence.Action ranks b C (flagInclusion b ranks C) (glObject (k := k) (idx := idx))
      (generalLinearGroupPointsIso k idx) where
  onProduct := productAction b ranks C
  onFlags := flagAction b ranks C
  restricts := flagAction_restricts b ranks C
  transport := productAction_plane b ranks C
  one_onProduct := productAction_one b ranks C
  mul_onProduct := productAction_mul b ranks C
  one := flagAction_one b ranks C
  mul := flagAction_mul b ranks C

theorem flagIncidenceWithAction : ConstructionWithAction.{u} := by
  intro k V idx _ _ _ _ _ b m ranks hmono hr
  choose C P hP using fun i : Fin m ↦
    GrassmannianCharts.construction k V idx b (ranks i) (hr i)
  exact ⟨C, P, flagPresentation b ranks C P hP, (generalLinearGroup k idx).val,
    generalLinearGroupPointsIso k idx, ⟨intrinsicFlagAction b ranks C⟩,
    flagBasisPoints b ranks C hmono.monotone hr⟩

end ActionLaws

section AdaptedFiberBasis

variable {R F : Type u} [CommRing R] [Field F] [Algebra R F]

/-- A basis of a fibre can be selected from the images of elements of the module. -/
private theorem exists_lifted_fibre_basis (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) (hn : Module.finrank F (F ⊗[R] M) = n) :
    ∃ v : Fin n → M, ∃ B : Module.Basis (Fin n) F (F ⊗[R] M),
      ∀ j, B j = 1 ⊗ₜ[R] v j := by
  classical
  let T : Set (F ⊗[R] M) := Set.range fun x : M ↦ (1 : F) ⊗ₜ[R] x
  have hT : ⊤ ≤ Submodule.span F T := by
    intro y hy
    clear hy
    induction y using TensorProduct.inductionOn with
    | tmul f x =>
      have hx : (1 : F) ⊗ₜ[R] x ∈ Submodule.span F T := Submodule.subset_span ⟨x, rfl⟩
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (Submodule.span F T).smul_mem f hx
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  let B₀ := Module.Basis.ofSpan hT
  let order := B₀.indexEquiv (Module.finBasisOfFinrankEq F (F ⊗[R] M) hn)
  let B := B₀.reindex order
  have hB₀ : Set.range B₀ ⊆ T := Module.Basis.ofSpan_subset hT
  have hB (i : Fin n) : B i ∈ T := by
    dsimp only [B]
    rw [Module.Basis.reindex_apply]
    exact hB₀ (Set.mem_range_self (order.symm i))
  choose v hv using hB
  exact ⟨v, B, fun i ↦ (hv i).symm⟩

private def submoduleInclusionEquiv {M : Type u} [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (h : P ≤ Q) : P.comap Q.subtype ≃ₗ[R] P where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem submoduleInclusion_compl {M : Type u} [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (h : P ≤ Q) (C : Submodule R M) (hc : IsCompl P C) :
    ∃ D : Submodule R Q, IsCompl (P.comap Q.subtype) D := by
  let f := (submoduleInclusionEquiv h).symm.toLinearMap.comp
    ((P.projectionOnto C hc).comp Q.subtype)
  have hf (x : P.comap Q.subtype) : f x = x := by
    change (submoduleInclusionEquiv h).symm
      (P.projectionOnto C hc (Q.subtype x)) = x
    rw [show Q.subtype x = ((submoduleInclusionEquiv h) x).val from rfl,
      Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  exact ⟨f.ker, LinearMap.isCompl_of_proj hf⟩

/-- Inductively split off the final complement and concatenate lifted fibre
bases. Containment of the chosen columns already holds over the original ring. -/
private theorem exists_lifted_adapted_fibre_basis (m : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (P : Fin m → Submodule R M) (ranks : Fin m → ℕ) (n : ℕ),
      Monotone P → Monotone ranks →
      (∀ i, ∃ Q : Submodule R M, IsCompl (P i) Q) →
      (∀ i, Module.finrank F (F ⊗[R] P i) = ranks i) →
      Module.finrank F (F ⊗[R] M) = n →
      ∃ v : Fin n → M, ∃ B : Module.Basis (Fin n) F (F ⊗[R] M),
        (∀ j, B j = 1 ⊗ₜ[R] v j) ∧ ∀ i j, j.val < ranks i → v j ∈ P i := by
  classical
  induction m with
  | zero =>
    intro M _ _ _ P ranks n _ _ _ _ hM
    obtain ⟨v, B, hB⟩ := exists_lifted_fibre_basis M n hM
    exact ⟨v, B, hB, fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    intro M _ _ _ P ranks n hP hr hC hR hM
    let l : Fin (m + 1) := Fin.last m
    let L := P l
    obtain ⟨Q, hQ⟩ := hC l
    let s := L.prodEquivOfIsCompl Q hQ
    let : Module.Finite R L := Module.Finite.of_surjective
      ((LinearMap.fst R L Q).comp s.symm.toLinearMap) (fun x ↦ ⟨s (x, 0), by simp⟩)
    let : Module.Finite R Q := Module.Finite.of_surjective
      ((LinearMap.snd R L Q).comp s.symm.toLinearMap) (fun x ↦ ⟨s (0, x), by simp⟩)
    let P' (i : Fin m) := (P i.castSucc).comap L.subtype
    have hle (i : Fin m) : P i.castSucc ≤ L := hP (Fin.le_last _)
    have hP' : Monotone P' := fun _ _ hij ↦ Submodule.comap_mono (hP (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hC' (i : Fin m) : ∃ D : Submodule R L, IsCompl (P' i) D := by
      obtain ⟨D, hD⟩ := hC i.castSucc
      exact submoduleInclusion_compl (hle i) D hD
    have hR' (i : Fin m) : Module.finrank F (F ⊗[R] P' i) = ranks i.castSucc :=
      ((submoduleInclusionEquiv (hle i)).baseChange R F _ _).finrank_eq.trans (hR i.castSucc)
    obtain ⟨v₁, B₁, hB₁, hv₁⟩ := ih L P' (fun i ↦ ranks i.castSucc) (ranks l)
      hP' (fun _ _ hij ↦ hr (Fin.castSucc_le_castSucc_iff.mpr hij)) hC' hR' (hR l)
    let t := Module.finrank F (F ⊗[R] Q)
    obtain ⟨v₂, B₂, hB₂⟩ := exists_lifted_fibre_basis Q t rfl
    let e := (TensorProduct.prodRight R F F L Q).symm ≪≫ₗ s.baseChange R F _ _
    have hn : ranks l + t = n := by
      have hh := e.finrank_eq
      rw [Module.finrank_prod, hR l, hM] at hh
      exact hh
    let c : Fin (ranks l) ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
    let v : Fin n → M := fun i ↦ Sum.elim (fun j ↦ (v₁ j : M)) (fun j ↦ (v₂ j : M)) (c.symm i)
    let B := ((B₁.prod B₂).map e).reindex c
    refine ⟨v, B, ?_, ?_⟩
    · intro i
      obtain ⟨j, rfl⟩ := c.surjective i
      rw [show B (c j) = e (B₁.prod B₂ j) from by simp [B], show v (c j) = _ from
        congrArg (Sum.elim (fun j ↦ (v₁ j : M)) (fun j ↦ (v₂ j : M))) (c.symm_apply_apply j)]
      cases j with
      | inl j =>
        simp only [Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply,
          hB₁, e, LinearEquiv.trans_apply]
        have hzero : (0 : F ⊗[R] Q) = (1 : F) ⊗ₜ[R] (0 : Q) := by simp
        rw [hzero, TensorProduct.prodRight_symm_tmul, LinearEquiv.baseChange_tmul,
          Submodule.coe_prodEquivOfIsCompl']
        simp
      | inr j =>
        simp only [Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
          hB₂, e, LinearEquiv.trans_apply]
        have hzero : (0 : F ⊗[R] L) = (1 : F) ⊗ₜ[R] (0 : L) := by simp
        rw [hzero, TensorProduct.prodRight_symm_tmul, LinearEquiv.baseChange_tmul,
          Submodule.coe_prodEquivOfIsCompl']
        simp
    · intro i j
      obtain ⟨j, rfl⟩ := c.surjective j
      rw [show v (c j) = _ from congrArg
        (Sum.elim (fun j ↦ (v₁ j : M)) (fun j ↦ (v₂ j : M))) (c.symm_apply_apply j)]
      cases j with
      | inl j =>
        change j.val < ranks i → (v₁ j : M) ∈ P i
        refine Fin.lastCases (fun _ ↦ (v₁ j).property) (fun i hj ↦ ?_) i
        exact hv₁ i j hj
      | inr j =>
        change ranks l + j.val < ranks i → _
        have hh : ranks i ≤ ranks l := hr (Fin.le_last i)
        omega

end AdaptedFiberBasis

section AdaptedNeighborhood

open private awayAlgebra awayMap awayMap_left_range tensorExtension
  tensorExtension_eq_of_hom tensorExtension_mem_planeMap
  from LinearAlgebraicGroups.Flag.GrassmannianCharts
open GrassmannianCharts (planeSplitAndRank)

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {R : TestAlgebra k} {d m : ℕ}

private theorem planes_eq_of_le (L M : Plane k V d R) (h : L.toSubmodule ≤ M.toSubmodule) :
    L = M := by
  let f := Submodule.factor h
  have hc : f.comp L.toSubmodule.mkQ = M.toSubmodule.mkQ := Submodule.factor_comp_mk h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := M.toSubmodule.mkQ_surjective y
    exact ⟨L.toSubmodule.mkQ x, DFunLike.congr_fun hc x⟩
  have hinj := (Module.bijective_of_surjective_of_rankAtStalk_eq hsurj (fun p hp ↦
    (L.rankAtStalk_eq ⟨p, hp.isPrime⟩).trans (M.rankAtStalk_eq ⟨p, hp.isPrime⟩).symm)).injective
  apply Module.Grassmannian.ext
  apply h.antisymm
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply hinj
  rw [map_zero]
  exact (DFunLike.congr_fun hc x).trans ((Submodule.Quotient.mk_eq_zero _).mpr hx)

private theorem localAdaptedBasis {n : ℕ} (β : Module.Basis (Fin n) k V)
    (ranks : Fin m → ℕ) (hn : Monotone ranks) (hr : ∀ i, ranks i ≤ Module.finrank k V)
    (L : AffineFlag k V ranks R) (p : PrimeSpectrum R) :
    ∃ z : R, z ∉ p.asIdeal ∧ ∃ B : Module.Basis (Fin n) (awayAlgebra R z)
        ((awayAlgebra R z) ⊗[k] V), ∀ i : Fin m,
      (Module.Grassmannian.map (awayMap R z).hom (L.val i)).toSubmodule =
        Submodule.span (awayAlgebra R z) (B '' {j | j.val < ranks i}) := by
  let F := p.asIdeal.ResidueField
  let bR := β.baseChange R
  let : Module.Finite k V := Module.Finite.of_basis β
  let : Module.Finite R (R ⊗[k] V) := Module.Finite.of_basis bR
  let : Module.Free R (R ⊗[k] V) := Module.Free.of_basis bR
  have hdim : Module.finrank k V = n := by simp [Module.finrank_eq_card_basis β]
  let P (i : Fin m) := (L.val i).toSubmodule
  have hP : Monotone P := fun _ _ hij ↦ hij.eq_or_lt.elim (fun h ↦ h ▸ le_rfl) (fun h ↦ L.property h)
  have h (i : Fin m) := planeSplitAndRank k V (ranks i) (hr i) R (L.val i)
  have hR (i : Fin m) : Module.finrank F (F ⊗[R] P i) = ranks i := by
    let := (h i).2.1
    let := (h i).2.2.1
    exact (p.asIdeal.finrank_fiber_eq_rankAtStalk).trans ((h i).2.2.2 p)
  have hM : Module.finrank F (F ⊗[R] (R ⊗[k] V)) = n := by
    simpa using Module.finrank_eq_card_basis (bR.baseChange F)
  obtain ⟨v, B, hB, hv⟩ := exists_lifted_adapted_fibre_basis m (R ⊗[k] V) P ranks n
    hP hn (fun i ↦ (h i).1) hR hM
  let f := bR.constr R v
  have hmap : f.baseChange F = ((bR.baseChange F).equiv B (Equiv.refl _)).toLinearMap := by
    apply (bR.baseChange F).ext
    intro i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, hB]
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, Module.Basis.constr_basis]
  have hf : IsUnit (f.baseChange F) := by
    rw [hmap]
    exact (LinearMap.GeneralLinearGroup.ofLinearEquiv
      ((bR.baseChange F).equiv B (Equiv.refl _))).isUnit
  let z := LinearMap.det f
  have hz : z ∉ p.asIdeal := by
    intro hz
    have hunit := (LinearMap.isUnit_iff_isUnit_det _).mp hf
    rw [LinearMap.det_baseChange] at hunit
    exact hunit.ne_zero (Ideal.algebraMap_residueField_eq_zero.mpr hz)
  let A := awayAlgebra R z
  let a := awayMap R z
  let : Algebra R A := inferInstanceAs (Algebra R (Localization.Away z))
  let : IsScalarTower k R A := inferInstanceAs (IsScalarTower k R (Localization.Away z))
  have hfA : IsUnit (f.baseChange A) := by
    apply (LinearMap.isUnit_iff_isUnit_det _).mpr
    rw [LinearMap.det_baseChange]
    exact IsLocalization.map_units A (⟨z, Submonoid.mem_powers z⟩ : Submonoid.powers z)
  let eA := LinearMap.GeneralLinearGroup.toLinearEquiv hfA.unit
  let e := eA ≪≫ₗ cancelBaseChange k R A A V
  let B' := (bR.baseChange A).map e
  refine ⟨z, hz, B', fun i ↦ ?_⟩
  let C := prefixPlane β ((hr i).trans_eq hdim) A
  let g := (β.baseChange A).equiv B' (Equiv.refl _)
  let D := linearTransportPlane g C
  have hD : D.toSubmodule = Submodule.span A (B' '' {j | j.val < ranks i}) := by
    change C.toSubmodule.map g.toLinearMap = _
    rw [prefixPlane_submodule, prefixSubmodule]
    exact map_span_basis_subset (β.baseChange A) B' _
  have hle : D.toSubmodule ≤ (Module.Grassmannian.map a.hom (L.val i)).toSubmodule := by
    rw [hD]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    have hB' : B' j = tensorExtensionOfHom a (v j) := by
      have hc : eA.toLinearMap = f.baseChange A := hfA.unit_spec
      change (cancelBaseChange k R A A V) (eA.toLinearMap ((bR.baseChange A) j)) = _
      rw [hc, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
        Module.Basis.constr_basis, ← tensorExtension_eq_of_hom a rfl]
      rfl
    rw [hB']
    exact tensorExtension_mem_planeMap a (L.val i) (hv i j hj)
  rw [← hD]
  exact congrArg Module.Grassmannian.toSubmodule (planes_eq_of_le _ _ hle).symm

variable {idx : Type u} [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

/-- Every flag family has bases adapted to the entire flag locally in the Zariski topology. -/
theorem localFlagAdaptedBases (hn : Monotone ranks) (hr : ∀ i, ranks i ≤ Module.finrank k V) :
    HasLocalAdaptedBases ranks b C (flagInclusion b ranks C) := by
  intro S f x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : S.left.Opens)) (show x ∈ (⊤ : S.left.Opens) from trivial)
  let U' : S.left.affineOpens := ⟨U, hU⟩
  let R := affineOpenRing U'
  let a := affineOpenProbe U'
  obtain ⟨p, hp⟩ : x ∈ Set.range a.left := by
    change x ∈ Set.range hU.fromSpec
    rwa [IsAffineOpen.range_fromSpec]
  let q := a ≫ f
  let I := flagInclusion b ranks C
  let L : AffineFlag k V ranks R :=
    ⟨productPlanes ranks b C (q ≫ I), fun {i j} hij ↦
      (factorsThroughFlag_iff b ranks C I).mp ⟨𝟙 _, Category.id_comp _⟩ R q hij⟩
  let : Module.Finite k V := Module.Finite.of_basis b
  let β := Module.finBasis k V
  obtain ⟨z, hz, B, hB⟩ := localAdaptedBasis β ranks hn hr L p
  let c := (testSpec k).map (awayMap R z).op
  have hc : IsOpenImmersion c.left :=
    IsOpenImmersion.of_isLocalization (f := z)
  have ha : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hca : IsOpenImmersion (c ≫ a).left := inferInstanceAs (IsOpenImmersion (c.left ≫ a.left))
  refine ⟨awayAlgebra R z, c ≫ a, hca, ?_, B, ?_⟩
  · have hh : p ∈ Set.range c.left := by
      rw [awayMap_left_range z]
      exact hz
    obtain ⟨y, hy⟩ := hh
    exact ⟨y, (congrArg a.left hy).trans hp⟩
  · intro i
    have he : (c ≫ a) ≫ f ≫ I = c ≫ (q ≫ I) := by simp only [q, Category.assoc]
    change (productPlanes ranks b C (((c ≫ a) ≫ f) ≫ I) i).toSubmodule = _
    rw [Category.assoc (c ≫ a), he]
    exact (congrArg Module.Grassmannian.toSubmodule
      (productPlanes_naturality b ranks C (awayMap R z) (q ≫ I) i)).trans (hB i)

end AdaptedNeighborhood

section Transitivity

open StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
variable {k V idx : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
  {m : ℕ} (ranks : Fin m → ℕ)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

private theorem prefixPlane_map {R A : TestAlgebra k} (a : R ⟶ A) {n d : ℕ}
    (β : Module.Basis (Fin n) k V) (hd : d ≤ n) :
    Module.Grassmannian.map a.hom (prefixPlane β hd R) = prefixPlane β hd A := by
  unfold prefixPlane
  rw [GrassmannianCharts.graphPlane_map]
  congr 1
  ext i j
  exact map_zero a.hom

private theorem exists_matrixTransport {R : TestAlgebra k}
    (e : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V)) :
    ∃ M : Matrix.GeneralLinearGroup idx R, matrixTransport b R M = e := by
  let c := coordinates b R
  let f := c.symm.trans (e.trans c)
  let g := LinearMap.GeneralLinearGroup.ofLinearEquiv f
  let M := Matrix.GeneralLinearGroup.toLin.symm g
  refine ⟨M, ?_⟩
  unfold matrixTransport
  change c.trans ((Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.trans c.symm) = e
  rw [show Matrix.GeneralLinearGroup.toLin M = g from MulEquiv.apply_symm_apply _ _]
  have hg : g.toLinearEquiv = f := LinearEquiv.ext fun _ ↦ rfl
  rw [hg]
  apply LinearEquiv.ext
  intro v
  simp only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- On the affine neighborhoods carrying adapted bases, transport of the
rational flag of any ordered basis gives the given family. -/
theorem localFlagTransitivity (hn : Monotone ranks) (hr : ∀ i, ranks i ≤ Module.finrank k V) :
    HasLocalTransitivity ranks b C (flagInclusion b ranks C) (glObject (k := k) (idx := idx))
      (generalLinearGroupPointsIso k idx) (intrinsicFlagAction b ranks C) := by
  intro n β
  have hdim : Module.finrank k V = n := by simp [Module.finrank_eq_card_basis β]
  subst n
  let I := flagInclusion b ranks C
  obtain ⟨z, hz⟩ := flagBasisPoints b ranks C hn hr _ β
  refine ⟨z, hz, ?_⟩
  intro S p x
  obtain ⟨R, a, ha, hx, B, hB⟩ := localFlagAdaptedBases b ranks C hn hr S p x
  let e := (β.baseChange R).equiv B (Equiv.refl _)
  obtain ⟨M, hM⟩ := exists_matrixTransport b e
  let E := generalLinearGroupPointsIso k idx
  let g : Points (glObject (k := k) (idx := idx)).X R := E.inv.app R M
  have hg : matrixAt g = M :=
    congrArg (fun h : (Specs.StandardGroups.generalLinearPoints k idx).obj R ⟶
      (Specs.StandardGroups.generalLinearPoints k idx).obj R ↦ h M) (E.inv_hom_id_app R)
  let c : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let zR := mapPoints c z
  refine ⟨R, a, g, ha, hx, ?_⟩
  change prod.lift g zR ≫ flagAction b ranks C = a ≫ p
  apply flags_eq_of_planes b ranks C
  intro i
  have hzR : (productPlanes ranks b C (zR ≫ I) i).toSubmodule =
      prefixSubmodule β R (ranks i) := by
    have h : productPlanes ranks b C (z ≫ I) i = prefixPlane β (hr i) (CommAlgCat.of k k) :=
      Module.Grassmannian.ext ((hz i).trans (prefixPlane_submodule β (hr i) _).symm)
    change (productPlanes ranks b C (((testSpec k).map c.op ≫ z) ≫ I) i).toSubmodule = _
    rw [Category.assoc]
    change (productPlanes ranks b C (mapPoints c (z ≫ I)) i).toSubmodule = _
    rw [productPlanes_naturality, h, prefixPlane_map, prefixPlane_submodule]
  rw [flagAction_plane, hg, hM, hzR, hB, prefixSubmodule]
  exact map_span_basis_subset (β.baseChange R) B _

/-- The flag scheme for an arbitrary finite rank sequence, including its
linear action, basis points and Zariski-local transitivity. -/
theorem completeFlagIncidence : CompleteConstruction.{u} := by
  intro k V idx _ _ _ _ _ b m ranks hmono hr
  choose C P hP using fun i : Fin m ↦
    GrassmannianCharts.construction k V idx b (ranks i) (hr i)
  exact ⟨C, P, flagPresentation b ranks C P hP, (generalLinearGroup k idx).val,
    generalLinearGroupPointsIso k idx, intrinsicFlagAction b ranks C,
    localFlagAdaptedBases b ranks C hmono.monotone hr,
    localFlagTransitivity b ranks C hmono.monotone hr⟩

end Transitivity

end

end LinearAlgebraicGroups.FlagIncidence
