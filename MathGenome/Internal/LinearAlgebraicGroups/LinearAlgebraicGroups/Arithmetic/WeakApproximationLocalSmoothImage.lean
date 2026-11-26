import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.RingTheory.Unramified.LocalStructure
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Filter Set Topology ContinuousLinearMap
open IsDedekindDomain
open scoped Topology Polynomial NumberField WithZero

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open AdelicGroups

set_option linter.style.haveILetI false
set_option maxHeartbeats 500000

section Analytic

variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]

private theorem eventually_exists_root {A X : Type*} [CommRing A] [TopologicalSpace X]
    (e : X → A →+* F) (he : ∀ a, Continuous (fun x => e x a))
    (p : A[X]) {x₀ : X} {z₀ : F} (hp : p.eval₂ (e x₀) z₀ = 0)
    (hd : p.derivative.eval₂ (e x₀) z₀ ≠ 0)
    {V : Set F} (hV : V ∈ 𝓝 z₀) :
    ∀ᶠ x in 𝓝 x₀, ∃ z ∈ V, p.eval₂ (e x) z = 0 := by
  classical
  let I := {j // j ∈ p.support}
  let E := I → F
  let c (x : X) : E := fun j => e x (p.coeff j.val)
  let Q (v : E × F) : F := ∑ j : I, v.1 j * v.2 ^ j.val
  let a : E × F := (c x₀, z₀)
  have ev (x : X) (z : F) : Q (c x, z) = p.eval₂ (e x) z := by
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact (Finset.sum_subtype p.support (fun _ => Iff.rfl)
      (fun j => e x (p.coeff j) * z ^ j)).symm
  let D (j : I) : (E × F) →L[F] F :=
    a.1 j • ((j.val • a.2 ^ (j.val - 1)) • snd F E F) +
      a.2 ^ j.val • (proj j).comp (fst F E F)
  have hQ : HasStrictFDerivAt Q (∑ j : I, D j) a := by
    have hterm (j : I) :
        HasStrictFDerivAt (fun v : E × F => v.1 j * v.2 ^ j.val) (D j) a :=
      (((proj j).comp (fst F E F)).hasStrictFDerivAt).fun_mul
        ((hasStrictFDerivAt_snd (𝕜 := F) (p := a)).pow j.val)
    have hsum := HasStrictFDerivAt.sum (u := Finset.univ) (fun j _ => hterm j)
    have hfun : (∑ j : I, fun v : E × F => v.1 j * v.2 ^ j.val) = Q := by
      funext v
      exact Finset.sum_apply v Finset.univ _
    exact hfun ▸ hsum
  let L : (E × F) →L[F] F := ∑ j : I, D j
  let d := p.derivative.eval₂ (e x₀) z₀
  have hL : L.comp (inr F E F) = toSpanSingleton F d := by
    have hline : HasStrictFDerivAt (fun z : F => (c x₀, z)) (inr F E F) z₀ := by
      simpa [inr] using (hasStrictFDerivAt_const (𝕜 := F) (c x₀) z₀).prodMk
        (hasStrictFDerivAt_id (𝕜 := F) z₀)
    have hcomp := hQ.comp z₀ hline
    have hpoly : HasStrictFDerivAt (fun z : F => Q (c x₀, z))
        (toSpanSingleton F d) z₀ := by
      simp_rw [ev]
      simpa [d, Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using
        (((p.map (e x₀)).hasStrictDerivAt z₀).hasStrictFDerivAt)
    exact hcomp.hasFDerivAt.unique hpoly.hasFDerivAt
  let Φ (v : E × F) : E × F := (v.1, Q v)
  have hΦ : HasStrictFDerivAt Φ ((fst F E F).prod L) a :=
    hasStrictFDerivAt_fst.prodMk hQ
  have hsurj : Function.Surjective ((fst F E F).prod L) := by
    intro ⟨b, y⟩
    let t := (y - L (b, 0)) / d
    refine ⟨(b, t), Prod.ext rfl ?_⟩
    change L (b, t) = y
    have ht : L (0, t) = t * d := DFunLike.congr_fun hL t
    calc
      L (b, t) = L (b, 0) + L (0, t) := by
        rw [← map_add]
        simp
      _ = y := by rw [ht, div_mul_cancel₀ _ hd]; ring
  have hmap := hΦ.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
  have hS : (Set.univ ×ˢ V : Set (E × F)) ∈ 𝓝 a := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem hV
  have himage : Φ '' (Set.univ ×ˢ V : Set (E × F)) ∈ 𝓝 (c x₀, 0) := by
    rw [show (c x₀, 0) = Φ a by simp [Φ, a, ev, hp], ← hmap]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hS (Set.subset_preimage_image Φ _))
  have hc : Continuous (fun x => (c x, (0 : F))) :=
    (continuous_pi fun j : I => he (p.coeff j.val)).prodMk continuous_const
  filter_upwards [hc.continuousAt.preimage_mem_nhds himage] with x hx
  obtain ⟨⟨b, z⟩, hmem, hEq⟩ := hx
  have hb : b = c x := congrArg Prod.fst hEq
  have hz : Q (b, z) = 0 := congrArg Prod.snd hEq
  exact ⟨z, hmem.2, by simpa [hb, ev] using hz⟩

omit [CompleteSpace F] in
private theorem continuous_eval₂ {A X : Type*} [CommRing A] [TopologicalSpace X]
    (e : X → A →+* F) (he : ∀ a, Continuous (fun x => e x a)) (p : A[X]) :
    Continuous (fun v : X × F => p.eval₂ (e v.1) v.2) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact continuous_finsetSum _ (fun j _ =>
    ((he (p.coeff j)).comp continuous_fst).mul (continuous_snd.pow j))

end Analytic

section Lifting

variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]

/-- A point of a smooth affine morphism lifts all sufficiently nearby points of the
base, for any topology that makes all the base evaluations continuous. -/
private theorem eventually_lift_smooth
    {A B X : Type*} [CommRing A] [CommRing B] [TopologicalSpace X]
    (r : A →+* B) (hr : r.Smooth)
    (e : X → A →+* F) (he : ∀ a, Continuous (fun x => e x a))
    {x₀ : X} (b₀ : B →+* F) (hb₀ : b₀.comp r = e x₀) :
    ∀ᶠ x in 𝓝 x₀, ∃ b : B →+* F, b.comp r = e x := by
  letI : Algebra A B := r.toAlgebra
  letI : Algebra.Smooth A B := hr
  let q := RingHom.ker b₀
  letI : q.IsPrime := RingHom.ker_isPrime b₀
  haveI : Algebra.IsSmoothAt A q := Algebra.FormallySmooth.comp A B _
  obtain ⟨s, hs, n, hC, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q)
  let C := MvPolynomial (Fin n) A
  let S := Localization.Away s
  letI : Algebra C S := hC
  letI : IsScalarTower A C S := hTower
  letI : Algebra.IsStandardEtale C S := hEtale
  let P : StandardEtalePresentation C S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  have hs' : IsUnit (b₀ s) := isUnit_iff_ne_zero.mpr hs
  let bS₀ : S →+* F := IsLocalization.Away.lift s hs'
  have hbS₀ (a : B) : bS₀ (algebraMap B S a) = b₀ a :=
    IsLocalization.Away.lift_eq s hs' a
  let t (j : Fin n) : F := bS₀ (algebraMap C S (MvPolynomial.X j))
  let eC (x : X) : C →+* F := MvPolynomial.eval₂Hom (e x) t
  have heC (a : C) : Continuous (fun x => eC x a) := by
    induction a using MvPolynomial.induction_on with
    | C a =>
      simp_rw [show ∀ x, eC x (MvPolynomial.C a) = e x a from
        fun x => MvPolynomial.eval₂Hom_C (e x) t a]
      exact he a
    | add p q hp hq =>
      simp_rw [map_add]
      exact hp.add hq
    | mul_X p j hp =>
      simp_rw [map_mul, show ∀ x, eC x (MvPolynomial.X j) = t j from
        fun x => MvPolynomial.eval₂Hom_X' (e x) t j]
      exact hp.mul continuous_const
  have heC₀ : eC x₀ = bS₀.comp (algebraMap C S) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [show eC x₀ (MvPolynomial.C a) = e x₀ a from
        MvPolynomial.eval₂Hom_C (e x₀) t a]
      change e x₀ a = bS₀ (algebraMap C S (MvPolynomial.C a))
      rw [← show algebraMap A C a = MvPolynomial.C a from rfl,
        ← IsScalarTower.algebraMap_apply A C S, IsScalarTower.algebraMap_apply A B S,
        hbS₀]
      exact (DFunLike.congr_fun hb₀ a).symm
    · intro j
      exact MvPolynomial.eval₂Hom_X' (e x₀) t j
  let z₀ := bS₀ P.x
  have hCenter :
      P.f.eval₂ (eC x₀) z₀ = 0 ∧
      P.f.derivative.eval₂ (eC x₀) z₀ ≠ 0 ∧ P.g.eval₂ (eC x₀) z₀ ≠ 0 := by
    letI : Algebra C F := (eC x₀).toAlgebra
    let bA : S →ₐ[C] F :=
      { bS₀ with commutes' := fun a => (DFunLike.congr_fun heC₀ a).symm }
    have hz : P.P.HasMap z₀ := P.hasMap.map bA
    exact ⟨hz.1, hz.isUnit_derivative_f.ne_zero, hz.2.ne_zero⟩
  have hG : {v : X × F | P.g.eval₂ (eC v.1) v.2 ≠ 0} ∈ 𝓝 (x₀, z₀) :=
    ((isOpen_ne_fun (continuous_eval₂ eC heC P.g) continuous_const).mem_nhds hCenter.2.2)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hG
  have hRoots := eventually_exists_root eC heC P.f hCenter.1 hCenter.2.1 hV
  filter_upwards [hU, hRoots] with x hx hroot
  obtain ⟨z, hzV, hz0⟩ := hroot
  letI : Algebra C F := (eC x).toAlgebra
  have hz : P.P.HasMap z :=
    ⟨hz0, isUnit_iff_ne_zero.mpr (hUV (a := (x, z)) ⟨hx, hzV⟩)⟩
  let bS : S →ₐ[C] F :=
    (P.P.lift z hz).comp P.equivRing.toAlgHom
  refine ⟨bS.toRingHom.comp (algebraMap B S), RingHom.ext fun a => ?_⟩
  change bS (algebraMap B S (r a)) = e x a
  change bS (algebraMap B S (algebraMap A B a)) = e x a
  rw [← IsScalarTower.algebraMap_apply A B S, IsScalarTower.algebraMap_apply A C S,
    bS.commutes]
  change MvPolynomial.eval₂Hom (e x) t (MvPolynomial.C a) = e x a
  exact MvPolynomial.eval₂Hom_C _ _ _

end Lifting

section Affine

set_option backward.isDefEq.respectTransparency false

open private glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixPresentation continuous_glEvaluation coordinateMap_of_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [Algebra K F]

omit [CompleteSpace F] in
private theorem continuous_coordinateEval (i : MatrixRealization G)
    (A : TestAlgebra K) (E : (testSpec K).obj (op A) ≅ G.val.X) (c : A) :
    Continuous (fun g : PointsIn i F => (coordinateMap (g ≫ E.inv)).hom c) := by
  obtain ⟨m, hm, heval⟩ := matrixPresentation A E i
  obtain ⟨d, hd⟩ := hm c
  have h (g : PointsIn i F) :
      glEvaluation (asMatrix i F g) d = (coordinateMap (g ≫ E.inv)).hom c := by
    rw [← hd]
    exact DFunLike.congr_fun (heval F g) d
  simp_rw [← h]
  exact (continuous_glEvaluation d).comp continuous_induced_dom

private theorem coordinateMap_comp {A B C : TestAlgebra K}
    (f : (testSpec K).obj (op A) ⟶ (testSpec K).obj (op B))
    (g : (testSpec K).obj (op B) ⟶ (testSpec K).obj (op C)) :
    coordinateMap (f ≫ g) = coordinateMap g ≫ coordinateMap f := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
  rw [coordinateMap_spec, op_comp, Functor.map_comp, coordinateMap_spec, coordinateMap_spec]

private theorem smooth_coordinateMap {A B : TestAlgebra K}
    (f : (testSpec K).obj (op B) ⟶ (testSpec K).obj (op A)) (hf : Smooth f.left) :
    (coordinateMap f).hom.toRingHom.Smooth := by
  rw [← coordinateMap_spec f, algSpec_map_left] at hf
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hf

omit [CompleteSpace F] in
private theorem affinePointLift (i : MatrixRealization G)
    (A B : TestAlgebra K) (E : (testSpec K).obj (op A) ≅ G.val.X)
    (f : (testSpec K).obj (op B) ⟶ G.val.X) (x : PointsIn i F)
    (b : B →+* F)
    (hb : b.comp (coordinateMap (f ≫ E.inv)).hom.toRingHom =
      (coordinateMap (x ≫ E.inv)).hom.toRingHom) :
    ∃ z : Points ((testSpec K).obj (op B)) (CommAlgCat.of K F), z ≫ f = x := by
  let r := (coordinateMap (f ≫ E.inv)).hom
  have hbA (k : K) : b (algebraMap K B k) = algebraMap K F k := by
    rw [← r.commutes k]
    exact (DFunLike.congr_fun hb (algebraMap K A k)).trans
      ((coordinateMap (x ≫ E.inv)).hom.commutes k)
  let bA : B →ₐ[K] F := { b with commutes' := hbA }
  let z : Points ((testSpec K).obj (op B)) (CommAlgCat.of K F) :=
    (testSpec K).map (CommAlgCat.ofHom bA).op
  refine ⟨z, (cancel_mono E.inv).mp ?_⟩
  have hcoord : coordinateMap ((z ≫ f) ≫ E.inv) = coordinateMap (x ≫ E.inv) := by
    rw [Category.assoc, coordinateMap_comp,
      show coordinateMap z = CommAlgCat.ofHom bA from coordinateMap_of_map _]
    apply CommAlgCat.hom_ext
    ext c
    change b (r c) = (coordinateMap (x ≫ E.inv)).hom c
    exact DFunLike.congr_fun hb c
  have hMap := congrArg (fun q : A ⟶ CommAlgCat.of K F => (testSpec K).map q.op) hcoord
  rw [coordinateMap_spec, coordinateMap_spec] at hMap
  exact hMap

/-- Smoothness of the parameter map gives a neighborhood of the image of any
point over a complete nontrivially normed extension. -/
private theorem affineImageNeighborhood (i : MatrixRealization G) (B : TestAlgebra K)
    (f : (testSpec K).obj (op B) ⟶ G.val.X) (hf : Smooth f.left)
    (a : Points ((testSpec K).obj (op B)) (CommAlgCat.of K F)) :
    Set.range (fun b : Points ((testSpec K).obj (op B)) (CommAlgCat.of K F) =>
      (b ≫ f : PointsIn i F)) ∈ 𝓝 (show PointsIn i F from a ≫ f) := by
  obtain ⟨Aop, ⟨E⟩⟩ := essImage_algSpec.mpr G.prop.1
  let A := Aop.unop
  let r : A ⟶ B := coordinateMap (f ≫ E.inv)
  have hr : r.hom.toRingHom.Smooth := by
    letI : Smooth f.left := hf
    letI : IsIso E.inv.left := inferInstanceAs (IsIso ((Over.forget _).map E.inv))
    exact smooth_coordinateMap (f ≫ E.inv)
      (inferInstanceAs (Smooth (f.left ≫ E.inv.left)))
  let e (x : PointsIn i F) : A →+* F :=
    (coordinateMap (x ≫ E.inv)).hom.toRingHom
  have he (c : A) : Continuous (fun x => e x c) :=
    continuous_coordinateEval i A E c
  have ha : (coordinateMap a).hom.toRingHom.comp r.hom.toRingHom = e (a ≫ f) := by
    change _ = (coordinateMap ((a ≫ f) ≫ E.inv)).hom.toRingHom
    rw [Category.assoc, coordinateMap_comp]
    rfl
  have hlifts := eventually_lift_smooth r.hom.toRingHom hr e he
    (coordinateMap a).hom.toRingHom ha
  filter_upwards [hlifts] with x hx
  obtain ⟨b, hb⟩ := hx
  exact affinePointLift i A B E f x b hb

end Affine

section NumberCompletions

set_option backward.isDefEq.respectTransparency false

private def completionParameter {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (w : D.Place) {U : SchemeOver K} (a : Points U (CommAlgCat.of K K)) :
    Points U (CommAlgCat.of K (D.Completion w)) :=
  mapPoints (CommAlgCat.ofHom (Algebra.ofId K (D.Completion w))) a

private theorem completionParameter_comp {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (w : D.Place) {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    {U : SchemeOver K} (a : Points U (CommAlgCat.of K K)) (f : U ⟶ G.val.X) :
    (completionParameter D w a ≫ f : LocalPoints D i w) = localPoint D i w (a ≫ f) := by
  change (_ ≫ a) ≫ f = _ ≫ (a ≫ f)
  exact Category.assoc _ _ _

variable {K : Type u} [Field K] [NumberField K]

private abbrev finiteNormedField (w : NumberFinitePlace K) :
    NontriviallyNormedField (w.adicCompletion K) :=
  Valued.toNontriviallyNormedField (w.adicCompletion K) ℤᵐ⁰

private abbrev infiniteNormedField (w : NumberField.InfinitePlace K) :
    NontriviallyNormedField w.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    have hn : ‖(2 : w.Completion)‖ = 2 := by
      have he := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq
        (2 : w.Completion) 0
      simpa only [map_zero, map_ofNat, dist_zero_right, Complex.norm_ofNat] using he.symm
    refine ⟨2, ?_, by rw [hn]; norm_num⟩
    exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)

/-- At every number-field place, the image of a smooth principal-open parameter
map contains a neighborhood of the image of the given rational parameter. -/
theorem localSmoothImage :
    LinearAlgebraicGroups.Specs.WeakApproximationLocalSmoothImage.LocalSmoothImage.{u, v} := by
  intro K _ _ G _ i n p f hf a w
  let D : GlobalFieldData.{u, v} K := numberData K
  rw [← completionParameter_comp D w i a f]
  cases w with
  | inl w =>
    letI : NontriviallyNormedField (w.adicCompletion K) := finiteNormedField w
    letI : Algebra K (w.adicCompletion K) := completionAlgebra D (.inl w)
    exact affineImageNeighborhood i (CommAlgCat.of K (Localization.Away p)) f hf (completionParameter D (.inl w) a)
  | inr w =>
    letI : NontriviallyNormedField w.Completion := infiniteNormedField w
    letI : Algebra K w.Completion := completionAlgebra D (.inr w)
    exact affineImageNeighborhood i (CommAlgCat.of K (Localization.Away p)) f hf (completionParameter D (.inr w) a)

end NumberCompletions

end LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage
