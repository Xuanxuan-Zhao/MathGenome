import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.SmoothSingularComplex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical Topology
namespace SmoothManifolds.SimplexPullbackIntegral
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  SmoothSingularData CornerData IntegrationCochainData Set MeasureTheory Filter
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S}

/-- The standard simplex is compact in every dimension, including zero. -/
theorem simplex_isCompact (q : ℕ) : IsCompact (simplexSet q) := by
  have hc : IsClosed (simplexSet q) := by
    have hcoord (i : Fin q) : IsClosed {x : Euclidean q | 0 ≤ x i} :=
      isClosed_le continuous_const (continuous_apply i)
    have hsum : IsClosed {x : Euclidean q | ∑ i, x i ≤ 1} :=
      isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
    have heq : simplexSet q = (⋂ i : Fin q, {x : Euclidean q | 0 ≤ x i}) ∩
        {x : Euclidean q | ∑ i, x i ≤ 1} := by
      ext x
      simp [simplexSet]
    rw [heq]
    exact (isClosed_iInter hcoord).inter hsum
  apply (isCompact_Icc : IsCompact (Icc (0 : Euclidean q) 1)).of_isClosed_subset hc
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  exact le_trans (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)) hx.2

/-- The simplex is convex, including its zero-dimensional case. -/
theorem simplex_convex (q : ℕ) : Convex ℝ (simplexSet q) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

/-- A strictly positive barycentric point is interior in every ambient dimension. -/
theorem simplex_interior_nonempty (q : ℕ) : (interior (simplexSet q)).Nonempty := by
  let O : Set (Euclidean q) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hopen : IsOpen O := by
    have heq : O = (⋂ i : Fin q, {x : Euclidean q | 0 < x i}) ∩
        {x : Euclidean q | ∑ i, x i < 1} := by ext; simp [O]
    rw [heq]
    exact (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))).inter
      (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  have hsub : O ⊆ simplexSet q := by
    intro x hx
    exact ⟨fun i => (hx.1 i).le, hx.2.le⟩
  let z : Euclidean q := fun _ => 1 / ((q : ℝ) + 1)
  have hp : 0 < (q : ℝ) + 1 := by positivity
  have hz : z ∈ O := by
    constructor
    · intro i
      exact one_div_pos.mpr hp
    · change ∑ _ : Fin q, 1 / ((q : ℝ) + 1) < 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_one_div, div_lt_one hp]
      linarith
  exact ⟨z, (interior_mono hsub) (hopen.interior_eq.symm ▸ hz)⟩

/-- No dimension or stratum is excluded from uniqueness of within derivatives. -/
theorem simplex_uniqueDiff (q : ℕ) : UniqueDiffOn ℝ (simplexSet q) :=
  uniqueDiffOn_convex (simplex_convex q) (simplex_interior_nonempty q)

/-- Transfer agreement of germs on the subtype to ambient within germs. -/
theorem eventuallyEq_within {q : ℕ} {F : Type*}
    {f g : Euclidean q → F} {x : SmoothSingularData.Simplex q}
    (h : (fun y : SmoothSingularData.Simplex q => f y.val) =ᶠ[𝓝 x]
      (fun y => g y.val)) : f =ᶠ[𝓝[simplexSet q] x.val] g := by
  rw [← map_nhds_subtype_val x]
  exact h

/-- The Jacobian is independent of which differentiable ambient germ is used. -/
theorem extension_independent :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.extension_independentType := by
  intro n q x F G hF hG h
  have he := (eventuallyEq_within h).fderivWithin_eq_of_mem (𝕜 := ℝ) x.property
  rw [hF.fderivWithin (simplex_uniqueDiff q x.val x.property),
    hG.fderivWithin (simplex_uniqueDiff q x.val x.property)] at he
  exact he

/-- The totalized expression is differentiated only along the actual simplex. -/
theorem chartExpression_jacobian {q : ℕ} (σ : SingularSimplex S q)
    (c : ModelChart n a M) (x : SmoothSingularData.Simplex q)
    (F : Euclidean q → Euclidean n) (hF : DifferentiableAt ℝ F x.val)
    (he : (fun y : SmoothSingularData.Simplex q => F y.val) =ᶠ[𝓝 x]
      (fun y => (c (σ.val y)).val)) :
    fderivWithin ℝ (chartExpression S σ c) (simplexSet q) x.val = fderiv ℝ F x.val := by
  have hg : (fun y : SmoothSingularData.Simplex q => chartExpression S σ c y.val) =ᶠ[𝓝 x]
      (fun y => F y.val) := by
    filter_upwards [he] with y hy
    simpa [chartExpression, y.property] using hy.symm
  rw [(eventuallyEq_within hg).fderivWithin_eq_of_mem (𝕜 := ℝ) x.property]
  exact hF.fderivWithin (simplex_uniqueDiff q x.val x.property)

/-- Simplex smoothness supplies a genuine local smooth extension with this Jacobian. -/
theorem chart_jacobian :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.chart_jacobianType := by
  intro n q a M _ S σ c hc x hx
  obtain ⟨U, hU, hxU, F, hF, he⟩ := σ.property.2 x c hc hx
  refine ⟨U, hU, hxU, F, hF, he, ?_⟩
  exact chartExpression_jacobian σ c x F
    ((hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)) he

/-- The local chain rule uses genuine extensions, which may leave the target model. -/
theorem chart_composition_jacobian {m q : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N)
    (σ : SingularSimplex S q) (τ : SingularSimplex T q)
    (f : M → N) (hf : MapData.IsSmoothMap S T f) (hτ : τ.val = f ∘ σ.val)
    (x : SmoothSingularData.Simplex q)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hx : σ.val x ∈ e.source)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val) (hfx : f (σ.val x) ∈ d.source) :
    ∃ H : Euclidean n → Euclidean m,
      (∀ (E : TangentSpace S (σ.val x) ≃ₗ[ℝ] Euclidean n)
          (D : TangentSpace T (f (σ.val x)) ≃ₗ[ℝ] Euclidean m)
          (L : TangentSpace S (σ.val x) →ₗ[ℝ] TangentSpace T (f (σ.val x))),
        DifferentialData.IsChartCoordinates S (σ.val x) e E →
        DifferentialData.IsChartCoordinates T (f (σ.val x)) d D →
        DifferentialData.IsDifferential S T f (σ.val x) L →
        ∀ v, D (L v) = fderiv ℝ H (e (σ.val x)).val (E v)) ∧
      fderivWithin ℝ (chartExpression T τ d) (simplexSet q) x.val =
        (fderiv ℝ H (e (σ.val x)).val).comp
          (fderivWithin ℝ (chartExpression S σ e) (simplexSet q) x.val) := by
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := (hf (σ.val x)).2 e he d hd hx hfx
  obtain ⟨V, hV, hxV, F, hF, heF, hDF⟩ := chart_jacobian S σ e he x hx
  have hFx : F x.val = (e (σ.val x)).val := heF.eq_of_nhds
  have hFd : DifferentiableAt ℝ F x.val :=
    (hF.contDiffAt (hV.mem_nhds hxV)).differentiableAt (by simp)
  have hHd : DifferentiableAt ℝ H (F x.val) := by
    rw [hFx]
    exact (hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have heHF : (fun y : SmoothSingularData.Simplex q => (H ∘ F) y.val) =ᶠ[𝓝 x]
      (fun y => (d (τ.val y)).val) := by
    have heHσ := heH.comp_tendsto (σ.property.1.continuousAt : Tendsto σ.val (𝓝 x) _)
    filter_upwards [heF, heHσ] with y hy hz
    simpa only [Function.comp_apply, hy, hτ] using hz
  refine ⟨H, ?_, ?_⟩
  · intro E D L hE hD hL v
    exact differential_jacobian S T f hf (σ.val x) L hL e d he hd hx hfx
      E D hE hD U H hU hpU hH heH v
  · rw [chartExpression_jacobian τ d x (H ∘ F) (hHd.comp x.val hFd) heHF,
      fderiv_comp x.val hHd hFd, hFx, hDF]

/-- Every target chart computes the same intrinsic simplex differential. -/
theorem simplexDifferential_chart {q : ℕ} (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hx : σ.val x ∈ c.source) (v : Euclidean q) :
    C.tangent.fiberCoordinates.equiv c hc (σ.val x) hx
      (simplexDifferential S C σ x v) =
        fderivWithin ℝ (chartExpression S σ c) (simplexSet q) x.val v := by
  let e := targetChart S (σ.val x)
  have he := targetChart_mem S (σ.val x)
  have hxe := mem_targetChart_source S (σ.val x)
  have hid : MapData.IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
  obtain ⟨H, hH, hcomp⟩ := chart_composition_jacobian S σ σ id hid rfl x e he hxe c hc hx
  have h := hH (C.tangent.fiberCoordinates.equiv e he (σ.val x) hxe)
    (C.tangent.fiberCoordinates.equiv c hc (σ.val x) hx) LinearMap.id
    (C.tangent.fiberCoordinates.isCoordinates e he (σ.val x) hxe)
    (C.tangent.fiberCoordinates.isCoordinates c hc (σ.val x) hx)
    (differential_id S (σ.val x)) (simplexDifferential S C σ x v)
  dsimp only [e] at hcomp h
  simpa only [LinearMap.id_apply, simplexDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, LinearEquiv.apply_symm_apply,
    hcomp, ContinuousLinearMap.comp_apply] using h

/-- Auxiliary bundle choices do not affect the intrinsic map dσ. -/
theorem simplexDifferential_independent {q : ℕ} (A : CotangentBundle S)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) :
    simplexDifferential S C σ x = simplexDifferential S A σ x := by
  let c := targetChart S (σ.val x)
  have hc := targetChart_mem S (σ.val x)
  have hx := mem_targetChart_source S (σ.val x)
  have heq := TangentBundle.chartCoordinates_unique
    (C.tangent.fiberCoordinates.isCoordinates c hc (σ.val x) hx)
    (A.tangent.fiberCoordinates.isCoordinates c hc (σ.val x) hx)
  dsimp only [c] at heq
  dsimp only [simplexDifferential]
  rw [heq]

/-- The simplex differential obeys the intrinsic chain rule for smooth postcomposition. -/
theorem simplexDifferential_postcompose {m q : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N) (A : CotangentBundle T)
    (σ : SingularSimplex S q) (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (hσ : SimplexSmooth T (f ∘ σ.val)) (x : SmoothSingularData.Simplex q)
    (v : Euclidean q) :
    simplexDifferential T A ⟨f ∘ σ.val,hσ⟩ x v = L (σ.val x) (simplexDifferential S C σ x v) := by
  let e := targetChart S (σ.val x)
  let d := targetChart T (f (σ.val x))
  have he := targetChart_mem S (σ.val x)
  have hd := targetChart_mem T (f (σ.val x))
  have hx := mem_targetChart_source S (σ.val x)
  have hfx := mem_targetChart_source T (f (σ.val x))
  obtain ⟨H, hH, hcomp⟩ := chart_composition_jacobian T σ ⟨f ∘ σ.val,hσ⟩ f hf rfl
    x e he hx d hd hfx
  apply (A.tangent.fiberCoordinates.equiv d hd (f (σ.val x)) hfx).injective
  have h := hH (C.tangent.fiberCoordinates.equiv e he (σ.val x) hx)
    (A.tangent.fiberCoordinates.equiv d hd (f (σ.val x)) hfx) (L (σ.val x))
    (C.tangent.fiberCoordinates.isCoordinates e he (σ.val x) hx)
    (A.tangent.fiberCoordinates.isCoordinates d hd (f (σ.val x)) hfx) (hL (σ.val x))
    (simplexDifferential S C σ x v)
  rw [simplexDifferential_chart (C := C) σ x e he hx v] at h
  calc
    _ = fderivWithin ℝ (chartExpression T ⟨f ∘ σ.val,hσ⟩ d) (simplexSet q) x.val v :=
      simplexDifferential_chart (C := A) ⟨f ∘ σ.val,hσ⟩ x d hd hfx v
    _ = _ := (congrArg (fun J : Euclidean q →L[ℝ] Euclidean m => J v) hcomp).trans h.symm

@[simp] theorem coordinatePullback_apply {q r : ℕ} (ω : Field S r)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) (v : Fin r → Euclidean q) :
    coordinatePullback (C := C) ω σ x.val v =
      evaluate (TangentSpace S (σ.val x)) r (ω (σ.val x))
        (fun i => simplexDifferential S C σ x (v i)) := by
  have hcont : Continuous (simplexPullback (C := C) ω σ x) :=
    ExteriorDerivativeResults.Euclidean.continuous_multilinear_euclidean
      (simplexPullback (C := C) ω σ x).toMultilinearMap
  simp only [coordinatePullback, x.property, dite_true, hcont]
  rfl

/-- In any target chart the covector is evaluated against its genuine within Jacobian. -/
theorem coordinatePullback_chart {q r : ℕ} (ω : Field S r)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hx : σ.val x ∈ c.source)
    (v : Fin r → Euclidean q) :
    coordinatePullback (C := C) ω σ x.val v =
      evaluate (TangentSpace S (σ.val x)) r (ω (σ.val x))
        (fun i => (C.tangent.fiberCoordinates.equiv c hc (σ.val x) hx).symm
          (fderivWithin ℝ (chartExpression S σ c) (simplexSet q) x.val (v i))) := by
  rw [coordinatePullback_apply]
  congr 1
  funext i
  apply (C.tangent.fiberCoordinates.equiv c hc (σ.val x) hx).injective
  rw [LinearEquiv.apply_symm_apply, simplexDifferential_chart]

/-- The determinant normalization is unchanged by the coordinate realization. -/
theorem coordinatePullback_decomposable {q r : ℕ}
    (β : (p : M) → Fin r → Module.Dual ℝ (TangentSpace S p))
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) (v : Fin r → Euclidean q) :
    coordinatePullback (C := C) (fun p => exteriorPower.ιMulti ℝ r (β p)) σ x.val v =
      (Matrix.of (fun i j => β (σ.val x) i (simplexDifferential S C σ x (v j)))).det := by
  rw [coordinatePullback_apply, ExteriorAlgebraResults.determinant_normalization]

/-- The top coefficient used by the literal integral is this covector on the ordered frame. -/
theorem coordinatePullback_top {q : ℕ} (ω : Field S q) (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) :
    coordinatePullback (C := C) ω σ x.val (LocalStokesData.frame q) = pullbackCoefficient S C ω σ x := by
  rw [coordinatePullback_apply]
  rfl

/-- Pullback of intrinsic forms and smooth postcomposition give identical coordinate covectors. -/
theorem coordinatePullback_postcompose {m q r : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N) (A : CotangentBundle T)
    (σ : SingularSimplex S q) (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (hσ : SimplexSmooth T (f ∘ σ.val)) (ω : Field T r) :
    coordinatePullback (C := C) (FormPullbackData.pullbackField S T f L ω) σ =
      coordinatePullback (C := A) ω ⟨f ∘ σ.val,hσ⟩ := by
  funext y
  by_cases hy : y ∈ simplexSet q
  · ext v
    rw [show y = (⟨y,hy⟩ : SmoothSingularData.Simplex q).val from rfl,
      coordinatePullback_apply, coordinatePullback_apply]
    have hpb := @FormPullbackResults.evaluate_fiberPullback.{u}
      (TangentSpace S (σ.val ⟨y,hy⟩)) (TangentSpace T (f (σ.val ⟨y,hy⟩)))
      _ _ _ _ r (L (σ.val ⟨y,hy⟩)) (ω (f (σ.val ⟨y,hy⟩)))
      (fun i => simplexDifferential S C σ ⟨y,hy⟩ (v i))
    calc
      _ = evaluate (TangentSpace T (f (σ.val ⟨y,hy⟩))) r (ω (f (σ.val ⟨y,hy⟩)))
          (fun i => L (σ.val ⟨y,hy⟩) (simplexDifferential S C σ ⟨y,hy⟩ (v i))) := by
            dsimp only [FormPullbackData.pullbackField]
            exact hpb
      _ = _ := by
        congr 1
        funext i
        exact (simplexDifferential_postcompose (C := C) T A σ f hf L hL hσ ⟨y,hy⟩ (v i)).symm
  · simp only [coordinatePullback, hy, dite_false]

/-- Naturality holds for the literal Lebesgue integral, without an integrability premise. -/
theorem simplexIntegral_postcompose {m q : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N) (A : CotangentBundle T)
    (σ : SingularSimplex S q) (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (hσ : SimplexSmooth T (f ∘ σ.val)) (ω : Field T q) :
    simplexIntegral S C (FormPullbackData.pullbackField S T f L ω) σ =
      simplexIntegral T A ω ⟨f ∘ σ.val,hσ⟩ := by
  have h := coordinatePullback_postcompose (C := C) T A σ f hf L hL hσ ω
  unfold simplexIntegral
  congr 1
  funext y
  by_cases hy : y ∈ simplexSet q
  · simp only [ambientPullbackCoefficient, hy, dite_true]
    exact (coordinatePullback_top (C := C) _ σ ⟨y,hy⟩).symm.trans
      ((congrArg (fun Ω : LocalStokesData.CoordinateForm q q => Ω y (LocalStokesData.frame q)) h).trans
        (coordinatePullback_top (C := A) ω ⟨f ∘ σ.val,hσ⟩ ⟨y,hy⟩))
  · simp only [ambientPullbackCoefficient, hy, dite_false]

/-- Fixed evaluations on the coordinate vectors detect every alternating covector. -/
def alternatingCoordinates (q r : ℕ) : ((Euclidean q) [⋀^Fin r]→L[ℝ] ℝ) →ₗ[ℝ]
    ((Fin r → Fin q) → ℝ) where
  toFun A j := A (fun i => Pi.single (j i) 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem alternatingCoordinates_injective (q r : ℕ) : Function.Injective (alternatingCoordinates q r) := by
  intro A B h
  have he : A.toAlternatingMap = B.toAlternatingMap :=
    (Pi.basisFun ℝ (Fin q)).ext_alternating (fun j _ => by
      simpa [alternatingCoordinates] using congrFun h j)
  ext v
  exact congrArg (fun f : AlternatingMap ℝ (Euclidean q) ℝ (Fin r) => f v) he

/-- A varying alternating map evaluated on varying vectors is smooth. -/
theorem contDiffOn_alternating_apply {p q r : ℕ} {s : Set (Euclidean p)}
    {A : Euclidean p → (Euclidean q) [⋀^Fin r]→L[ℝ] ℝ}
    {v : Euclidean p → Fin r → Euclidean q}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A s) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => A y (v y)) s := by
  have he (y : Euclidean p) : A y (v y) =
      ∑ j : Fin r → Fin q, (∏ i, v y i (j i)) * A y (fun i => Pi.single (j i) 1) := by
    calc
      _ = A y (fun i => ∑ l : Fin q, (v y i l) • Pi.single l (1 : ℝ)) := by
        congr 1
        funext i l
        simp [Pi.single_apply]
      _ = _ := by
        change (A y).toMultilinearMap _ = _
        rw [(A y).toMultilinearMap.map_sum]
        simp only [MultilinearMap.map_smul_univ, smul_eq_mul]
        rfl
  rw [show (fun y => A y (v y)) = _ from funext he]
  apply ContDiffOn.sum
  intro j hj
  apply ContDiffOn.mul
  · apply contDiffOn_prod
    intro i hi
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp hv i) (j i))
  · exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Euclidean q) ℝ
      (fun i => Pi.single (j i) 1)).comp
        (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)).contDiff.comp_contDiffOn hA

/-- Smoothness of pullback as a function of the form and of the linear map. -/
theorem contDiffOn_alternating_comp {p q m r : ℕ} {s : Set (Euclidean p)}
    {A : Euclidean p → (Euclidean m) [⋀^Fin r]→L[ℝ] ℝ}
    {L : Euclidean p → Euclidean q →L[ℝ] Euclidean m}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A s) (hL : ContDiffOn ℝ (⊤ : ℕ∞) L s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (A y).compContinuousLinearMap (L y)) s := by
  let E := alternatingCoordinates q r
  let R := E.leftInverse.toContinuousLinearMap
  have hi : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot.mpr (alternatingCoordinates_injective q r)
  have he : (fun y => (A y).compContinuousLinearMap (L y)) =
      fun y => R (fun j : Fin r → Fin q => A y (fun i => L y (Pi.single (j i) 1))) := by
    funext y
    exact (E.leftInverse_apply_of_inj hi _).symm
  rw [he]
  apply R.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro j
  apply contDiffOn_alternating_apply hA
  apply contDiffOn_pi.mpr
  intro i
  exact hL.clm_apply contDiffOn_const

/-- A fixed target chart and genuine local extensions compute the pullback germ. -/
theorem coordinatePullback_extension_germ {q r : ℕ}
    (ω : Field S r) (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hx : σ.val x ∈ c.source)
    (U : Set (Euclidean q)) (hU : IsOpen U) (hxU : x.val ∈ U)
    (F : Euclidean q → Euclidean n) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (heF : (fun y : SmoothSingularData.Simplex q => F y.val) =ᶠ[𝓝 x]
      (fun y => (c (σ.val y)).val))
    (V : Set (Euclidean n)) (hV : IsOpen V) (hpV : (c (σ.val x)).val ∈ V)
    (G : Euclidean n → Index n r → ℝ)
    (heG : ∀ p : c.source, (c p.val).val ∈ V → G (c p.val).val =
      fun I => coefficients C r c hc ω p I) :
    (fun y : SmoothSingularData.Simplex q =>
      (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n r (G (F y.val))).compContinuousLinearMap
        (fderiv ℝ F y.val)) =ᶠ[𝓝 x]
      (fun y => coordinatePullback (C := C) ω σ y.val) := by
  have hcoord : ContinuousAt (fun y : SmoothSingularData.Simplex q => (c (σ.val y)).val) x :=
    continuous_subtype_val.continuousAt.comp ((c.continuousAt hx).comp σ.property.1.continuousAt)
  have hder := (eventually_eventually_nhds.mpr heF)
  filter_upwards [hder, σ.property.1.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx),
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU),
    hcoord.preimage_mem_nhds (hV.mem_nhds hpV)] with y hy hyc hyU hyV
  change σ.val y ∈ c.source at hyc
  ext v
  have hj := chartExpression_jacobian σ c y F
    ((hF.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)) hy
  have hy' : (fun z : SmoothSingularData.Simplex q => F z.val) =ᶠ[𝓝 y]
      (fun z => (c (σ.val z)).val) := hy
  have hFy := hy'.eq_of_nhds
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hFy, heG ⟨σ.val y,hyc⟩ hyV]
  rw [coordinatePullback_chart ω σ y c hc hyc v, hj]
  change ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n r
    ((((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc (σ.val y) hyc).symm).dualBasis.exteriorPower r).equivFun
        (ω (σ.val y))) (fun i => fderiv ℝ F y.val (v i)) = _
  with_reducible exact (@ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
    (TangentSpace S (σ.val y)) _ _ n r
    (C.tangent.fiberCoordinates.equiv c hc (σ.val y) hyc) (ω (σ.val y))
    (fun i => fderiv ℝ F y.val (v i)))

/-- Every smooth form has a genuine smooth ambient pullback germ, also at corners. -/
theorem coordinatePullback_local {q r : ℕ} (B : FormBundle C r)
    (ω : Field S r) (hω : IsForm B ω) (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) :
    ∃ U : Set (Euclidean q), IsOpen U ∧ x.val ∈ U ∧
      ∃ Φ : LocalStokesData.CoordinateForm q r, ContDiffOn ℝ (⊤ : ℕ∞) Φ U ∧
        (fun y : SmoothSingularData.Simplex q => Φ y.val) =ᶠ[𝓝 x]
          (fun y => coordinatePullback (C := C) ω σ y.val) := by
  let c := targetChart S (σ.val x)
  have hc := targetChart_mem S (σ.val x)
  have hx := mem_targetChart_source S (σ.val x)
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := σ.property.2 x c hc hx
  obtain ⟨V, hV, hpV, G, hG, heG⟩ :=
    ExteriorDerivativeResults.smooth_regular C r B ω ⊤ hω c hc ⟨σ.val x,hx⟩
  let A := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n r
  let Φ : LocalStokesData.CoordinateForm q r := fun y =>
    (A (G (F y))).compContinuousLinearMap (fderiv ℝ F y)
  have hFx : F x.val = (c (σ.val x)).val := heF.eq_of_nhds
  refine ⟨U ∩ F ⁻¹' V, hF.continuousOn.isOpen_inter_preimage hU hV,
    ⟨hxU, by simpa [hFx] using hpV⟩, Φ, ?_, ?_⟩
  · apply contDiffOn_alternating_comp
    · exact A.contDiff.comp_contDiffOn (hG.comp (hF.mono inter_subset_left) (fun _ hy => hy.2))
    · exact (hF.fderiv_of_isOpen hU (by simp)).mono inter_subset_left
  · exact coordinatePullback_extension_germ ω σ x c hc hx U hU hxU F hF heF V hV hpV G heG

/-- Germ extensions give the project's stronger neighborhood extension convention. -/
theorem coordinatePullback_smooth {q r : ℕ} (B : FormBundle C r)
    (ω : Field S r) (hω : IsForm B ω) (σ : SingularSimplex S q) :
    LocallySmoothOn (simplexSet q) (fun x => coordinatePullback (C := C) ω σ x.val) := by
  intro x
  obtain ⟨U, hU, hxU, Φ, hΦ, he⟩ := coordinatePullback_local B ω hω σ x
  have he' := eventuallyEq_within he
  obtain ⟨W, hW, hxW, hEq⟩ := mem_nhdsWithin.mp he'
  refine ⟨U ∩ W, hU.inter hW, ⟨hxU,hxW⟩, Φ, hΦ.mono inter_subset_left, ?_⟩
  intro y hy
  exact hEq ⟨hy.2,y.property⟩

/-- The actual top coefficient is integrable for every smooth form on every smooth simplex. -/
theorem simplexIntegral_integrable {q : ℕ} (B : FormBundle C q)
    (ω : Field S q) (hω : IsForm B ω) (σ : SingularSimplex S q) :
    IntegrableOn (ambientPullbackCoefficient S C ω σ) (simplexSet q) := by
  have hΩ := ExteriorDerivativeResults.locallyContDiffOn_contDiffOn ⊤ (simplexSet q)
    (coordinatePullback (C := C) ω σ) (coordinatePullback_smooth B ω hω σ)
  have hc := (contDiffOn_alternating_apply hΩ (contDiffOn_const (c := LocalStokesData.frame q))).continuousOn
  have hcoef : ContinuousOn (ambientPullbackCoefficient S C ω σ) (simplexSet q) := by
    apply hc.congr
    intro y hy
    simp only [ambientPullbackCoefficient, hy, dite_true]
    exact (coordinatePullback_top ω σ ⟨y,hy⟩).symm
  exact hcoef.integrableOn_compact (simplex_isCompact q)

/-- Ambient smooth precomposition obeys the chain rule on the closed simplex. -/
theorem simplexDifferential_precompose {p q : ℕ} (σ : SingularSimplex S q)
    (g : SmoothSingularData.Simplex p → SmoothSingularData.Simplex q)
    (G : Euclidean p → Euclidean q) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hg : ∀ x, (g x).val = G x.val)
    (hσ : SimplexSmooth S (σ.val ∘ g)) (x : SmoothSingularData.Simplex p)
    (v : Euclidean p) :
    simplexDifferential S C ⟨σ.val ∘ g,hσ⟩ x v =
      simplexDifferential S C σ (g x) (fderiv ℝ G x.val v) := by
  let c := targetChart S (σ.val (g x))
  have hc := targetChart_mem S (σ.val (g x))
  have hx := mem_targetChart_source S (σ.val (g x))
  have hgc : Continuous g := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, hg] using hG.continuous.comp continuous_subtype_val
  obtain ⟨U, hU, hxU, F, hF, heF, hj⟩ := chart_jacobian S σ c hc (g x) hx
  have hFd : DifferentiableAt ℝ F (G x.val) := by
    rw [← hg]
    exact (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have heFG : (fun y : SmoothSingularData.Simplex p => (F ∘ G) y.val) =ᶠ[𝓝 x]
      (fun y => (c ((σ.val ∘ g) y)).val) := by
    simpa only [Function.comp_def, hg] using heF.comp_tendsto hgc.continuousAt
  have hj' := chartExpression_jacobian ⟨σ.val ∘ g,hσ⟩ c x (F ∘ G)
    (hFd.comp x.val (hG.differentiable (by simp) x.val)) heFG
  apply (C.tangent.fiberCoordinates.equiv c hc (σ.val (g x)) hx).injective
  calc
    _ = fderivWithin ℝ (chartExpression S ⟨σ.val ∘ g,hσ⟩ c) (simplexSet p) x.val v :=
      simplexDifferential_chart (C := C) ⟨σ.val ∘ g,hσ⟩ x c hc hx v
    _ = fderiv ℝ F (g x).val (fderiv ℝ G x.val v) := by
      rw [hj', fderiv_comp x.val hFd (hG.differentiable (by simp) x.val), ← hg]
      rfl
    _ = _ := by rw [simplexDifferential_chart (C := C) σ (g x) c hc hx, hj]

/-- The corresponding identity of the actual alternating covectors. -/
theorem coordinatePullback_precompose {p q r : ℕ} (ω : Field S r) (σ : SingularSimplex S q)
    (g : SmoothSingularData.Simplex p → SmoothSingularData.Simplex q)
    (G : Euclidean p → Euclidean q) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hg : ∀ x, (g x).val = G x.val)
    (hσ : SimplexSmooth S (σ.val ∘ g)) (x : SmoothSingularData.Simplex p) :
    coordinatePullback (C := C) ω ⟨σ.val ∘ g,hσ⟩ x.val =
      (coordinatePullback (C := C) ω σ (g x).val).compContinuousLinearMap (fderiv ℝ G x.val) := by
  ext v
  rw [coordinatePullback_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    coordinatePullback_apply]
  congr 1
  funext i
  exact simplexDifferential_precompose σ g G hG hg hσ x (v i)

@[simp] theorem pullbackCoefficient_add {q : ℕ} (α β : Field S q)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) :
    pullbackCoefficient S C (α+β) σ x =
      pullbackCoefficient S C α σ x + pullbackCoefficient S C β σ x := by
  simp [pullbackCoefficient]

@[simp] theorem pullbackCoefficient_smul {q : ℕ} (r : ℝ) (α : Field S q)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) :
    pullbackCoefficient S C (r • α) σ x = r * pullbackCoefficient S C α σ x := by
  simp [pullbackCoefficient]

@[simp] theorem ambientPullbackCoefficient_add {q : ℕ} (α β : Field S q)
    (σ : SingularSimplex S q) :
    ambientPullbackCoefficient S C (α+β) σ =
      ambientPullbackCoefficient S C α σ + ambientPullbackCoefficient S C β σ := by
  funext x
  by_cases hx : x ∈ simplexSet q <;> simp [ambientPullbackCoefficient, hx]

@[simp] theorem ambientPullbackCoefficient_smul {q : ℕ} (r : ℝ) (α : Field S q)
    (σ : SingularSimplex S q) :
    ambientPullbackCoefficient S C (r • α) σ = r • ambientPullbackCoefficient S C α σ := by
  funext x
  by_cases hx : x ∈ simplexSet q <;> simp [ambientPullbackCoefficient, hx]

/-- Additivity of the literal integral; the integrability inputs are explicit. -/
theorem simplexIntegral_add {q : ℕ} (α β : Field S q) (σ : SingularSimplex S q)
    (hα : IntegrableOn (ambientPullbackCoefficient S C α σ) (simplexSet q))
    (hβ : IntegrableOn (ambientPullbackCoefficient S C β σ) (simplexSet q)) :
    simplexIntegral S C (α+β) σ = simplexIntegral S C α σ + simplexIntegral S C β σ := by
  unfold simplexIntegral
  rw [ambientPullbackCoefficient_add]
  exact integral_add hα hβ

theorem simplexIntegral_smul {q : ℕ} (r : ℝ) (α : Field S q) (σ : SingularSimplex S q) :
    simplexIntegral S C (r • α) σ = r • simplexIntegral S C α σ := by
  unfold simplexIntegral
  rw [ambientPullbackCoefficient_smul]
  exact integral_smul r _

/-- Degree-zero exterior evaluation is the scalar coefficient, with no factorial. -/
theorem evaluate_zero (V : Type u) [AddCommGroup V] [Module ℝ V]
    (ω : Fiber V 0) (v : Fin 0 → V) :
    evaluate V 0 ω v = exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V) ω := by
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm.surjective ω
  simp [evaluate, exteriorPower.zeroEquiv_symm_apply]

/-- The integral over the ordered zero-simplex is evaluation at its unique point. -/
theorem simplexIntegral_zero (ω : Field S 0) (σ : SingularSimplex S 0)
    (x : SmoothSingularData.Simplex 0) :
    simplexIntegral S C ω σ =
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S (σ.val x))) (ω (σ.val x)) := by
  have hset : simplexSet 0 = univ := by ext y; simp [simplexSet]
  unfold simplexIntegral
  rw [hset, MeasureTheory.setIntegral_univ]
  have hf : ambientPullbackCoefficient S C ω σ = fun _ => pullbackCoefficient S C ω σ x := by
    funext y
    simp only [ambientPullbackCoefficient, hset, mem_univ, dite_true]
    congr 1
    exact Subtype.ext (Subsingleton.elim _ _)
  rw [hf, integral_const]
  have hv : (volume : Measure (Euclidean 0)) univ = 1 :=
    Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
  simpa only [Measure.real, hv, ENNReal.toReal_one, one_smul, pullbackCoefficient] using
    (evaluate_zero (TangentSpace S (σ.val x)) (ω (σ.val x))
      (fun i => simplexDifferential S C σ x (Pi.single i 1)))

/-- Exterior differentiation of the coordinate pullback is the intrinsic de Rham derivative. -/
theorem coordinatePullback_derivative {q r : ℕ} (B : ∀ k, FormBundle C k)
    (K : DeRhamData.Calculus C B) (ω : Field S r) (hω : IsForm (B r) ω)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) :
    extDerivWithin (coordinatePullback (C := C) ω σ) (simplexSet q) x.val =
      coordinatePullback (C := C) (K.D r ω) σ x.val := by
  let c := targetChart S (σ.val x)
  have hc := targetChart_mem S (σ.val x)
  have hx := mem_targetChart_source S (σ.val x)
  obtain ⟨U, hU, hxU, F, hF, heF, hj⟩ := chart_jacobian S σ c hc x hx
  obtain ⟨V, hV, hpV, G, hG, heG⟩ :=
    ExteriorDerivativeResults.smooth_regular C r (B r) ω ⊤ hω c hc ⟨σ.val x,hx⟩
  let A := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n r
  let Ψ : LocalStokesData.CoordinateForm n r := fun z => A (G z)
  let Φ : LocalStokesData.CoordinateForm q r := fun y =>
    (Ψ (F y)).compContinuousLinearMap (fderiv ℝ F y)
  have hFx : F x.val = (c (σ.val x)).val := heF.eq_of_nhds
  have hopen : IsOpen (U ∩ F ⁻¹' V) := hF.continuousOn.isOpen_inter_preimage hU hV
  have hmem : x.val ∈ U ∩ F ⁻¹' V := ⟨hxU, by simpa only [mem_preimage, hFx] using hpV⟩
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ∩ F ⁻¹' V) := by
    apply contDiffOn_alternating_comp
    · exact A.contDiff.comp_contDiffOn (hG.comp (hF.mono inter_subset_left) (fun _ hy => hy.2))
    · exact (hF.fderiv_of_isOpen hU (by simp)).mono inter_subset_left
  have heΦ : (fun y : SmoothSingularData.Simplex q => Φ y.val) =ᶠ[𝓝 x]
      (fun y => coordinatePullback (C := C) ω σ y.val) :=
    coordinatePullback_extension_germ ω σ x c hc hx U hU hxU F hF heF V hV hpV G heG
  have heD : extDerivWithin (coordinatePullback (C := C) ω σ) (simplexSet q) x.val =
      extDeriv Φ x.val := by
    rw [(eventuallyEq_within heΦ.symm).extDerivWithin_eq_of_mem x.property]
    unfold extDerivWithin extDeriv
    rw [((hΦ.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)).fderivWithin
      (simplex_uniqueDiff q x.val x.property)]
  have hΨd : DifferentiableAt ℝ Ψ (F x.val) := by
    rw [hFx]
    exact (A.contDiff.comp_contDiffOn hG).contDiffAt (hV.mem_nhds hpV) |>.differentiableAt (by simp)
  have hnat := extDeriv_pullback hΨd (hF.contDiffAt (hU.mem_nhds hxU)) (by simp)
  ext v
  calc
    _ = extDeriv Φ x.val v := congrArg (fun Λ : (Euclidean q) [⋀^Fin (r+1)]→L[ℝ] ℝ => Λ v) heD
    _ = extDeriv Ψ (c (σ.val x)).val (fun i => fderiv ℝ F x.val (v i)) := by
      have hh := congrArg (fun Λ : (Euclidean q) [⋀^Fin (r+1)]→L[ℝ] ℝ => Λ v) hnat
      simpa only [Φ, hFx, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using hh
    _ = evaluate (TangentSpace S (σ.val x)) (r+1) (K.D r ω (σ.val x))
        (fun i => (C.tangent.fiberCoordinates.equiv c hc (σ.val x) hx).symm
          (fderiv ℝ F x.val (v i))) := by
      rw [K.coordinates r ω hω c hc (σ.val x) hx]
      exact (ExteriorDerivativeResults.coordinateDerivative_evaluate_extension C r c hc ω (σ.val x) hx
        V hV hpV G (hG.of_le (by simp)) heG (fun i => fderiv ℝ F x.val (v i))).symm
    _ = _ := by
      have hh := coordinatePullback_chart (C := C) (K.D r ω) σ x c hc hx v
      rw [hj] at hh
      exact hh.symm

/-- Postcomposition constructs a smooth simplex and preserves the actual covector field. -/
theorem postcomposition :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.postcompositionType := by
  intro n a M _ S C m q r b N _ T A σ f hf L hL
  refine ⟨⟨f ∘ σ.val, SmoothSingular.smooth_postcompose hf σ.property⟩, rfl, ?_⟩
  intro ω
  exact coordinatePullback_postcompose T A σ f hf L hL
    (SmoothSingular.smooth_postcompose hf σ.property) ω

/-- Every ordered face has the affine pullback law, including endpoint faces. -/
theorem ordered_faces :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.ordered_facesType := by
  intro n a M _ S C q r σ j
  refine ⟨⟨σ.val ∘ face j, SmoothSingular.smooth_face σ.property j⟩, rfl, ?_⟩
  intro ω x
  exact coordinatePullback_precompose ω σ (face j) (faceAmbient j)
    (SmoothSingular.faceAmbient_smooth j) (SmoothSingular.face_val j)
    (SmoothSingular.smooth_face σ.property j) x

/-- Integrability holds for every bundled smooth form without further premises. -/
theorem integrability :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.integrabilityType := by
  intro n q a M _ S C B ω σ
  exact simplexIntegral_integrable B ω.field ω.smooth σ

/-- The literal integral is real linear on all smooth forms. -/
theorem integral_linearity :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.integral_linearityType := by
  intro n a M _ S C q B α β σ
  exact ⟨simplexIntegral_add α.field β.field σ
    (simplexIntegral_integrable B α.field α.smooth σ)
    (simplexIntegral_integrable B β.field β.smooth σ),
    fun t => simplexIntegral_smul t α.field σ⟩

/-- Naturality constructs the smooth postcomposition rather than assuming it. -/
theorem integral_naturality :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.integral_naturalityType := by
  intro n a M _ S C m q b N _ T A σ f hf L hL
  refine ⟨⟨f ∘ σ.val, SmoothSingular.smooth_postcompose hf σ.property⟩, rfl, ?_⟩
  intro ω
  exact simplexIntegral_postcompose T A σ f hf L hL
    (SmoothSingular.smooth_postcompose hf σ.property) ω

end SmoothManifolds.SimplexPullbackIntegral

/-! Candidate-owned exports of the shared canonical constructions. The definitions
remain in the independent interface so that downstream Specs can use them; these
exports are definitionally equal to those same objects, with no second choice of
charts, differential, pullback, or integral. -/
namespace SmoothManifolds.SimplexPullbackIntegral.Construction

def targetChart : Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.targetChartType :=
  @SmoothManifolds.IntegrationCochainData.targetChart

def chartExpression : Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.chartExpressionType :=
  @SmoothManifolds.IntegrationCochainData.chartExpression

def simplexDifferential :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.simplexDifferentialType :=
  @SmoothManifolds.IntegrationCochainData.simplexDifferential

def pullbackCoefficient :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.pullbackCoefficientType :=
  @SmoothManifolds.IntegrationCochainData.pullbackCoefficient

def ambientPullbackCoefficient :
    Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.ambientPullbackCoefficientType :=
  @SmoothManifolds.IntegrationCochainData.ambientPullbackCoefficient

def simplexIntegral : Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.simplexIntegralType :=
  @SmoothManifolds.IntegrationCochainData.simplexIntegral

def simplexPullback : Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.simplexPullbackType :=
  @SmoothManifolds.SimplexPullbackIntegral.simplexPullback

def coordinatePullback : Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral.coordinatePullbackType :=
  @SmoothManifolds.SimplexPullbackIntegral.coordinatePullback

end SmoothManifolds.SimplexPullbackIntegral.Construction
