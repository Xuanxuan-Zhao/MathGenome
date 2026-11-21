import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricApproximation
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.SymmetricSobolevEnergy
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathGenome.Internal.FourierSobolev.P102.U2.Young
import MathGenome.Internal.FourierSobolev.P102.U2.ApproximateIdentities
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SupportedCompactness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
set_option maxHeartbeats 300000
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace P201.Hyperbolic.SymmetricApproximation
open P201Specs
open P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricApproximation
open P201.Hyperbolic.SymmetricSobolevEnergy

/-- The reindexing used in the independent intermediate-solution statement
covers every source Sobolev order, including the lowest possible order 2. -/
theorem source_order : OrderStatement := by
  intro n s hn hs
  omega

/-- Restrict the actual weak derivative tuple to a lower Sobolev order. -/
def truncateScalar {n a b : ℕ} {𝕜 : Type} [RCLike 𝕜] (h : b ≤ a)
    (u : H 𝕜 (⊤ : Domain n) a) : H 𝕜 (⊤ : Domain n) b :=
  ⟨WithLp.toLp 2 (fun α => u.val ⟨α.val, α.property.trans h⟩), by
    apply (P102.U4.mem_sobolevSubmodule_iff ⊤ b 2 _).mpr
    intro α φ
    exact (P102.U4.mem_sobolevSubmodule_iff ⊤ a 2
      (hilbertTupleToSum 𝕜 ⊤ a u.val)).mp u.property ⟨α.val, α.property.trans h⟩ φ⟩

theorem truncateScalar_norm_le {n a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (h : b ≤ a) (u : H 𝕜 (⊤ : Domain n) a) : ‖truncateScalar h u‖ ≤ ‖u‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(truncateScalar h u).val‖ ^ 2 ≤ ‖u.val‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  let e : P102.U4.SobolevIndex n b → P102.U4.SobolevIndex n a :=
    fun α => ⟨α.val, α.property.trans h⟩
  have he : Function.Injective e := by
    intro α β he
    apply Subtype.ext
    exact congrArg (fun γ : P102.U4.SobolevIndex n a => γ.val) he
  change (∑ α, ‖u.val (e α)‖ ^ 2) ≤ ∑ γ, ‖u.val γ‖ ^ 2
  calc
    _ = ∑ γ ∈ Finset.univ.image e, ‖u.val γ‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => he h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

/-- Natural Sobolev inclusions are contractions for the precise source norm. -/
def truncate {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜] (h : b ≤ a) :
    WholeH n m 𝕜 a →L[𝕜] WholeH n m 𝕜 b :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 (fun i => truncateScalar h (u i))
      map_add' := by intros; apply PiLp.ext; intro i; apply Subtype.ext; rfl
      map_smul' := by intros; apply PiLp.ext; intro i; apply Subtype.ext; rfl }
    1 (fun u => by
      rw [one_mul]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (truncateScalar_norm_le h (u i)))

def toZero {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    WholeH n m 𝕜 q →L[𝕜] WholeH n m 𝕜 0 := truncate (Nat.zero_le q)

def toOne {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 1 := truncate (by omega)

theorem toZero_same {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 q) : SameSection v (toZero v) := by
  intro i
  rfl

theorem toOne_same {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 (q + 1)) : SameSection v (toOne v) := by
  intro i
  rfl

theorem sameSection_refl {n m a : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 a) : SameSection v v := fun _ => rfl

theorem sameSection_symm {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {v : WholeH n m 𝕜 a} {w : WholeH n m 𝕜 b}
    (h : SameSection v w) : SameSection w v := fun i => (h i).symm

theorem sameSection_trans {n m a b c : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {v : WholeH n m 𝕜 a} {w : WholeH n m 𝕜 b} {z : WholeH n m 𝕜 c}
    (h : SameSection v w) (h' : SameSection w z) : SameSection v z :=
  fun i => (h i).trans (h' i)

theorem sameSection_underlying {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {v : WholeH n m 𝕜 a} {w : WholeH n m 𝕜 b}
    (h : SameSection v w) : underlyingSection v = underlyingSection w := by
  funext x
  apply PiLp.ext
  intro i
  exact congrArg (fun z : P201Specs.Lp 𝕜 (⊤ : Domain n) 2 => z x) (h i)

theorem sameSection_injective {n m a : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {v w : WholeH n m 𝕜 a} (h : SameSection v w) : v = w := by
  apply PiLp.ext
  intro i
  exact P201.hilbertUnderlyingInjective ⊤ a (h i)

/-- Across orders, the weak derivatives of a given section are unique. -/
theorem sameSection_derivative {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {v : WholeH n m 𝕜 a} {w : WholeH n m 𝕜 b}
    (h : SameSection v w) (α : MultiIndex n) (ha : α.card ≤ a) (hb : α.card ≤ b) :
    derivativeSection v ⟨α, ha⟩ = derivativeSection w ⟨α, hb⟩ := by
  funext x
  apply PiLp.ext
  intro i
  have he : P102.U4.sobolevDerivative (hToW 𝕜 ⊤ a (v i)) ⟨α, ha⟩ =
      P102.U4.sobolevDerivative (hToW 𝕜 ⊤ b (w i)) ⟨α, hb⟩ := by
    apply P102.U4.regularLp_injective ⊤ 2
    change P102.U4.regularDistribution ⊤
      (P102.U4.sobolevDerivative (hToW 𝕜 ⊤ a (v i)) ⟨α, ha⟩) =
      P102.U4.regularDistribution ⊤
      (P102.U4.sobolevDerivative (hToW 𝕜 ⊤ b (w i)) ⟨α, hb⟩)
    calc
      _ = P102.U4.distributionPartial α
          (P102.U4.regularDistribution ⊤ (hUnderlying ⊤ a (v i))) :=
        (P201.hilbertDerivativeDistribution ⊤ a (v i) ⟨α, ha⟩).symm
      _ = P102.U4.distributionPartial α
          (P102.U4.regularDistribution ⊤ (hUnderlying ⊤ b (w i))) := by rw [h i]
      _ = _ := P201.hilbertDerivativeDistribution ⊤ b (w i) ⟨α, hb⟩
  exact congrArg (fun z : P201Specs.Lp 𝕜 (⊤ : Domain n) 2 => z x) he

/-- The PDE section is unchanged by passing from H^(q+1) to H¹. -/
theorem toOne_pSection {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → Space n → Operator m 𝕜) (B : Space n → Operator m 𝕜)
    (v : WholeH n m 𝕜 (q + 1)) :
    pSection A B (toOne v) = pSection A B v := by
  funext x
  dsimp [pSection]
  rw [← sameSection_underlying (toOne_same v)]
  congr 2

/-- Every intermediate solution has the legitimate H¹/L² energy regularity.
The PDE survives the canonical order inclusions. -/
theorem intermediate_regular {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    {f : ℝ → WholeH n m 𝕜 (q + 2)}
    {u : ℝ → WholeH n m 𝕜 (q + 1)} {w du : ℝ → WholeH n m 𝕜 q}
    (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T))
    (hu : IsIntermediateSolution T A B f u w du) :
    IsRegularSolution T A B (fun t => toZero (w t)) (fun t => toZero (du t))
      (fun t => toZero (f t)) (fun t => toOne (u t)) := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) q)
  letI : NormedSpace ℝ (WholeH n m 𝕜 0) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) 0)
  let Z : WholeH n m 𝕜 q →L[𝕜] WholeH n m 𝕜 0 := toZero
  let F : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 0 := toZero
  rcases hu with ⟨huc, hwc, hduc, hsame, hd, he⟩
  refine ⟨Z.continuous.comp_continuousOn hwc,
    Z.continuous.comp_continuousOn hduc,
    F.continuous.comp_continuousOn hf, ?_, ?_, ?_⟩
  · intro t ht
    have hD : HasDerivAt w (du t) t :=
      HasDerivWithinAt.hasDerivAt (f := w) (f' := du t)
        (hd t ⟨ht.1.le, ht.2.le⟩) (Icc_mem_nhds ht.1 ht.2)
    exact (Z.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hD
  · intro t ht
    exact sameSection_trans (sameSection_symm (toOne_same (u t)))
      (sameSection_trans (hsame t ht) (toZero_same (w t)))
  · intro t ht
    have hsub := underlyingSection_sub (toZero (du t)) (toZero (f t))
    have hdu := sameSection_underlying (toZero_same (du t))
    have hff := sameSection_underlying (toZero_same (f t))
    have hp := toOne_pSection (fun j => A j t) (B t) (u t)
    filter_upwards [hsub, he t ht] with x hx hex
    rw [hx, ← hdu, ← hff, hp]
    change underlyingSection (du t) x - underlyingSection (f t) x = _
    rw [hex]
    abel

/-- Uniqueness is obtained from the proved spatial H¹/L² energy estimate,
not from a smooth-solution uniqueness assumption. -/
theorem uniqueness : P201Specs.Hyperbolic.SymmetricApproximation.UniquenessStatement := by
  intro n q hn hs K hK m 𝕜 _ T hT A B hAB f hf u v w du z dv hu hv hinit
  obtain ⟨C, hC, hest⟩ := evolution_estimate n (q + 2) hn hs K hK
  obtain ⟨_, hdiff⟩ := hest T hT A B hAB 0 (by omega)
  have huR := intermediate_regular hT hf hu
  have hvR := intermediate_regular hT hf hv
  have h0 : w 0 = z 0 := by
    apply sameSection_injective
    intro i
    exact (hu.2.2.2.1 0 ⟨le_rfl, hT⟩ i).symm.trans
      ((congrArg (fun y : WholeH n m 𝕜 (q + 1) => hUnderlying ⊤ (q + 1) (y i)) hinit).trans
        (hv.2.2.2.1 0 ⟨le_rfl, hT⟩ i))
  intro t ht
  have hb := hdiff (fun r => toZero (w r)) (fun r => toZero (du r))
    (fun r => toZero (f r)) (fun r => toZero (z r)) (fun r => toZero (dv r))
    (fun r => toZero (f r)) (fun r => toOne (u r)) (fun r => toOne (v r))
    huR hvR t ht
  have heq : toZero (w t) = toZero (z t) := by
    have hnorm : ‖toZero (w t) - toZero (z t)‖ ≤ 0 := by simpa [h0] using hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  apply sameSection_injective
  intro i
  calc
    hUnderlying ⊤ (q + 1) (u t i) = hUnderlying ⊤ q (w t i) := hu.2.2.2.1 t ht i
    _ = hUnderlying ⊤ 0 (toZero (w t) i) := toZero_same (w t) i
    _ = hUnderlying ⊤ 0 (toZero (z t) i) := by rw [heq]
    _ = hUnderlying ⊤ q (z t i) := (toZero_same (z t) i).symm
    _ = hUnderlying ⊤ (q + 1) (v t i) := (hv.2.2.2.1 t ht i).symm

/-- The canonical order-zero inclusion preserves the underlying section. -/
theorem sameSection_toZero_eq {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {v : WholeH n m 𝕜 a} {w : WholeH n m 𝕜 b} (h : SameSection v w) :
    toZero v = toZero w := by
  apply sameSection_injective
  exact sameSection_trans (sameSection_symm (toZero_same v))
    (sameSection_trans h (toZero_same w))

theorem toZero_injective {n m a : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    Function.Injective (toZero : WholeH n m 𝕜 a →L[𝕜] WholeH n m 𝕜 0) := by
  intro v w h
  apply sameSection_injective
  exact sameSection_trans (toZero_same v)
    (sameSection_trans (by rw [h]; exact sameSection_refl _)
      (sameSection_symm (toZero_same w)))

/-! The weak-compactness step is proved for complete Hilbert spaces, then
specialized to the canonical Sobolev inclusions. No compact spatial embedding
is used; the spatial domain may be the whole Euclidean space. -/
section HilbertLimits
open Filter Topology
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Riesz representation transfers the compact weak-* dual ball to the weak
Hilbert ball. This works over both scalar fields without a separability premise. -/
theorem isCompact_weak_closedBall (R : ℝ) :
    IsCompact {x : WeakSpace 𝕜 X | ‖(toWeakSpace 𝕜 X).symm x‖ ≤ R} := by
  let D := InnerProductSpace.toDual 𝕜 X
  let F : WeakDual 𝕜 X → WeakSpace 𝕜 X :=
    fun q => toWeakSpace 𝕜 X (D.symm q.toStrongDual)
  have hF : Continuous F := by
    apply WeakBilin.continuous_of_continuous_eval
    intro L
    have he (q : WeakDual 𝕜 X) :
        L (D.symm q.toStrongDual) = star (q (D.symm L)) := by
      calc
        _ = inner 𝕜 (D.symm L) (D.symm q.toStrongDual) :=
          (InnerProductSpace.toDual_symm_apply).symm
        _ = star (inner 𝕜 (D.symm q.toStrongDual) (D.symm L)) :=
          (inner_conj_symm _ _).symm
        _ = _ := by rw [InnerProductSpace.toDual_symm_apply]; rfl
    change Continuous (fun q : WeakDual 𝕜 X => L (D.symm q.toStrongDual))
    simp_rw [he]
    exact (WeakDual.eval_continuous (D.symm L)).star
  have hc := (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 X) R).image hF
  have himage : F '' (WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual 𝕜 X) R) =
      {x : WeakSpace 𝕜 X | ‖(toWeakSpace 𝕜 X).symm x‖ ≤ R} := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      change ‖D.symm q.toStrongDual‖ ≤ R
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map] using hq
    · intro hx
      change ‖(toWeakSpace 𝕜 X).symm x‖ ≤ R at hx
      refine ⟨StrongDual.toWeakDual (D ((toWeakSpace 𝕜 X).symm x)), ?_, ?_⟩
      · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hx
      · simp only [F, StrongDual.toStrongDual_toWeakDual,
          LinearIsometryEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rwa [himage] at hc

/-- A uniform high-norm bound and a strong lower-norm limit produce a
high-regularity lift with exactly the same norm bound. -/
theorem exists_lift_of_bounded_tendsto {I : Type*} {l : Filter I} [l.NeBot]
    (J : X →L[𝕜] Y) (z : I → X) (y : Y) (R : ℝ)
    (hz : ∀ᶠ i in l, ‖z i‖ ≤ R)
    (hy : Tendsto (fun i => J (z i)) l (𝓝 y)) :
    ∃ x : X, J x = y ∧ ‖x‖ ≤ R := by
  have hmem : ∀ᶠ i in l, toWeakSpace 𝕜 X (z i) ∈
      {x : WeakSpace 𝕜 X | ‖(toWeakSpace 𝕜 X).symm x‖ ≤ R} := hz
  have hc := isCompact_weak_closedBall (𝕜 := 𝕜) (X := X) R
  obtain ⟨x, hx, hcluster⟩ := hc.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨U, hUl, hU⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  refine ⟨(toWeakSpace 𝕜 X).symm x, ?_, hx⟩
  have h1 := (WeakSpace.map J).continuous.tendsto x |>.comp hU
  have h2 := ((toWeakSpaceCLM 𝕜 Y).continuous.tendsto y).comp (hy.mono_left hUl)
  exact (toWeakSpace 𝕜 Y).injective (tendsto_nhds_unique h1 h2)

/-- If the lower-norm realization is injective, a bounded family converging
in that norm converges weakly in the high Hilbert norm along the original filter. -/
theorem weak_tendsto_of_bounded_lower_tendsto {I : Type*} {l : Filter I}
    (J : X →L[𝕜] Y) (hJ : Function.Injective J) (z : I → X) (x : X) (R : ℝ)
    (hz : ∀ᶠ i in l, ‖z i‖ ≤ R)
    (hy : Tendsto (fun i => J (z i)) l (𝓝 (J x))) :
    Tendsto (fun i => toWeakSpace 𝕜 X (z i)) l (𝓝 (toWeakSpace 𝕜 X x)) := by
  have hc := isCompact_weak_closedBall (𝕜 := 𝕜) (X := X) R
  apply hc.tendsto_nhds_of_unique_mapClusterPt hz
  intro v _ hcluster
  obtain ⟨U, hUl, hU⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have h1 := (WeakSpace.map J).continuous.tendsto v |>.comp hU
  have h2 := ((toWeakSpaceCLM 𝕜 Y).continuous.tendsto (J x)).comp (hy.mono_left hUl)
  have he := (toWeakSpace 𝕜 Y).injective (tendsto_nhds_unique h1 h2)
  exact (toWeakSpace 𝕜 X).symm.injective (hJ he)

/-- A uniformly bounded high-order lift of a continuous lower-order path is
weakly continuous. Local compactness or compact spatial embedding is unnecessary. -/
theorem weak_continuousOn_of_bounded_lower {Z : Type*} [TopologicalSpace Z]
    (J : X →L[𝕜] Y) (hJ : Function.Injective J)
    (V : Z → X) (S : Set Z) (R : ℝ) (hV : ∀ t ∈ S, ‖V t‖ ≤ R)
    (hc : ContinuousOn (fun t => J (V t)) S) :
    ∀ L : X →L[𝕜] 𝕜, ContinuousOn (fun t => L (V t)) S := by
  intro L t ht
  have hw := weak_tendsto_of_bounded_lower_tendsto J hJ V (V t) R
    (Filter.mem_of_superset self_mem_nhdsWithin (fun r hr => hV r hr)) (hc t ht)
  exact (WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip L).tendsto
    (toWeakSpace 𝕜 X (V t)) |>.comp hw

/-- Pointwise strong lower limits of a bounded high-order family have weakly
continuous high-order lifts. The bound may depend continuously on time and is
retained pointwise, rather than replaced by its maximum. -/
theorem bounded_limit_lift {Z : Type*} [TopologicalSpace Z]
    (J : X →L[𝕜] Y) (hJ : Function.Injective J) (S : Set Z) (hS : IsCompact S)
    (z : ℕ → Z → X) (u : Z → Y) (b : Z → ℝ)
    (hu : ContinuousOn u S) (hb : ContinuousOn b S)
    (hz : ∀ i t, t ∈ S → ‖z i t‖ ≤ b t)
    (hl : ∀ t ∈ S, Tendsto (fun i => J (z i t)) atTop (𝓝 (u t))) :
    ∃ V : Z → X, (∀ t ∈ S, J (V t) = u t ∧ ‖V t‖ ≤ b t) ∧
      ∀ L : X →L[𝕜] 𝕜, ContinuousOn (fun t => L (V t)) S := by
  classical
  have hex : ∀ t, ∃ v : X, t ∈ S → J v = u t ∧ ‖v‖ ≤ b t := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨v, hv, hvb⟩ := exists_lift_of_bounded_tendsto J (fun i => z i t)
        (u t) (b t) (Eventually.of_forall (fun i => hz i t ht)) (hl t ht)
      exact ⟨v, fun _ => ⟨hv, hvb⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose V hV using hex
  obtain ⟨R, hR⟩ := hS.bddAbove_image hb
  refine ⟨V, hV, weak_continuousOn_of_bounded_lower J hJ V S R ?_ ?_⟩
  · intro t ht
    exact (hV t ht).2.trans (hR (mem_image_of_mem b ht))
  · exact hu.congr (fun t ht => (hV t ht).1)

end HilbertLimits

set_option backward.isDefEq.respectTransparency false in
/-- Weak compactness recovers high-order values, the quantitative bound,
weak continuity, and the initial datum for every real or complex Sobolev limit. -/
theorem bounded_sobolev_limit : BoundedLimitStatement := by
  intro n m a b 𝕜 _ T hT g z w u R hu hR hinit hz hsame hlim
  letI : InnerProductSpace 𝕜 (WholeH n m 𝕜 a) :=
    PiLp.innerProductSpace (fun _ : Fin m => P201Specs.H 𝕜 (⊤ : Domain n) a)
  let J : WholeH n m 𝕜 a →L[𝕜] WholeH n m 𝕜 0 := toZero
  let L : WholeH n m 𝕜 b →L[𝕜] WholeH n m 𝕜 0 := toZero
  have hlow : ∀ t ∈ Icc 0 T,
      Filter.Tendsto (fun i => J (z i t)) Filter.atTop (nhds (L (u t))) := by
    intro t ht
    have he : (fun i => J (z i t)) = (fun i => L (w i t)) := by
      funext i
      exact sameSection_toZero_eq (hsame i t ht)
    rw [he]
    exact (L.continuous.tendsto (u t)).comp (hlim t ht)
  obtain ⟨V, hV, hVc⟩ := bounded_limit_lift (𝕜 := 𝕜) (X := WholeH n m 𝕜 a)
    (Y := WholeH n m 𝕜 0) J (toZero_injective (n := n) (m := m) (a := a))
    (Icc 0 T) isCompact_Icc
    z (fun t => L (u t)) R (L.continuous.comp_continuousOn hu) hR hz hlow
  have hsec (t : ℝ) (ht : t ∈ Icc 0 T) : SameSection (V t) (u t) := by
    have heq : toZero (V t) = toZero (u t) := (hV t ht).1
    have hs0 : SameSection (toZero (V t)) (toZero (u t)) := by
      rw [heq]
      exact sameSection_refl _
    exact sameSection_trans (toZero_same (V t))
      (sameSection_trans hs0 (sameSection_symm (toZero_same (u t))))
  refine ⟨V, hsec, ?_, fun t ht => (hV t ht).2, hVc⟩
  exact sameSection_injective (sameSection_trans (hsec 0 ⟨le_rfl, hT⟩)
    (sameSection_symm hinit))


open Filter Topology
open scoped ContDiff

/-- Elementary derivative interpolation; all hypotheses are actual pointwise
line derivatives and L² membership, with no assumed Fourier equivalence. -/
theorem line_derivative_interpolation {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f df ddf : Space n → E} (v : Space n)
    (hf : ∀ x, HasLineDerivAt ℝ f (df x) x v)
    (hdf : ∀ x, HasLineDerivAt ℝ df (ddf x) x v)
    (hf2 : MemLp f 2) (hdf2 : MemLp df 2) (hddf2 : MemLp ddf 2) :
    lpNorm df 2 volume ^ 2 ≤ lpNorm f 2 volume * lpNorm ddf 2 volume := by
  have hint {a b : Space n → E} (ha : MemLp a 2) (hb : MemLp b 2) :
      Integrable (fun x => inner ℝ (a x) (b x)) := by
    exact (ha.norm.integrable_mul hb.norm).mono'
      (ha.aestronglyMeasurable.inner hb.aestronglyMeasurable)
      (Eventually.of_forall fun x => norm_inner_le_norm _ _)
  have hip := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := innerSL ℝ) (hint hdf2 hdf2) (hint hf2 hddf2) (hint hf2 hdf2)
    (fun x _ => hf x) (fun x _ => hdf x)
  change (∫ x, inner ℝ (f x) (ddf x)) = -(∫ x, inner ℝ (df x) (df x)) at hip
  have hs : (∫ x, inner ℝ (df x) (df x)) = lpNorm df 2 volume ^ 2 := by
    simp_rw [real_inner_self_eq_norm_sq]
    rw [P201.Hyperbolic.SymmetricEnergy.lpNorm_two_eq_sqrt_integral
      hdf2.aestronglyMeasurable,
      Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖df x‖))]
  have hb : |∫ x, inner ℝ (f x) (ddf x)| ≤
      lpNorm f 2 volume * lpNorm ddf 2 volume := by
    calc
      _ ≤ ∫ x, ‖f x‖ * ‖ddf x‖ := by
        simpa only [Real.norm_eq_abs, Pi.mul_apply] using
          norm_integral_le_of_norm_le (f := fun x => inner ℝ (f x) (ddf x))
            (hf2.norm.integrable_mul hddf2.norm)
            (Eventually.of_forall fun x => norm_inner_le_norm _ _)
      _ ≤ _ := P201.Hyperbolic.SymmetricEnergy.integral_norm_mul_le_lpNorm_two hf2 hddf2
  rw [hip, hs, abs_neg, abs_of_nonneg (sq_nonneg _)] at hb
  exact hb

/-- Adjacent Sobolev interpolation for a smooth representative, retaining
exactly the derivative-square norm and a constant independent of the fiber. -/
theorem smooth_sobolev_interpolation {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 (q + 2)) {f : Space n → Fiber 𝕜 m}
    (hf : ContDiff ℝ ∞ f) (hrep : underlyingSection u =ᵐ[volume] f) :
    ‖lowerOrderCLM u‖ ^ 2 ≤ (Fintype.card (P102.U4.SobolevIndex n (q + 1)) : ℝ) *
      (‖lowerOrderCLM (lowerOrderCLM u)‖ * ‖u‖) := by
  classical
  let w : WholeH n m 𝕜 (q + 1) := lowerOrderCLM u
  let z : WholeH n m 𝕜 q := lowerOrderCLM w
  have hw : underlyingSection w =ᵐ[volume] f := by
    simpa only [w, lowerOrderCLM_underlying] using hrep
  have hz : underlyingSection z =ᵐ[volume] f := by
    simpa only [z, lowerOrderCLM_underlying] using hw
  have hzu : ‖z‖ ≤ ‖u‖ := by
    have h1 : ‖w‖ ≤ ‖u‖ := by
      exact ((lowerOrderCLM (n := n) (m := m) (𝕜 := 𝕜) (k := q + 1)).le_opNorm u).trans
        ((mul_le_mul_of_nonneg_right (wholeDerivativeCLM_norm_le (P102.U4.zeroSobolevIndex n 1)) (norm_nonneg u)).trans_eq (one_mul ‖u‖))
    have h2 : ‖z‖ ≤ ‖w‖ := by
      exact ((lowerOrderCLM (n := n) (m := m) (𝕜 := 𝕜) (k := q)).le_opNorm w).trans
        ((mul_le_mul_of_nonneg_right (wholeDerivativeCLM_norm_le (P102.U4.zeroSobolevIndex n 1)) (norm_nonneg w)).trans_eq (one_mul ‖w‖))
    exact h2.trans h1
  have hb (α : P102.U4.SobolevIndex n (q + 1)) :
      lpNorm (derivativeSection w α) 2 volume ^ 2 ≤ ‖z‖ * ‖u‖ := by
    let l := α.val.sort (· ≤ ·)
    have hl : l.length ≤ q + 1 := by simpa only [l, Multiset.length_sort] using α.property
    have heq : lpNorm (derivativeSection w α) 2 volume = lpNorm (spatialWord f l) 2 volume :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae (derivativeSection_eq_smooth w hf hw α))
    rw [heq]
    by_cases hlow : l.length ≤ q
    · have hbound := (smooth_word_lpNorm_le z hf hz l hlow).2
      have hnon : 0 ≤ lpNorm (spatialWord f l) 2 volume := lpNorm_nonneg
      calc
        _ ≤ ‖z‖ ^ 2 := (sq_le_sq₀ hnon (norm_nonneg _)).mpr hbound
        _ ≤ ‖z‖ * ‖u‖ := by nlinarith [norm_nonneg z]
    · cases he : l with
      | nil => simp only [he, List.length_nil] at hlow; omega
      | cons j ls =>
        have hls : ls.length ≤ q := by simp only [he, List.length_cons] at hl; omega
        have hmid : (j :: ls).length ≤ q + 2 := by simp only [he] at hl; omega
        have htop : (j :: j :: ls).length ≤ q + 2 := by simp only [List.length_cons]; omega
        have hbase := smooth_word_lpNorm_le z hf hz ls hls
        have hmiddle := smooth_word_lpNorm_le u hf hrep (j :: ls) hmid
        have hhigh := smooth_word_lpNorm_le u hf hrep (j :: j :: ls) htop
        have hi := line_derivative_interpolation (coordinate n j)
          (fun x => ((spatialWord_contDiff hf ls).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (coordinate n j))
          (fun x => ((spatialWord_contDiff hf (j :: ls)).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (coordinate n j))
          hbase.1 hmiddle.1 hhigh.1
        exact hi.trans (mul_le_mul hbase.2 hhigh.2 (lpNorm_nonneg (f := spatialWord f (j :: j :: ls))) (norm_nonneg z))
  change ‖w‖ ^ 2 ≤ _
  rw [(section_norm w).2]
  calc
    _ ≤ ∑ _α : P102.U4.SobolevIndex n (q + 1), ‖z‖ * ‖u‖ :=
      Finset.sum_le_sum (fun α _ => hb α)
    _ = _ := by simp [z, w]

/-- Adjacent integer-order interpolation for the actual canonical Sobolev
spaces. The coefficient depends only on spatial dimension and order. -/
theorem sobolev_interpolation_sq {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 (q + 2)) :
    ‖lowerOrderCLM u‖ ^ 2 ≤ (Fintype.card (P102.U4.SobolevIndex n (q + 1)) : ℝ) *
      (‖lowerOrderCLM (lowerOrderCLM u)‖ * ‖u‖) := by
  have hclosed : IsClosed {v : WholeH n m 𝕜 (q + 2) |
      ‖lowerOrderCLM v‖ ^ 2 ≤ (Fintype.card (P102.U4.SobolevIndex n (q + 1)) : ℝ) *
        (‖lowerOrderCLM (lowerOrderCLM v)‖ * ‖v‖)} := by
    apply isClosed_le
    · exact lowerOrderCLM.continuous.norm.pow 2
    · exact continuous_const.mul
        ((lowerOrderCLM.continuous.comp lowerOrderCLM.continuous).norm.mul continuous_norm)
  obtain ⟨φ, v, hrep, hv⟩ := wholeH_smooth_density u
  apply hclosed.mem_of_tendsto hv
  apply Eventually.of_forall
  intro r
  exact smooth_sobolev_interpolation (v r) (testSection_contDiff (φ r))
    (testSection_represents (φ r) (v r) (hrep r))



namespace BoundedODE
open scoped NNReal
open Set MeasureTheory Metric Function intervalIntegral
open scoped Nat NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ} (hab : a ≤ b) (F : ℝ → E → E) (K : ℝ≥0)
variable (hL : ∀ t ∈ Icc a b, LipschitzWith K (F t))
variable (hC : ∀ x, ContinuousOn (fun t => F t x) (Icc a b))

abbrev Curves := C(Icc a b, E)

def extension (α : C(Icc a b, E)) (t : ℝ) : E :=
  α (projIcc a b hab t)

lemma extension_continuous (α : C(Icc a b, E)) :
    Continuous (extension hab α) := α.continuous.comp continuous_projIcc

lemma extension_of_mem (α : C(Icc a b, E)) {t : ℝ} (ht : t ∈ Icc a b) :
    extension hab α t = α ⟨t, ht⟩ := by
  simp [extension, projIcc_of_mem hab ht]

include K hL hC

lemma field_continuous : ContinuousOn (uncurry F) (Icc a b ×ˢ univ) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K
    (fun t ht => (hL t ht).lipschitzOnWith) (fun x _ => hC x)

lemma integrand_continuous (α : C(Icc a b, E)) :
    ContinuousOn (fun t => F t (extension hab α t)) (Icc a b) :=
  ODE.continuousOn_comp (field_continuous F K hL hC)
    (extension_continuous hab α).continuousOn (fun _ _ => mem_univ _)

lemma integrand_integrable (α : C(Icc a b, E)) (t : Icc a b) :
    IntervalIntegrable (fun t => F t (extension hab α t)) volume a t :=
  ((integrand_continuous hab F K hL hC α).mono
    (uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2)).intervalIntegrable

def next (x : E) (α : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := x + ∫ τ in a..t.val, F τ (extension hab α τ)
  continuous_toFun := by
    have hi : IntegrableOn (fun τ => F τ (extension hab α τ)) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact (integrand_continuous hab F K hL hC α).integrableOn_Icc
    have hcont := continuousOn_primitive_interval hi
    rw [uIcc_of_le hab] at hcont
    exact continuous_const.add hcont.domRestrict

@[simp] lemma next_apply (x : E) (α : C(Icc a b, E)) (t : Icc a b) :
    next hab F K hL hC x α t = x + ∫ τ in a..t.val, F τ (extension hab α τ) := rfl

lemma dist_comp_iterate_next_le (x : E) (n : ℕ) (t : Icc a b)
    {α β : C(Icc a b, E)}
    (h : dist ((next hab F K hL hC x)^[n] α t) ((next hab F K hL hC x)^[n] β t) ≤
      (K * |t.val - a|) ^ n / n ! * dist α β) :
    dist (F t ((next hab F K hL hC x)^[n] α t))
      (F t ((next hab F K hL hC x)^[n] β t)) ≤
      K ^ (n + 1) * |t.val - a| ^ n / n ! * dist α β := by
  calc
    _ ≤ K * dist ((next hab F K hL hC x)^[n] α t)
        ((next hab F K hL hC x)^[n] β t) := (hL t t.2).dist_le_mul _ _
    _ ≤ K ^ (n + 1) * |t.val - a| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

lemma dist_iterate_next_apply_le (x : E) (α β : C(Icc a b, E))
    (n : ℕ) (t : Icc a b) :
    dist ((next hab F K hL hC x)^[n] α t) ((next hab F K hL hC x)^[n] β t) ≤
      (K * |t.val - a|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (integrand_integrable hab F K hL hC _ t)
        (integrand_integrable hab F K hL hC _ t)]
    calc
      _ ≤ ∫ τ in uIoc a t.val, K ^ (n + 1) * |τ - a| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        have ht' : t' ∈ Icc a b :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2) ht'
        rw [← dist_eq_norm, extension_of_mem _ _ ht', extension_of_mem _ _ ht']
        exact dist_comp_iterate_next_le hab F K hL hC x _ ⟨t', ht'⟩ (hn _)
      _ ≤ (K * |t.val - a|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

lemma dist_iterate_next_le (x : E) (α β : C(Icc a b, E)) (n : ℕ) :
    dist ((next hab F K hL hC x)^[n] α) ((next hab F K hL hC x)^[n] β) ≤
      (K * (b - a)) ^ n / n ! * dist α β := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_next_apply_le hab F K hL hC x α β n t
    gcongr
    rw [abs_of_nonneg (sub_nonneg.mpr t.2.1)]
    exact sub_le_sub_right t.2.2 _
  · positivity

include hab

lemma exists_solution (x : E) :
    ∃ u : ℝ → E, ContinuousOn u (Icc a b) ∧ u a = x ∧
      ContinuousOn (fun t => F t (u t)) (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (F t (u t)) (Icc a b) t := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * (b - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hpos : 0 ≤ (K * (b - a)) ^ n / n ! := by positivity
  have hc : ContractingWith (⟨_, hpos⟩ : ℝ≥0) (next hab F K hL hC x)^[n] :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun α β => dist_iterate_next_le hab F K hL hC x α β n⟩
  let α : C(Icc a b, E) := hc.fixedPoint
  have hfix : IsFixedPt (next hab F K hL hC x) α := hc.isFixedPt_fixedPoint_iterate
  have hα (t : Icc a b) : extension hab α t.val = ODE.picard F a x (extension hab α) t.val := by
    rw [extension_of_mem _ _ t.2]
    exact (congrArg (fun β : C(Icc a b, E) => β t) hfix).symm
  refine ⟨extension hab α, (extension_continuous hab α).continuousOn, ?_,
    integrand_continuous hab F K hL hC α, ?_⟩
  · simpa using hα ⟨a, le_rfl, hab⟩
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc ⟨le_rfl, hab⟩
      (field_continuous F K hL hC) (extension_continuous hab α).continuousOn
      (fun _ _ => mem_univ _) x ht).congr_of_mem _ ht
    intro t' ht'
    exact hα ⟨t', ht'⟩

end BoundedODE

namespace BoundedODE
open scoped NNReal

/-- A bounded strongly continuous time-dependent linear coefficient generates
an actual global solution on a compact time interval. Operator-norm continuity
is not a hypothesis. -/
theorem exists_affine_solution {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[𝕜] E) (f : ℝ → E)
    (K : ℝ≥0) (hbound : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    (hA : ∀ x, ContinuousOn (fun t => A t x) (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (g : E) :
    ∃ u : ℝ → E, ContinuousOn u (Icc a b) ∧ u a = g ∧
      ContinuousOn (fun t => A t (u t) + f t) (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (A t (u t) + f t) (Icc a b) t := by
  apply exists_solution hab (fun t x => A t x + f t) K ?_ ?_ g
  · intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using
      (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hbound t ht)).dist_le_mul x y
  · intro x
    exact (hA x).add hf

end BoundedODE


set_option backward.isDefEq.respectTransparency false
section StrongFamilies
variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [TopologicalSpace Z]

theorem continuousOn_apply_of_strongly_continuous
    (M : Z → X →L[𝕜] Y) (S : Set Z) (C : ℝ)
    (hM : ∀ t ∈ S, ‖M t‖ ≤ C)
    (hc : ∀ x, ContinuousOn (fun t => M t x) S)
    (u : Z → X) (hu : ContinuousOn u S) :
    ContinuousOn (fun t => M t (u t)) S := by
  intro t ht
  have hzero : Tendsto (fun r => M r (u r - u t)) (𝓝[S] t) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun r => C * ‖u r - u t‖)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact (M r).le_opNorm (u r - u t) |>.trans
        (mul_le_mul_of_nonneg_right (hM r hr) (norm_nonneg _))
    · simpa using tendsto_const_nhds.mul (((hu t ht).sub_const (u t)).norm)
  have hsum := hzero.add (hc (u t) t ht)
  change Tendsto (fun r => M r (u r)) (𝓝[S] t) (𝓝 (M t (u t)))
  simpa only [map_sub, sub_add_cancel, zero_add] using hsum
end StrongFamilies

section IntegralCurves
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem integral_curve_hasDerivWithinAt {T : ℝ} (c : ℝ → X)
    (hc : ContinuousOn c (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => ∫ r in (0 : ℝ)..t, c r) (c t) (Icc 0 T) t := by
  letI : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  apply intervalIntegral.integral_hasDerivWithinAt_right
    ((hc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hc t ht)

end IntegralCurves

open P201Specs
open P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricApproximation
open P201.Hyperbolic.SymmetricSobolevEnergy

/-- Once the lower-order integral equation has passed to the limit, its
continuous right-hand side gives the intermediate PDE class, including the
one-sided time derivatives at both endpoints. -/
theorem intermediate_of_integral {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (Q : ℝ → WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q)
    (C : ℝ) (hQ : ∀ t ∈ Icc 0 T,
      RealizesP (fun j => A j t) (B t) (Q t) ∧ ‖Q t‖ ≤ C)
    (hQc : ∀ x, ContinuousOn (fun t => Q t x) (Icc 0 T))
    (f : ℝ → WholeH n m 𝕜 (q + 2)) (hf : ContinuousOn f (Icc 0 T))
    (u : ℝ → WholeH n m 𝕜 (q + 1)) (hu : ContinuousOn u (Icc 0 T))
    (hi : ∀ t ∈ Icc 0 T,
      truncate (Nat.le_succ q) (u t) = truncate (Nat.le_succ q) (u 0) +
        ∫ r in (0 : ℝ)..t, Q r (u r) + truncate (by omega : q ≤ q + 2) (f r)) :
    IsIntermediateSolution T A B f u
      (fun t => truncate (Nat.le_succ q) (u t))
      (fun t => Q t (u t) + truncate (by omega : q ≤ q + 2) (f t)) := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) q)
  let J : WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q := truncate (Nat.le_succ q)
  let F : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 q := truncate (by omega)
  have hc : ContinuousOn (fun t => Q t (u t) + F (f t)) (Icc 0 T) :=
    (continuousOn_apply_of_strongly_continuous Q (Icc 0 T) C
      (fun t ht => (hQ t ht).2) hQc u hu).add
      (F.continuous.comp_continuousOn hf)
  refine ⟨hu, J.continuous.comp_continuousOn hu, hc, ?_, ?_, ?_⟩
  · intro t ht i
    rfl
  · intro t ht
    have hd := (integral_curve_hasDerivWithinAt _ hc ht).const_add (J (u 0))
    exact hd.congr_of_mem hi ht
  · intro t ht
    filter_upwards [underlyingSection_add (Q t (u t)) (F (f t)), (hQ t ht).1 (u t)]
      with x hx hp
    rw [hx]
    change underlyingSection (Q t (u t)) x + underlyingSection (F (f t)) x = _
    rw [hp]
    rfl


/-- Interpolation is independent of any chosen realization maps. -/
theorem sobolev_interpolation : InterpolationStatement := by
  intro n m q 𝕜 _ u v w huv hvw
  have hv : v = lowerOrderCLM u :=
    sameSection_injective (sameSection_trans (sameSection_symm huv)
      (lowerOrderCLM_realizes u))
  have hw : w = lowerOrderCLM v :=
    sameSection_injective (sameSection_trans (sameSection_symm hvw)
      (lowerOrderCLM_realizes v))
  rw [hw, hv]
  exact sobolev_interpolation_sq u



namespace RegularizedEnergy

variable {𝕜 X : Type} [RCLike 𝕜] [NormedAddCommGroup X]
variable [InnerProductSpace 𝕜 X] [CompleteSpace X]

/-- Moving an actual self-adjoint contraction through the Hilbert pairing
preserves the uniform energy constant of the unregularized operator. -/
theorem pairing_bound (J : X →L[𝕜] X) (hself : IsSelfAdjoint J)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) {C : ℝ} (hC : 0 ≤ C) (v w f : X)
    (hp : RCLike.re (inner 𝕜 (J v) w) ≤ C * ‖J v‖ ^ 2) :
    RCLike.re (inner 𝕜 v (J w + J f)) ≤
      C * ‖v‖ ^ 2 + ‖v‖ * ‖f‖ := by
  rw [inner_add_right, map_add, ← hself.isSymmetric.apply_clm v w,
    ← hself.isSymmetric.apply_clm v f]
  have hf : RCLike.re (inner 𝕜 (J v) f) ≤ ‖v‖ * ‖f‖ := by
    calc
      _ ≤ ‖J v‖ * ‖f‖ := (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hJ v) (norm_nonneg _)
  have hc : C * ‖J v‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
    gcongr
    exact hJ v
  linarith

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- Uniform energy estimate for the genuine regularized ODE. `W t` denotes
`P(t)J(u(t))` at the Sobolev order on which the ODE is solved; its energy pairing
is assumed only as the spatial estimate, never as an existence certificate. -/
theorem estimate (J : X →L[𝕜] X) (hself : IsSelfAdjoint J)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (u du f W : ℝ → X) (g : X)
    (hu : ContinuousOn u (Icc 0 T)) (hdu : ContinuousOn du (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T)) (hinit : u 0 = J g)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, du t = J (W t) + J (f t))
    (hp : ∀ t ∈ Icc 0 T,
      RCLike.re (inner 𝕜 (J (u t)) (W t)) ≤ C * ‖J (u t)‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (C * t) *
      (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hb := P201.Hyperbolic.SymmetricSobolevEnergy.rclike_hilbert_comparison
    (𝕜 := 𝕜) t C u du f ht.1 hC (hu.mono hsub) (hdu.mono hsub) (hf.mono hsub)
    (fun r hr => (hd r (hsub ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2)))
    (fun r hr => by
      rw [heq r (hsub hr)]
      exact pairing_bound J hself hJ hC (u r) (W r) (f r) (hp r (hsub hr)))
  apply hb.trans
  rw [hinit]
  gcongr
  exact hJ g

/-- The same pairing estimate with an arbitrary source, needed when comparing
regularizations with distinct mollifiers. -/
theorem pairing_bound_with_source (J : X →L[𝕜] X) (hself : IsSelfAdjoint J)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) {C : ℝ} (hC : 0 ≤ C) (v w f : X)
    (hp : RCLike.re (inner 𝕜 (J v) w) ≤ C * ‖J v‖ ^ 2) :
    RCLike.re (inner 𝕜 v (J w + f)) ≤
      C * ‖v‖ ^ 2 + ‖v‖ * ‖f‖ := by
  rw [inner_add_right, map_add, ← hself.isSymmetric.apply_clm v w]
  have hf : RCLike.re (inner 𝕜 v f) ≤ ‖v‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hc : C * ‖J v‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
    gcongr
    exact hJ v
  linarith

/-- Comparison estimate for an actual regularized difference equation.
The forcing term need not lie in the range of the regularizer. -/
theorem estimate_with_source (J : X →L[𝕜] X) (hself : IsSelfAdjoint J)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) {T C : ℝ} (hC : 0 ≤ C)
    (u du f W : ℝ → X)
    (hu : ContinuousOn u (Icc 0 T)) (hdu : ContinuousOn du (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, du t = J (W t) + f t)
    (hp : ∀ t ∈ Icc 0 T,
      RCLike.re (inner 𝕜 (J (u t)) (W t)) ≤ C * ‖J (u t)‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (C * t) *
      (‖u 0‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  apply P201.Hyperbolic.SymmetricSobolevEnergy.rclike_hilbert_comparison
    (𝕜 := 𝕜) t C u du f ht.1 hC (hu.mono hsub) (hdu.mono hsub) (hf.mono hsub)
    (fun r hr => (hd r (hsub ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2)))
  intro r hr
  rw [heq r (hsub hr)]
  exact pairing_bound_with_source J hself hJ hC (u r) (W r) (f r) (hp r (hsub hr))

end RegularizedEnergy


namespace TopOperator
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201.Hyperbolic.SymmetricSobolevEnergy

/-- The accepted multiplier estimate also constructs P:H^(s+1)→H^s:
this requires coefficient derivatives only through s. -/
theorem operator_family_through_order :
    ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
      (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T s K A B → ∀ k ≤ s,
      ∃ Q : ℝ → WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k,
        (∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t) ∧ ‖Q t‖ ≤ C) ∧
        ∀ v, ContinuousOn (fun t => Q t v) (Icc 0 T) := by
  classical
  intro n s hn hs K hK
  obtain ⟨C, hC, hm⟩ := multiplier_family n s hn hs K hK
  refine ⟨(n + 1 : ℝ) * C, by positivity, ?_⟩
  intro m 𝕜 _ T hT A B hAB k hk
  have ha (j : Fin n) := hm T hT (A j) (hAB.1 j) k hk
  choose M hMa hMc using ha
  obtain ⟨N, hNa, hNc⟩ := hm T hT B hAB.2.1 k hk
  refine ⟨fun t => operatorFromMultipliers (fun j => M j t) (N t), ?_, ?_⟩
  · intro t ht
    exact ⟨operatorFromMultipliers_realizes (fun j => A j t) (B t) _ _
        (fun j => (hMa j t ht).1) (hNa t ht).1,
      operatorFromMultipliers_norm_le hC _ _ (fun j => (hMa j t ht).2) (hNa t ht).2⟩
  · intro v
    change ContinuousOn
      (fun t => (-(∑ j, (M j t).comp (partialCLM j)) - (N t).comp lowerOrderCLM) v) (Icc 0 T)
    simp only [sub_apply, neg_apply, sum_apply, ContinuousLinearMap.comp_apply]
    exact (continuousOn_finsetSum _ (fun j _ => hMc j (partialCLM j v))).neg.sub
      (hNc (lowerOrderCLM v))

/-- A realization of the actual distribution-defined P is unique. -/
theorem realizesP_unique {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q R : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k}
    (hQ : RealizesP A B Q) (hR : RealizesP A B R) : Q = R := by
  apply ContinuousLinearMap.ext
  intro v
  exact underlying_injective ((hQ v).trans (hR v).symm)

/-- Actual bounded, strongly continuous realizations through the top order,
with the accepted spatial pairing estimate for these same realizations. -/
theorem operator_family_with_pairing :
    ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
      (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T s K A B → ∀ k ≤ s,
      ∃ Q : ℝ → WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k,
        (∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t) ∧ ‖Q t‖ ≤ C) ∧
        (∀ v, ContinuousOn (fun t => Q t v) (Icc 0 T)) ∧
        ∀ t ∈ Icc 0 T, ∀ (v : WholeH n m 𝕜 (k + 1)) (w : WholeH n m 𝕜 k),
          IsLowerOrder v w → |RCLike.re (inner 𝕜 w (Q t v))| ≤ C * ‖w‖ ^ 2 := by
  intro n s hn hs K hK
  obtain ⟨D, hD, hoperator⟩ := operator_family_through_order n s hn hs K hK
  obtain ⟨C, hC, hpairing⟩ := pairing_bound n s hn hs K hK
  refine ⟨max C D, le_max_of_le_left hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB k hk
  obtain ⟨Q, hQ, hQc⟩ := hoperator T hT A B hAB k hk
  obtain ⟨R, hR, hRp⟩ := hpairing T hT A B hAB k hk
  refine ⟨Q, ?_, hQc, ?_⟩
  · intro t ht
    exact ⟨(hQ t ht).1, (hQ t ht).2.trans (le_max_right _ _)⟩
  · intro t ht v w hvw
    have heq : Q t = R t := realizesP_unique (hQ t ht).1 (hR t ht)
    rw [heq]
    exact (hRp t ht v w hvw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

end TopOperator


namespace IntegralLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A uniform integrand error gives an error proportional to the length of the interval. -/
theorem intervalIntegral_sub_bound {T t e : ℝ} {f g : ℝ → E}
    (ht : t ∈ Icc 0 T) (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (h : ∀ r ∈ Icc 0 T, ‖f r - g r‖ ≤ e) :
    ‖(∫ r in (0 : ℝ)..t, f r) - ∫ r in (0 : ℝ)..t, g r‖ ≤ e * t := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hfi := (hf.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hgi := (hg.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := e) (f := fun r => f r - g r) (by
      intro r hr
      rw [uIoc_of_le ht.1] at hr
      exact h r ⟨hr.1.le, hr.2.trans ht.2⟩)
  simpa only [sub_zero, abs_of_nonneg ht.1] using hb

/-- A uniform norm error bound tending to zero supplies uniform convergence. -/
theorem tendstoUniformlyOn_of_norm_error {I Z : Type*} {l : Filter I}
    {S : Set Z} {c : Z → E} {cs : I → Z → E} {e : I → ℝ}
    (he : Tendsto e l (𝓝 0))
    (hbound : ∀ i t, t ∈ S → ‖cs i t - c t‖ ≤ e i) :
    TendstoUniformlyOn cs c l S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp he).2 ε hε] with i hi
  intro t ht
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound i t ht).trans_lt hi

/-- Uniform convergence of continuous integrands on a closed interval gives
uniform convergence of their primitives, with no countability condition on the filter. -/
theorem tendstoUniformlyOn_intervalIntegral {I : Type*} {l : Filter I}
    {T : ℝ} (hT : 0 ≤ T) {c : ℝ → E} {cs : I → ℝ → E}
    (hc : ContinuousOn c (Icc 0 T))
    (hcs : ∀ i, ContinuousOn (cs i) (Icc 0 T))
    (hlim : TendstoUniformlyOn cs c l (Icc 0 T)) :
    TendstoUniformlyOn (fun i t => ∫ r in (0 : ℝ)..t, cs i r)
      (fun t => ∫ r in (0 : ℝ)..t, c r) l (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  have hden : 0 < T + 1 := by linarith
  have hδ : 0 < ε / (T + 1) := div_pos hε hden
  filter_upwards [hlim (ε / (T + 1)) hδ] with i hi
  intro t ht
  rw [dist_eq_norm]
  have hb := intervalIntegral_sub_bound ht hc (hcs i)
    (fun r hr => by simpa only [dist_eq_norm] using (hi r hr).le)
  have hε' : ε / (T + 1) * T < ε := by
    have heq : ε / (T + 1) * (T + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  exact hb.trans_lt ((mul_le_mul_of_nonneg_left ht.2 hδ.le).trans_lt hε')

/-- An integral equation survives pointwise convergence of the paths and data,
provided its continuous right hand sides converge uniformly. -/
theorem integral_equation_of_tendsto {I : Type*} {l : Filter I} [l.NeBot]
    {T : ℝ} (hT : 0 ≤ T) {g : E} {gs : I → E}
    {u c : ℝ → E} {us cs : I → ℝ → E}
    (hc : ContinuousOn c (Icc 0 T))
    (hcs : ∀ i, ContinuousOn (cs i) (Icc 0 T))
    (hg : Tendsto gs l (𝓝 g))
    (hu : ∀ t ∈ Icc 0 T, Tendsto (fun i => us i t) l (𝓝 (u t)))
    (hclim : TendstoUniformlyOn cs c l (Icc 0 T))
    (heq : ∀ i t, t ∈ Icc 0 T → us i t = gs i + ∫ r in (0 : ℝ)..t, cs i r) :
    ∀ t ∈ Icc 0 T, u t = g + ∫ r in (0 : ℝ)..t, c r := by
  intro t ht
  have hInt := (tendstoUniformlyOn_intervalIntegral hT hc hcs hclim).tendsto_at ht
  have heq' : (fun i => us i t) = (fun i => gs i + ∫ r in (0 : ℝ)..t, cs i r) :=
    funext (fun i => heq i t ht)
  have hut := hu t ht
  rw [heq'] at hut
  exact tendsto_nhds_unique hut (hg.add hInt)

end IntegralLimit


namespace RegularizedEnergy
open scoped NNReal

/-- A bounded strongly continuous regularized coefficient has an actual
solution and the uniform spatial-energy bound. `S` gains a derivative, `J`
is its realization at the current order, and the spatial pairing premise
is precisely the estimate to be supplied by the actual PDE operator. -/
theorem exists_solution {𝕜 E F : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (J : E →L[𝕜] E) (S : E →L[𝕜] F) (hself : IsSelfAdjoint J)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    {T C L : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (Q : ℝ → F →L[𝕜] E)
    (hQ : ∀ t ∈ Icc 0 T, ‖Q t‖ ≤ L)
    (hQc : ∀ v, ContinuousOn (fun t => Q t v) (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, ∀ v,
      RCLike.re (inner 𝕜 (J v) (Q t (S v))) ≤ C * ‖J v‖ ^ 2)
    (f : ℝ → E) (hf : ContinuousOn f (Icc 0 T)) (g : E) :
    ∃ u : ℝ → E, ContinuousOn u (Icc 0 T) ∧ u 0 = J g ∧
      ContinuousOn (fun t => J (Q t (S (u t))) + J (f t)) (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T,
        HasDerivWithinAt u (J (Q t (S (u t))) + J (f t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (C * t) *
        (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  let A : ℝ → E →L[𝕜] E := fun t => J.comp ((Q t).comp S)
  let K : ℝ≥0 := ‖J‖₊ * ⟨L, hL⟩ * ‖S‖₊
  have hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K := by
    intro t ht
    calc
      ‖A t‖ ≤ ‖J‖ * ‖(Q t).comp S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖J‖ * (‖Q t‖ * ‖S‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ ‖J‖ * (L * ‖S‖) := by gcongr; exact hQ t ht
      _ = (K : ℝ) := by
        change ‖J‖ * (L * ‖S‖) = ‖J‖ * L * ‖S‖
        ring
  have hAc : ∀ v, ContinuousOn (fun t => A t v) (Icc 0 T) := by
    intro v
    exact J.continuous.comp_continuousOn (hQc (S v))
  obtain ⟨u, hu, hinit, hdu, hd⟩ := BoundedODE.exists_affine_solution hT A
    (fun t => J (f t)) K hA hAc (J.continuous.comp_continuousOn hf) (J g)
  refine ⟨u, hu, hinit, hdu, hd, ?_⟩
  exact estimate J hself hJ hT hC u (fun t => A t (u t) + J (f t)) f
    (fun t => Q t (S (u t))) g hu hdu hf hinit hd (fun _ _ => rfl)
    (fun t ht => hp t ht (u t))

end RegularizedEnergy



namespace InterpolationLimit

variable {𝕜 X Y Z D : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A high-norm bound and a low-norm Cauchy estimate give uniform Cauchy
convergence in the intermediate norm whenever a quadratic interpolation bound holds. -/
theorem uniformCauchySeqOn_of_interpolation
    (J : X →L[𝕜] Y) (K : X →L[𝕜] Z) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hinterp : ∀ v : X, ‖J v‖ ^ 2 ≤ C * (‖K v‖ * ‖v‖))
    (z : ℕ → D → X) (S : Set D)
    (hbound : ∀ i t, t ∈ S → ‖z i t‖ ≤ R)
    (hlow : UniformCauchySeqOn (fun i t => K (z i t)) atTop S) :
    UniformCauchySeqOn (fun i t => J (z i t)) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff] at hlow ⊢
  intro ε hε
  let A : ℝ := C * (2 * R)
  have hA : 0 ≤ A := mul_nonneg hC (mul_nonneg (by linarith) hR)
  have hden : 0 < A + 1 := by linarith
  let δ : ℝ := ε ^ 2 / (A + 1)
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨N, hN⟩ := hlow δ hδ
  refine ⟨N, ?_⟩
  intro i hi j hj t ht
  have hzdiff : ‖z i t - z j t‖ ≤ 2 * R := by
    exact (norm_sub_le _ _).trans (by linarith [hbound i t ht, hbound j t ht])
  have hlowdiff : ‖K (z i t - z j t)‖ < δ := by
    simpa only [map_sub, dist_eq_norm] using hN i hi j hj t ht
  have hmid : ‖J (z i t - z j t)‖ ^ 2 ≤ A * ‖K (z i t - z j t)‖ := by
    calc
      _ ≤ C * (‖K (z i t - z j t)‖ * ‖z i t - z j t‖) := hinterp _
      _ ≤ C * (‖K (z i t - z j t)‖ * (2 * R)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hzdiff (norm_nonneg _)) hC
      _ = _ := by dsimp [A]; ring
  have hAδ : A * δ < ε ^ 2 := by
    have heq : δ * (A + 1) = ε ^ 2 := div_mul_cancel₀ _ hden.ne'
    nlinarith
  have hmidlt : ‖J (z i t - z j t)‖ ^ 2 < ε ^ 2 :=
    hmid.trans_lt ((mul_le_mul_of_nonneg_left hlowdiff.le hA).trans_lt hAδ)
  rw [dist_eq_norm, ← map_sub]
  nlinarith [norm_nonneg (J (z i t - z j t))]

/-- On a complete intermediate space, the interpolation transfer constructs
a continuous path and uniform convergence to it. -/
theorem exists_continuousOn_uniform_limit_of_interpolation
    [TopologicalSpace D] [CompleteSpace Y]
    (J : X →L[𝕜] Y) (K : X →L[𝕜] Z) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hinterp : ∀ v : X, ‖J v‖ ^ 2 ≤ C * (‖K v‖ * ‖v‖))
    (z : ℕ → D → X) (S : Set D)
    (hcont : ∀ i, ContinuousOn (z i) S)
    (hbound : ∀ i t, t ∈ S → ‖z i t‖ ≤ R)
    (hlow : UniformCauchySeqOn (fun i t => K (z i t)) atTop S) :
    ∃ u : D → Y, ContinuousOn u S ∧
      TendstoUniformlyOn (fun i t => J (z i t)) u atTop S := by
  classical
  have hmid := uniformCauchySeqOn_of_interpolation J K hC hR hinterp z S hbound hlow
  have hex : ∀ t, ∃ y : Y, t ∈ S →
      Tendsto (fun i => J (z i t)) atTop (𝓝 y) := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨y, hy⟩ := cauchy_map_iff_exists_tendsto.mp (hmid.cauchy_map ht)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose u hu using hex
  have huni := hmid.tendstoUniformlyOn_of_tendsto hu
  refine ⟨u, ?_, huni⟩
  exact huni.continuousOn (Eventually.of_forall (fun i =>
    J.continuous.comp_continuousOn (hcont i))).frequently

end InterpolationLimit



namespace TopOperator
/-- Canonical order lowering retains every remaining derivative coordinate. -/
theorem derivativeSection_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 (k + 1)) (α : P102.U4.SobolevIndex n k) :
    derivativeSection (lowerOrderCLM v) α =
      derivativeSection v ⟨α.val, α.property.trans (Nat.le_succ k)⟩ := by
  funext x
  apply PiLp.ext
  intro i
  change (v i).val (shiftedIndex (P102.U4.zeroSobolevIndex n 1) α) x = _
  have hi : shiftedIndex (P102.U4.zeroSobolevIndex n 1) α =
      (⟨α.val, α.property.trans (Nat.le_succ k)⟩ : P102.U4.SobolevIndex n (k + 1)) :=
    Subtype.ext (add_zero α.val)
  rw [hi]
  rfl

/-- The actual spatial differential expression commutes with order lowering. -/
theorem pSection_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → Space n → Operator m 𝕜) (B : Space n → Operator m 𝕜)
    (v : WholeH n m 𝕜 (k + 1 + 1)) :
    pSection A B (lowerOrderCLM v) = pSection A B v := by
  have hd (j : Fin n) :
      derivativeSection (lowerOrderCLM (k := k + 1) v) ⟨{j}, by simp⟩ =
        derivativeSection v ⟨{j}, by simp⟩ :=
    derivativeSection_lowerOrder v ⟨{j}, by simp⟩
  funext x
  simp only [pSection, hd, lowerOrderCLM_underlying]

/-- Actual P-realizations at adjacent orders form the compatible Sobolev-scale
maps required by the two-loss regularization estimate. -/
theorem operator_order_compatible {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k}
    {P : WholeH n m 𝕜 (k + 1 + 1) →L[𝕜] WholeH n m 𝕜 (k + 1)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P) :
    Q.comp lowerOrderCLM = lowerOrderCLM.comp P := by
  apply ContinuousLinearMap.ext
  intro v
  apply underlying_injective
  simp only [ContinuousLinearMap.comp_apply, lowerOrderCLM_underlying]
  exact (hQ (lowerOrderCLM v)).trans
    ((Filter.EventuallyEq.of_eq (pSection_lowerOrder A B v)).trans (hP v).symm)


end TopOperator


namespace RegularizationError

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
variable [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]

/-- The two-loss decomposition of the difference of regularized first-order
operators, on a compatible scale X→Y→Z. -/
theorem decomposition (L : X →L[𝕜] Y) (R : Y →L[𝕜] Z)
    (P : X →L[𝕜] Y) (Q : Y →L[𝕜] Z)
    (hcompat : Q.comp L = R.comp P)
    (A A' : X →L[𝕜] X) (B B' : Z →L[𝕜] Z) :
    B.comp (R.comp (P.comp A)) - B'.comp (R.comp (P.comp A')) =
      ((B - B').comp R).comp (P.comp A) +
        B'.comp (Q.comp (L.comp (A - A'))) := by
  apply ContinuousLinearMap.ext
  intro x
  have hc (v : X) : Q (L v) = R (P v) :=
    congrArg (fun H : X →L[𝕜] Z => H v) hcompat
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [hc, hc]
  abel

/-- A quantitative version of the source's two-derivative loss estimate.
`δ₁` measures the regularizer difference after losing one derivative;
`δ₂` measures that difference before the first-order operator acts. -/
theorem norm_difference_le (L : X →L[𝕜] Y) (R : Y →L[𝕜] Z)
    (P : X →L[𝕜] Y) (Q : Y →L[𝕜] Z)
    (hcompat : Q.comp L = R.comp P)
    (A A' : X →L[𝕜] X) (B B' : Z →L[𝕜] Z)
    {C δ₁ δ₂ : ℝ} (hC : 0 ≤ C) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hA : ‖A‖ ≤ 1) (hB' : ‖B'‖ ≤ 1) (hP : ‖P‖ ≤ C) (hQ : ‖Q‖ ≤ C)
    (hfirst : ‖(B - B').comp R‖ ≤ δ₁)
    (hsecond : ‖L.comp (A - A')‖ ≤ δ₂) :
    ‖B.comp (R.comp (P.comp A)) - B'.comp (R.comp (P.comp A'))‖ ≤
      C * (δ₁ + δ₂) := by
  rw [decomposition L R P Q hcompat A A' B B']
  have hPA : ‖P.comp A‖ ≤ C := by
    calc
      _ ≤ ‖P‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul hP hA (norm_nonneg _) hC
      _ = C := mul_one _
  have hterm₁ : ‖((B - B').comp R).comp (P.comp A)‖ ≤ δ₁ * C := by
    calc
      _ ≤ ‖(B - B').comp R‖ * ‖P.comp A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ δ₁ * C := mul_le_mul hfirst hPA (norm_nonneg _) hδ₁
  have hQL : ‖Q.comp (L.comp (A - A'))‖ ≤ C * δ₂ := by
    calc
      _ ≤ ‖Q‖ * ‖L.comp (A - A')‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * δ₂ := mul_le_mul hQ hsecond (norm_nonneg _) hC
  have hterm₂ : ‖B'.comp (Q.comp (L.comp (A - A')))‖ ≤ C * δ₂ := by
    calc
      _ ≤ ‖B'‖ * ‖Q.comp (L.comp (A - A'))‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (C * δ₂) := mul_le_mul hB' hQL (norm_nonneg _) (by norm_num)
      _ = C * δ₂ := one_mul _
  calc
    _ ≤ ‖((B - B').comp R).comp (P.comp A)‖ +
        ‖B'.comp (Q.comp (L.comp (A - A')))‖ := norm_add_le _ _
    _ ≤ δ₁ * C + C * δ₂ := add_le_add hterm₁ hterm₂
    _ = _ := by ring

/-- The corresponding consistency estimate against the unregularized P,
used to pass the actual integral equation to its lower-order limit. -/
theorem norm_difference_identity_le (L : X →L[𝕜] Y) (R : Y →L[𝕜] Z)
    (P : X →L[𝕜] Y) (Q : Y →L[𝕜] Z)
    (hcompat : Q.comp L = R.comp P)
    (A : X →L[𝕜] X) (B : Z →L[𝕜] Z)
    {C δ₁ δ₂ : ℝ} (hC : 0 ≤ C) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hA : ‖A‖ ≤ 1) (hP : ‖P‖ ≤ C) (hQ : ‖Q‖ ≤ C)
    (hfirst : ‖(B - ContinuousLinearMap.id 𝕜 Z).comp R‖ ≤ δ₁)
    (hsecond : ‖L.comp (A - ContinuousLinearMap.id 𝕜 X)‖ ≤ δ₂) :
    ‖B.comp (R.comp (P.comp A)) - R.comp P‖ ≤ C * (δ₁ + δ₂) := by
  simpa using norm_difference_le L R P Q hcompat A (ContinuousLinearMap.id 𝕜 X)
    B (ContinuousLinearMap.id 𝕜 Z) hC hδ₁ hδ₂ hA ContinuousLinearMap.norm_id_le
    hP hQ hfirst hsecond

end RegularizationError


/-- With any actual compatible smoothing maps, the original coefficient
hypotheses produce genuine regularized Sobolev solutions and the uniform
source bound. The map hypotheses are discharged below by the concrete convolution
operators; they are not premises of the main existence statement. -/
theorem regularized_sobolev_existence :
    ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
      (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T s K A B →
      ∀ (J : WholeH n m 𝕜 s →L[𝕜] WholeH n m 𝕜 s)
        (S : WholeH n m 𝕜 s →L[𝕜] WholeH n m 𝕜 (s + 1)),
        IsSelfAdjoint J → (∀ v, ‖J v‖ ≤ ‖v‖) →
        (∀ v, IsLowerOrder (S v) (J v)) →
      ∀ (g : WholeH n m 𝕜 s) (f : ℝ → WholeH n m 𝕜 s),
        ContinuousOn f (Icc 0 T) →
      ∃ (Q : ℝ → WholeH n m 𝕜 (s + 1) →L[𝕜] WholeH n m 𝕜 s)
        (u : ℝ → WholeH n m 𝕜 s),
        (∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t)) ∧
        ContinuousOn u (Icc 0 T) ∧ u 0 = J g ∧
        ContinuousOn (fun t => J (Q t (S (u t))) + J (f t)) (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt u (J (Q t (S (u t))) + J (f t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (C * t) *
          (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  intro n s hn hs K hK
  obtain ⟨C, hC, hfamily⟩ := TopOperator.operator_family_with_pairing n s hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB J S hself hJ hS g f hf
  letI : InnerProductSpace 𝕜 (WholeH n m 𝕜 s) :=
    PiLp.innerProductSpace (fun _ : Fin m => H 𝕜 (⊤ : Domain n) s)
  letI : NormedSpace ℝ (WholeH n m 𝕜 s) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) s)
  obtain ⟨Q, hQ, hQc, hpair⟩ := hfamily T hT A B hAB s le_rfl
  obtain ⟨u, hu, hinit, hdu, hd, hest⟩ := RegularizedEnergy.exists_solution
    (𝕜 := 𝕜) J S hself hJ hT hC hC Q (fun t ht => (hQ t ht).2) hQc
    (fun t ht v => (le_abs_self _).trans (hpair t ht (S v) (J v) (hS v))) f hf g
  exact ⟨Q, u, fun t ht => (hQ t ht).1, hu, hinit, hdu, hd, hest⟩



section IntegralCurves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual differentiable regularized path satisfies its integral equation. -/
theorem integral_equation_of_derivative {T : ℝ} (u du : ℝ → E)
    (hu : ContinuousOn u (Icc 0 T)) (hdu : ContinuousOn du (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, u t = u 0 + ∫ r in (0 : ℝ)..t, du r := by
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hu.mono hsub)
    (fun r hr => (hd r (hsub ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2)))
    ((hdu.mono hsub).intervalIntegrable_of_Icc ht.1)
  rw [hi]
  abel

/-- A two-index error tending to zero supplies the uniform Cauchy estimate
needed by adjacent-order interpolation. -/
theorem uniformCauchySeqOn_of_norm_error {D : Type*} (z : ℕ → D → E)
    (S : Set D) {A : ℝ} (hA : 0 ≤ A) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ i j t, t ∈ S → ‖z i t - z j t‖ ≤ A * (e i + e j)) :
    UniformCauchySeqOn z atTop S := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hden : 0 < 2 * (A + 1) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp he).2
    (ε / (2 * (A + 1))) (div_pos hε hden))
  refine ⟨N, ?_⟩
  intro i hi j hj t ht
  have hb := hbound i j t ht
  have hmul : ε / (2 * (A + 1)) * (2 * (A + 1)) = ε := div_mul_cancel₀ _ hden.ne'
  rw [dist_eq_norm]
  have hh : A * (e i + e j) < ε := by
    have hi' := hN i hi
    have hj' := hN j hj
    have hd : 0 < ε / (2 * (A + 1)) := div_pos hε hden
    nlinarith
  exact hb.trans_lt hh
end IntegralCurves



section Mollifiers
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
open P102.U4 TopologicalSpace

private theorem convolution_memLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    MemLp (localConvolution (P201Specs.regularDistribution ⊤ f) ρ) 2
      (P201Specs.domainMeasure (⊤ : Domain n)) := by
  have hf : MemLp (f : Space n → 𝕜) 2 volume := by
    simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using Lp.memLp f
  have hρ : MemLp (ρ : Space n → 𝕜) 1 volume :=
    ρ.continuous.memLp_of_hasCompactSupport ρ.hasCompactSupport
  have hy := P102.U2.Young.young (G := P201Specs.Space n) volume (p := 1) (q := 2) (r := 2)
    (by norm_num) (by norm_num) (by norm_num) (by simp) hρ hf
  simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ]
  rw [localConvolution_regular_whole (hf.locallyIntegrable (by norm_num))]
  exact hy.2.1

/-- The actual scalar L² convolution class for a compact smooth kernel. -/
def convolutionLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    P201Specs.Lp 𝕜 (⊤ : Domain n) 2 :=
  (convolution_memLp ρ f).toLp (localConvolution (P201Specs.regularDistribution ⊤ f) ρ)

theorem convolutionLp_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    (convolutionLp ρ f : Space n → 𝕜) =ᵐ[volume]
      localConvolution (P201Specs.regularDistribution ⊤ f) ρ := by
  simpa only [convolutionLp, P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using
    (convolution_memLp ρ f).coeFn_toLp

theorem convolutionLp_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    ‖convolutionLp ρ f‖ ≤ lpNorm ρ 1 volume * ‖f‖ := by
  have hf : MemLp (f : Space n → 𝕜) 2 volume := by
    simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using Lp.memLp f
  have hρ : MemLp (ρ : Space n → 𝕜) 1 volume :=
    ρ.continuous.memLp_of_hasCompactSupport ρ.hasCompactSupport
  have hy := P102.U2.Young.young (G := P201Specs.Space n) volume (p := 1) (q := 2) (r := 2)
    (by norm_num) (by norm_num) (by norm_num) (by simp) hρ hf
  have hnorm := ENNReal.toReal_mono (ENNReal.mul_ne_top hρ.eLpNorm_ne_top hf.eLpNorm_ne_top) hy.2.2.1
  rw [ENNReal.toReal_mul] at hnorm
  rw [Lp.norm_def]
  rw [show eLpNorm (convolutionLp ρ f) 2 (P201Specs.domainMeasure (⊤ : Domain n)) =
    eLpNorm (localConvolution (P201Specs.regularDistribution ⊤ f) ρ) 2 volume by
      simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using
        eLpNorm_congr_ae (convolutionLp_ae ρ f)]
  rw [localConvolution_regular_whole (hf.locallyIntegrable (by norm_num))]
  convert hnorm using 1 <;> first | rfl | simp only [lpNorm, Lp.norm_def, P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ]

private theorem convolutionLp_regular {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    P201Specs.regularDistribution ⊤ (convolutionLp ρ f) =
      P201Specs.regularDistribution ⊤
        (localConvolution (P201Specs.regularDistribution ⊤ f) ρ) := by
  apply (regular_injectivity n 𝕜 ⊤ _ _ (domainLp_locallyIntegrable ⊤ 2 _)
    ((localConvolution_contDiff _ _).continuous.continuousOn.locallyIntegrableOn
      isOpen_univ.measurableSet)).mpr
  exact ae_restrict_of_ae (convolutionLp_ae ρ f)

theorem convolutionLp_distribution {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : H 𝕜 (⊤ : Domain n) k)
    (α : SobolevIndex n k) :
    distributionPartial α.val (P201Specs.regularDistribution ⊤
      (convolutionLp ρ (P201Specs.hUnderlying ⊤ k u))) =
    P201Specs.regularDistribution ⊤
      (convolutionLp ρ (sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k u) α)) := by
  rw [convolutionLp_regular, convolutionLp_regular,
    derivative_classicalCompatibility n 𝕜 ⊤ α.val _
      ((localConvolution_contDiff _ _).of_le (by simp)).contDiffOn]
  congr 1
  exact wholeSpace_weakMollification k 2 (P201Specs.hToW 𝕜 ⊤ k u) ρ α

/-- Convolution preserves every weak derivative coordinate of the canonical
closed Sobolev graph, with no support hypothesis on the input. -/
def scalarConvolution {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : H 𝕜 (⊤ : Domain n) k) : H 𝕜 (⊤ : Domain n) k :=
  ⟨WithLp.toLp 2 (fun α => convolutionLp ρ (sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k u) α)), by
    apply (mem_sobolevSubmodule_iff ⊤ k 2 _).mpr
    intro α φ
    exact (distributionPartial_eq_regularLp_iff ⊤ 2 α.val _ _).mp
      (convolutionLp_distribution ρ u α) φ⟩

theorem scalarConvolution_coordinate {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : H 𝕜 (⊤ : Domain n) k) (α : SobolevIndex n k) :
    sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (scalarConvolution ρ u)) α =
      convolutionLp ρ (sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k u) α) := rfl

theorem scalarConvolution_norm_le {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : H 𝕜 (⊤ : Domain n) k) :
    ‖scalarConvolution ρ u‖ ≤ lpNorm ρ 1 volume * ‖u‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg lpNorm_nonneg (norm_nonneg u))).mp
  change ‖(scalarConvolution ρ u).val‖ ^ 2 ≤ (lpNorm ρ 1 volume * ‖u.val‖) ^ 2
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  change ‖convolutionLp ρ (u.val α)‖ ^ 2 ≤ lpNorm ρ 1 volume ^ 2 * ‖u.val α‖ ^ 2
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg lpNorm_nonneg (norm_nonneg _))).mpr
      (convolutionLp_norm_le ρ (u.val α))

private theorem regularLp_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    P201Specs.regularDistribution ⊤ (c • f) = c • P201Specs.regularDistribution ⊤ f := by
  ext φ
  simp only [regularLp_pairing ⊤ 2, map_smul, smul_apply]

theorem convolutionLp_add {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f g : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    convolutionLp ρ (f + g) = convolutionLp ρ f + convolutionLp ρ g := by
  apply Lp.ext
  apply ae_restrict_of_ae
  have hsum := Lp.coeFn_add (convolutionLp ρ f) (convolutionLp ρ g)
  simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at hsum
  filter_upwards [convolutionLp_ae ρ (f + g), convolutionLp_ae ρ f,
    convolutionLp_ae ρ g, hsum] with x hfg hf hg hsum
  rw [hsum, hfg]
  simp only [Pi.add_apply]
  rw [hf, hg]
  have hadd : P201Specs.regularDistribution ⊤ (f + g) =
      P201Specs.regularDistribution ⊤ f + P201Specs.regularDistribution ⊤ g := regularLp_add f g
  rw [hadd]
  simp only [localConvolution, add_apply]
  split <;> simp

theorem convolutionLp_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (c : 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    convolutionLp ρ (c • f) = c • convolutionLp ρ f := by
  apply Lp.ext
  apply ae_restrict_of_ae
  have hsm := Lp.coeFn_smul c (convolutionLp ρ f)
  simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at hsm
  filter_upwards [convolutionLp_ae ρ (c • f), convolutionLp_ae ρ f, hsm] with x hcf hf hsm
  rw [hsm, hcf]
  simp only [Pi.smul_apply]
  rw [hf, regularLp_smul]
  simp only [localConvolution, smul_apply]
  split <;> simp

/-- The convolution acts continuously and linearly on the exact scalar L² classes. -/
def convolutionLpCLM {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (ρ : WholeTests n 𝕜) :
    P201Specs.Lp 𝕜 (⊤ : Domain n) 2 →L[𝕜] P201Specs.Lp 𝕜 (⊤ : Domain n) 2 :=
  LinearMap.mkContinuous
    { toFun := convolutionLp ρ
      map_add' := convolutionLp_add ρ
      map_smul' := fun c f => convolutionLp_smul ρ c f }
    (lpNorm ρ 1 volume) (convolutionLp_norm_le ρ)

/-- A compact smooth kernel gains arbitrarily many derivatives from an L²
input. The coordinates are convolution by its actual differentiated kernels. -/
def convolutionToH {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (k : ℕ) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    H 𝕜 (⊤ : Domain n) k :=
  ⟨WithLp.toLp 2 (fun α => convolutionLp (kernelPartial α.val ρ) f), by
    apply (mem_sobolevSubmodule_iff ⊤ k 2 _).mpr
    intro α φ
    apply (distributionPartial_eq_regularLp_iff ⊤ 2 α.val _ _).mp _ φ
    change distributionPartial α.val (P201Specs.regularDistribution ⊤
      (convolutionLp (kernelPartial 0 ρ) f)) =
      P201Specs.regularDistribution ⊤ (convolutionLp (kernelPartial α.val ρ) f)
    have h0 : kernelPartial (0 : P102.U4.MultiIndex n) ρ = ρ := by
      simp only [kernelPartial, Multiset.sort_zero]
      rfl
    rw [h0, convolutionLp_regular, convolutionLp_regular,
      derivative_classicalCompatibility n 𝕜 ⊤ α.val _
        ((localConvolution_contDiff _ _).of_le (by simp)).contDiffOn]
    congr 1
    funext x
    exact localConvolution_derivative n 𝕜 ⊤ α.val _ ρ x (by simp [convolutionDomain])⟩

theorem convolutionToH_underlying {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (k : ℕ) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    P201Specs.hUnderlying ⊤ k (convolutionToH ρ k f) = convolutionLp ρ f := by
  change convolutionLp (kernelPartial 0 ρ) f = convolutionLp ρ f
  simp only [kernelPartial, Multiset.sort_zero]
  rfl

/-- Fixed compact smooth convolution acts on the exact H^k Hilbert space. -/
def scalarConvolutionCLM {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) : H 𝕜 (⊤ : Domain n) k →L[𝕜] H 𝕜 (⊤ : Domain n) k :=
  LinearMap.mkContinuous
    { toFun := scalarConvolution ρ
      map_add' := by
        intro u v
        apply Subtype.ext
        apply PiLp.ext
        intro α
        exact convolutionLp_add ρ (u.val α) (v.val α)
      map_smul' := by
        intro c u
        apply Subtype.ext
        apply PiLp.ext
        intro α
        exact convolutionLp_smul ρ c (u.val α) }
    (lpNorm ρ 1 volume) (scalarConvolution_norm_le ρ)

/-- Componentwise smoothing retains the Euclidean fiber norm, so its
contraction bound has no dependence on the number of components. -/
def wholeConvolutionCLM {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 (fun i => scalarConvolutionCLM ρ (u i))
      map_add' := by intro u v; apply PiLp.ext; intro i; exact map_add _ _ _
      map_smul' := by
        intro c u
        apply PiLp.ext
        intro i
        exact (scalarConvolutionCLM (k := k) ρ).map_smul c (u i) }
    (lpNorm ρ 1 volume) (fun u => by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg lpNorm_nonneg (norm_nonneg u))).mp
      change ‖WithLp.toLp 2 (fun i => scalarConvolutionCLM ρ (u i))‖ ^ 2 ≤ (lpNorm ρ 1 volume * ‖u‖) ^ 2
      rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      change ‖scalarConvolution ρ (u i)‖ ^ 2 ≤ lpNorm ρ 1 volume ^ 2 * ‖u i‖ ^ 2
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg lpNorm_nonneg (norm_nonneg _))).mpr
          (scalarConvolution_norm_le ρ (u i)))

theorem wholeConvolution_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : WholeH n m 𝕜 k) :
    ‖wholeConvolutionCLM ρ u‖ ≤ lpNorm ρ 1 volume * ‖u‖ := by
  have hn : ‖wholeConvolutionCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜) ρ‖ ≤ lpNorm ρ 1 volume := by
    unfold wholeConvolutionCLM
    exact LinearMap.mkContinuous_norm_le _ lpNorm_nonneg _
  exact ((wholeConvolutionCLM ρ).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg u))

theorem scalarConvolution_underlying {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : H 𝕜 (⊤ : Domain n) k) :
    P201Specs.hUnderlying ⊤ k (scalarConvolutionCLM ρ u) =
      convolutionLpCLM ρ (P201Specs.hUnderlying ⊤ k u) := rfl

theorem wholeConvolution_underlying {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : WholeH n m 𝕜 k) (i : Fin m) :
    P201Specs.hUnderlying ⊤ k (wholeConvolutionCLM ρ u i) =
      convolutionLpCLM ρ (P201Specs.hUnderlying ⊤ k (u i)) := rfl

theorem mollifierKernel_norm_one {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    lpNorm (sobolevMollifierKernel n 𝕜 ε) 1 volume = 1 := by
  rw [lpNorm_one_eq_integral_norm (sobolevMollifierKernel n 𝕜 ε).continuous.aestronglyMeasurable]
  change (∫ x, ‖((sobolevMollifierBump n ε).normed volume x : 𝕜)‖) = 1
  simp_rw [RCLike.norm_ofReal, abs_of_nonneg (ContDiffBump.nonneg_normed _ _)]
  exact ContDiffBump.integral_normed _

theorem mollifierKernel_even {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) (x : Space n) :
    sobolevMollifierKernel n 𝕜 ε (-x) = sobolevMollifierKernel n 𝕜 ε x := by
  change ((sobolevMollifierBump n ε).normed volume (-x) : 𝕜) =
    ((sobolevMollifierBump n ε).normed volume x : 𝕜)
  rw [ContDiffBump.normed_neg]

theorem mollifierKernel_star {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) (x : Space n) :
    star (sobolevMollifierKernel n 𝕜 ε x) = sobolevMollifierKernel n 𝕜 ε x := by
  change star ((sobolevMollifierBump n ε).normed volume x : 𝕜) =
    ((sobolevMollifierBump n ε).normed volume x : 𝕜)
  simp

/-- Canonical even, real-valued, mass-one smoothing at every Sobolev order. -/
def mollifierCLM {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k :=
  wholeConvolutionCLM (sobolevMollifierKernel n 𝕜 ε)

theorem mollifierCLM_contraction {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ)
    (u : WholeH n m 𝕜 k) : ‖mollifierCLM ε u‖ ≤ ‖u‖ := by
  simpa only [mollifierCLM, mollifierKernel_norm_one, one_mul] using
    wholeConvolution_norm_le (sobolevMollifierKernel n 𝕜 ε) u

theorem mollifierCLM_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    ‖mollifierCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜) ε‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by
    simpa only [one_mul] using mollifierCLM_contraction ε u)



/-- For a fixed compact smooth kernel, all finitely many differentiated
kernels have finite L¹ norm; their Euclidean aggregate bounds L²→H^k. -/
def kernelSobolevBound {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (k : ℕ) : ℝ :=
  Real.sqrt (∑ α : SobolevIndex n k, lpNorm (kernelPartial α.val ρ) 1 volume ^ 2)

theorem convolutionToH_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (k : ℕ) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    ‖convolutionToH ρ k f‖ ≤ kernelSobolevBound ρ k * ‖f‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  change ‖(convolutionToH ρ k f).val‖ ^ 2 ≤ (kernelSobolevBound ρ k * ‖f‖) ^ 2
  rw [PiLp.norm_sq_eq_of_L2, mul_pow]
  unfold kernelSobolevBound
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun α _ => sq_nonneg _)), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  change ‖convolutionLp (kernelPartial α.val ρ) f‖ ^ 2 ≤
    lpNorm (kernelPartial α.val ρ) 1 volume ^ 2 * ‖f‖ ^ 2
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg lpNorm_nonneg (norm_nonneg f))).mpr
      (convolutionLp_norm_le (kernelPartial α.val ρ) f)

/-- Convolution with a fixed compact smooth kernel is an actual bounded
linear map from L² into any finite-order canonical Sobolev space. -/
def convolutionToHCLM {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (k : ℕ) :
    P201Specs.Lp 𝕜 (⊤ : Domain n) 2 →L[𝕜] H 𝕜 (⊤ : Domain n) k :=
  LinearMap.mkContinuous
    { toFun := convolutionToH ρ k
      map_add' := by
        intro f g
        apply Subtype.ext
        apply PiLp.ext
        intro α
        exact convolutionLp_add (kernelPartial α.val ρ) f g
      map_smul' := by
        intro c f
        apply Subtype.ext
        apply PiLp.ext
        intro α
        exact convolutionLp_smul (kernelPartial α.val ρ) c f }
    (kernelSobolevBound ρ k) (convolutionToH_norm_le ρ k)

/-- One derivative of smoothing on the original scalar H^k space. -/
def scalarConvolutionGain {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) : H 𝕜 (⊤ : Domain n) k →L[𝕜] H 𝕜 (⊤ : Domain n) (k + 1) :=
  (convolutionToHCLM ρ (k + 1)).comp (P201Specs.hUnderlying ⊤ k)

theorem scalarConvolutionGain_same {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : H 𝕜 (⊤ : Domain n) k) :
    P201Specs.hUnderlying ⊤ (k + 1) (scalarConvolutionGain ρ u) =
      P201Specs.hUnderlying ⊤ k (scalarConvolution ρ u) := by
  change P201Specs.hUnderlying ⊤ (k + 1)
    (convolutionToH ρ (k + 1) (P201Specs.hUnderlying ⊤ k u)) = _
  rw [convolutionToH_underlying]
  rfl

/-- The vector-valued gain map uses the exact Euclidean fiber norm, with a
bound independent of the number of components. -/
def convolutionGain {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 (k + 1) :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 (fun i => scalarConvolutionGain ρ (u i))
      map_add' := by
        intro u v
        apply PiLp.ext
        intro i
        exact map_add _ _ _
      map_smul' := by
        intro c u
        apply PiLp.ext
        intro i
        exact (scalarConvolutionGain (k := k) ρ).map_smul c (u i) }
    ‖scalarConvolutionGain (k := k) ρ‖ (fun u => by
      change ‖WithLp.toLp 2 (fun i : Fin m => scalarConvolutionGain ρ (u i))‖ ≤
        ‖scalarConvolutionGain (k := k) ρ‖ * ‖u‖
      have hS : 0 ≤ ‖scalarConvolutionGain (k := k) ρ‖ := ContinuousLinearMap.opNorm_nonneg _
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hS (norm_nonneg u))).mp
      rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hS (norm_nonneg _))).mpr
          ((scalarConvolutionGain (k := k) ρ).le_opNorm (u i)))

theorem convolutionGain_same {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (u : WholeH n m 𝕜 k) :
    IsLowerOrder (convolutionGain ρ u) (wholeConvolutionCLM ρ u) := by
  intro i
  exact scalarConvolutionGain_same ρ (u i)

/-- The smoothing map gaining one derivative is the same actual section as
the canonical same-order convolution, rather than an unrelated regularizer. -/
theorem convolutionGain_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) :
    lowerOrderCLM.comp (convolutionGain (m := m) (k := k) ρ) = wholeConvolutionCLM ρ := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ k
  exact (lowerOrderCLM_realizes (convolutionGain ρ u) i).symm.trans
    (convolutionGain_same ρ u i)

/-- The canonical even mass-one mollifier, gaining one derivative at fixed ε. -/
def mollifierGainCLM {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 (k + 1) :=
  convolutionGain (sobolevMollifierKernel n 𝕜 ε)

theorem mollifierGainCLM_same {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ε : ℝ) (u : WholeH n m 𝕜 k) :
    IsLowerOrder (mollifierGainCLM ε u) (mollifierCLM ε u) :=
  convolutionGain_same (sobolevMollifierKernel n 𝕜 ε) u

theorem mollifierGainCLM_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    lowerOrderCLM.comp (mollifierGainCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜) ε) =
      mollifierCLM ε := convolutionGain_lowerOrder (sobolevMollifierKernel n 𝕜 ε)


end Mollifiers



namespace MollifierAdjoint
open MeasureTheory.Measure
section Generic
open P102.U2.ApproximateIdentities

variable {G 𝕜 : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [RCLike 𝕜]
    (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [SigmaFinite μ] [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- Opposite translations are inverse on actual L² classes. -/
theorem translate_neg_cancel (y : G) (f : MeasureTheory.Lp 𝕜 2 μ) :
    translate μ y (translate μ (-y) f) = f := by
  unfold translate
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply]
  have heq : (fun x : G => x - -y) ∘ (fun x : G => x - y) = id := by
    ext x
    simp
  simp only [heq, MeasureTheory.Lp.compMeasurePreserving_id_apply]

/-- The L² adjoint of translation by y is translation by -y. -/
theorem inner_translate (y : G) (f g : MeasureTheory.Lp 𝕜 2 μ) :
    inner 𝕜 (translate μ y f) g = inner 𝕜 f (translate μ (-y) g) := by
  let T : MeasureTheory.Lp 𝕜 2 μ →ₗᵢ[𝕜] MeasureTheory.Lp 𝕜 2 μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : G => x - y) (measurePreserving_sub_right μ y)
  have h := T.inner_map_map f (translate μ (-y) g)
  change inner 𝕜 (translate μ y f) (translate μ y (translate μ (-y) g)) = _ at h
  rwa [translate_neg_cancel] at h

private theorem inner_integral_left {F : G → MeasureTheory.Lp 𝕜 2 μ}
    (hF : Integrable F μ) (g : MeasureTheory.Lp 𝕜 2 μ) :
    inner 𝕜 (∫ y, F y ∂μ) g = ∫ y, inner 𝕜 (F y) g ∂μ := by
  have h := congrArg (starRingEnd 𝕜) (integral_inner (𝕜 := 𝕜) hF g)
  rw [← integral_conj] at h
  simpa only [inner_conj_symm] using h.symm

/-- Integrable conjugate-even kernels yield self-adjoint L² convolution.
The weighted-translation integral equals the ordinary convolution L² class. -/
theorem weighted_convolution_selfadjoint {k : G → 𝕜} (hk : Integrable k μ)
    (hkeven : ∀ y, star (k (-y)) = k y) (f g : MeasureTheory.Lp 𝕜 2 μ) :
    inner 𝕜 (∫ y, k y • translate μ y f ∂μ) g =
      inner 𝕜 f (∫ y, k y • translate μ y g ∂μ) := by
  rw [inner_integral_left μ (integrable_weighted_translate μ (by norm_num) f hk)]
  simp_rw [inner_smul_left, inner_translate μ]
  rw [← integral_neg_eq_self]
  simp_rw [starRingEnd_apply, neg_neg, hkeven]
  rw [← integral_inner (integrable_weighted_translate μ (by norm_num) g hk) f]
  congr 1
  funext y
  exact (inner_smul_right _ _ _).symm

end Generic

open P201Specs P201Specs.Hyperbolic.SymmetricSobolevEnergy P102.U4
open P102.U2.ApproximateIdentities

/-- The identity map on functions identifies whole-domain L² with volume L². -/
def wholeLpToVolume {n : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    P201Specs.Lp 𝕜 (⊤ : Domain n) 2 →ₗᵢ[𝕜] MeasureTheory.Lp 𝕜 2 (volume : Measure (Space n)) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ 𝕜 id (by
    simpa only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ] using (MeasurePreserving.id (volume : Measure (Space n))))

theorem wholeLpToVolume_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    wholeLpToVolume f =ᵐ[volume] (f : Space n → 𝕜) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f _

/-- The actual convolution class is the Bochner integral of translations. -/
theorem convolutionLp_toVolume {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (f : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    wholeLpToVolume (convolutionLp ρ f) =
      ∫ y : Space n, ρ y • translate volume y (wholeLpToVolume f) := by
  have hρ : Integrable (ρ : Space n → 𝕜) volume :=
    ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
  rw [integral_translate_eq_convolution volume (by norm_num) (wholeLpToVolume f) hρ]
  apply MeasureTheory.Lp.ext
  have hf : MemLp (f : Space n → 𝕜) 2 volume := by
    simpa only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ] using MeasureTheory.Lp.memLp f
  have h0 := (wholeLpToVolume_ae (convolutionLp ρ f)).trans (convolutionLp_ae ρ f)
  rw [localConvolution_regular_whole (hf.locallyIntegrable (by norm_num))] at h0
  have heq := P102.U2.Young.integralConvolution_congr volume
    (Filter.EventuallyEq.rfl : (ρ : Space n → 𝕜) =ᵐ[volume] ρ)
    (wholeLpToVolume_ae f).symm
  rw [heq] at h0
  exact h0.trans (MemLp.coeFn_toLp _).symm

theorem convolutionLp_selfadjoint {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (hρ : ∀ y, star (ρ (-y)) = ρ y)
    (f g : P201Specs.Lp 𝕜 (⊤ : Domain n) 2) :
    inner 𝕜 (convolutionLp ρ f) g = inner 𝕜 f (convolutionLp ρ g) := by
  let W := wholeLpToVolume (n := n) (𝕜 := 𝕜)
  calc
    _ = inner 𝕜 (W (convolutionLp ρ f)) (W g) := (W.inner_map_map _ _).symm
    _ = inner 𝕜 (W f) (W (convolutionLp ρ g)) := by
      dsimp only [W]
      rw [convolutionLp_toVolume, convolutionLp_toVolume]
      exact weighted_convolution_selfadjoint volume
        (ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport) hρ _ _
    _ = _ := W.inner_map_map _ _

/-- Self-adjointness on H^k follows coordinatewise in the full derivative tuple. -/
theorem scalarConvolutionCLM_inner {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (hρ : ∀ y, star (ρ (-y)) = ρ y)
    (u v : P201Specs.H 𝕜 (⊤ : Domain n) k) :
    inner 𝕜 (scalarConvolutionCLM ρ u) v = inner 𝕜 u (scalarConvolutionCLM ρ v) := by
  change inner 𝕜 (scalarConvolution ρ u).val v.val =
    inner 𝕜 u.val (scalarConvolution ρ v).val
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro α _
  exact convolutionLp_selfadjoint ρ hρ (u.val α) (v.val α)

/-- The Euclidean finite product of the scalar smoothing maps remains self-adjoint. -/
theorem wholeConvolutionCLM_inner {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (hρ : ∀ y, star (ρ (-y)) = ρ y)
    (u v : WholeH n m 𝕜 k) :
    inner 𝕜 (wholeConvolutionCLM ρ u) v = inner 𝕜 u (wholeConvolutionCLM ρ v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact scalarConvolutionCLM_inner ρ hρ (u i) (v i)

theorem mollifierCLM_isSelfAdjoint {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    IsSelfAdjoint (mollifierCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜) ε) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  exact wholeConvolutionCLM_inner (sobolevMollifierKernel n 𝕜 ε)
    (fun y => by rw [mollifierKernel_even, mollifierKernel_star]) u v

end MollifierAdjoint



/-- Actual Friedrichs-regularized solutions, built from the concrete even
mass-one convolution operators, with a uniform exact H^s energy bound. -/
theorem mollified_sobolev_existence :
    ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
      (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T s K A B → ∀ ε : ℝ,
      ∀ (g : WholeH n m 𝕜 s) (f : ℝ → WholeH n m 𝕜 s),
        ContinuousOn f (Icc 0 T) →
      ∃ (Q : ℝ → WholeH n m 𝕜 (s + 1) →L[𝕜] WholeH n m 𝕜 s)
        (u : ℝ → WholeH n m 𝕜 s),
        (∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t)) ∧
        ContinuousOn u (Icc 0 T) ∧ u 0 = mollifierCLM ε g ∧
        ContinuousOn (fun t => mollifierCLM ε (Q t (mollifierGainCLM ε (u t))) +
          mollifierCLM ε (f t)) (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u
          (mollifierCLM ε (Q t (mollifierGainCLM ε (u t))) + mollifierCLM ε (f t))
          (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (C * t) *
          (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  intro n s hn hs K hK
  obtain ⟨C, hC, h⟩ := regularized_sobolev_existence n s hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB ε g f hf
  exact h T hT A B hAB (mollifierCLM ε) (mollifierGainCLM ε)
    (MollifierAdjoint.mollifierCLM_isSelfAdjoint ε) (mollifierCLM_contraction ε)
    (mollifierGainCLM_same ε) g f hf



section MollifierErrors
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
open P102.U4 TopologicalSpace

/-- An actual fixed approximation coefficient; it is independent of fiber dimension.
Only finiteness, not its optimal value, is used in the convergence proof. -/
def scalarGradientBound (n : ℕ) (𝕜 : Type) [RCLike 𝕜] : ℝ :=
  ‖P102.Sobolev.gradientCLM (d := n) (𝕜 := 𝕜) (p := 2)‖ *
    ‖(P201Specs.hToW 𝕜 (⊤ : Domain n) 1).toContinuousLinearMap‖

theorem scalarGradientBound_nonneg (n : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    0 ≤ scalarGradientBound n 𝕜 := mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem scalar_gradientNorm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : H 𝕜 (⊤ : Domain n) 1) :
    P102.Sobolev.gradientNorm (P201Specs.hToW 𝕜 ⊤ 1 u) ≤ scalarGradientBound n 𝕜 * ‖u‖ := by
  change ‖P102.Sobolev.gradientLp (P201Specs.hToW 𝕜 ⊤ 1 u)‖ ≤ _
  rw [← P102.Sobolev.gradientCLM_eq]
  calc
    _ ≤ ‖P102.Sobolev.gradientCLM (d := n) (𝕜 := 𝕜) (p := 2)‖ *
        ‖P201Specs.hToW 𝕜 ⊤ 1 u‖ :=
      (P102.Sobolev.gradientCLM (d := n) (𝕜 := 𝕜) (p := 2)).le_opNorm _
    _ ≤ ‖P102.Sobolev.gradientCLM (d := n) (𝕜 := 𝕜) (p := 2)‖ *
        (‖(P201Specs.hToW 𝕜 (⊤ : Domain n) 1).toContinuousLinearMap‖ * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (P201Specs.hToW 𝕜 (⊤ : Domain n) 1).toContinuousLinearMap.le_opNorm u
    _ = _ := by simp only [scalarGradientBound, mul_assoc]


/-- The pointwise and Bochner versions of real-kernel convolution agree
for every canonical L² input, including complex-valued inputs. -/
theorem wholeLp_convolution_eq_smoothLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (η : WholeTests n ℝ) (ρ : WholeTests n 𝕜) (hρ : ∀ x, ρ x = (η x : 𝕜))
    (u : H 𝕜 (⊤ : Domain n) 1) :
    P102.Sobolev.wholeLp (convolutionLp ρ (P201Specs.hUnderlying ⊤ 1 u)) =
      P102.Sobolev.smoothLp η (P201Specs.hToW 𝕜 ⊤ 1 u) := by
  apply Lp.ext
  have hf : MemLp (P201Specs.hUnderlying ⊤ 1 u : Space n → 𝕜) 2 volume := by
    simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (P201Specs.hUnderlying ⊤ 1 u)
  have hpoint : localConvolution (P201Specs.regularDistribution ⊤ (P201Specs.hUnderlying ⊤ 1 u)) ρ =
      P102.Sobolev.smoothFunction η (P201Specs.hToW 𝕜 ⊤ 1 u) := by
    rw [localConvolution_regular_whole (hf.locallyIntegrable (by norm_num))]
    funext x
    apply integral_congr_ae
    filter_upwards [P102.Sobolev.wholeLp_ae (P201Specs.hUnderlying ⊤ 1 u)] with y hy
    change ρ (x - y) * P201Specs.hUnderlying ⊤ 1 u y =
      η (x - y) • P102.Sobolev.wholeLp (P201Specs.hUnderlying ⊤ 1 u) y
    rw [hρ, hy, RCLike.real_smul_eq_coe_mul]
  filter_upwards [P102.Sobolev.wholeLp_ae (convolutionLp ρ (P201Specs.hUnderlying ⊤ 1 u)),
    convolutionLp_ae ρ (P201Specs.hUnderlying ⊤ 1 u),
    P102.Sobolev.smoothLp_ae (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) η (P201Specs.hToW 𝕜 ⊤ 1 u)]
      with x h1 h2 h3
  rw [h1, h2, h3, hpoint]

/-- Quantitative one-order approximation at the canonical scalar H¹/L²
interface, with an actual finite fixed coefficient. -/
theorem scalar_mollifier_error {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (u : H 𝕜 (⊤ : Domain n) 1) :
    ‖convolutionLp (sobolevMollifierKernel n 𝕜 ε) (P201Specs.hUnderlying ⊤ 1 u) -
        P201Specs.hUnderlying ⊤ 1 u‖ ≤ ε * scalarGradientBound n 𝕜 * ‖u‖ := by
  let η : WholeTests n ℝ :=
    ⟨(sobolevMollifierBump n ε).normed volume,
      (sobolevMollifierBump n ε).contDiff_normed,
      (sobolevMollifierBump n ε).hasCompactSupport_normed, subset_univ _⟩
  have hη : P102.Sobolev.IsProbabilityKernel η :=
    ⟨ContDiffBump.nonneg_normed _, ContDiffBump.integral_normed _⟩
  have hsupp : tsupport η ⊆ Metric.closedBall 0 ε := by
    change tsupport ((sobolevMollifierBump n ε).normed volume) ⊆ _
    rw [ContDiffBump.tsupport_normed_eq]
    simp [sobolevMollifierBump, hε]
  have heq : P102.Sobolev.wholeLp
      (convolutionLp (sobolevMollifierKernel n 𝕜 ε) (P201Specs.hUnderlying ⊤ 1 u)) =
      P102.Sobolev.smoothLp η (P201Specs.hToW 𝕜 ⊤ 1 u) :=
    wholeLp_convolution_eq_smoothLp η _ (fun _ => rfl) u
  have hb := (P102.Sobolev.supported_smoothing hn 2 (by norm_num) ε hε η hη hsupp
    (P201Specs.hToW 𝕜 ⊤ 1 u)).2.2.2.1
  rw [← heq] at hb
  change ‖P102.Sobolev.wholeLpCLM
      (convolutionLp (sobolevMollifierKernel n 𝕜 ε) (P201Specs.hUnderlying ⊤ 1 u)) -
      P102.Sobolev.wholeLpCLM (P201Specs.hUnderlying ⊤ 1 u)‖ ≤ _ at hb
  rw [← map_sub] at hb
  change ‖P102.Sobolev.wholeLp
      (convolutionLp (sobolevMollifierKernel n 𝕜 ε) (P201Specs.hUnderlying ⊤ 1 u) -
      P201Specs.hUnderlying ⊤ 1 u)‖ ≤ _ at hb
  rw [P102.Sobolev.norm_wholeLp] at hb
  exact hb.trans (by nlinarith [scalar_gradientNorm_le u])

/-- Changing only a provably equal natural order is a canonical isometry. -/
def scalarOrderCongr {n a b : ℕ} {𝕜 : Type} [RCLike 𝕜] (h : a = b) :
    H 𝕜 (⊤ : Domain n) a ≃ₗᵢ[𝕜] H 𝕜 (⊤ : Domain n) b := by
  subst b
  exact LinearIsometryEquiv.refl 𝕜 _

theorem scalarOrderCongr_coordinate {n a b : ℕ} {𝕜 : Type} [RCLike 𝕜] (h : a = b)
    (u : H 𝕜 (⊤ : Domain n) a) (α : P102.U4.MultiIndex n) (ha : α.card ≤ a) :
    (scalarOrderCongr h u).val ⟨α, ha.trans_eq h⟩ = u.val ⟨α, ha⟩ := by
  subst b
  rfl

/-- A derivative of order at most k of an H^(k+1) element is an actual H¹
vector; the source Hilbert norm controls its H¹ norm by contraction. -/
def scalarDerivativeToOne {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (β : SobolevIndex n k) (u : H 𝕜 (⊤ : Domain n) (k + 1)) :
    H 𝕜 (⊤ : Domain n) 1 :=
  scalarDerivativeCLM ⊤ β (scalarOrderCongr (Nat.add_comm k 1) u)

theorem scalarDerivativeToOne_norm_le {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (β : SobolevIndex n k) (u : H 𝕜 (⊤ : Domain n) (k + 1)) :
    ‖scalarDerivativeToOne β u‖ ≤ ‖u‖ := by
  exact (scalarDerivative_norm_le ⊤ β _).trans_eq (LinearIsometryEquiv.norm_map _ _)

theorem scalarDerivativeToOne_underlying {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (β : SobolevIndex n k) (u : H 𝕜 (⊤ : Domain n) (k + 1)) :
    P201Specs.hUnderlying ⊤ 1 (scalarDerivativeToOne β u) =
      u.val ⟨β.val, β.property.trans (Nat.le_succ k)⟩ := by
  change (scalarOrderCongr (Nat.add_comm k 1) u).val
    (shiftedIndex β (zeroSobolevIndex n 1)) = _
  have he : shiftedIndex β (zeroSobolevIndex n 1) =
      (⟨β.val, by simpa only [Nat.add_comm] using β.property.trans (Nat.le_succ k)⟩ :
        SobolevIndex n (1 + k)) := Subtype.ext (zero_add β.val)
  rw [he]
  exact scalarOrderCongr_coordinate (Nat.add_comm k 1) u β.val _

theorem scalarLower_coordinate {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : H 𝕜 (⊤ : Domain n) (k + 1)) (β : SobolevIndex n k) :
    (scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u).val β =
      u.val ⟨β.val, β.property.trans (Nat.le_succ k)⟩ := by
  change u.val (shiftedIndex (zeroSobolevIndex n 1) β) = _
  have he : shiftedIndex (zeroSobolevIndex n 1) β =
      (⟨β.val, β.property.trans (Nat.le_succ k)⟩ : SobolevIndex n (k + 1)) := by
    apply Subtype.ext
    exact add_zero β.val
  rw [he]

/-- Each derivative-coordinate error loses precisely one Sobolev derivative. -/
theorem scalar_mollifier_coordinate_error {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (u : H 𝕜 (⊤ : Domain n) (k + 1)) (β : SobolevIndex n k) :
    ‖convolutionLp (sobolevMollifierKernel n 𝕜 ε)
        ((scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u).val β) -
      (scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u).val β‖ ≤
      ε * scalarGradientBound n 𝕜 * ‖u‖ := by
  have hb := scalar_mollifier_error hn ε hε (scalarDerivativeToOne β u)
  rw [scalarDerivativeToOne_underlying] at hb
  rw [scalarLower_coordinate]
  exact hb.trans (mul_le_mul_of_nonneg_left (scalarDerivativeToOne_norm_le β u)
    (mul_nonneg hε.le (scalarGradientBound_nonneg n 𝕜)))

/-- The scalar same-order mollifier error on the one-order inclusion, in the
exact derivative-square norm. -/
theorem scalar_mollifier_error_sq {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (u : H 𝕜 (⊤ : Domain n) (k + 1)) :
    ‖scalarConvolutionCLM (sobolevMollifierKernel n 𝕜 ε)
        (scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u) -
      scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u‖ ^ 2 ≤
      (Fintype.card (SobolevIndex n k) : ℝ) *
        (ε * scalarGradientBound n 𝕜) ^ 2 * ‖u‖ ^ 2 := by
  classical
  change ‖(scalarConvolutionCLM (sobolevMollifierKernel n 𝕜 ε)
        (scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u) -
      scalarDerivativeCLM ⊤ (zeroSobolevIndex n 1) u).val‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _β : SobolevIndex n k, (ε * scalarGradientBound n 𝕜 * ‖u‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro β _
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
        (mul_nonneg hε.le (scalarGradientBound_nonneg n 𝕜)) (norm_nonneg u))).mpr
      exact scalar_mollifier_coordinate_error hn ε hε u β
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow]; ring

/-- Uniform one-order approximation for the canonical vector Sobolev spaces.
The constant is independent of the number of components. -/
theorem mollifier_error_sq {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (u : WholeH n m 𝕜 (k + 1)) :
    ‖mollifierCLM ε (lowerOrderCLM u) - lowerOrderCLM u‖ ^ 2 ≤
      (Fintype.card (SobolevIndex n k) : ℝ) *
        (ε * scalarGradientBound n 𝕜) ^ 2 * ‖u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mollifier_error_sq hn ε hε (u i)

/-- A finite one-order approximation constant for each fixed spatial dimension
and scalar field; it has no fiber-dimension dependence. -/
def mollifierErrorBound (n k : ℕ) (𝕜 : Type) [RCLike 𝕜] : ℝ :=
  Real.sqrt (Fintype.card (SobolevIndex n k) : ℝ) * scalarGradientBound n 𝕜

theorem mollifierErrorBound_nonneg (n k : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    0 ≤ mollifierErrorBound n k 𝕜 :=
  mul_nonneg (Real.sqrt_nonneg _) (scalarGradientBound_nonneg n 𝕜)

/-- The source's O(ε) one-derivative approximation estimate. -/
theorem mollifier_error {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (u : WholeH n m 𝕜 (k + 1)) :
    ‖mollifierCLM ε (lowerOrderCLM u) - lowerOrderCLM u‖ ≤
      ε * mollifierErrorBound n k 𝕜 * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg hε.le (mollifierErrorBound_nonneg n k 𝕜)) (norm_nonneg u))).mp
  have hb := mollifier_error_sq hn ε hε u
  have he : (ε * mollifierErrorBound n k 𝕜 * ‖u‖) ^ 2 =
      (Fintype.card (SobolevIndex n k) : ℝ) *
        (ε * scalarGradientBound n 𝕜) ^ 2 * ‖u‖ ^ 2 := by
    simp only [mollifierErrorBound, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (SobolevIndex n k)))]
    ring
  rwa [he]

/-- Every genuine weak spatial derivative commutes with compact smooth
convolution, as an equality of the canonical Hilbert-space elements. -/
theorem wholeConvolution_derivative {n m k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : WholeTests n 𝕜) (β : SobolevIndex n l) (u : WholeH n m 𝕜 (k + l)) :
    wholeDerivativeCLM (k := k) β (wholeConvolutionCLM ρ u) =
      wholeConvolutionCLM ρ (wholeDerivativeCLM (k := k) β u) := by
  apply PiLp.ext
  intro i
  apply Subtype.ext
  apply PiLp.ext
  intro α
  rfl

theorem mollifier_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ε : ℝ) (u : WholeH n m 𝕜 (k + 1)) :
    lowerOrderCLM (mollifierCLM ε u) = mollifierCLM ε (lowerOrderCLM u) :=
  wholeConvolution_derivative _ (zeroSobolevIndex n 1) u

theorem mollifier_partial {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ε : ℝ) (j : Fin n) (u : WholeH n m 𝕜 (k + 1)) :
    partialCLM j (mollifierCLM ε u) = mollifierCLM ε (partialCLM j u) :=
  wholeConvolution_derivative _ (⟨{j}, by simp⟩ : SobolevIndex n 1) u


end MollifierErrors


/-- Convolution commutes with the genuine order-lowering inclusion. -/
theorem mollifierCLM_lowerOrder_commute {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    lowerOrderCLM.comp (mollifierCLM (n := n) (m := m) (k := k + 1) (𝕜 := 𝕜) ε) =
      (mollifierCLM ε).comp lowerOrderCLM := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ k
  change hUnderlying ⊤ k (lowerOrderCLM (mollifierCLM ε u) i) =
    hUnderlying ⊤ k (mollifierCLM ε (lowerOrderCLM u) i)
  rw [← lowerOrderCLM_realizes (mollifierCLM ε u) i]
  change convolutionLp _ (hUnderlying ⊤ (k + 1) (u i)) =
    convolutionLp _ (hUnderlying ⊤ k (lowerOrderCLM u i))
  rw [← lowerOrderCLM_realizes u i]

/-- Smoothing after lowering the input realizes smoothing at the higher order. -/
theorem mollifierGainCLM_lower_input {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    (mollifierGainCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜) ε).comp lowerOrderCLM =
      mollifierCLM ε := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ (k + 1)
  change hUnderlying ⊤ (k + 1) (mollifierGainCLM ε (lowerOrderCLM u) i) =
    hUnderlying ⊤ (k + 1) (mollifierCLM ε u i)
  rw [mollifierGainCLM_same ε (lowerOrderCLM u) i]
  change convolutionLp _ (hUnderlying ⊤ k (lowerOrderCLM u i)) =
    convolutionLp _ (hUnderlying ⊤ (k + 1) (u i))
  rw [← lowerOrderCLM_realizes u i]




section FurtherConstruction
set_option maxHeartbeats 1000000

/-- The actual one-derivative approximation bound as an operator norm. -/
theorem mollifier_error_comp_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ‖((mollifierCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜) ε) -
        ContinuousLinearMap.id 𝕜 _).comp lowerOrderCLM‖ ≤
      ε * mollifierErrorBound n k 𝕜 := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hε.le (mollifierErrorBound_nonneg n k 𝕜))
  intro u
  simpa only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply] using mollifier_error hn ε hε u

/-- The same error after lowering the output rather than the input. -/
theorem mollifier_lower_error_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ‖lowerOrderCLM.comp ((mollifierCLM (n := n) (m := m) (k := k + 1) (𝕜 := 𝕜) ε) -
        ContinuousLinearMap.id 𝕜 _)‖ ≤ ε * mollifierErrorBound n k 𝕜 := by
  have he : lowerOrderCLM.comp ((mollifierCLM (n := n) (m := m) (k := k + 1) (𝕜 := 𝕜) ε) -
        ContinuousLinearMap.id 𝕜 _) =
      ((mollifierCLM ε) - ContinuousLinearMap.id 𝕜 _).comp lowerOrderCLM := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub,
      ContinuousLinearMap.id_apply, mollifier_lowerOrder]
  rw [he]
  exact mollifier_error_comp_norm_le hn hε

/-- Gain smoothing also commutes with lowering the spatial order. -/
theorem mollifierGainCLM_order_compatible {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) :
    lowerOrderCLM.comp (mollifierGainCLM (n := n) (m := m) (k := k + 1) (𝕜 := 𝕜) ε) =
      (mollifierGainCLM ε).comp lowerOrderCLM := by
  rw [mollifierGainCLM_lowerOrder, mollifierGainCLM_lower_input]

/-- Actual adjacent-order P-realizations yield compatible regularized ODE
operators, so a high-order ODE lowers to the same lower-order ODE. -/
theorem mollified_operator_order_compatible {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k}
    {P : WholeH n m 𝕜 (k + 1 + 1) →L[𝕜] WholeH n m 𝕜 (k + 1)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P) (ε : ℝ) :
    lowerOrderCLM.comp ((mollifierCLM ε).comp (P.comp (mollifierGainCLM ε))) =
      ((mollifierCLM ε).comp (Q.comp (mollifierGainCLM ε))).comp lowerOrderCLM := by
  have hc := TopOperator.operator_order_compatible hQ hP
  have hcv (v : WholeH n m 𝕜 (k + 1 + 1)) :
      lowerOrderCLM (P v) = Q (lowerOrderCLM v) := by
    exact (congrArg (fun R => R v) hc).symm
  have hgain (v : WholeH n m 𝕜 (k + 1)) :
      lowerOrderCLM (mollifierGainCLM ε v) = mollifierGainCLM ε (lowerOrderCLM v) :=
    congrArg (fun R => R v) (mollifierGainCLM_order_compatible ε)
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  rw [mollifier_lowerOrder, hcv, hgain]

/-- The elementwise adjacent-order identity for the actual regularized RHS. -/
theorem mollified_operator_lower_apply {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k}
    {P : WholeH n m 𝕜 (k + 1 + 1) →L[𝕜] WholeH n m 𝕜 (k + 1)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P) (ε : ℝ)
    (u : WholeH n m 𝕜 (k + 1)) :
    lowerOrderCLM (mollifierCLM ε (P (mollifierGainCLM ε u))) =
      mollifierCLM ε (Q (mollifierGainCLM ε (lowerOrderCLM u))) :=
  congrArg (fun R => R u) (mollified_operator_order_compatible hQ hP ε)



/-- A fixed top-order P-family produces an actual full sequence of mollified
solutions, all with the same quantitative high-order bound. -/
theorem exists_mollified_sequence {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (Q : ℝ → WholeH n m 𝕜 (s + 1) →L[𝕜] WholeH n m 𝕜 s)
    (hQ : ∀ t ∈ Icc 0 T, ‖Q t‖ ≤ C)
    (hQc : ∀ v, ContinuousOn (fun t => Q t v) (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, ∀ (v : WholeH n m 𝕜 (s + 1)) (w : WholeH n m 𝕜 s),
      IsLowerOrder v w → |RCLike.re (inner 𝕜 w (Q t v))| ≤ C * ‖w‖ ^ 2)
    (e : ℕ → ℝ) (g : WholeH n m 𝕜 s) (f : ℝ → WholeH n m 𝕜 s)
    (hf : ContinuousOn f (Icc 0 T)) :
    ∃ U : ℕ → ℝ → WholeH n m 𝕜 s, ∀ i,
      ContinuousOn (U i) (Icc 0 T) ∧ U i 0 = mollifierCLM (e i) g ∧
      ContinuousOn (fun t => mollifierCLM (e i) (Q t (mollifierGainCLM (e i) (U i t))) +
        mollifierCLM (e i) (f t)) (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (U i)
        (mollifierCLM (e i) (Q t (mollifierGainCLM (e i) (U i t))) + mollifierCLM (e i) (f t))
        (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖U i t‖ ≤ Real.exp (C * t) *
        (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  letI : InnerProductSpace 𝕜 (WholeH n m 𝕜 s) :=
    PiLp.innerProductSpace (fun _ : Fin m => H 𝕜 (⊤ : Domain n) s)
  letI : NormedSpace ℝ (WholeH n m 𝕜 s) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) s)
  have hex (i : ℕ) := RegularizedEnergy.exists_solution (𝕜 := 𝕜)
    (E := WholeH n m 𝕜 s) (F := WholeH n m 𝕜 (s + 1))
    (mollifierCLM (e i)) (mollifierGainCLM (e i))
    (MollifierAdjoint.mollifierCLM_isSelfAdjoint (e i)) (mollifierCLM_contraction (e i))
    hT hC hC Q hQ hQc
    (fun t ht v => (le_abs_self _).trans
      (hp t ht _ _ (mollifierGainCLM_same (e i) v))) f hf g
  choose U hU using hex
  exact ⟨U, hU⟩

/-- The high-order quantitative bound is continuous on the source time interval. -/
theorem continuousOn_energy_bound {X : Type*} [NormedAddCommGroup X]
    {T : ℝ} (hT : 0 ≤ T) (C : ℝ) (g : X) (f : ℝ → X)
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t => Real.exp (C * t) * (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖))
      (Icc 0 T) := by
  have hfi : IntegrableOn (fun r => ‖f r‖) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT] using hf.norm.integrableOn_Icc
  have hi := intervalIntegral.continuousOn_primitive_interval hfi
  rw [uIcc_of_le hT] at hi
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
    (continuousOn_const.add hi)

/-- Compact-time continuity gives a finite nonnegative uniform bound. -/
theorem exists_nonneg_uniform_bound {X : Type*} [NormedAddCommGroup X]
    {T : ℝ} (u : ℝ → X) (hu : ContinuousOn u (Icc 0 T)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ‖u t‖ ≤ M := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hu.norm
  exact ⟨max B 0, le_max_right _ _, fun t ht =>
    (hB (mem_image_of_mem _ ht)).trans (le_max_left _ _)⟩


end FurtherConstruction



section FinalApproximationBridges
set_option maxHeartbeats 1000000

/-- Pointwise two-derivative consistency with the actual unregularized P. -/
theorem mollified_consistency_apply_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k}
    {P : WholeH n m 𝕜 (k + 1 + 1) →L[𝕜] WholeH n m 𝕜 (k + 1)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P)
    (hbQ : ‖Q‖ ≤ C) (hbP : ‖P‖ ≤ C) (u : WholeH n m 𝕜 (k + 1 + 1)) :
    ‖mollifierCLM ε (lowerOrderCLM (P (mollifierCLM ε u))) - lowerOrderCLM (P u)‖ ≤
      C * (ε * mollifierErrorBound n k 𝕜 + ε * mollifierErrorBound n (k + 1) 𝕜) * ‖u‖ := by
  let a : WholeH n m 𝕜 (k + 1 + 1) := mollifierCLM ε u
  have hc (v : WholeH n m 𝕜 (k + 1 + 1)) :
      Q (lowerOrderCLM v) = lowerOrderCLM (P v) :=
    congrArg (fun R => R v) (TopOperator.operator_order_compatible hQ hP)
  have hPa : ‖P a‖ ≤ C * ‖u‖ := by
    exact (P.le_opNorm a).trans
      (mul_le_mul hbP (mollifierCLM_contraction ε u) (norm_nonneg a) hC)
  have hfirst : ‖mollifierCLM ε (lowerOrderCLM (P a)) - lowerOrderCLM (P a)‖ ≤
      ε * mollifierErrorBound n k 𝕜 * (C * ‖u‖) :=
    (mollifier_error hn ε hε (P a)).trans
      (mul_le_mul_of_nonneg_left hPa (mul_nonneg hε.le (mollifierErrorBound_nonneg n k 𝕜)))
  have hsmall : ‖lowerOrderCLM (a - u)‖ ≤ ε * mollifierErrorBound n (k + 1) 𝕜 * ‖u‖ := by
    simpa only [a, map_sub, mollifier_lowerOrder] using mollifier_error hn ε hε u
  have hsecond : ‖Q (lowerOrderCLM (a - u))‖ ≤
      C * (ε * mollifierErrorBound n (k + 1) 𝕜 * ‖u‖) :=
    (Q.le_opNorm _).trans (mul_le_mul hbQ hsmall (norm_nonneg _) hC)
  have he : mollifierCLM ε (lowerOrderCLM (P a)) - lowerOrderCLM (P u) =
      (mollifierCLM ε (lowerOrderCLM (P a)) - lowerOrderCLM (P a)) +
        Q (lowerOrderCLM (a - u)) := by
    rw [hc, map_sub, map_sub]
    abel
  change ‖mollifierCLM ε (lowerOrderCLM (P a)) - lowerOrderCLM (P u)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

/-- The same consistency estimate in operator norm. -/
theorem mollified_consistency_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k}
    {P : WholeH n m 𝕜 (k + 1 + 1) →L[𝕜] WholeH n m 𝕜 (k + 1)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P)
    (hbQ : ‖Q‖ ≤ C) (hbP : ‖P‖ ≤ C) :
    ‖(mollifierCLM ε).comp (lowerOrderCLM.comp (P.comp (mollifierCLM ε))) -
        lowerOrderCLM.comp P‖ ≤
      C * (ε * mollifierErrorBound n k 𝕜 + ε * mollifierErrorBound n (k + 1) 𝕜) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (add_nonneg
    (mul_nonneg hε.le (mollifierErrorBound_nonneg n k 𝕜))
    (mul_nonneg hε.le (mollifierErrorBound_nonneg n (k + 1) 𝕜))))
  intro u
  exact mollified_consistency_apply_le hn hε hC hQ hP hbQ hbP u



/-- Lowering the genuine high regularized right hand side twice gives the
same regularized operator at the lower Sobolev order. -/
theorem mollified_rhs_two_lower {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q}
    {P : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 (q + 1)}
    {S : WholeH n m 𝕜 (q + 2 + 1) →L[𝕜] WholeH n m 𝕜 (q + 2)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P) (hS : RealizesP A B S)
    (ε : ℝ) (u f : WholeH n m 𝕜 (q + 2)) :
    lowerOrderCLM (lowerOrderCLM
      (mollifierCLM ε (S (mollifierGainCLM ε u)) + mollifierCLM ε f)) =
    mollifierCLM ε (Q (mollifierGainCLM ε (lowerOrderCLM (lowerOrderCLM u)))) +
      mollifierCLM ε (lowerOrderCLM (lowerOrderCLM f)) := by
  simp only [map_add]
  rw [mollified_operator_lower_apply hP hS,
    mollified_operator_lower_apply hQ hP, mollifier_lowerOrder, mollifier_lowerOrder]

/-- The actual high-order ODE supplies the lower-order strong derivative,
with the canonical real scalar structures and closed-interval endpoints. -/
theorem lower_mollified_derivative {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T t : ℝ} {A : Fin n → Space n → Operator m 𝕜} {B : Space n → Operator m 𝕜}
    {Q : WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q}
    {P : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 (q + 1)}
    {S : WholeH n m 𝕜 (q + 2 + 1) →L[𝕜] WholeH n m 𝕜 (q + 2)}
    (hQ : RealizesP A B Q) (hP : RealizesP A B P) (hS : RealizesP A B S)
    (ε : ℝ) (U : ℝ → WholeH n m 𝕜 (q + 2)) (f : WholeH n m 𝕜 (q + 2))
    (hd : HasDerivWithinAt U
      (mollifierCLM ε (S (mollifierGainCLM ε (U t))) + mollifierCLM ε f) (Icc 0 T) t) :
    HasDerivWithinAt (fun r => lowerOrderCLM (lowerOrderCLM (U r)))
      (mollifierCLM ε (Q (mollifierGainCLM ε (lowerOrderCLM (lowerOrderCLM (U t))))) +
        mollifierCLM ε (lowerOrderCLM (lowerOrderCLM f))) (Icc 0 T) t := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 (q + 2)) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) (q + 2))
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => H 𝕜 (⊤ : Domain n) q)
  let F : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 q :=
    lowerOrderCLM.comp lowerOrderCLM
  have h := (F.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  exact h.congr_deriv (mollified_rhs_two_lower hQ hP hS ε (U t) f)


end FinalApproximationBridges



namespace ActualLimit
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricApproximation
open P201.Hyperbolic.SymmetricSobolevEnergy

section UniformRHS
variable {𝕜 X Y D I : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Uniform convergence is preserved by a uniformly bounded time-dependent
operator family and an error tending uniformly to zero. -/
theorem uniform_rhs_of_error {l : Filter I} (Q : D → X →L[𝕜] Y) (S : Set D)
    {C : ℝ} (hC : 0 ≤ C) (hQ : ∀ t ∈ S, ‖Q t‖ ≤ C)
    (v : I → D → X) (u : D → X) (f : D → Y) (c : I → D → Y)
    (e : I → ℝ) (he : Tendsto e l (𝓝 0))
    (hv : TendstoUniformlyOn v u l S)
    (hc : ∀ i t, t ∈ S → ‖c i t - (Q t (v i t) + f t)‖ ≤ e i) :
    TendstoUniformlyOn c (fun t => Q t (u t) + f t) l S := by
  rw [Metric.tendstoUniformlyOn_iff] at hv ⊢
  intro ε hε
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < (ε / 2) / (C + 1) := div_pos (by linarith) hden
  filter_upwards [(tendsto_order.mp he).2 (ε / 2) (by linarith),
    hv ((ε / 2) / (C + 1)) hδ] with i hi hiv
  intro t ht
  rw [dist_eq_norm, norm_sub_rev]
  have hdiff : ‖v i t - u t‖ < (ε / 2) / (C + 1) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hiv t ht
  have hop : ‖Q t (v i t - u t)‖ ≤ C * ‖v i t - u t‖ :=
    (Q t).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right (hQ t ht) (norm_nonneg _))
  have heq : c i t - (Q t (u t) + f t) =
      (c i t - (Q t (v i t) + f t)) + Q t (v i t - u t) := by
    rw [map_sub]
    abel
  rw [heq]
  have hsmall : C * ((ε / 2) / (C + 1)) < ε / 2 := by
    have heq' := div_mul_cancel₀ (ε / 2) hden.ne'
    nlinarith
  exact (norm_add_le _ _).trans_lt
    ((add_le_add (hc i t ht) (hop.trans
      (mul_le_mul_of_nonneg_left hdiff.le hC))).trans_lt (by linarith))
end UniformRHS

/-- The one-step canonical order inclusion agrees with the direct truncation. -/
theorem lowerOrder_eq_truncate {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    (lowerOrderCLM : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k) =
      truncate (Nat.le_succ k) := by
  apply ContinuousLinearMap.ext
  intro v
  apply sameSection_injective
  exact sameSection_trans (sameSection_symm (lowerOrderCLM_realizes v))
    (fun i => rfl)

/-- Two adjacent canonical inclusions agree with direct truncation. -/
theorem lowerOrder_twice_eq_truncate {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    (lowerOrderCLM : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k).comp
      (lowerOrderCLM : WholeH n m 𝕜 (k + 2) →L[𝕜] WholeH n m 𝕜 (k + 1)) =
      truncate (by omega : k ≤ k + 2) := by
  apply ContinuousLinearMap.ext
  intro v
  apply sameSection_injective
  exact sameSection_trans
    (sameSection_symm (sameSection_trans (lowerOrderCLM_realizes v)
      (lowerOrderCLM_realizes (lowerOrderCLM v)))) (fun i => rfl)

/-- Pointwise actual high bounds and a converging sequence of lower integral
equations construct the whole intermediate solution and its weak high lift. -/
theorem limit_of_lower_integral_equations {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) {T : ℝ} (hT : 0 ≤ T)
    (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜)
    (Q : ℝ → WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q)
    (C : ℝ) (hQ : ∀ t ∈ Icc 0 T,
      RealizesP (fun j => A j t) (B t) (Q t) ∧ ‖Q t‖ ≤ C)
    (hQc : ∀ x, ContinuousOn (fun t => Q t x) (Icc 0 T))
    (g : WholeH n m 𝕜 (q + 2)) (f : ℝ → WholeH n m 𝕜 (q + 2))
    (hf : ContinuousOn f (Icc 0 T))
    (eps : ℕ → ℝ) (heps : ∀ i, 0 < eps i) (heps0 : Tendsto eps atTop (𝓝 0))
    (U : ℕ → ℝ → WholeH n m 𝕜 (q + 2))
    (hinit : ∀ i, U i 0 = mollifierCLM (eps i) g)
    (u : ℝ → WholeH n m 𝕜 (q + 1)) (hu : ContinuousOn u (Icc 0 T))
    (hmid : TendstoUniformlyOn (fun i t => lowerOrderCLM (U i t)) u atTop (Icc 0 T))
    (R : ℝ → ℝ) (hR : ContinuousOn R (Icc 0 T))
    (hbound : ∀ i t, t ∈ Icc 0 T → ‖U i t‖ ≤ R t)
    (cs : ℕ → ℝ → WholeH n m 𝕜 q)
    (hcs : ∀ i, ContinuousOn (cs i) (Icc 0 T))
    (hcslim : TendstoUniformlyOn cs
      (fun t => Q t (u t) + truncate (by omega : q ≤ q + 2) (f t)) atTop (Icc 0 T))
    (heq : ∀ i t, t ∈ Icc 0 T →
      lowerOrderCLM (lowerOrderCLM (U i t)) =
        lowerOrderCLM (lowerOrderCLM (U i 0)) + ∫ r in (0 : ℝ)..t, cs i r) :
    ∃ (V : ℝ → WholeH n m 𝕜 (q + 2)) (w du : ℝ → WholeH n m 𝕜 q),
      IsIntermediateSolution T A B f u w du ∧
      (∀ t ∈ Icc 0 T, SameSection (V t) (u t)) ∧ V 0 = g ∧
      (∀ L : WholeH n m 𝕜 (q + 2) →L[𝕜] 𝕜,
        ContinuousOn (fun t => L (V t)) (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖V t‖ ≤ R t := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => P201Specs.H 𝕜 (⊤ : Domain n) q)
  let L : WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q := lowerOrderCLM
  let F : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 q := L.comp lowerOrderCLM
  let c : ℝ → WholeH n m 𝕜 q :=
    fun t => Q t (u t) + truncate (by omega : q ≤ q + 2) (f t)
  have hc : ContinuousOn c (Icc 0 T) :=
    (continuousOn_apply_of_strongly_continuous Q (Icc 0 T) C
      (fun t ht => (hQ t ht).2) hQc u hu).add
      ((truncate (by omega : q ≤ q + 2)).continuous.comp_continuousOn hf)
  have hlow : ∀ t ∈ Icc 0 T,
      Tendsto (fun i => F (U i t)) atTop (𝓝 (L (u t))) := by
    intro t ht
    exact (L.continuous.tendsto _).comp (hmid.tendsto_at ht)
  have hi := IntegralLimit.integral_equation_of_tendsto hT hc hcs
    (hlow 0 ⟨le_rfl, hT⟩) hlow hcslim heq
  have hi' : ∀ t ∈ Icc 0 T,
      truncate (Nat.le_succ q) (u t) = truncate (Nat.le_succ q) (u 0) +
        ∫ r in (0 : ℝ)..t, Q r (u r) + truncate (by omega : q ≤ q + 2) (f r) := by
    simpa only [L, lowerOrder_eq_truncate, c] using hi
  have hsol := intermediate_of_integral Q C hQ hQc f hf u hu hi'
  have hinitlim : Tendsto (fun i => lowerOrderCLM (U i 0)) atTop
      (𝓝 (lowerOrderCLM g : WholeH n m 𝕜 (q + 1))) := by
    have hz : Tendsto (fun i => lowerOrderCLM (U i 0) - lowerOrderCLM g)
        atTop (𝓝 0) := by
      apply squeeze_zero_norm' (a := fun i =>
        eps i * mollifierErrorBound n (q + 1) 𝕜 * ‖g‖)
      · apply Eventually.of_forall
        intro i
        rw [hinit i, mollifier_lowerOrder]
        exact mollifier_error hn (eps i) (heps i) g
      · simpa only [zero_mul] using
          (heps0.mul_const (mollifierErrorBound n (q + 1) 𝕜)).mul_const ‖g‖
    simpa only [sub_add_cancel, zero_add] using hz.add_const (lowerOrderCLM g)
  have hu0 : u 0 = lowerOrderCLM g :=
    tendsto_nhds_unique (hmid.tendsto_at ⟨le_rfl, hT⟩) hinitlim
  have hsame0 : SameSection g (u 0) := by
    rw [hu0]
    exact lowerOrderCLM_realizes g
  obtain ⟨V, hVu, hV0, hVb, hVc⟩ := bounded_sobolev_limit T hT g U
    (fun i t => lowerOrderCLM (U i t)) u R hu hR hsame0 hbound
    (fun i t ht => lowerOrderCLM_realizes (U i t))
    (fun t ht => hmid.tendsto_at ht)
  exact ⟨V, _, _, hsol, hVu, hV0, hVc, hVb⟩

/-- Actual Friedrichs curves with the established bounds and a middle-norm
uniform limit yield the required PDE solution, high bound, and weak continuity. -/
theorem actual_mollified_limit {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 0 < n) {T : ℝ} (hT : 0 ≤ T)
    (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜)
    (Q : ℝ → WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q)
    (P : ℝ → WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 (q + 1))
    (S : ℝ → WholeH n m 𝕜 (q + 2 + 1) →L[𝕜] WholeH n m 𝕜 (q + 2))
    {C : ℝ} (hC : 0 ≤ C)
    (hQ : ∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t) ∧ ‖Q t‖ ≤ C)
    (hP : ∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (P t) ∧ ‖P t‖ ≤ C)
    (hS : ∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (S t))
    (hQc : ∀ x, ContinuousOn (fun t => Q t x) (Icc 0 T))
    (g : WholeH n m 𝕜 (q + 2)) (f : ℝ → WholeH n m 𝕜 (q + 2))
    (hf : ContinuousOn f (Icc 0 T))
    (eps : ℕ → ℝ) (heps : ∀ i, 0 < eps i) (heps0 : Tendsto eps atTop (𝓝 0))
    (U : ℕ → ℝ → WholeH n m 𝕜 (q + 2))
    (hUc : ∀ i, ContinuousOn (U i) (Icc 0 T))
    (hinit : ∀ i, U i 0 = mollifierCLM (eps i) g)
    (hduc : ∀ i, ContinuousOn (fun t =>
      mollifierCLM (eps i) (S t (mollifierGainCLM (eps i) (U i t))) +
        mollifierCLM (eps i) (f t)) (Icc 0 T))
    (hd : ∀ i t, t ∈ Icc 0 T → HasDerivWithinAt (U i)
      (mollifierCLM (eps i) (S t (mollifierGainCLM (eps i) (U i t))) +
        mollifierCLM (eps i) (f t)) (Icc 0 T) t)
    (u : ℝ → WholeH n m 𝕜 (q + 1)) (hu : ContinuousOn u (Icc 0 T))
    (hmid : TendstoUniformlyOn (fun i t => lowerOrderCLM (U i t)) u atTop (Icc 0 T))
    (R : ℝ → ℝ) (hR : ContinuousOn R (Icc 0 T))
    (hbound : ∀ i t, t ∈ Icc 0 T → ‖U i t‖ ≤ R t)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hUM : ∀ i t, t ∈ Icc 0 T → ‖U i t‖ ≤ M)
    (hfN : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ N) :
    ∃ (V : ℝ → WholeH n m 𝕜 (q + 2)) (w du : ℝ → WholeH n m 𝕜 q),
      IsIntermediateSolution T A B f u w du ∧
      (∀ t ∈ Icc 0 T, SameSection (V t) (u t)) ∧ V 0 = g ∧
      (∀ L : WholeH n m 𝕜 (q + 2) →L[𝕜] 𝕜,
        ContinuousOn (fun t => L (V t)) (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖V t‖ ≤ R t := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => P201Specs.H 𝕜 (⊤ : Domain n) q)
  letI : NormedSpace ℝ (WholeH n m 𝕜 (q + 2)) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m => P201Specs.H 𝕜 (⊤ : Domain n) (q + 2))
  let L : WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q := lowerOrderCLM
  let H : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 (q + 1) := lowerOrderCLM
  let F := L.comp H
  let ds : ℕ → ℝ → WholeH n m 𝕜 (q + 2) := fun i t =>
    mollifierCLM (eps i) (S t (mollifierGainCLM (eps i) (U i t))) +
      mollifierCLM (eps i) (f t)
  let cs : ℕ → ℝ → WholeH n m 𝕜 q := fun i t => F (ds i t)
  have hcs : ∀ i, ContinuousOn (cs i) (Icc 0 T) :=
    fun i => F.continuous.comp_continuousOn (hduc i)
  have hFJ (ε : ℝ) (v : WholeH n m 𝕜 (q + 2)) :
      F (mollifierCLM ε v) = mollifierCLM ε (F v) := by
    simp only [F, L, H, ContinuousLinearMap.comp_apply, mollifier_lowerOrder]
  have hkey (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      cs i t = mollifierCLM (eps i) (L (P t (mollifierCLM (eps i) (U i t)))) +
        mollifierCLM (eps i) (F (f t)) := by
    dsimp only [cs, ds]
    rw [map_add]
    congr 1
    · change lowerOrderCLM (lowerOrderCLM
        (mollifierCLM (eps i) (S t (mollifierGainCLM (eps i) (U i t))))) = _
      rw [mollified_operator_lower_apply (hP t ht).1 (hS t ht)]
      have hg := congrArg (fun K => K (U i t))
        (mollifierGainCLM_lower_input (n := n) (m := m) (k := q + 1) (𝕜 := 𝕜) (eps i))
      simp only [ContinuousLinearMap.comp_apply] at hg
      rw [hg, mollifier_lowerOrder]
  let D : ℝ := C * (mollifierErrorBound n q 𝕜 + mollifierErrorBound n (q + 1) 𝕜) * M +
    mollifierErrorBound n q 𝕜 * N
  have herror : ∀ i t, t ∈ Icc 0 T →
      ‖cs i t - (Q t (H (U i t)) + F (f t))‖ ≤ eps i * D := by
    intro i t ht
    let E : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 q :=
      (mollifierCLM (eps i)).comp (L.comp ((P t).comp (mollifierCLM (eps i)))) - L.comp (P t)
    have hEn : ‖E‖ ≤ C * (eps i * mollifierErrorBound n q 𝕜 +
        eps i * mollifierErrorBound n (q + 1) 𝕜) :=
      mollified_consistency_norm_le hn (heps i) hC (hQ t ht).1 (hP t ht).1
        (hQ t ht).2 (hP t ht).2
    have hEU := E.le_of_opNorm_le_of_le hEn (hUM i t ht)
    have hcompat : Q t (H (U i t)) = L (P t (U i t)) :=
      congrArg (fun K => K (U i t)) (TopOperator.operator_order_compatible (hQ t ht).1 (hP t ht).1)
    have hEq : cs i t - (Q t (H (U i t)) + F (f t)) =
        E (U i t) + (mollifierCLM (eps i) (F (f t)) - F (f t)) := by
      rw [hkey i t ht, hcompat]
      simp only [E, sub_apply, ContinuousLinearMap.comp_apply]
      abel
    have hHnorm : ‖H (f t)‖ ≤ N := by
      have hb : ‖H (f t)‖ ≤ ‖f t‖ := by
        simpa only [one_mul] using H.le_of_opNorm_le
          (wholeDerivativeCLM_norm_le (P102.U4.zeroSobolevIndex n 1)) (f t)
      exact hb.trans (hfN t ht)
    have hsource : ‖mollifierCLM (eps i) (F (f t)) - F (f t)‖ ≤
        eps i * mollifierErrorBound n q 𝕜 * N := by
      exact (mollifier_error hn (eps i) (heps i) (H (f t))).trans
        (mul_le_mul_of_nonneg_left hHnorm
          (mul_nonneg (heps i).le (mollifierErrorBound_nonneg n q 𝕜)))
    rw [hEq]
    calc
      _ ≤ ‖E (U i t)‖ + ‖mollifierCLM (eps i) (F (f t)) - F (f t)‖ := norm_add_le _ _
      _ ≤ C * (eps i * mollifierErrorBound n q 𝕜 +
          eps i * mollifierErrorBound n (q + 1) 𝕜) * M +
          eps i * mollifierErrorBound n q 𝕜 * N := add_le_add hEU hsource
      _ = eps i * D := by dsimp [D]; ring
  have herror0 : Tendsto (fun i => eps i * D) atTop (𝓝 0) := by
    simpa only [zero_mul] using heps0.mul_const D
  have hcslim := uniform_rhs_of_error Q (Icc 0 T) hC (fun t ht => (hQ t ht).2)
    (fun i t => H (U i t)) u (fun t => F (f t)) cs (fun i => eps i * D)
    herror0 hmid herror
  have heq : ∀ i t, t ∈ Icc 0 T → F (U i t) = F (U i 0) +
      ∫ r in (0 : ℝ)..t, cs i r := by
    intro i t ht
    have hEq := integral_equation_of_derivative (U i) (ds i) (hUc i) (hduc i) (hd i) t ht
    have hi := congrArg F hEq
    rw [map_add, ← F.intervalIntegral_comp_comm
      (((hduc i).mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1)] at hi
    exact hi
  apply limit_of_lower_integral_equations hn hT A B Q C hQ hQc g f hf eps heps heps0 U hinit
    u hu hmid R hR hbound cs hcs
  · simpa only [F, L, H, lowerOrder_twice_eq_truncate] using hcslim
  · exact heq

end ActualLimit



namespace ActualCauchy
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201.Hyperbolic.SymmetricSobolevEnergy
open P201.Hyperbolic.SymmetricApproximation

variable {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- The actual regularized low coefficient. -/
def lowCoefficient (Q : (WholeH n m 𝕜 (q + 1)) →L[𝕜] (WholeH n m 𝕜 q)) (ε : ℝ) : (WholeH n m 𝕜 q) →L[𝕜] (WholeH n m 𝕜 q) :=
  (mollifierCLM (k:=q) ε).comp (Q.comp (mollifierGainCLM (k:=q) ε))

/-- The same coefficient, restricted to high-order inputs. -/
def highCoefficient (Q : (WholeH n m 𝕜 (q + 2)) →L[𝕜] (WholeH n m 𝕜 (q + 1))) (ε : ℝ) : (WholeH n m 𝕜 (q + 2)) →L[𝕜] (WholeH n m 𝕜 q) :=
  (mollifierCLM (k:=q) ε).comp ((lowerOrderCLM (k:=q)).comp (Q.comp (mollifierCLM (k:=q+2) ε)))

/-- Actual scale compatibility identifies the low equation on high inputs. -/
theorem lowCoefficient_two_lower
    (Q : (WholeH n m 𝕜 (q + 1)) →L[𝕜] (WholeH n m 𝕜 q))
    (P : (WholeH n m 𝕜 (q + 2)) →L[𝕜] (WholeH n m 𝕜 (q + 1)))
    (hcompat : Q.comp (lowerOrderCLM (k:=q+1)) = (lowerOrderCLM (k:=q)).comp P) (ε : ℝ) :
    (lowCoefficient Q ε).comp ((lowerOrderCLM (k:=q)).comp (lowerOrderCLM (k:=q+1))) = highCoefficient P ε := by
  apply ContinuousLinearMap.ext
  intro v
  have hs := congrArg (fun H : (WholeH n m 𝕜 (q + 1)) →L[𝕜] (WholeH n m 𝕜 (q + 1)) => H (lowerOrderCLM v))
    (mollifierGainCLM_lower_input (n:=n) (m:=m) (k:=q) (𝕜:=𝕜) ε)
  have hj := congrArg (fun H : (WholeH n m 𝕜 (q + 2)) →L[𝕜] (WholeH n m 𝕜 (q + 1)) => H v)
    (mollifierCLM_lowerOrder_commute (n:=n) (m:=m) (k:=q+1) (𝕜:=𝕜) ε)
  have hq := congrArg (fun H : (WholeH n m 𝕜 (q + 2)) →L[𝕜] (WholeH n m 𝕜 q) => H (mollifierCLM ε v)) hcompat
  change mollifierCLM ε (Q (mollifierGainCLM ε (lowerOrderCLM (lowerOrderCLM v)))) =
    mollifierCLM ε (lowerOrderCLM (P (mollifierCLM ε v)))
  simp only [ContinuousLinearMap.comp_apply] at hs hj hq
  rw [hs, ← hj, hq]

theorem mollifier_difference_lower_norm_le (hn : 0 < n) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ‖((mollifierCLM (n:=n) (m:=m) (k:=q) (𝕜:=𝕜) ε) - mollifierCLM δ).comp lowerOrderCLM‖ ≤
      (ε + δ) * mollifierErrorBound n q 𝕜 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (add_pos hε hδ).le (mollifierErrorBound_nonneg n q 𝕜)
  · intro v
    change ‖mollifierCLM ε (lowerOrderCLM v) - mollifierCLM δ (lowerOrderCLM v)‖ ≤ _
    have ha := mollifier_error hn ε hε v
    have hb := mollifier_error hn δ hδ v
    have he : mollifierCLM ε (lowerOrderCLM v) - mollifierCLM δ (lowerOrderCLM v) =
        (mollifierCLM ε (lowerOrderCLM v) - lowerOrderCLM v) -
          (mollifierCLM δ (lowerOrderCLM v) - lowerOrderCLM v) := by abel
    rw [he]
    calc
      _ ≤ ‖mollifierCLM ε (lowerOrderCLM v) - lowerOrderCLM v‖ +
          ‖mollifierCLM δ (lowerOrderCLM v) - lowerOrderCLM v‖ := norm_sub_le _ _
      _ ≤ ε * mollifierErrorBound n q 𝕜 * ‖v‖ + δ * mollifierErrorBound n q 𝕜 * ‖v‖ := add_le_add ha hb
      _ = _ := by ring

theorem lower_mollifier_difference_norm_le (hn : 0 < n) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ‖(lowerOrderCLM (n:=n) (m:=m) (k:=q) (𝕜:=𝕜)).comp (mollifierCLM ε - mollifierCLM δ)‖ ≤
      (ε + δ) * mollifierErrorBound n q 𝕜 := by
  rw [ContinuousLinearMap.comp_sub, mollifierCLM_lowerOrder_commute,
    mollifierCLM_lowerOrder_commute, ← ContinuousLinearMap.sub_comp]
  exact mollifier_difference_lower_norm_le hn hε hδ

/-- The concrete two-loss operator difference estimate used for Cauchy convergence. -/
theorem highCoefficient_difference_norm_le (hn : 0 < n) {ε δ C : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 ≤ C)
    (Q : (WholeH n m 𝕜 (q + 1)) →L[𝕜] (WholeH n m 𝕜 q))
    (P : (WholeH n m 𝕜 (q + 2)) →L[𝕜] (WholeH n m 𝕜 (q + 1)))
    (hcompat : Q.comp (lowerOrderCLM (k:=q+1)) = (lowerOrderCLM (k:=q)).comp P)
    (hQ : ‖Q‖ ≤ C) (hP : ‖P‖ ≤ C) :
    ‖highCoefficient P ε - highCoefficient P δ‖ ≤
      C * (mollifierErrorBound n q 𝕜 + mollifierErrorBound n (q+1) 𝕜) * (ε + δ) := by
  have h := RegularizationError.norm_difference_le
    (lowerOrderCLM (n:=n) (m:=m) (k:=q+1) (𝕜:=𝕜))
    (lowerOrderCLM (k:=q)) P Q hcompat
    (mollifierCLM ε) (mollifierCLM δ) (mollifierCLM ε) (mollifierCLM δ)
    hC (by exact mul_nonneg (add_pos hε hδ).le (mollifierErrorBound_nonneg n q 𝕜))
    (by exact mul_nonneg (add_pos hε hδ).le (mollifierErrorBound_nonneg n (q+1) 𝕜))
    (mollifierCLM_norm_le ε) (mollifierCLM_norm_le δ) hP hQ
    (mollifier_difference_lower_norm_le hn hε hδ)
    (lower_mollifier_difference_norm_le hn hε hδ)
  change ‖highCoefficient P ε - highCoefficient P δ‖ ≤ _ at h
  exact h.trans_eq (by ring)

def twoLower : WholeH n m 𝕜 (q+2) →L[𝕜] WholeH n m 𝕜 q :=
  (lowerOrderCLM (k:=q)).comp (lowerOrderCLM (k:=q+1))

theorem lower_norm_le {k : ℕ} (v : WholeH n m 𝕜 (k+1)) :
    ‖lowerOrderCLM v‖ ≤ ‖v‖ := by
  have h : ‖lowerOrderCLM (n:=n) (m:=m) (k:=k) (𝕜:=𝕜)‖ ≤ 1 :=
    wholeDerivativeCLM_norm_le (m:=m) (k:=k) (𝕜:=𝕜) (P102.U4.zeroSobolevIndex n 1)
  calc
    _ ≤ ‖lowerOrderCLM (n:=n) (m:=m) (k:=k) (𝕜:=𝕜)‖ * ‖v‖ :=
      (lowerOrderCLM (n:=n) (m:=m) (k:=k) (𝕜:=𝕜)).le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right h (norm_nonneg v)
    _ = _ := one_mul _

theorem twoLower_mollifier (ε : ℝ) (v : WholeH n m 𝕜 (q+2)) :
    twoLower (mollifierCLM ε v) = mollifierCLM ε (twoLower v) := by
  change lowerOrderCLM (lowerOrderCLM (mollifierCLM ε v)) = _
  rw [mollifier_lowerOrder, mollifier_lowerOrder]
  rfl

/-- Actual high-order trajectories satisfying the regularized equation are
uniformly Cauchy after two canonical Sobolev inclusions. All approximation and
energy estimates used in this theorem concern the concrete convolution maps. -/
theorem uniformCauchy_of_low_equations
    (hn : 0 < n) {T C M F : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hF : 0 ≤ F)
    (Q : ℝ → WholeH n m 𝕜 (q+1) →L[𝕜] WholeH n m 𝕜 q)
    (P : ℝ → WholeH n m 𝕜 (q+2) →L[𝕜] WholeH n m 𝕜 (q+1))
    (hcompat : ∀ t ∈ Icc 0 T,
      (Q t).comp (lowerOrderCLM (k:=q+1)) = (lowerOrderCLM (k:=q)).comp (P t))
    (hQ : ∀ t ∈ Icc 0 T, ‖Q t‖ ≤ C)
    (hP : ∀ t ∈ Icc 0 T, ‖P t‖ ≤ C)
    (hQc : ∀ v, ContinuousOn (fun t => Q t v) (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, ∀ (v : WholeH n m 𝕜 (q+1)) (w : WholeH n m 𝕜 q),
      IsLowerOrder v w → |RCLike.re (inner 𝕜 w (Q t v))| ≤ C * ‖w‖ ^ 2)
    (e : ℕ → ℝ) (hepos : ∀ i, 0 < e i) (helim : Tendsto e atTop (𝓝 0))
    (g : WholeH n m 𝕜 (q+2)) (f : ℝ → WholeH n m 𝕜 (q+2))
    (hf : ContinuousOn f (Icc 0 T)) (hfb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ F)
    (U : ℕ → ℝ → WholeH n m 𝕜 (q+2))
    (hUc : ∀ i, ContinuousOn (U i) (Icc 0 T))
    (hinit : ∀ i, U i 0 = mollifierCLM (e i) g)
    (hUb : ∀ i t, t ∈ Icc 0 T → ‖U i t‖ ≤ M)
    (hd : ∀ i t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun r => twoLower (U i r))
        (lowCoefficient (Q t) (e i) (twoLower (U i t)) + mollifierCLM (e i) (twoLower (f t)))
        (Icc 0 T) t) :
    UniformCauchySeqOn (fun i t => twoLower (U i t)) atTop (Icc 0 T) := by
  let v : ℕ → ℝ → WholeH n m 𝕜 q := fun i t => twoLower (U i t)
  let f0 : ℝ → WholeH n m 𝕜 q := fun t => twoLower (f t)
  have hvc (i) : ContinuousOn (v i) (Icc 0 T) := twoLower.continuous.comp_continuousOn (hUc i)
  have hfc : ContinuousOn f0 (Icc 0 T) := twoLower.continuous.comp_continuousOn hf
  have hop (i j) : ContinuousOn (fun t => lowCoefficient (Q t) (e i) (v j t)) (Icc 0 T) := by
    exact (mollifierCLM (e i)).continuous.comp_continuousOn
      (continuousOn_apply_of_strongly_continuous Q _ C hQ hQc _
        ((mollifierGainCLM (e i)).continuous.comp_continuousOn (hvc j)))
  let J (i : ℕ) : WholeH n m 𝕜 q →L[𝕜] WholeH n m 𝕜 q := mollifierCLM (e i)
  let d : ℕ → ℝ → WholeH n m 𝕜 q := fun i t =>
    lowCoefficient (Q t) (e i) (v i t) + J i (f0 t)
  have hdc (i) : ContinuousOn (d i) (Icc 0 T) :=
    (hop i i).add ((mollifierCLM (e i)).continuous.comp_continuousOn hfc)
  let D := mollifierErrorBound n q 𝕜
  let E := C * (D + mollifierErrorBound n (q+1) 𝕜) * M + D * F
  have hD : 0 ≤ D := mollifierErrorBound_nonneg n q 𝕜
  have hE : 0 ≤ E := by
    exact add_nonneg (mul_nonneg (mul_nonneg hC (add_nonneg hD
      (mollifierErrorBound_nonneg n (q+1) 𝕜))) hM) (mul_nonneg hD hF)
  let A := Real.exp (C * T) * (D * ‖g‖ + T * E)
  have hA : 0 ≤ A := mul_nonneg (Real.exp_nonneg _) (add_nonneg
    (mul_nonneg hD (norm_nonneg g)) (mul_nonneg hT hE))
  apply uniformCauchySeqOn_of_norm_error (fun i t => twoLower (U i t)) (Icc 0 T) hA e helim
  intro i j t ht
  let err : ℝ → WholeH n m 𝕜 q := fun r =>
    lowCoefficient (Q r) (e i) (v j r) - lowCoefficient (Q r) (e j) (v j r) +
      (J i - J j) (f0 r)
  have herrc : ContinuousOn err (Icc 0 T) :=
    ((hop i j).sub (hop j j)).add
      ((J i - J j).continuous.comp_continuousOn hfc)
  have herr : ∀ r ∈ Icc 0 T, ‖err r‖ ≤ E * (e i + e j) := by
    intro r hr
    have hsum : 0 ≤ e i + e j := (add_pos (hepos i) (hepos j)).le
    have hop_eq (l : ℕ) : lowCoefficient (Q r) (e l) (v j r) = highCoefficient (P r) (e l) (U j r) :=
      congrArg (fun H => H (U j r)) (lowCoefficient_two_lower (Q r) (P r) (hcompat r hr) (e l))
    have hnorm := highCoefficient_difference_norm_le hn (hepos i) (hepos j) hC
      (Q r) (P r) (hcompat r hr) (hQ r hr) (hP r hr)
    have hfirst : ‖lowCoefficient (Q r) (e i) (v j r) - lowCoefficient (Q r) (e j) (v j r)‖ ≤
        C * (D + mollifierErrorBound n (q+1) 𝕜) * (e i + e j) * M := by
      rw [hop_eq, hop_eq, ← sub_apply]
      have hfactor : 0 ≤ C * (D + mollifierErrorBound n (q+1) 𝕜) * (e i + e j) :=
        mul_nonneg (mul_nonneg hC (add_nonneg hD (mollifierErrorBound_nonneg n (q+1) 𝕜))) hsum
      exact ((highCoefficient (P r) (e i) - highCoefficient (P r) (e j)).le_opNorm (U j r)).trans
        (mul_le_mul hnorm (hUb j r hr) (norm_nonneg _) hfactor)
    have hnorm0 := mollifier_difference_lower_norm_le (m:=m) (q:=q) (𝕜:=𝕜) hn (hepos i) (hepos j)
    have hsecond : ‖(J i - J j) (f0 r)‖ ≤ (e i + e j) * D * F := by
      have hb : ‖lowerOrderCLM (k:=q+1) (f r)‖ ≤ F := (lower_norm_le (f r)).trans (hfb r hr)
      change ‖((J i - J j).comp (lowerOrderCLM (k:=q)))
        (lowerOrderCLM (k:=q+1) (f r))‖ ≤ _
      calc
        _ ≤ ‖(J i - J j).comp (lowerOrderCLM (k:=q))‖ *
            ‖lowerOrderCLM (k:=q+1) (f r)‖ :=
          ((J i - J j).comp (lowerOrderCLM (k:=q))).le_opNorm _
        _ ≤ (e i + e j) * D * F := mul_le_mul hnorm0 hb
          (norm_nonneg (lowerOrderCLM (k:=q+1) (f r))) (mul_nonneg hsum hD)
    exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by dsimp [E]; ring))
  have hinitial : ‖v i 0 - v j 0‖ ≤ D * ‖g‖ * (e i + e j) := by
    change ‖twoLower (U i 0) - twoLower (U j 0)‖ ≤ _
    rw [hinit, hinit, twoLower_mollifier, twoLower_mollifier]
    have hn0 := mollifier_difference_lower_norm_le (m:=m) (q:=q) (𝕜:=𝕜) hn (hepos i) (hepos j)
    change ‖((J i - J j).comp (lowerOrderCLM (k:=q))) (lowerOrderCLM (k:=q+1) g)‖ ≤ _
    calc
      _ ≤ ‖(J i - J j).comp (lowerOrderCLM (k:=q))‖ * ‖lowerOrderCLM (k:=q+1) g‖ :=
        ((J i - J j).comp (lowerOrderCLM (k:=q))).le_opNorm _
      _ ≤ ((e i + e j) * D) * ‖g‖ := mul_le_mul hn0 (lower_norm_le g)
        (norm_nonneg (lowerOrderCLM (k:=q+1) g)) (mul_nonneg (add_pos (hepos i) (hepos j)).le hD)
      _ = _ := by ring
  have hest := RegularizedEnergy.estimate_with_source (𝕜:=𝕜)
    (mollifierCLM (e i)) (MollifierAdjoint.mollifierCLM_isSelfAdjoint (e i))
    (mollifierCLM_contraction (e i)) hC (fun r => v i r - v j r) (fun r => d i r - d j r) err
    (fun r => Q r (mollifierGainCLM (e i) (v i r - v j r)))
    ((hvc i).sub (hvc j)) ((hdc i).sub (hdc j)) herrc
    (fun r hr => (hd i r hr).sub (hd j r hr))
    (fun r hr => by
      dsimp [d, err, J]
      simp only [lowCoefficient, ContinuousLinearMap.comp_apply, map_sub, sub_apply]
      abel)
    (fun r hr => (le_abs_self _).trans
      (hp r hr _ _ (mollifierGainCLM_same (e i) (v i r - v j r)))) t ht
  have hInt : (∫ r in (0 : ℝ)..t, ‖err r‖) ≤ t * (E * (e i + e j)) := by
    have hb := intervalIntegral.integral_mono_on ht.1
      ((herrc.norm.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => E * (e i + e j)) volume 0 t)
      (fun r hr => herr r ((Icc_subset_Icc_right ht.2) hr))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hb
  have hb := hest.trans (mul_le_mul_of_nonneg_left (add_le_add hinitial hInt) (Real.exp_nonneg _))
  have hpos : 0 ≤ D * ‖g‖ + T * E := add_nonneg (mul_nonneg hD (norm_nonneg _)) (mul_nonneg hT hE)
  have hexp : Real.exp (C * t) ≤ Real.exp (C * T) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hC)
  have hinside : D * ‖g‖ * (e i + e j) + t * (E * (e i + e j)) ≤
      (D * ‖g‖ + T * E) * (e i + e j) := by
    nlinarith [mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hE (add_pos (hepos i) (hepos j)).le)]
  exact hb.trans ((mul_le_mul hexp hinside (add_nonneg (mul_nonneg (mul_nonneg hD (norm_nonneg g)) (add_pos (hepos i) (hepos j)).le) (mul_nonneg ht.1 (mul_nonneg hE (add_pos (hepos i) (hepos j)).le))) (Real.exp_nonneg _)).trans_eq (by dsimp [A]; ring))

end ActualCauchy



set_option maxHeartbeats 1000000 in
/-- The full intermediate Friedrichs construction, retaining the exact source
energy bound, initial datum and weak high-order continuity. -/
theorem existence : ExistenceStatement := by
  intro n q hn hs K hK
  obtain ⟨C, hC, hfamily⟩ := TopOperator.operator_family_with_pairing n (q + 2) hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB g f hf
  obtain ⟨Qlow, hQl, hQlc, hQlp⟩ := hfamily T hT A B hAB q (by omega)
  obtain ⟨Qmid, hQm, hQmc, hQmp⟩ := hfamily T hT A B hAB (q + 1) (by omega)
  obtain ⟨Qhigh, hQh, hQhc, hQhp⟩ := hfamily T hT A B hAB (q + 2) le_rfl
  let e : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hepos : ∀ i, 0 < e i := by intro i; dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := by
    simpa only [e, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨U, hU⟩ := exists_mollified_sequence hT hC Qhigh
    (fun t ht => (hQh t ht).2) hQhc hQhp e g f hf
  let R : ℝ → ℝ := fun t => Real.exp (C * t) * (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖)
  have hRc : ContinuousOn R (Icc 0 T) := continuousOn_energy_bound hT C g f hf
  obtain ⟨M, hM, hMb⟩ := exists_nonneg_uniform_bound R hRc
  obtain ⟨F, hF, hFb⟩ := exists_nonneg_uniform_bound f hf
  have hbound : ∀ i t, t ∈ Icc 0 T → ‖U i t‖ ≤ M := by
    intro i t ht
    have hb : ‖U i t‖ ≤ R t := (hU i).2.2.2.2 t ht
    exact hb.trans ((le_abs_self (R t)).trans (hMb t ht))
  let J : WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 (q + 1) := lowerOrderCLM
  let L : WholeH n m 𝕜 (q + 1) →L[𝕜] WholeH n m 𝕜 q := lowerOrderCLM
  have hn0 : 0 < n := by omega
  have hlow := ActualCauchy.uniformCauchy_of_low_equations
    (n := n) (m := m) (q := q) (𝕜 := 𝕜) hn0 hT hC hM hF Qlow Qmid
    (fun t ht => TopOperator.operator_order_compatible (hQl t ht).1 (hQm t ht).1)
    (fun t ht => (hQl t ht).2) (fun t ht => (hQm t ht).2) hQlc hQlp
    e hepos helim g f hf hFb U (fun i => (hU i).1) (fun i => (hU i).2.1) hbound
    (fun i t ht => by
      simpa only [ActualCauchy.twoLower, ActualCauchy.lowCoefficient,
        ContinuousLinearMap.comp_apply] using
        lower_mollified_derivative (n := n) (m := m) (q := q) (𝕜 := 𝕜)
          (hQl t ht).1 (hQm t ht).1 (hQh t ht).1 (e i) (U i) (f t)
          ((hU i).2.2.2.1 t ht))
  have hlow' : UniformCauchySeqOn (fun i t => (L.comp J) (U i t)) atTop (Icc 0 T) := by
    simpa only [L, J, ActualCauchy.twoLower, ContinuousLinearMap.comp_apply] using hlow
  obtain ⟨u, hu, hmid⟩ := InterpolationLimit.exists_continuousOn_uniform_limit_of_interpolation
    (𝕜 := 𝕜) (X := WholeH n m 𝕜 (q + 2)) (Y := WholeH n m 𝕜 (q + 1))
    (Z := WholeH n m 𝕜 q) J (L.comp J)
    (Nat.cast_nonneg (Fintype.card (P102.U4.SobolevIndex n (q + 1)))) hM
    (fun v => sobolev_interpolation_sq v) U (Icc 0 T)
    (fun i => (hU i).1) hbound hlow'
  obtain ⟨V, w, du, hsol, hVu, hV0, hVc, hVb⟩ := ActualLimit.actual_mollified_limit
    (n := n) (m := m) (q := q) (𝕜 := 𝕜) hn0 hT A B Qlow Qmid Qhigh hC
    hQl hQm (fun t ht => (hQh t ht).1) hQlc g f hf e hepos helim U
    (fun i => (hU i).1) (fun i => (hU i).2.1) (fun i => (hU i).2.2.1)
    (fun i => (hU i).2.2.2.1) u hu hmid R hRc (fun i => (hU i).2.2.2.2)
    M F hM hF hbound hFb
  exact ⟨V, u, w, du, hsol, hVu, hV0, hVc, hVb⟩


end P201.Hyperbolic.SymmetricApproximation

/- Mathlib proof attribution
Adapted portion near line 599:
The factorial estimate for the iterated approximation in the symmetric
hyperbolic construction.

Upstream: Mathlib/Analysis/ODE/PicardLindelof.lean (around line 329)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
