import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.PolyconvexExistence
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.StrongWeakLowerSemicontinuity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.AffineCoercivity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Structure
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.WeakMinors
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.ReflexiveWeakCompactness
import Mathlib.Topology.Instances.Matrix

import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.StrongWeakLowerSemicontinuity
noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology ENNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
universe u
namespace VariationalNotes.Sobolev.Polyconvex
open Minors

/-- Every minor is a polynomial, hence continuous, in the matrix entries. -/
theorem continuous_allMinors {m d : ℕ} : Continuous (@allMinors m d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : AllIndex m d => ℝ)).comp
  apply continuous_pi
  intro a
  exact (continuous_pi fun i =>
    continuous_pi fun j => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m × Fin d => ℝ)
      (a.2.1.val i, a.2.2.val j)).continuous).matrix_det

/-- Substitution of the full minor vector retains finite Carathéodory regularity
and transfers the coercive bound back to actual gradients. -/
theorem Hypotheses.coercivity {d m : ℕ} [NeZero d] [NeZero m]
    {Ω : Opens (Domain d)} {p q : Exponent}
    {G : Domain d → Vector m → Coordinates m d → ℝ}
    {α C : ℝ} {a : Domain d → ℝ} (H : Hypotheses Ω p q G α C a) :
    CoercivityHypotheses Ω p q (density G) α C a := by
  refine ⟨H.bounded, H.state_lt, ?_, ?_, H.alpha_pos, H.C_nonneg,
    H.a_integrable, ?_⟩
  · intro s Z
    exact (H.caratheodory.1 (s, allMinors Z)).aemeasurable
  · filter_upwards [H.caratheodory.2] with x hx
    exact hx.comp (continuous_fst.prodMk (continuous_allMinors.comp continuous_snd))
  · filter_upwards [H.lower_bound] with x hx
    intro s Z
    simpa only [density, matrix_recovery (NeZero.pos m) (NeZero.pos d) Z] using hx s (allMinors Z)

/-- The direct-method conclusion, isolated from the specific minor-coordinate
lower-semicontinuity argument. The premise concerns precisely weak Sobolev
and strong state limits of sequences in the prescribed class. -/
theorem finiteMinimum_of_lowerSemicontinuity {d m : ℕ} [NeZero d] [NeZero m]
    (Ω : Opens (Domain d)) (p q : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ) (α C : ℝ) (a : Domain d → ℝ)
    (H : CoercivityHypotheses Ω p q F α C a)
    (hc : ∃ v ∈ affineClass Ω m p u₀, ∃ e : ℝ, energy Ω m p F v = (e : EReal))
    (hlsc : ∀ (u : ℕ → W1p Ω m p) (v : W1p Ω m p),
      (∀ n, u n ∈ affineClass Ω m p u₀) → WeaklyConverges u v →
      Tendsto (fun n => value Ω m p (u n)) atTop (𝓝 (value Ω m p v)) →
      energy Ω m p F v ≤ liminf (fun n => energy Ω m p F (u n)) atTop) :
    FiniteMinimum Ω p u₀ F := by
  obtain ⟨I, hI, u, hu, _, hb, ht⟩ :=
    affine_bounded_minimizing_sequence Ω p q u₀ F α C a H hc
  obtain ⟨k, hk, v, hv⟩ := VariationalNotes.Existence.reflexive_weak_subsequence
    (W1p Ω m p) (reflexive Ω p (lt_of_le_of_lt q.one_le H.exponent_lt)) u hb
  have hw : WeaklyConverges (fun n => u (k n)) v := by
    intro ℓ
    exact ((WeakBilin.eval_continuous (topDualPairing ℝ (W1p Ω m p)).flip ℓ).tendsto
      (toWeakSpace ℝ _ v)).comp hv
  have hclass : v ∈ affineClass Ω m p u₀ := by
    have hmem := (affine_closed Ω p u₀).2.mem_of_tendsto hv
      (Eventually.of_forall (fun n => mem_image_of_mem _ (hu (k n))))
    obtain ⟨w, hw, heq⟩ := hmem
    exact (toWeakSpace ℝ _).injective heq ▸ hw
  have hs := WeakMinors.strong_affine (NeZero.pos d) Ω H.bounded m p u₀
    (fun n => u (k n)) v (fun n => hu (k n)) hw
  have hmin : energy Ω m p F v ≤ (I : EReal) := by
    have h := hlsc (fun n => u (k n)) v (fun n => hu (k n)) hw hs
    have heq : liminf (fun n => energy Ω m p F (u (k n))) atTop = (I : EReal) :=
      (ht.comp hk.tendsto_atTop).liminf_eq
    exact heq ▸ h
  have hlow : ∀ w ∈ affineClass Ω m p u₀, (I : EReal) ≤ energy Ω m p F w := by
    intro w hw
    rw [← hI]
    exact sInf_le (mem_image_of_mem _ hw)
  exact ⟨v, hclass, I, le_antisymm hmin (hlow v hclass),
    fun w hw => hmin.trans (hlow w hw)⟩

/-- Reindex one minor vector by a standard finite coordinate set. This is an
isometry, so no change of the Euclidean norm or Lp exponent is involved. -/
def blockIsometry (m d j : ℕ) : MinorVector m d j ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (Fintype.card (Index m d j))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (Index m d j))

abbrev Block (m d : ℕ) (i : Fin (min m d)) :=
  EuclideanSpace ℝ (Fin (Fintype.card (Index m d (i.val+1))))

/-- Assemble the independent order-by-order fibers into the canonical full
minor-coordinate vector. This is linear on arbitrary independent fibers. -/
def assembleLinear (m d : ℕ) : (∀ i : Fin (min m d), Block m d i) →ₗ[ℝ]
    Coordinates m d where
  toFun z := WithLp.toLp 2 (fun a => (blockIsometry m d (a.1.val+1)).symm (z a.1) a.2)
  map_add' z w := by
    apply PiLp.ext
    intro a
    simp
  map_smul' c z := by
    apply PiLp.ext
    intro a
    simp

/-- Continuity follows from the finite-dimensional domain. -/
def assemble (m d : ℕ) : (∀ i : Fin (min m d), Block m d i) →L[ℝ] Coordinates m d :=
  (assembleLinear m d).toContinuousLinearMap

theorem assemble_minors {m d : ℕ} (Z : Gradient m d) :
    assemble m d (fun i => blockIsometry m d (i.val+1) (minors (i.val+1) Z)) =
      allMinors Z := by
  apply PiLp.ext
  intro a
  change (blockIsometry m d (a.1.val+1)).symm
    (blockIsometry m d (a.1.val+1) (minors (a.1.val+1) Z)) a.2 = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The canonical signed energy agrees with the energy on the reindexed fibers,
provided their representatives are the actual minors almost everywhere. -/
theorem energy_eq_blocks {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (G : Domain d → Vector m → Coordinates m d → ℝ) (u : W1p Ω m p)
    (r : Fin (min m d) → ℝ≥0∞)
    (z : ∀ i, Lp (Block m d i) (r i) (domainMeasure Ω))
    (hz : ∀ i, (z i : Domain d → Block m d i) =ᵐ[domainMeasure Ω]
      fun x => blockIsometry m d (i.val+1) (minors (i.val+1) (gradient Ω m p u x))) :
    energy Ω m p (density G) u = CaratheodorySpecs.extendedIntegral (domainMeasure Ω)
      (fun x => G x (value Ω m p u x) (assemble m d (fun i => z i x))) := by
  change CaratheodorySpecs.extendedIntegral (domainMeasure Ω)
    (fun x => G x (value Ω m p u x) (allMinors (gradient Ω m p u x))) = _
  apply extendedIntegral_congr_ae
  filter_upwards [Filter.eventually_all.mpr hz] with x hx
  have heq : (fun i : Fin (min m d) => z i x) = fun i : Fin (min m d) =>
      blockIsometry m d (i.val+1) (minors (i.val+1) (gradient Ω m p u x)) := funext hx
  rw [heq, assemble_minors]

/-- The lower state power is bounded by a constant plus the coercive power.
This lets the strong Lp convergence supplied by compactness be used directly. -/
theorem norm_power_le {E : Type*} [SeminormedAddCommGroup E]
    (s : E) (p q : Exponent) (hqp : q.real ≤ p.real) :
    ‖s‖ ^ q.real ≤ 1 + ‖s‖ ^ p.real := by
  by_cases hs : ‖s‖ ≤ 1
  · have h := Real.rpow_le_one (norm_nonneg s) hs q.pos.le
    linarith [Real.rpow_nonneg (norm_nonneg s) p.real]
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hs)) hqp
    linarith

/-- Universe transport for the frozen premise. A measure-preserving measurable
ULift equivalence transports genuine Lp classes, their strong/weak convergence,
and both halves of the signed extended integral. Thus the full premise at the
owner's universe parameter applies to the concrete Euclidean base space. -/
theorem mixed_lowerSemicontinuity_small
    (hlsc : StrongWeakSpecs.strong_weak_lowerSemicontinuity.{u}) :
    StrongWeakSpecs.strong_weak_lowerSemicontinuity.{0} := by
  intro S _ μ _ m k d q r hq hqt hr hrt
  letI : Fact (1 ≤ q) := ⟨hq⟩
  letI : ∀ i, Fact (1 ≤ r i) := fun i => ⟨(hr i).le⟩
  intro F hF hconv a ha C hC hlower sn s zn z hs hz
  let e : ULift.{u} S ≃ᵐ S := MeasurableEquiv.ulift
  let ν : Measure (ULift.{u} S) := μ.map e.symm
  have he : MeasurePreserving e ν μ := ⟨e.measurable, e.map_map_symm⟩
  let Tq : Lp (Vector m) q μ →L[ℝ] Lp (Vector m) q ν :=
    (Lp.compMeasurePreservingₗᵢ ℝ e he).toContinuousLinearMap
  let Tr (i : Fin k) : Lp (Vector (d i)) (r i) μ →L[ℝ]
      Lp (Vector (d i)) (r i) ν :=
    (Lp.compMeasurePreservingₗᵢ ℝ e he).toContinuousLinearMap
  have hFlift : CaratheodorySpecs.MixedCaratheodory ν (fun x => F (e x)) :=
    ⟨fun y => (hF.1 y).comp e.measurable, he.quasiMeasurePreserving.ae hF.2⟩
  have hzl (i : Fin k) :
      Tendsto (fun n => toWeakSpace ℝ _ (Tr i (zn n i))) atTop
        (𝓝 (toWeakSpace ℝ _ (Tr i (z i)))) :=
    ((WeakSpace.map (Tr i)).continuous.tendsto (toWeakSpace ℝ _ (z i))).comp (hz i)
  have h := hlsc ν q r hq hqt hr hrt (fun x => F (e x)) hFlift
    (he.quasiMeasurePreserving.ae hconv) (fun x => a (e x))
    (he.integrable_comp_of_integrable ha) C hC (he.quasiMeasurePreserving.ae hlower)
    (fun n => Tq (sn n)) (Tq s) (fun n i => Tr i (zn n i)) (fun i => Tr i (z i))
    ((Tq.continuous.tendsto s).comp hs) hzl
  have henergy (s' : Lp (Vector m) q μ)
      (z' : ∀ i, Lp (Vector (d i)) (r i) μ) :
      CaratheodorySpecs.extendedIntegral ν
        (fun x => F (e x) (Tq s' x) (fun i => Tr i (z' i) x)) =
      CaratheodorySpecs.extendedIntegral μ (fun x => F x (s' x) (fun i => z' i x)) := by
    have hsq := Lp.coeFn_compMeasurePreserving s' he
    have hzr := Filter.eventually_all.mpr (fun i => Lp.coeFn_compMeasurePreserving (z' i) he)
    calc
      _ = CaratheodorySpecs.extendedIntegral ν
          (fun x => F (e x) (s' (e x)) (fun i => z' i (e x))) := by
        apply extendedIntegral_congr_ae
        filter_upwards [hsq, hzr] with x hx hy
        change F (e x) (Lp.compMeasurePreserving e he s' x)
          (fun i => Lp.compMeasurePreserving e he (z' i) x) = _
        rw [hx]
        congr 1
        exact funext hy
      _ = _ := by
        unfold CaratheodorySpecs.extendedIntegral
        rw [he.lintegral_comp_emb e.measurableEmbedding
          (fun x => ENNReal.ofReal (F x (s' x) (fun i => z' i x))),
          he.lintegral_comp_emb e.measurableEmbedding
          (fun x => ENNReal.ofReal (-F x (s' x) (fun i => z' i x)))]
  simpa only [henergy] using h

/-- Transfer the full mixed-exponent lower-semicontinuity premise to actual
Sobolev minor fields. This statement uses each exponent p/(i+1) separately. -/
theorem lowerSemicontinuity_of_mixed
    (hlsc : StrongWeakSpecs.strong_weak_lowerSemicontinuity.{u})
    {d m : ℕ} [NeZero d] [NeZero m] (Ω : Opens (Domain d))
    (p q : Exponent) (G : Domain d → Vector m → Coordinates m d → ℝ)
    (α C : ℝ) (a : Domain d → ℝ) (H : Hypotheses Ω p q G α C a)
    (u : ℕ → W1p Ω m p) (v : W1p Ω m p)
    (hw : WeaklyConverges u v)
    (hs : Tendsto (fun n => value Ω m p (u n)) atTop (𝓝 (value Ω m p v))) :
    energy Ω m p (density G) v ≤ liminf (fun n => energy Ω m p (density G) (u n)) atTop := by
  classical
  letI : IsFiniteMeasure (domainMeasure Ω) :=
    isFiniteMeasure_restrict.mpr H.bounded.measure_lt_top.ne
  have hi (i : Fin (min m d)) : (i.val+1 : ℕ) < p.real :=
    (Nat.cast_le.mpr (Nat.succ_le_of_lt i.isLt)).trans_lt H.minor_lt
  let ex (i : Fin (min m d)) : Exponent := WeakMinors.minorExponent p i.val (hi i).le
  let r (i : Fin (min m d)) : ℝ≥0∞ := (ex i).ennreal
  have hr (i : Fin (min m d)) : 1 < r i := by
    have hh : 1 < p.real / (i.val+1) :=
      (lt_div_iff₀ (by positivity)).2 (by simpa using hi i)
    change 1 < ENNReal.ofReal (p.real / (i.val+1))
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hh)).mpr hh
  have hrt (i : Fin (min m d)) : r i ≠ ∞ := by simp [r, Exponent.ennreal]
  have hbc (i : Fin (min m d)) : WeakMinors.HasWeakLpLimit Ω (ex i)
      (fun n x => blockIsometry m d (i.val+1) (minors (i.val+1) (gradient Ω m p (u n) x)))
      (fun x => blockIsometry m d (i.val+1) (minors (i.val+1) (gradient Ω m p v x))) :=
    (WeakMinors.weak_continuity Ω H.bounded p u v hw hs i.val (hi i)
      (Nat.succ_le_of_lt i.isLt)).map
        (blockIsometry m d (i.val+1)).toContinuousLinearEquiv.toContinuousLinearMap
  choose zn z hzn hz hwz using hbc
  let F : Domain d → Vector m → (∀ i : Fin (min m d), Block m d i) → ℝ :=
    fun x s w => G x s (assemble m d w)
  have hF : CaratheodorySpecs.MixedCaratheodory (domainMeasure Ω) F := by
    refine ⟨fun y => H.caratheodory.1 (y.1, assemble m d y.2), ?_⟩
    filter_upwards [H.caratheodory.2] with x hx
    exact hx.comp (continuous_fst.prodMk ((assemble m d).continuous.comp continuous_snd))
  have hconv : ∀ᵐ x ∂domainMeasure Ω, ∀ s, ConvexOn ℝ univ (F x s) := by
    filter_upwards [H.convex] with x hx
    intro s
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ a b ha hb hab
    change G x s (assemble m d (a • z + b • w)) ≤ _
    rw [map_add, map_smul, map_smul]
    exact (hx s).2 (mem_univ _) (mem_univ _) ha hb hab
  have hbound : ∀ᵐ x ∂domainMeasure Ω, ∀ s w,
      -(a x + C) - C * ‖s‖ ^ p.ennreal.toReal ≤ F x s w := by
    filter_upwards [H.lower_bound] with x hx
    intro s w
    have hh := hx s (assemble m d w)
    have hpow := mul_le_mul_of_nonneg_left (norm_power_le s p q H.state_lt.le) H.C_nonneg
    have hn := mul_nonneg H.alpha_pos.le
      (Real.rpow_nonneg (norm_nonneg (firstMatrix (NeZero.pos m) (NeZero.pos d)
        (assemble m d w))) p.real)
    dsimp [F]
    rw [Exponent.toReal]
    linarith
  have hzweak (i : Fin (min m d)) :
      Tendsto (fun n => toWeakSpace ℝ _ (zn i n)) atTop (𝓝 (toWeakSpace ℝ _ (z i))) := by
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _
      (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℝ _))).mpr
    exact hwz i
  have h := mixed_lowerSemicontinuity_small hlsc (domainMeasure Ω) p.ennreal r (show 1 ≤ p.ennreal from (inferInstance : Fact (1 ≤ p.ennreal)).out)
    (by simp [Exponent.ennreal]) hr hrt F hF hconv (fun x => a x + C)
    (H.a_integrable.add (integrable_const C)) C H.C_nonneg hbound
    (fun n => value Ω m p (u n)) (value Ω m p v)
    (fun n i => zn i n) z hs hzweak
  rw [← energy_eq_blocks Ω p G v r z hz] at h
  have he (n : ℕ) := energy_eq_blocks Ω p G (u n) r (fun i => zn i n) (fun i => hzn i n)
  simpa only [F, ← he] using h

/-- Conditional draft of the source's full polyconvex existence theorem.
The ordered premises are exactly the two frozen upstream propositions. -/
theorem existence_conditional
    (_hnegative : StrongWeakSpecs.mixed_energy_negativePartIntegrable.{u})
    (hlsc : StrongWeakSpecs.strong_weak_lowerSemicontinuity.{u}) : Expected.Existence := by
  intro d m _ _ Ω p q u₀ G α C a H hc
  apply finiteMinimum_of_lowerSemicontinuity Ω p q u₀ (density G) α C a H.coercivity hc
  intro u v _ hw hs
  exact lowerSemicontinuity_of_mixed hlsc Ω p q G α C a H u v hw hs

/-- The unique full-order row/column selection for a 2×2 matrix. -/
def determinantIndex : Index 2 2 2 :=
  (⟨id, strictMono_id⟩, ⟨id, strictMono_id⟩)

/-- Projection onto the independent determinant coordinate. -/
def determinantCoordinate : Coordinates 2 2 →ₗ[ℝ] ℝ where
  toFun z := z ⟨⟨1, by decide⟩, determinantIndex⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical full minor coordinates specialize to a matrix and an
independent real determinant coordinate. -/
def matrixDetCoordinates : Coordinates 2 2 →L[ℝ] (Gradient 2 2 × ℝ) :=
  ((firstMatrix (by decide) (by decide)).prod determinantCoordinate).toContinuousLinearMap

theorem matrixDetCoordinates_allMinors (Z : Gradient 2 2) :
    matrixDetCoordinates (allMinors Z) = (Z, determinant Z) := by
  apply Prod.ext
  · exact matrix_recovery (by decide) (by decide) Z
  · rfl

/-- Conditional draft of the explicitly requested real 2×2 specialization.
Its lower bound is on every independent pair (matrix, real number). -/
theorem matrixDet_existence_conditional
    (hnegative : StrongWeakSpecs.mixed_energy_negativePartIntegrable.{u})
    (hlsc : StrongWeakSpecs.strong_weak_lowerSemicontinuity.{u}) :
    Expected.MatrixDetExistence := by
  intro Ω p q u₀ G α C a hb hp hqp hreg hconv hα hC ha hlower hc
  let G' : Domain 2 → Vector 2 → Coordinates 2 2 → ℝ :=
    fun x s z => G x s (matrixDetCoordinates z)
  have hdensity : density G' = matrixDetDensity G := by
    funext x s Z
    exact congrArg (G x s) (matrixDetCoordinates_allMinors Z)
  have H : Hypotheses Ω p q G' α C a := by
    refine ⟨hb, ?_, hqp, ?_, ?_, hα, hC, ha, ?_⟩
    · simpa using hp
    · refine ⟨fun y => hreg.1 (y.1, matrixDetCoordinates y.2), ?_⟩
      filter_upwards [hreg.2] with x hx
      exact hx.comp (continuous_fst.prodMk (matrixDetCoordinates.continuous.comp continuous_snd))
    · filter_upwards [hconv] with x hx
      intro s
      refine ⟨convex_univ, ?_⟩
      intro z _ w _ a b ha hb hab
      change G x s (matrixDetCoordinates (a • z + b • w)) ≤ _
      rw [map_add, map_smul, map_smul]
      exact (hx s).2 (mem_univ _) (mem_univ _) ha hb hab
    · filter_upwards [hlower] with x hx
      intro s z
      exact hx s (firstMatrix (NeZero.pos 2) (NeZero.pos 2) z) (determinantCoordinate z)
  have hc' : ∃ v ∈ affineClass Ω 2 p u₀, ∃ e : ℝ,
      energy Ω 2 p (density G') v = (e : EReal) := by
    simpa only [hdensity] using hc
  have h := existence_conditional hnegative hlsc Ω p q u₀ G' α C a H hc'
  simpa only [hdensity] using h

end VariationalNotes.Sobolev.Polyconvex

namespace VariationalNotes.Sobolev.Polyconvex

/-- A finite attained minimum for a finite Carathéodory polyconvex density. -/
theorem existence : Expected.Existence :=
  existence_conditional.{0} mixed_energy_negativePartIntegrable.{0}
    strong_weak_lowerSemicontinuity.{0}

/-- The real 2×2 matrix-and-determinant specialization. -/
theorem matrixDet_existence : Expected.MatrixDetExistence :=
  matrixDet_existence_conditional.{0} mixed_energy_negativePartIntegrable.{0}
    strong_weak_lowerSemicontinuity.{0}

end VariationalNotes.Sobolev.Polyconvex
