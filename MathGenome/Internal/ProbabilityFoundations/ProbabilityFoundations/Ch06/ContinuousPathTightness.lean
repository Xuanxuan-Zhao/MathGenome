import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuousPathTightness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuousPathModulus
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Tightness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.MeasureContinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

open MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace ProbabilityFoundations.Ch06

noncomputable section
open ProbabilityFoundations.Ch06.Specs

local instance (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance (d : ℕ) : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

local instance (T : ℝ) (d : ℕ) : MeasurableSpace (Specs.Path T d) := borel _
local instance (T : ℝ) (d : ℕ) : BorelSpace (Specs.Path T d) := ⟨rfl⟩

/-- The modulus is increasing with its radius. -/
theorem pathModulus_mono {T : ℝ} (hT : 0 < T) {d : ℕ} (x : Specs.Path T d)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : modulus x a ≤ modulus x b := by
  apply csSup_le
  · exact ⟨0, ⟨0, le_rfl, hT.le⟩, ⟨0, le_rfl, hT.le⟩, by simpa using ha, by simp⟩
  · rintro r ⟨s, t, hst, rfl⟩
    exact (modulus_finite T hT d x b (ha.trans hab)).2.2.2 s t (hst.trans hab)

/-- A compact family has one modulus bound valid for all of its paths. -/
theorem compact_uniform_modulus {T : ℝ} (hT : 0 < T) {d : ℕ}
    {K : Set (Specs.Path T d)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, modulus x δ < η := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × Set.Icc (0 : ℝ) T => (p.1 : Specs.Path T d) p.2) :=
    continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff_le.mp
    (CompactSpace.uniformContinuous_of_continuous hc) (η / 2) (half_pos hη)
  refine ⟨δ, hδ, fun x hx => lt_of_le_of_lt ?_ (half_lt_self hη)⟩
  apply csSup_le
  · exact ⟨0, ⟨0, le_rfl, hT.le⟩, ⟨0, le_rfl, hT.le⟩, by simpa using hδ.le, by simp⟩
  · rintro r ⟨s, t, hst, rfl⟩
    have hp : dist ((⟨x, hx⟩ : K), s) ((⟨x, hx⟩ : K), t) ≤ δ := by
      simpa [Prod.dist_eq, Subtype.dist_eq, Real.dist_eq] using hst
    simpa only [dist_eq_norm] using h hp

/-- Tightness passes to the time-zero marginal family. -/
theorem initialLaws_uniformlyTight {T : ℝ} (hT : 0 < T) {d : ℕ}
    {A : Set (ProbabilityMeasure (Specs.Path T d))} (hA : UniformlyTight A) :
    UniformlyTight (initialLaw hT '' A) := by
  rw [uniformlyTight_iff] at hA ⊢
  intro ε hε
  obtain ⟨K, hK, hb⟩ := hA ε hε
  have hc : Continuous (initialEval hT (d := d)) := continuous_eval_const _
  refine ⟨initialEval hT '' K, hK.image hc, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  change (Measure.map (initialEval hT) (μ : Measure (Specs.Path T d))) _ < _
  rw [Measure.map_apply hc.measurable (hK.image hc).measurableSet.compl]
  apply lt_of_le_of_lt (measure_mono ?_) (hb μ hμ)
  intro x hx hxK
  exact hx ⟨x, hxK, rfl⟩

/-- Tightness implies uniform control of the bad-modulus events. -/
theorem uniformlyTight_uniformModulus {T : ℝ} (hT : 0 < T) {d : ℕ}
    {A : Set (ProbabilityMeasure (Specs.Path T d))} (hA : UniformlyTight A) :
    UniformModulus A := by
  intro η hη ε hε
  obtain ⟨K, hK, hb⟩ := (uniformlyTight_iff A).mp hA ε hε
  obtain ⟨δ, hδ, hmod⟩ := compact_uniform_modulus hT hK hη
  refine ⟨δ, hδ, fun μ hμ => lt_of_le_of_lt (measure_mono ?_) (hb μ hμ)⟩
  intro x hx hxK
  exact (not_lt_of_ge (hmod x hxK).le) hx

/-- Chaining along a uniform subdivision bounds all values by the initial
value and one positive-radius modulus bound. -/
theorem path_bound_of_initial_modulus {T : ℝ} (hT : 0 < T) {d : ℕ}
    (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ x : Specs.Path T d, ‖initialEval hT x‖ ≤ M → modulus x δ ≤ 1 →
      ∀ t, ‖x t‖ ≤ R := by
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hTN : T / N ≤ δ := by
    apply (div_le_iff₀ hN).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    dsimp [N]
    push_cast
    nlinarith
  refine ⟨M + N, fun x hx hm t => ?_⟩
  have htN : 0 ≤ (t : ℝ) / N := div_nonneg t.property.1 hN.le
  have hstep : (t : ℝ) / N ≤ δ :=
    (div_le_div_of_nonneg_right t.property.2 hN.le).trans hTN
  let u (k : ℕ) (hk : k ≤ N) : Set.Icc (0 : ℝ) T :=
    ⟨k * ((t : ℝ) / N), mul_nonneg (Nat.cast_nonneg _) htN,
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) htN).trans
        (by rw [mul_div_cancel₀ _ (ne_of_gt hN)]; exact t.property.2)⟩
  have hu0 : u 0 (Nat.zero_le N) = (⟨0, le_rfl, hT.le⟩ : Set.Icc (0 : ℝ) T) := by
    apply Subtype.ext; simp [u]
  have huN : u N le_rfl = t := by
    apply Subtype.ext
    dsimp [u]
    field_simp
  have hind : ∀ k (hk : k ≤ N), ‖x (u k hk)‖ ≤ M + k := by
    intro k
    induction k with
    | zero => intro hk; simpa [hu0, initialEval] using hx
    | succ k ih =>
      intro hk
      have hk' := Nat.le_trans (Nat.le_succ k) hk
      have hinc : ‖x (u (k + 1) hk) - x (u k hk')‖ ≤ 1 := by
        apply le_trans ((modulus_finite T hT d x δ hδ.le).2.2.2 _ _ ?_) hm
        have heq : ((u (k + 1) hk : Set.Icc (0 : ℝ) T) : ℝ) - u k hk' =
            (t : ℝ) / N := by dsimp [u]; push_cast; ring
        rw [heq, abs_of_nonneg htN]
        exact hstep
      have hnorm := norm_add_le (x (u (k + 1) hk) - x (u k hk')) (x (u k hk'))
      rw [sub_add_cancel] at hnorm
      have hi := ih hk'
      push_cast
      linarith
  simpa [huN] using hind N le_rfl

/-- Closed initial-value and modulus constraints form a compact path set. -/
theorem isCompact_initial_modulus {T : ℝ} (hT : 0 < T) {d : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : IsCompact B)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    IsCompact {x : Specs.Path T d | initialEval hT x ∈ B ∧
      ∀ n : ℕ, modulus x (δ n) ≤ (1 / 2 : ℝ) ^ n} := by
  let K : Set (Specs.Path T d) := {x | initialEval hT x ∈ B ∧
    ∀ n : ℕ, modulus x (δ n) ≤ (1 / 2 : ℝ) ^ n}
  have hclosed : IsClosed K := by
    have heq : K = initialEval hT ⁻¹' B ∩
        ⋂ n : ℕ, {x | modulus x (δ n) ≤ (1 / 2 : ℝ) ^ n} := by
      ext x; simp [K]
    rw [heq]
    exact (hB.isClosed.preimage (continuous_eval_const _)).inter
      (isClosed_iInter fun n => (modulus_events T hT d (δ n) (hδ n).le _).2)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hB.isBounded
  obtain ⟨R, hR⟩ := path_bound_of_initial_modulus hT (d := d) M (hδ 0)
  have hb : ∀ x ∈ K, ∀ t, ‖x t‖ ≤ R := by
    intro x hx
    exact hR x (hM _ hx.1) (by simpa using hx.2 0)
  let e := (ContinuousMap.isometryEquivBoundedOfCompact
    (Set.Icc (0 : ℝ) T) (EuclideanSpace ℝ (Fin d))).toHomeomorph
  have hc : IsCompact (e '' K) := by
    apply BoundedContinuousFunction.arzela_ascoli₂
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) (isCompact_closedBall _ _)
      (e '' K) (e.isClosedMap _ hclosed)
    · rintro _ t ⟨x, hx, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right, e] using hb x hx t
    · intro t
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨δ n, hδ n, fun s hs f => ?_⟩
      obtain ⟨x, hx, hxf⟩ := f.property
      have hst : |(t : ℝ) - (s : ℝ)| ≤ δ n := by
        rw [← Real.dist_eq, ← Subtype.dist_eq, dist_comm]
        exact hs.le
      have hi := (modulus_finite T hT d x (δ n) (hδ n).le).2.2.2 t s hst
      have hh := hi.trans (hx.2 n)
      change dist ((f : BoundedContinuousFunction (Set.Icc (0 : ℝ) T) (EuclideanSpace ℝ (Fin d))) t)
        ((f : BoundedContinuousFunction (Set.Icc (0 : ℝ) T) (EuclideanSpace ℝ (Fin d))) s) < ε
      rw [← hxf]
      change ‖x t - x s‖ < ε
      exact hh.trans_lt hn
  have hh := hc.image e.symm.continuous
  simpa [Set.image_image, K] using hh

/-- The compact-set construction for the sufficient direction. -/
theorem uniformlyTight_of_initial_uniformModulus {T : ℝ} (hT : 0 < T) {d : ℕ}
    {A : Set (ProbabilityMeasure (Specs.Path T d))}
    (hinit : UniformlyTight (initialLaw hT '' A)) (hmod : UniformModulus A) :
    UniformlyTight A := by
  classical
  rw [uniformlyTight_iff] at hinit ⊢
  intro ε hε
  obtain ⟨B, hB, hinit⟩ := hinit (ε / 4) (by positivity)
  have hchoose : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ A,
      (μ : Measure (Specs.Path T d)) {x | (1 / 2 : ℝ) ^ n < modulus x δ} <
        ENNReal.ofReal (ε / 4 * (1 / 2 : ℝ) ^ n) := by
    intro n
    exact hmod _ (by positivity) _ (by positivity)
  choose δ hδ hbad using hchoose
  let K : Set (Specs.Path T d) := {x | initialEval hT x ∈ B ∧
    ∀ n : ℕ, modulus x (δ n) ≤ (1 / 2 : ℝ) ^ n}
  refine ⟨K, isCompact_initial_modulus hT B hB δ hδ, fun μ hμ => ?_⟩
  have hi : (μ : Measure (Specs.Path T d)) (initialEval hT ⁻¹' Bᶜ) <
      ENNReal.ofReal (ε / 4) := by
    have h := hinit (initialLaw hT μ) (Set.mem_image_of_mem _ hμ)
    change (Measure.map (initialEval hT) (μ : Measure (Specs.Path T d))) Bᶜ < _ at h
    have hc : Continuous (initialEval hT (d := d)) := continuous_eval_const _
    rwa [Measure.map_apply hc.measurable hB.measurableSet.compl] at h
  have hKc : Kᶜ = initialEval hT ⁻¹' Bᶜ ∪
      ⋃ n : ℕ, {x | (1 / 2 : ℝ) ^ n < modulus x (δ n)} := by
    ext x
    simp [K]
    tauto
  have hs : Summable (fun n : ℕ => ε / 4 * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _
  have hsum : (∑' n : ℕ, ENNReal.ofReal (ε / 4 * (1 / 2 : ℝ) ^ n)) =
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs,
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).tsum_mul_left]
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
    congr 1
    norm_num
    ring
  calc
    (μ : Measure (Specs.Path T d)) Kᶜ ≤
        (μ : Measure (Specs.Path T d)) (initialEval hT ⁻¹' Bᶜ) +
          (μ : Measure (Specs.Path T d)) (⋃ n : ℕ, {x | (1 / 2 : ℝ) ^ n < modulus x (δ n)}) := by
      rw [hKc]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 4) +
        ∑' n : ℕ, (μ : Measure (Specs.Path T d)) {x | (1 / 2 : ℝ) ^ n < modulus x (δ n)} :=
      add_le_add hi.le (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal (ε / 4) +
        ∑' n : ℕ, ENNReal.ofReal (ε / 4 * (1 / 2 : ℝ) ^ n) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum fun n => (hbad n μ hμ).le)
    _ = ENNReal.ofReal (ε / 4 + ε / 2) := by
      rw [hsum, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- The continuous-path tightness criterion, valid also for empty families and
zero-dimensional state spaces. -/
theorem continuousPath_tightness_quantified : Specs.ContinuousPathTightnessQuantified := by
  intro T hT d A
  change UniformlyTight A ↔ UniformlyTight (initialLaw hT '' A) ∧ UniformModulus A
  exact ⟨fun h => ⟨initialLaws_uniformlyTight hT h, uniformlyTight_uniformModulus hT h⟩,
    fun h => uniformlyTight_of_initial_uniformModulus hT h.1 h.2⟩

/-- The quantified condition is exactly the right-hand limit, without a
nonemptiness assumption on the family. -/
theorem uniformModulus_iff_limit : Specs.UniformModulusIffLimit := by
  intro T hT d A
  constructor
  · intro hmod η hη
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    by_cases htop : ε = ∞
    · simp [htop]
    obtain ⟨δ, hδ, hb⟩ := hmod η hη ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    have he : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < δ :=
      (eventually_lt_nhds hδ).filter_mono inf_le_left
    filter_upwards [he, self_mem_nhdsWithin] with a ha hapos
    apply iSup₂_le
    intro μ hμ
    calc
      (μ : Measure (Specs.Path T d)) {x | η < modulus x a} ≤
          (μ : Measure (Specs.Path T d)) {x | η < modulus x δ} := by
        apply measure_mono
        intro x hx
        exact hx.trans_le (pathModulus_mono hT x hapos.le ha.le)
      _ ≤ ENNReal.ofReal ε.toReal := (hb μ hμ).le
      _ ≤ ε := ENNReal.ofReal_toReal_le
  · intro hlim η hη ε hε
    have he := ENNReal.tendsto_nhds_zero.mp (hlim η hη)
      (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
    have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    obtain ⟨δ, hδ, hb⟩ := (hpos.and he).exists
    refine ⟨δ, hδ, fun μ hμ => ?_⟩
    apply lt_of_le_of_lt ((le_iSup₂ μ hμ).trans hb)
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)

/-- The criterion in the source's limit-of-suprema formulation. -/
theorem continuousPath_tightness : Specs.ContinuousPathTightness := by
  intro T hT d A
  rw [← uniformModulus_iff_limit T hT d A]
  exact continuousPath_tightness_quantified T hT d A

end
end ProbabilityFoundations.Ch06
