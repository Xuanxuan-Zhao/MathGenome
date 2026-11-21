import MathGenome.Internal.RealAnalysis.D11.Ch23.UndergraphOuterMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch23.SigmaRingExtension
import MathGenome.Internal.RealAnalysis.D11.Ch23.GeneratedRingAlgebra
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.LevelCylinderMeasure
import Mathlib.Tactic.Linarith

/-! Stone truncations generate measurable level cylinders. Their pullback defines
a measure on R_V; the native measure on A_V has precisely the preceding
infinity-outside-ring prescription. Finite level masses justify subtraction. -/

noncomputable section
universe u
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch23

abbrev levelTruncation {X : Type u} (f : X → ℝ) (b : ℝ) (n : ℕ) : X → ℝ :=
  Specs.LevelTruncation f b n
abbrev cylinderMass {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (c : ℝ) (A : Set X) : ℝ≥0∞ := Specs.CylinderMass V L c A
abbrev levelCylinderMeasure {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) : @Measure X (positiveLevelMeasurableSpace V) :=
  Specs.LevelCylinderMeasure V L

theorem levelTruncation_mem : Specs.LevelTruncationMem := by
  intro X V hStone f hf b hb n
  have h := hStone ((n : ℝ) • (f - (fun x => min (f x) b)))
    (V.smul_mem _ (V.sub_mem hf (min_const_mem V hStone f hf b hb)))
  change (fun x => min 1 ((n : ℝ) * (f x - min (f x) b))) ∈ V
  convert h using 1
  funext x
  exact min_comm _ _

theorem levelTruncation_nonneg {X : Type u} (f : X → ℝ) (b : ℝ) (n : ℕ) (x : X) :
    0 ≤ levelTruncation f b n x :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (min_le_left _ _)))

theorem levelTruncation_le_one {X : Type u} (f : X → ℝ) (b : ℝ) (n : ℕ) (x : X) :
    levelTruncation f b n x ≤ 1 := min_le_left _ _

theorem levelTruncation_mono {X : Type u} (f : X → ℝ) (b : ℝ) (x : X) :
    Monotone (fun n => levelTruncation f b n x) := by
  intro i j hij
  exact min_le_min_left _ (mul_le_mul_of_nonneg_right (by exact_mod_cast hij)
    (sub_nonneg.mpr (min_le_left _ _)))

/-- At each point the sequence is eventually exactly its limiting indicator. -/
theorem levelTruncation_eventually {X : Type u} (f : X → ℝ) (b : ℝ) (x : X) :
    ∀ᶠ n : ℕ in atTop, levelTruncation f b n x =
      ({x | b < f x} : Set X).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : b < f x
  · obtain ⟨N, hN⟩ := exists_nat_gt ((f x - b)⁻¹)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd : 0 < f x - b := sub_pos.mpr hx
    have hn' : (f x - b)⁻¹ < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
    have hp : 1 ≤ (n : ℝ) * (f x - b) := by
      have ht := (mul_lt_mul_of_pos_right hn' hd)
      rw [inv_mul_cancel₀ hd.ne'] at ht
      exact ht.le
    simp only [levelTruncation, Specs.LevelTruncation, min_eq_right hx.le,
      min_eq_left hp]
    exact (indicator_of_mem (show x ∈ {x | b < f x} from hx) (fun _ => (1 : ℝ))).symm
  · filter_upwards [] with n
    simp [levelTruncation, Specs.LevelTruncation, min_eq_left (le_of_not_gt hx),
      indicator_of_notMem (show x ∉ {x | b < f x} from hx)]

theorem levelTruncation_convergence : Specs.LevelTruncationConvergence := by
  intro X f b
  exact ⟨fun n x => ⟨levelTruncation_nonneg f b n x, levelTruncation_le_one f b n x⟩,
    levelTruncation_mono f b, fun x =>
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (levelTruncation_eventually f b x))⟩

/-- Increasing elementary intervals exhaust a level cylinder. -/
theorem levelTruncation_undergraph_union {X : Type u} (f : X → ℝ) (b c : ℝ)
    (_hc : 0 < c) :
    (⋃ n : ℕ, undergraph (0 : X → ℝ) (fun x => c * levelTruncation f b n x)) =
      {x | b < f x} ×ˢ Ico 0 c := by
  classical
  ext p
  simp only [mem_iUnion, undergraph, Specs.Undergraph, mem_ofPred_eq,
    Pi.zero_apply, mem_prod, mem_Ico]
  constructor
  · rintro ⟨n, h0, ht⟩
    have hx : b < f p.1 := by
      by_contra hx
      have he : levelTruncation f b n p.1 = 0 := by
        simp [levelTruncation, Specs.LevelTruncation, min_eq_left (le_of_not_gt hx)]
      rw [he, mul_zero] at ht
      exact (not_lt_of_ge h0) ht
    exact ⟨hx, h0, ht.trans_le (by nlinarith [levelTruncation_le_one f b n p.1])⟩
  · rintro ⟨hx, h0, ht⟩
    obtain ⟨n, hn⟩ := (levelTruncation_eventually f b p.1).exists
    have he : levelTruncation f b n p.1 = 1 := by simpa [hx] using hn
    exact ⟨n, h0, by simpa [he] using ht⟩

theorem levelTruncation_undergraph_mono {X : Type u} (f : X → ℝ) (b c : ℝ)
    (hc : 0 ≤ c) :
    Monotone (fun n : ℕ => undergraph (0 : X → ℝ)
      (fun x => c * levelTruncation f b n x)) := by
  intro i j hij p hp
  exact ⟨hp.1, hp.2.trans_le (mul_le_mul_of_nonneg_left
    (levelTruncation_mono f b p.1 hij) hc)⟩

theorem levelTruncation_undergraph_mem {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hStone : IsStone V) (f : X → ℝ) (hf : f ∈ V) (b : ℝ) (hb : 0 < b)
    (c : ℝ) (n : ℕ) :
    undergraph (0 : X → ℝ) (fun x => c * levelTruncation f b n x) ∈
      undergraphFamily V :=
  ⟨0, ⟨_, V.smul_mem c (levelTruncation_mem V hStone f hf b hb n)⟩, rfl⟩

theorem positiveLevel_cylinder_measurable : Specs.PositiveLevelCylinderMeasurable := by
  intro X V hStone f hf b hb c hc
  rw [← levelTruncation_undergraph_union f b c hc]
  let := undergraphMeasurableSpace V
  exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
    (levelTruncation_undergraph_mem V hStone f hf b hb c n)

/-- Cylinder formation preserves the sigma-ring operations. -/
theorem cylinder_sdiff {X : Type u} (A B : Set X) (c : ℝ) :
    (A \ B) ×ˢ Ico 0 c = (A ×ˢ Ico 0 c) \ (B ×ˢ Ico 0 c) := by
  ext p
  simp only [mem_prod, Set.mem_sdiff]
  tauto

theorem ring_cylinder_measurable : Specs.RingCylinderMeasurable := by
  intro X V hStone A hA c hc
  let := undergraphMeasurableSpace V
  let R : SigmaRing X :=
    { sets := {A | MeasurableSet[undergraphMeasurableSpace V] (A ×ˢ Ico 0 c)}
      empty_mem := by simp
      diff_mem := by
        intro A B hA hB
        change MeasurableSet ((A \ B) ×ˢ Ico 0 c)
        rw [cylinder_sdiff]
        change MeasurableSet (A ×ˢ Ico 0 c) at hA
        change MeasurableSet (B ×ˢ Ico 0 c) at hB
        exact hA.diff hB
      iUnion_mem := by
        intro A hA
        change MeasurableSet ((⋃ n, A n) ×ˢ Ico 0 c)
        rw [iUnion_prod_const]
        exact MeasurableSet.iUnion hA }
  apply positiveLevelSigmaRing_le V R ?_ hA
  rintro B ⟨f, hf, b, hb, rfl⟩
  exact positiveLevel_cylinder_measurable V hStone f hf b hb c hc

/-- The actual pullback measure on the sigma-ring, before adjoining complements. -/
def cylinderRingMeasure {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ) :
    SigmaRingMeasure (positiveLevelSigmaRing V) where
  toFun := fun A => Specs.CylinderMass V L 1 A.1
  empty' := by simp [Specs.CylinderMass]
  iUnion' := by
    intro A hA hd
    let := undergraphMeasurableSpace V
    change undergraphMeasure V L ((⋃ n, A n) ×ˢ Ico 0 1) = _
    rw [iUnion_prod_const]
    apply measure_iUnion
    · intro i j hij
      exact Set.disjoint_left.mpr fun p hp hq => Set.disjoint_left.mp (hd hij) hp.1 hq.1
    · intro n
      exact ring_cylinder_measurable V hStone (A n) (hA n) 1 zero_lt_one

theorem cylinderRingMeasure_exists : Specs.CylinderRingMeasureExists := by
  intro X V hStone L
  exact ⟨cylinderRingMeasure V hStone L, fun _ _ => rfl⟩

theorem cylinderExtension_exists {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ) :
    ∃ μ, Specs.CylinderExtensionFormula V L μ := by
  classical
  have he := SigmaRingMeasure.exists_extension (positiveLevelSigmaRing V)
    (cylinderRingMeasure V hStone L)
  rw [generateFrom_sigmaRing V] at he
  obtain ⟨μ, hμ⟩ := he
  refine ⟨μ, fun A hA => ?_⟩
  rw [hμ A hA]
  by_cases h : A ∈ positiveLevelSigmaRing V
  · rw [SigmaRingMeasure.extensionMass_of_mem _ _ h]
    change Specs.CylinderMass V L 1 A = if A ∈ positiveLevelSigmaRing V then _ else _
    exact (ite_eq_left h).symm
  · rw [SigmaRingMeasure.extensionMass_of_not_mem _ _ h]
    change ∞ = if A ∈ positiveLevelSigmaRing V then _ else _
    exact (ite_eq_right h).symm

theorem levelCylinderMeasure_apply : Specs.LevelCylinderMeasureApply := by
  classical
  intro X V hStone L
  unfold Specs.LevelCylinderMeasure
  rw [dite_eq_left (cylinderExtension_exists V hStone L)]
  exact (cylinderExtension_exists V hStone L).choose_spec

/-- The specified Stone truncation, as an element of the original subspace. -/
def levelTruncationElement {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hStone : IsStone V) (f : X → ℝ) (hf : f ∈ V) (b : ℝ) (hb : 0 < b) (n : ℕ) : V :=
  ⟨levelTruncation f b n, levelTruncation_mem V hStone f hf b hb n⟩

/-- Continuity from below expresses the cylinder mass using elementary values. -/
theorem positiveLevel_cylinder_iSup {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ)
    (hL : IsElementaryIntegral V L) (f : X → ℝ) (hf : f ∈ V)
    (b : ℝ) (hb : 0 < b) (c : ℝ) (hc : 0 < c) :
    Specs.CylinderMass V L c {x | b < f x} =
      ⨆ n, ENNReal.ofReal (c * L (levelTruncationElement V hStone f hf b hb n)) := by
  let := undergraphMeasurableSpace V
  change undergraphMeasure V L ({x | b < f x} ×ˢ Ico 0 c) = _
  rw [← levelTruncation_undergraph_union f b c hc,
    (levelTruncation_undergraph_mono f b c hc.le).measure_iUnion]
  apply iSup_congr
  intro n
  rw [undergraph_measure_exact V hV L hL _
    (levelTruncation_undergraph_mem V hStone f hf b hb c n)]
  have h := undergraph_content_of_le V L (0 : V)
    (c • levelTruncationElement V hStone f hf b hb n)
    (fun x => mul_nonneg hc.le (levelTruncation_nonneg f b n x))
  have he : ((c • levelTruncationElement V hStone f hf b hb n : V) : X → ℝ) =
      (fun x => c * levelTruncation f b n x) := by
    funext x
    rfl
  rw [he] at h
  simpa only [sub_zero, map_smul, smul_eq_mul, Submodule.coe_zero] using h

theorem positiveLevel_cylinder_scaling : Specs.PositiveLevelCylinderScaling := by
  intro X V hV hStone L hL f hf b hb c hc
  rw [positiveLevel_cylinder_iSup V hV hStone L hL f hf b hb c hc,
    positiveLevel_cylinder_iSup V hV hStone L hL f hf b hb 1 zero_lt_one,
    ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  rw [one_mul, ENNReal.ofReal_mul hc.le]

/-- A uniform bound for all the truncations, including where f is nonpositive. -/
theorem levelTruncation_le_positivePart_div {X : Type u} (f : X → ℝ) (b : ℝ)
    (hb : 0 < b) (n : ℕ) (x : X) :
    levelTruncation f b n x ≤ max (f x) 0 / b := by
  by_cases hx : b < f x
  · have h1 : 1 ≤ max (f x) 0 / b := (le_div_iff₀ hb).mpr (by
      simpa only [one_mul] using hx.le.trans (le_max_left (f x) 0))
    exact (levelTruncation_le_one f b n x).trans h1
  · have he : levelTruncation f b n x = 0 := by
      simp [levelTruncation, Specs.LevelTruncation, min_eq_left (le_of_not_gt hx)]
    rw [he]
    exact div_nonneg (le_max_right _ _) hb.le

theorem positiveLevel_mass_bound : Specs.PositiveLevelMassBound := by
  intro X V hV hStone L hL f b hb hp
  refine ⟨?_, ENNReal.ofReal_lt_top⟩
  rw [positiveLevel_cylinder_iSup V hV hStone L hL f f.property b hb 1 zero_lt_one]
  apply iSup_le
  intro n
  apply ENNReal.ofReal_le_ofReal
  rw [one_mul]
  have h := IsElementaryIntegral.mono hL (f := levelTruncationElement V hStone f f.property b hb n)
    (g := b⁻¹ • (⟨_, hp⟩ : V)) (fun x => by
      simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
        mul_comm, levelTruncationElement] using levelTruncation_le_positivePart_div f b hb n x)
  simpa only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- Every positive level has finite cylinder mass at every finite positive height. -/
theorem positiveLevel_cylinder_finite {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ)
    (hL : IsElementaryIntegral V L) (f : X → ℝ) (hf : f ∈ V)
    (b : ℝ) (hb : 0 < b) (c : ℝ) (hc : 0 < c) :
    Specs.CylinderMass V L c {x | b < f x} < ∞ := by
  rw [positiveLevel_cylinder_scaling V hV hStone L hL f hf b hb c hc]
  have h := positiveLevel_mass_bound V hV hStone L hL ⟨f, hf⟩ b hb
    (positivePart_mem V hV f hf)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.1.trans_lt h.2)

/-- Finite subtraction is legitimate at each of the two heights. -/
theorem nestedLevel_cylinder_scaling : Specs.NestedLevelCylinderScaling := by
  intro X V hV hStone L hL f hf g hg b d hb hd hsub c hc
  let := undergraphMeasurableSpace V
  have hsubset (a : ℝ) : {x | d < g x} ×ˢ Ico 0 a ⊆ {x | b < f x} ×ˢ Ico 0 a :=
    fun _ hp => ⟨hsub hp.1, hp.2⟩
  have hdiff (a : ℝ) (ha : 0 < a) :
      Specs.CylinderMass V L a ({x | b < f x} \ {x | d < g x}) =
        Specs.CylinderMass V L a {x | b < f x} - Specs.CylinderMass V L a {x | d < g x} := by
    change undergraphMeasure V L _ = _
    rw [cylinder_sdiff]
    exact measure_sdiff (hsubset a)
      (positiveLevel_cylinder_measurable V hStone g hg d hd a ha).nullMeasurableSet
      (positiveLevel_cylinder_finite V hV hStone L hL g hg d hd a ha).ne
  rw [hdiff c hc, hdiff 1 zero_lt_one,
    positiveLevel_cylinder_scaling V hV hStone L hL f hf b hb c hc,
    positiveLevel_cylinder_scaling V hV hStone L hL g hg d hd c hc]
  exact (ENNReal.mul_sub (fun _ _ => ENNReal.ofReal_ne_top)).symm

end D11.Ch23
