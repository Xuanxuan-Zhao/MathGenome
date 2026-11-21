import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.InfinityResidue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.Residue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Sphere
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace D12Complex.InfinityResidue
open Laurent

/-- The two absolutely summable halves give the ordinary integer-indexed sum. -/
theorem hasSum_integer_laurent {f : ℂ → ℂ} {c : ℤ → ℂ} {r : ℝ} {S : ℝ≥0∞}
    (hc : HasLaurentSeriesOn f 0 r S c) {z : ℂ} (hz : z ∈ annulus 0 r S) :
    HasSum (fun n : ℤ => c n * z ^ n) (f z) := by
  obtain ⟨hp, hn, heq⟩ := hc z hz
  rw [heq]
  apply HasSum.of_nat_of_neg_add_one
  · simpa only [positivePart, positiveTerm, sub_zero, zpow_natCast] using hp.hasSum
  · simpa only [negativePart, negativeTerm, neg_add, sub_eq_add_neg, neg_zero, add_zero]
      using hn.hasSum

/-- Conversely, split an absolutely convergent integer-indexed series into its
nonnegative and strictly negative terms. -/
theorem laurent_parts_of_hasSum {c : ℤ → ℂ} {z v : ℂ}
    (h : HasSum (fun n : ℤ => c n * z ^ n) v) :
    Summable (fun n => positiveTerm c 0 n z) ∧
    Summable (fun n => negativeTerm c 0 n z) ∧
    v = positivePart c 0 z + negativePart c 0 z := by
  have hp : Summable (fun n : ℕ => c (n : ℤ) * z ^ (n : ℤ)) :=
    h.summable.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ => c (-(n : ℤ) - 1) * z ^ (-(n : ℤ) - 1)) := by
    exact h.summable.comp_injective (fun i j hij => by omega)
  have hp' : Summable (fun n => positiveTerm c 0 n z) := by
    simpa only [positiveTerm, sub_zero, zpow_natCast] using hp
  have hn' : Summable (fun n => negativeTerm c 0 n z) := by
    simpa only [negativeTerm, sub_zero] using hn
  refine ⟨hp', hn', ?_⟩
  apply h.unique
  apply HasSum.of_nat_of_neg_add_one
  · simpa only [positivePart, positiveTerm, sub_zero, zpow_natCast] using hp'.hasSum
  · simpa only [negativePart, negativeTerm, neg_add, sub_eq_add_neg, neg_zero, add_zero]
      using hn'.hasSum

/-- Inversion sends the full punctured disk to the full exterior. -/
theorem inv_mem_exterior_of_mem_annulus {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ∈ annulus 0 0 (ENNReal.ofReal R⁻¹)) : w⁻¹ ∈ exterior R := by
  have hwpos : 0 < ‖w‖ := by simpa only [sub_zero] using hw.1
  have hwlt : ‖w‖ < R⁻¹ := by
    have h := hw.2
    rw [← ENNReal.ofReal_coe_nnreal] at h
    simpa only [sub_zero, coe_nnnorm] using
      (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hR)).mp h
  change R < ‖w⁻¹‖
  rw [norm_inv]
  exact (lt_inv_comm₀ hwpos hR).mp hwlt

theorem pullbackCoefficient_eq_deriv :
    Specs.D12Complex.Ch08.InfinityResidue.pullbackCoefficient_eq_deriv_type := by
  intro f w hw
  rw [(hasDerivAt_inv hw).deriv]
  simp [pullbackCoefficient, reciprocalPullback, zpow_neg, zpow_ofNat]

theorem differentialResidueAtInfinity_differential :
    Specs.D12Complex.Ch08.InfinityResidue.differentialResidueAtInfinity_differential_type := by
  intro f
  simp [differentialResidueAtInfinity, Residue.differential]

theorem holomorphicOn_pullbackCoefficient :
    Specs.D12Complex.Ch08.InfinityResidue.holomorphicOn_pullbackCoefficient_type := by
  intro f R hR hf
  refine ⟨?_, ?_⟩
  · have heq : annulus (0 : ℂ) 0 (ENNReal.ofReal R⁻¹) =
        {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R⁻¹} := by
      ext w
      simp only [annulus, mem_ofPred_eq, sub_zero]
      rw [← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hR)]
      rfl
    rw [heq]
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  · intro w hw
    have hw0 : w ≠ 0 := by
      exact norm_pos_iff.mp (by simpa only [sub_zero] using hw.1)
    have hi := (differentiableAt_inv_iff.mpr hw0)
    exact ((hf.2 _ (inv_mem_exterior_of_mem_annulus hR hw)).comp w hi).neg.mul
      (differentiableAt_id.zpow (Or.inl hw0))

theorem hasLaurentSeriesOn_pullbackCoefficient :
    Specs.D12Complex.Ch08.InfinityResidue.hasLaurentSeriesOn_pullbackCoefficient_type := by
  intro f R c hR hc w hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by simpa only [sub_zero] using hw.1)
  have hi : w⁻¹ ∈ annulus 0 R ⊤ := by
    refine ⟨?_, ENNReal.coe_lt_top⟩
    have hi := inv_mem_exterior_of_mem_annulus hR hw
    simpa only [exterior, mem_ofPred_eq, sub_zero] using hi
  have hs := (hasSum_integer_laurent hc hi).mul_right (-(w ^ (-2 : ℤ)))
  have hs' : HasSum (fun n : ℤ => (c n * (w⁻¹) ^ n) * -(w ^ (-2 : ℤ)))
      (pullbackCoefficient f w) := by
    simpa only [pullbackCoefficient, reciprocalPullback, mul_neg, neg_mul] using hs
  let e : ℤ ≃ ℤ :=
    ⟨fun n => -n - 2, fun n => -n - 2,
      by intro n; dsimp; omega, by intro n; dsimp; omega⟩
  have ht := e.hasSum_iff.mpr hs'
  apply laurent_parts_of_hasSum
  apply ht.congr_fun
  intro n
  symm
  change (c (-n - 2) * (w⁻¹) ^ (-n - 2)) * -(w ^ (-2 : ℤ)) =
    -c (-n - 2) * w ^ n
  calc
    _ = -c (-n - 2) * (w ^ (-(-n - 2)) * w ^ (-2 : ℤ)) := by
      rw [inv_zpow, ← zpow_neg]
      ring
    _ = _ := by rw [← zpow_add₀ hw0, show -(-n - 2) + (-2 : ℤ) = n by omega]

theorem residueAtInfinity_eq_neg_laurentCoefficient :
    Specs.D12Complex.Ch08.InfinityResidue.residueAtInfinity_eq_neg_laurentCoefficient_type := by
  intro f R c hR hc
  have hrep := hasLaurentSeriesOn_of_convergent hR hc
  -- Use a slightly smaller exterior if R = 0, so the reciprocal radius is finite.
  have hrep' : HasLaurentSeriesOn f 0 (R + 1) ⊤ c := by
    intro z hz
    exact hrep z ⟨by linarith [hz.1], hz.2⟩
  have hR' : 0 < R + 1 := by linarith
  have ht := hasLaurentSeriesOn_pullbackCoefficient f (R + 1) c hR' hrep'
  have he := Residue.residue_eq_laurentCoefficient (pullbackCoefficient f) 0
    (ENNReal.ofReal (R + 1)⁻¹) (transformedLaurentCoefficients c)
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hR')) (convergent_of_hasLaurentSeriesOn ht)
  simpa only [residueAtInfinity, transformedLaurentCoefficients, neg_neg,
    show (1 : ℤ) - 2 = -1 by omega] using he

theorem exists_exterior_laurent_with_residue :
    Specs.D12Complex.Ch08.InfinityResidue.exists_exterior_laurent_with_residue_type := by
  intro f hf
  obtain ⟨R, hR, hhol⟩ := (isolatedSingularityAtInfinity_iff_exterior f).mp hf
  have hA : HolomorphicOn (annulus 0 R ⊤) f := by
    convert hhol using 1
    ext z
    simp [annulus, exterior]
  obtain ⟨c, hc, _⟩ := laurent_exists 0 R ⊤ f hR.le (ENNReal.ofReal_lt_top) hA
  exact ⟨R, c, hR, hc, residueAtInfinity_eq_neg_laurentCoefficient f R c hR.le
    (convergent_of_hasLaurentSeriesOn hc)⟩

end D12Complex.InfinityResidue

namespace D12Complex.InfinityResidue.Definitions
abbrev pullbackCoefficient : Specs.D12Complex.Ch08.InfinityResidue.pullbackCoefficient_type :=
  D12Complex.InfinityResidue.pullbackCoefficient
abbrev residueAtInfinity : Specs.D12Complex.Ch08.InfinityResidue.residueAtInfinity_type :=
  D12Complex.InfinityResidue.residueAtInfinity
abbrev differentialResidueAtInfinity :
    Specs.D12Complex.Ch08.InfinityResidue.differentialResidueAtInfinity_type :=
  D12Complex.InfinityResidue.differentialResidueAtInfinity
abbrev transformedLaurentCoefficients :
    Specs.D12Complex.Ch08.InfinityResidue.transformedLaurentCoefficients_type :=
  D12Complex.InfinityResidue.transformedLaurentCoefficients
end D12Complex.InfinityResidue.Definitions
