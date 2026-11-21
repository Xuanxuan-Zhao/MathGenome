import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.CantorModel
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Uniformity

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology

namespace D10Topology.Ch18

open Specs.D10Topology.Ch18.CantorModel

abbrev CantorSpace := Specs.D10Topology.Ch18.CantorModel.CantorSpace

/-- A cylinder fixes finitely many positive-indexed binary coordinates. -/
abbrev cantorCylinder := cylinder

/-- The exact positive-indexed ternary series in the source. -/
abbrev cantorMap := series

abbrev cantorPrefixSum := prefixSum
abbrev cantorRetainedStage := retainedStage

theorem cantor_nonempty : Nonempty CantorSpace := ⟨fun _ => false⟩

theorem cantor_compact : IsCompact (univ : Set CantorSpace) := isCompact_univ

theorem cylinder_clopen (s : Finset ℕ+) (a : CantorSpace) : IsClopen (cylinder s a) := by
  change IsClopen ((s : Set ℕ+).pi fun n => {a n})
  exact ⟨isClosed_set_pi (fun _ _ => isClosed_discrete _),
    isOpen_set_pi s.finite_toSet (fun _ _ => isOpen_discrete _)⟩

theorem cylinder_basis : TopologicalSpace.IsTopologicalBasis cylinders := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨s, a, rfl⟩
    exact (cylinder_clopen s a).isOpen
  · intro a U ha hU
    obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.mp hU a ha
    refine ⟨cylinder s a, ⟨s, a, rfl⟩, (fun _ _ => rfl), ?_⟩
    intro b hb
    exact hsub (fun n hn => (hb n hn) ▸ (hu n hn).2)

theorem cylinder_has_other (s : Finset ℕ+) (a : CantorSpace) :
    ∃ b ∈ cylinder s a, b ≠ a := by
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset s
  refine ⟨Function.update a n (!(a n)), ?_, ?_⟩
  · intro i hi
    exact Function.update_of_ne (ne_of_mem_of_not_mem hi hn) _ _
  · intro h
    have h' := congrFun h n
    simp at h'

theorem cantor_no_isolated (a : CantorSpace) : ¬ IsOpen ({a} : Set CantorSpace) := by
  intro ha
  obtain ⟨U, ⟨s, b, rfl⟩, _, hsub⟩ :=
    cylinder_basis.exists_subset_of_mem_open (mem_singleton a) ha
  obtain ⟨c, hc, hne⟩ := cylinder_has_other s b
  have hb : b = a := hsub (fun _ _ => rfl)
  exact hne ((hsub hc).trans hb.symm)

/-- The inverse indexing equivalence sends n to n+1, with the product topology. -/
def positiveReindex : CantorSpace ≃ₜ (ℕ → Bool) :=
  Homeomorph.piCongrLeft (Y := fun _ => Bool) Equiv.pnatEquivNat

theorem positive_reindex :
    ∃ h : CantorSpace ≃ₜ (ℕ → Bool), ∀ a n, h a n = a n.succPNat :=
  ⟨positiveReindex, fun _ _ => rfl⟩

theorem cantor_metrizable : MetrizableSpace CantorSpace := by
  let : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  exact positiveReindex.isEmbedding.metrizableSpace

theorem digitTerm_bridge (a : CantorSpace) (n : ℕ) :
    digitTerm a n.succPNat =
      Real.ofDigitsTerm (fun n => cond (a n.succPNat) (2 : Fin 3) 0) n := by
  cases h : a n.succPNat <;> simp [digitTerm, Real.ofDigitsTerm, h, div_eq_mul_inv]

theorem digit_series_bridge (a : CantorSpace) :
    series a = Real.ofDigits (fun n => cond (a n.succPNat) (2 : Fin 3) 0) := by
  rw [series, ← Equiv.pnatEquivNat.symm.tsum_eq]
  exact tsum_congr (digitTerm_bridge a)

theorem series_hasSum (a : CantorSpace) : HasSum (digitTerm a) (series a) := by
  apply Summable.hasSum
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  simpa only [Function.comp_def, Equiv.pnatEquivNat_symm_apply, digitTerm_bridge] using
    (Real.summable_ofDigitsTerm (digits := fun n => cond (a n.succPNat) (2 : Fin 3) 0))

theorem series_uniform : TendstoUniformly prefixSum series atTop := by
  have heq : (fun a : CantorSpace => ∑' n : ℕ, digitTerm a n.succPNat) = series := by
    funext a
    exact Equiv.pnatEquivNat.symm.tsum_eq (digitTerm a)
  rw [← heq]
  change TendstoUniformly (fun r a => ∑ n ∈ Finset.range r, digitTerm a n.succPNat)
    (fun a => ∑' n : ℕ, digitTerm a n.succPNat) atTop
  apply tendstoUniformly_tsum_nat (u := fun n : ℕ => (3⁻¹ : ℝ) ^ n)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro n a
    rw [digitTerm_bridge, Real.norm_eq_abs, abs_of_nonneg Real.ofDigitsTerm_nonneg]
    apply Real.ofDigitsTerm_le.trans
    norm_num
    rw [pow_succ, mul_inv_rev, ← inv_pow]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3⁻¹) n]

theorem series_continuous : Continuous series := by
  simp_rw [show series = fun a =>
      Real.ofDigits (fun n => cond (a n.succPNat) (2 : Fin 3) 0) from
    funext digit_series_bridge]
  exact Real.continuous_ofDigits.comp (by fun_prop)

private def canonicalHomeomorph : CantorSpace ≃ₜ cantorSet :=
  positiveReindex.trans cantorSetHomeomorphNatToBool.symm

private theorem canonicalHomeomorph_apply (a : CantorSpace) :
    (canonicalHomeomorph a : ℝ) = series a := (digit_series_bridge a).symm

theorem series_injective : Function.Injective series := by
  intro a b h
  apply canonicalHomeomorph.injective
  apply Subtype.ext
  simpa only [canonicalHomeomorph_apply] using h

theorem series_image : range series = cantorSet := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rw [← canonicalHomeomorph_apply]
    exact (canonicalHomeomorph a).property
  · intro hx
    obtain ⟨a, ha⟩ := canonicalHomeomorph.surjective ⟨x, hx⟩
    exact ⟨a, by simpa only [canonicalHomeomorph_apply] using congrArg Subtype.val ha⟩

theorem series_unitInterval (a : CantorSpace) : series a ∈ Icc (0 : ℝ) 1 :=
  cantorSet_subset_unitInterval (series_image ▸ mem_range_self a)

theorem cantor_homeomorph :
    ∃ h : CantorSpace ≃ₜ cantorSet, ∀ a, (h a : ℝ) = series a :=
  ⟨canonicalHomeomorph, canonicalHomeomorph_apply⟩

/-- Finite ternary prefix on zero-based binary sequences, used only to
compare the two concrete constructions. -/
private def zeroPrefix (r : ℕ) (a : ℕ → Bool) : ℝ :=
  ∑ n ∈ Finset.range r, 2 * (a n).toNat / (3 : ℝ) ^ (n + 1)

private theorem prefixSum_eq_zeroPrefix (r : ℕ) (a : CantorSpace) :
    prefixSum r a = zeroPrefix r (positiveReindex a) := rfl

private theorem zeroPrefix_succ (r : ℕ) (a : ℕ → Bool) :
    zeroPrefix (r + 1) a =
      (2 * (a 0).toNat + zeroPrefix r (fun n => a (n + 1))) / 3 := by
  have ht (n : ℕ) :
      2 * (a (n + 1)).toNat / (3 : ℝ) ^ (n + 1 + 1) =
        (2 * (a (n + 1)).toNat / (3 : ℝ) ^ (n + 1)) / 3 := by
    rw [pow_succ, div_mul_eq_div_div]
  rw [zeroPrefix, Finset.sum_range_succ']
  simp_rw [ht]
  rw [← Finset.sum_div]
  simp only [zeroPrefix, zero_add, pow_one]
  ring

private def zeroStage (r : ℕ) : Set ℝ :=
  ⋃ a : ℕ → Bool, Icc (zeroPrefix r a) (zeroPrefix r a + 1 / (3 : ℝ) ^ r)

private theorem retainedStage_eq_zeroStage (r : ℕ) : retainedStage r = zeroStage r := by
  ext x
  simp only [retainedStage, zeroStage, mem_iUnion, prefixSum_eq_zeroPrefix]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨positiveReindex a, ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := positiveReindex.surjective a
    exact ⟨b, ha⟩

private theorem zeroStage_succ (r : ℕ) :
    zeroStage (r + 1) = (fun x : ℝ => x / 3) '' zeroStage r ∪
      (fun x : ℝ => (2 + x) / 3) '' zeroStage r := by
  have hpow : 1 / (3 : ℝ) ^ (r + 1) = (1 / (3 : ℝ) ^ r) / 3 := by
    rw [pow_succ, div_mul_eq_div_div]
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    rw [zeroPrefix_succ, hpow] at ha
    let d : ℝ := 2 * (a 0).toNat
    have hy : 3 * x - d ∈ Icc (zeroPrefix r (fun n => a (n + 1)))
        (zeroPrefix r (fun n => a (n + 1)) + 1 / (3 : ℝ) ^ r) := by
      dsimp [d]
      constructor <;> linarith [ha.1, ha.2]
    have hymem : 3 * x - d ∈ zeroStage r := mem_iUnion.mpr ⟨_, hy⟩
    cases hd : a 0
    · exact Or.inl ⟨3 * x - d, hymem, by dsimp [d]; simp [hd]⟩
    · exact Or.inr ⟨3 * x - d, hymem, by dsimp [d]; simp [hd]⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      let b : ℕ → Bool := fun n => Nat.casesOn n false (fun k => a k)
      apply mem_iUnion.mpr
      refine ⟨b, ?_⟩
      rw [zeroPrefix_succ, hpow]
      simp only [b, Nat.rec_zero, Bool.toNat_false, Nat.cast_zero, mul_zero, zero_add]
      constructor <;> linarith [ha.1, ha.2]
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      let b : ℕ → Bool := fun n => Nat.casesOn n true (fun k => a k)
      apply mem_iUnion.mpr
      refine ⟨b, ?_⟩
      rw [zeroPrefix_succ, hpow]
      simp only [b, Nat.rec_zero, Bool.toNat_true, Nat.cast_one, mul_one]
      constructor <;> linarith [ha.1, ha.2]

theorem middle_thirds_stages (r : ℕ) : retainedStage r = preCantorSet r := by
  rw [retainedStage_eq_zeroStage]
  induction r with
  | zero => simp [zeroStage, zeroPrefix, iUnion_const]
  | succ r ih => rw [zeroStage_succ, preCantorSet_succ, ih]

theorem middle_thirds_intersection : (⋂ r, retainedStage r) = cantorSet := by
  simp only [middle_thirds_stages, cantorSet]

end D10Topology.Ch18
