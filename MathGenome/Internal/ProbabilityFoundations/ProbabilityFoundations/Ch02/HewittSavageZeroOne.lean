import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependentGrouping
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceJointLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.HewittSavageZeroOne
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-! Hewitt--Savage (paper.tex:749–789), for arbitrary measurable state spaces.
The proof uses density of the generating cylinder algebra, invariance of the
sequence law, and independence of disjoint blocks. Null invariance is converted
to almost-everywhere equality only for the selected block swap. -/

open MeasureTheory Set ProbabilityTheory
open scoped symmDiff ENNReal

namespace ProbabilityFoundations.Ch02
universe u v

/-- Finite initial blocks are dense in measure in the product sigma-algebra.
No countability or separation property of the state space is required. -/
theorem finiteBlock_approximation {S : Type u} [MeasurableSpace S]
    (μ : Measure (ℕ → S)) [IsFiniteMeasure μ]
    (A : Set (ℕ → S)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (m : ℕ) (B : Set (ℕ → S)),
      MeasurableSet[cylinderEvents (X := fun _ : ℕ => S) (Iio m)] B ∧
      μ (A ∆ B) < ε := by
  let C := measurableCylinders (fun _ : ℕ => S)
  have hC : IsSetRing C :=
    ⟨empty_mem_measurableCylinders _, fun {_ _} hs ht => union_mem_measurableCylinders hs ht,
      fun {_ _} hs ht => sdiff_mem_measurableCylinders hs ht⟩
  have hcover : ∃ D : Set (Set (ℕ → S)), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, ?_, ?_⟩
    · exact singleton_subset_iff.mpr (univ_mem_measurableCylinders (fun _ : ℕ => S))
    · simp
  obtain ⟨B, hB, herr⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    hC hcover generateFrom_measurableCylinders.symm hA hε
  rw [show C = _ from measurableCylinders_nat] at hB
  simp only [mem_iUnion, mem_singleton_iff] at hB
  obtain ⟨n, T, hT, rfl⟩ := hB
  refine ⟨n + 1, cylinder (Finset.Iic n) T, ?_, ?_⟩
  · let : MeasurableSpace (ℕ → S) := cylinderEvents (X := fun _ : ℕ => S) (Iio (n + 1))
    apply hT.preimage
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_cylinderEvent_apply (by simpa using Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2))
  · simpa only [symmDiff_comm] using herr

/-- The law of independent, identically distributed coordinates is invariant
under every coordinate permutation, hence in particular every finite one. -/
theorem iid_coordinate_permutation_invariant {S : Type u} [MeasurableSpace S]
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (hind : iIndepFun (fun i (x : ℕ → S) => x i) μ)
    (hid : ∀ i j, μ.map (fun x => x i) = μ.map (fun x => x j))
    (σ : Equiv.Perm ℕ) : μ.map (fun x i => x (σ i)) = μ := by
  have hp : Measurable (fun (x : ℕ → S) i => x (σ i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply _)
  have : IsProbabilityMeasure (μ.map (fun x i => x (σ i))) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  refine ext_of_generate_finite (measurableCylinders (fun _ : ℕ => S))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ (by simp)
  intro B hB
  obtain ⟨s, T, hT, rfl⟩ := (mem_measurableCylinders B).mp hB
  have hfin : μ.map (fun x (i : s) => x (σ i)) = μ.map (fun x (i : s) => x i) := by
    have h1 := (hind.precomp (g := fun i : s => σ i)
      (σ.injective.comp Subtype.val_injective)).map_fun_eq_pi_map
      (fun i => (measurable_pi_apply _).aemeasurable)
    have h2 := (hind.precomp (g := fun i : s => (i : ℕ))
      Subtype.val_injective).map_fun_eq_pi_map
      (fun i => (measurable_pi_apply _).aemeasurable)
    exact h1.trans ((congrArg Measure.pi (funext fun i : s => hid (σ i) i)).trans h2.symm)
  calc
    μ.map (fun x i => x (σ i)) (cylinder s T) =
        μ.map (fun x (i : s) => x (σ i)) T := by
      rw [Measure.map_apply hp hT.cylinder, Measure.map_apply (by fun_prop) hT]
      rfl
    _ = μ.map (fun x (i : s) => x i) T := by rw [hfin]
    _ = μ (cylinder s T) := Measure.map_apply (by fun_prop) hT

/-- Exchange two adjacent blocks of length `m`, fixing all later coordinates. -/
private def blockSwap (m : ℕ) : Equiv.Perm ℕ where
  toFun i := if i < m then i + m else if i < 2 * m then i - m else i
  invFun i := if i < m then i + m else if i < 2 * m then i - m else i
  left_inv i := by dsimp only; split_ifs <;> omega
  right_inv i := by dsimp only; split_ifs <;> omega

private theorem blockSwap_finite (m : ℕ) : {i | blockSwap m i ≠ i}.Finite := by
  apply (Finset.finite_toSet (Finset.range (2 * m))).subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  change (if i < m then i + m else if i < 2 * m then i - m else i) ≠ i at hi
  split_ifs at hi <;> omega

private theorem blockSwap_preimage (m : ℕ) :
    (blockSwap m) ⁻¹' Iio m = Ico m (2 * m) := by
  ext i
  change (if i < m then i + m else if i < 2 * m then i - m else i) < m ↔
    m ≤ i ∧ i < 2 * m
  split_ifs <;> omega

private theorem blockSwap_cylinder_measurable {S : Type u} [mS : MeasurableSpace S]
    (m : ℕ) {B : Set (ℕ → S)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : ℕ => S) (Iio m)] B) :
    MeasurableSet[cylinderEvents (X := fun _ : ℕ => S) (Ico m (2 * m))]
      ((fun x i => x (blockSwap m i)) ⁻¹' B) := by
  apply hB.preimage
  rw [measurable_cylinderEvents_iff]
  intro i hi
  apply measurable_cylinderEvent_apply
  have : blockSwap m (blockSwap m i) = i := (blockSwap m).left_inv i
  have hh : blockSwap m i ∈ (blockSwap m) ⁻¹' Iio m := by simpa only [mem_preimage, this] using hi
  rwa [blockSwap_preimage] at hh

/-- An event with arbitrarily accurate independent copies is independent of
itself in the limit. This estimate uses real probabilities only. -/
private theorem zero_one_of_independent_approximations
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ B C : Set Ω,
      MeasurableSet B ∧ MeasurableSet C ∧
      μ (B ∩ C) = μ B * μ C ∧ μ B = μ C ∧
      μ.real (A ∆ B) < ε ∧ μ.real (A ∆ C) < ε) :
    μ A = 0 ∨ μ A = 1 := by
  let a := μ.real A
  have ha0 : 0 ≤ a := measureReal_nonneg
  have ha1 : a ≤ 1 := measureReal_le_one
  have hbound (ε : ℝ) (hε : 0 < ε) : |a - a * a| ≤ 4 * ε := by
    obtain ⟨B, C, hB, hC, hBC, heq, herrB, herrC⟩ := happrox ε hε
    let b := μ.real B
    have hb0 : 0 ≤ b := measureReal_nonneg
    have hb1 : b ≤ 1 := measureReal_le_one
    have hprod : μ.real (B ∩ C) = b * b := by
      simp only [Measure.real, hBC, heq, ENNReal.toReal_mul, b]
    have hab : |a - b| ≤ ε :=
      (abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet
        hB.nullMeasurableSet).trans herrB.le
    have hinter : μ.real (A ∆ (B ∩ C)) ≤ 2 * ε := by
      calc
        μ.real (A ∆ (B ∩ C)) ≤ μ.real ((A ∆ B) ∪ (A ∆ C)) := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro x hx
          simp only [mem_symmDiff, mem_inter_iff, mem_union] at hx ⊢
          tauto
        _ ≤ μ.real (A ∆ B) + μ.real (A ∆ C) := measureReal_union_le _ _
        _ ≤ 2 * ε := by linarith
    have habb : |a - b * b| ≤ 2 * ε := by
      rw [← hprod]
      exact (abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet
        (hB.inter hC).nullMeasurableSet).trans hinter
    have hsquares : |b * b - a * a| ≤ 2 * ε := by
      calc
        |b * b - a * a| = |a - b| * |a + b| := by
          rw [← abs_mul, abs_sub_comm]
          congr 1
          ring
        _ ≤ ε * 2 := by
          apply mul_le_mul hab _ (abs_nonneg _) hε.le
          rw [abs_of_nonneg (add_nonneg ha0 hb0)]
          linarith
        _ = 2 * ε := by ring
    calc
      |a - a * a| = |(a - b * b) + (b * b - a * a)| := by congr 1; ring
      _ ≤ |a - b * b| + |b * b - a * a| := abs_add_le _ _
      _ ≤ 4 * ε := by linarith
  have hz : |a - a * a| = 0 := by
    by_contra hn
    have hp : 0 < |a - a * a| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
    have := hbound (|a - a * a| / 8) (by positivity)
    linarith
  have haa : a = a * a := sub_eq_zero.mp (abs_eq_zero.mp hz)
  have h01 : a = 0 ∨ a = 1 := by
    have : a * (a - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases h01 with h | h
  · left
    exact (ENNReal.toReal_eq_zero_iff (μ A)).mp h |>.resolve_right (measure_ne_top μ A)
  · right
    exact (ENNReal.toReal_eq_one_iff (μ A)).mp h

/-- Hewitt--Savage for a sequence law, expressed by its independent coordinate
maps and equal marginal laws. Invariance is only required modulo null sets. -/
theorem hewitt_savage_coordinate_zero_one {S : Type u} [mS : MeasurableSpace S]
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (hind : iIndepFun (fun i (x : ℕ → S) => x i) μ)
    (hid : ∀ i j, μ.map (fun x => x i) = μ.map (fun x => x j))
    (A : Set (ℕ → S)) (hA : MeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      μ (A ∆ ((fun x i => x (σ i)) ⁻¹' A)) = 0) :
    μ A = 0 ∨ μ A = 1 := by
  apply zero_one_of_independent_approximations μ A hA
  intro ε hε
  obtain ⟨m, B, hBblock, herr⟩ := finiteBlock_approximation μ A hA
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  let p : (ℕ → S) → (ℕ → S) := fun x i => x (blockSwap m i)
  let C := p ⁻¹' B
  have hp : Measurable p := measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
  have hmap : μ.map p = μ := iid_coordinate_permutation_invariant μ hind hid (blockSwap m)
  have hpres (D : Set (ℕ → S)) (hD : MeasurableSet D) : μ (p ⁻¹' D) = μ D := by
    rw [← Measure.map_apply hp hD, hmap]
  have hB : MeasurableSet B := cylinderEvents_le_pi _ hBblock
  have hC : MeasurableSet C := hB.preimage hp
  have hCblock : MeasurableSet[cylinderEvents (X := fun _ : ℕ => S) (Ico m (2 * m))] C :=
    blockSwap_cylinder_measurable m hBblock
  have hdisj : Disjoint (Iio m) (Ico m (2 * m)) := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact (not_le_of_gt hi) hj.1
  have hblocks := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le)
    hind.iIndep hdisj
  have hBC : μ (B ∩ C) = μ B * μ C := (Indep_iff _ _ μ).mp hblocks B C hBblock hCblock
  have herror : μ (A ∆ C) = μ (A ∆ B) := by
    calc
      μ (A ∆ C) = μ ((p ⁻¹' A) ∆ C) :=
        measure_congr ((measure_symmDiff_eq_zero_iff.mp
          (hinv (blockSwap m) (blockSwap_finite m))).symmDiff Filter.EventuallyEq.rfl)
      _ = μ (p ⁻¹' (A ∆ B)) := by rw [preimage_symmDiff]
      _ = μ (A ∆ B) := hpres _ (hA.symmDiff hB)
  have herrReal : μ.real (A ∆ B) < ε := by
    have := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr herr
    simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using this
  refine ⟨B, C, hB, hC, hBC, (hpres B hB).symm, herrReal, ?_⟩
  simpa only [Measure.real, herror] using herrReal

/-- The sequence law of any measurable iid sequence satisfies Hewitt--Savage.
The original probability space and the state space may both be incomplete. -/
theorem hewitt_savage_zero_one {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → S)
    (hX : ∀ i, Measurable (X i)) (hind : IndependentRandomElements P X)
    (hid : ∀ i j, Ch01.law P (X i) = Ch01.law P (X j))
    (A : Set (ℕ → S)) (hA : MeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      Ch01.jointLaw P X (A ∆ ((fun x i => x (σ i)) ⁻¹' A)) = 0) :
    Ch01.jointLaw P X A = 0 ∨ Ch01.jointLaw P X A = 1 := by
  let μ := Ch01.jointLaw P X
  have : IsProbabilityMeasure μ := Ch01.jointLaw_probability P X hX
  have hcoord (i : ℕ) : μ.map (fun x => x i) = Ch01.law P (X i) :=
    Ch01.jointLaw_coordinate P X hX i
  have hcoordIndep : iIndepFun (fun i (x : ℕ → S) => x i) μ := by
    rw [iIndepFun_iff_finset]
    intro s
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (i : s) (x : ℕ → S) => x i)
      (fun i : s => (measurable_pi_apply (i : ℕ)).aemeasurable)).mpr
    have h := ((independentRandomElements_iff_iIndepFun P X).mp hind).restrict s
    have hfin := h.map_fun_eq_pi_map (fun i : s => (hX i).aemeasurable)
    change μ.map (fun x (i : s) => x i) = Measure.pi (fun i : s => μ.map (fun x => x i))
    calc
      μ.map (fun x (i : s) => x i) = P.map (fun ω (i : s) => X i ω) :=
        Measure.map_map (by fun_prop) (Ch01.jointMap_measurable X hX)
      _ = Measure.pi (fun i : s => P.map (X i)) := hfin
      _ = _ := congrArg Measure.pi (funext fun i : s => (hcoord i).symm)
  exact hewitt_savage_coordinate_zero_one μ hcoordIndep
    (fun i j => (hcoord i).trans ((hid i j).trans (hcoord j).symm)) A hA hinv

end ProbabilityFoundations.Ch02
