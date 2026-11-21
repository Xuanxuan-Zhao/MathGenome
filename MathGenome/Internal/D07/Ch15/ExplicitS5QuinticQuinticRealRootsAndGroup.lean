import MathGenome.Internal.Specs.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
import MathGenome.Internal.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch06.Cauchy
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Eisenstein at 3 proves irreducibility. The three sign changes supply three
real roots. Rolle bounds the root count by one more than the derivative's;
any two derivative roots have equal fourth powers and are equal up to sign.
There are five distinct complex roots, so complex conjugation moves exactly
two of them. The root action is faithful. Cauchy supplies an element of order
5, and a full prime cycle together with a transposition generates the symmetric
group. Numbering the five roots gives the final group isomorphism.
-/

noncomputable section
namespace D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
open Polynomial Specs.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

private theorem quintic_degree : quintic.natDegree = 5 := by
  unfold quintic
  compute_degree!

theorem values : Values := by
  norm_num [Values, quintic]

theorem derivative : Derivative := by
  norm_num [Derivative, quintic, Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem irreducibility : Irreducibility := by
  let f : ℤ[X] := X ^ 5 - C 6 * X + C 3
  have hd : f.natDegree = 5 := by dsimp [f]; compute_degree!
  have hm : f.Monic := by dsimp [f]; monicity!
  obtain ⟨_, hq⟩ := D07.Ch11.Eisenstein.integerCriterion 3 f (by norm_num) (Or.inl hm)
    (by omega) (by rw [hm.leadingCoeff]; norm_num)
    (by intro i hi; rw [hd] at hi; interval_cases i <;> norm_num [f, Polynomial.coeff_X])
    (by norm_num [f, Polynomial.coeff_X])
  change Irreducible quintic
  convert hq using 1; norm_num [quintic, f, Polynomial.C_ofNat]

theorem roots_in_intervals : RootsInIntervals := by
  have hcont := (quintic.map (algebraMap ℚ ℝ)).continuous
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Ioo (by norm_num : (-2 : ℝ) ≤ 0) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo ((quintic.map (algebraMap ℚ ℝ)).eval (-2))
      ((quintic.map (algebraMap ℚ ℝ)).eval 0) by norm_num [quintic])
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo ((quintic.map (algebraMap ℚ ℝ)).eval 1)
      ((quintic.map (algebraMap ℚ ℝ)).eval 0) by norm_num [quintic])
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo ((quintic.map (algebraMap ℚ ℝ)).eval 1)
      ((quintic.map (algebraMap ℚ ℝ)).eval 2) by norm_num [quintic])
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_⟩
  · simpa only [Polynomial.eval_map_algebraMap] using hfa
  · simpa only [Polynomial.eval_map_algebraMap] using hfb
  · simpa only [Polynomial.eval_map_algebraMap] using hfc

private theorem derivative_roots_le_two : Fintype.card (quintic.derivative.rootSet ℝ) ≤ 2 := by
  classical
  by_cases h : (quintic.derivative.rootSet ℝ).Nonempty
  · obtain ⟨a, ha⟩ := h
    have eqpow (x : ℝ) (hx : x ∈ quintic.derivative.rootSet ℝ) : x ^ 4 = a ^ 4 := by
      have ha' := (Polynomial.mem_rootSet.mp ha).2
      have hx' := (Polynomial.mem_rootSet.mp hx).2
      change aeval a (Polynomial.derivative quintic) = 0 at ha'
      change aeval x (Polynomial.derivative quintic) = 0 at hx'
      rw [derivative] at ha' hx'
      norm_num at ha' hx'
      linarith
    have hs : quintic.derivative.rootSet ℝ ⊆ ({a, -a} : Set ℝ) := by
      intro x hx
      rcases (pow_eq_pow_iff_of_ne_zero (by decide : (4 : ℕ) ≠ 0)).mp (eqpow x hx) with he | ⟨he, _⟩
      · simp [he]
      · simp [he]
    rw [Set.fintypeCard_eq_ncard]
    exact (Set.ncard_le_ncard hs).trans (by have := Set.ncard_insert_le a ({-a} : Set ℝ); simpa using this)
  · have he : quintic.derivative.rootSet ℝ = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he]

theorem derivative_root_count : DerivativeRootCount := by
  classical
  let p := quintic.derivative.map (algebraMap ℚ ℝ)
  have hcont := p.continuous
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Ioo' (by norm_num : (-2 : ℝ) ≤ 0) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (p.eval 0) (p.eval (-2)) by
      dsimp [p]; rw [derivative]; norm_num)
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 2) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (p.eval 0) (p.eval 2) by
      dsimp [p]; rw [derivative]; norm_num)
  have hn : quintic.derivative ≠ 0 := by
    rw [derivative]
    intro h
    have h0 := congrArg (fun p : ℚ[X] => p.coeff 0) h
    norm_num at h0
  have hab : a ≠ b := by linarith [ha.2, hb.1]
  have hmem : ({a, b} : Finset ℝ) ⊆ (quintic.derivative.rootSet ℝ).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa only [Set.mem_toFinset, Polynomial.mem_rootSet_of_ne hn,
        ← Polynomial.eval_map_algebraMap] using hfa
    · simpa only [Set.mem_toFinset, Polynomial.mem_rootSet_of_ne hn,
        ← Polynomial.eval_map_algebraMap] using hfb
  apply le_antisymm derivative_roots_le_two
  have := Finset.card_le_card hmem
  simpa [hab, Set.toFinset_card] using this

theorem real_root_count : RealRootCount := by
  classical
  obtain ⟨a, b, c, ha, hb, hc, hfa, hfb, hfc⟩ := roots_in_intervals
  have hab : a ≠ b := by linarith [ha.2, hb.1]
  have hac : a ≠ c := by linarith [ha.2, hc.1]
  have hbc : b ≠ c := by linarith [hb.2, hc.1]
  have hn : quintic ≠ 0 := by intro h; have := quintic_degree; simp [h] at this
  have hmem : ({a, b, c} : Finset ℝ) ⊆ (quintic.rootSet ℝ).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp [Polynomial.mem_rootSet_of_ne hn, *]
  have hlo : 3 ≤ Fintype.card (quintic.rootSet ℝ) := by
    have := Finset.card_le_card hmem
    simpa [hab, hac, hbc, Set.toFinset_card] using this
  have hhi := quintic.card_rootSet_le_derivative.trans (Nat.add_le_add_right derivative_roots_le_two 1)
  exact le_antisymm hhi hlo

theorem complex_root_count : ComplexRootCount := by
  change Fintype.card (quintic.rootSet ℂ) = 5
  rw [Polynomial.card_rootSet_eq_natDegree
    (show Irreducible quintic from irreducibility).separable (IsAlgClosed.splits _), quintic_degree]

theorem complex_splitting_field : ComplexSplittingField := by
  have hs : quintic.IsSplittingField ℚ complexSplittingField :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have := hs
  have : Normal ℚ complexSplittingField := Normal.of_isSplittingField quintic
  refine ⟨hs, (Complex.conjAe.restrictScalars ℚ).restrictNormal complexSplittingField, ?_⟩
  intro z
  exact (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes complexSplittingField z

theorem conjugation_action : ConjugationAction := by
  intro z
  exact Gal.galActionHom_restrict quintic ℂ (Complex.conjAe.restrictScalars ℚ) z

theorem conjugation_transposition : ConjugationTransposition := by
  classical
  rw [ConjugationTransposition, ← Equiv.Perm.card_support_eq_two]
  have h := Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv quintic
  simp only [Set.toFinset_card] at h
  have hr : Fintype.card (quintic.rootSet ℝ) = 3 := real_root_count
  have hc : Fintype.card (quintic.rootSet ℂ) = 5 := complex_root_count
  omega

theorem contains_five_cycle : ContainsFiveCycle := by
  classical
  have hp : quintic.natDegree.Prime := by rw [quintic_degree]; norm_num
  obtain ⟨σ, hσ⟩ := D07.Ch06.Cauchy.exists_element_order_eq quintic.Gal 5 (by norm_num)
    (by simpa only [quintic_degree] using (Gal.prime_degree_dvd_card
      (show Irreducible quintic from irreducibility) hp))
  have ho : orderOf (Gal.galActionHom quintic ℂ σ) = 5 :=
    (orderOf_injective _ (Gal.galActionHom_injective quintic ℂ) σ).trans hσ
  have hc : Fintype.card (quintic.rootSet ℂ) = 5 := complex_root_count
  have hcyc := Equiv.Perm.isCycle_of_prime_order'' (by rw [hc]; norm_num) (ho.trans hc.symm)
  exact ⟨σ, hcyc, hcyc.orderOf.symm.trans ho⟩

theorem cycle_and_transposition_generate : CycleAndTranspositionGenerate := by
  classical
  intro σ τ hσ hcard hτ
  exact Equiv.Perm.closure_prime_cycle_swap (by norm_num) hσ
    (Finset.eq_univ_of_card _ (by simpa using hcard)) hτ

theorem full_root_group : FullRootGroup := by
  apply Gal.galActionHom_bijective_of_prime_degree (show Irreducible quintic from irreducibility)
  · rw [quintic_degree]; norm_num
  · have hr : Fintype.card (quintic.rootSet ℝ) = 3 := real_root_count
    have hc : Fintype.card (quintic.rootSet ℂ) = 5 := complex_root_count
    omega

theorem galois_group_S5 : GaloisGroupS5 := by
  let b : quintic.rootSet ℂ ≃ Fin 5 := Fintype.equivFinOfCardEq complex_root_count
  exact ⟨(MulEquiv.ofBijective (Gal.galActionHom quintic ℂ) full_root_group).trans
    b.permCongrHom⟩

end D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
