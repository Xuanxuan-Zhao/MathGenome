import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.RealClasses
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Group
import MathGenome.Internal.D07.Ch23.Frobenius
import MathGenome.Internal.D07.Ch23.QuaternionAlgebra
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The real Brauer group has two elements, represented by ℝ and the Hamilton quaternions. -/

namespace RM03.Brauer

theorem quaternion_isCentralDivision : Specs.RM03.Brauer.QuaternionIsCentralDivision := by
  refine ⟨⟨?_⟩, inferInstance⟩
  intro q hq
  obtain ⟨r, hr⟩ := D07.Ch23.QuaternionAlgebra.centerReal.1 q |>.mp
    (fun p => ((Subalgebra.mem_center_iff.mp hq) p).symm)
  exact Algebra.mem_bot.mpr ⟨r, hr.symm⟩

theorem quaternion_conjugation : Specs.RM03.Brauer.QuaternionConjugation :=
  ⟨Quaternion.starAe, fun _ => rfl⟩

private theorem complex_alternative_impossible {D : Type} [DivisionRing D] [Algebra ℝ D]
    [Algebra.IsCentral ℝ D] (e : ℂ ≃ₐ[ℝ] D) : False := by
  have hcenter : e Complex.I ∈ Subalgebra.center ℝ D := by
    apply Subalgebra.mem_center_iff.mpr
    intro d
    obtain ⟨z, rfl⟩ := e.surjective d
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hcenter
  have h : Complex.I = algebraMap ℝ ℂ r := e.injective (hr.trans (e.commutes r).symm)
  have him := congrArg Complex.im h
  simp at him

theorem real_classes :
    Specs.RM03.Brauer.RealClasses quaternion_isCentralDivision (instAddCommGroup.{0, 0} ℝ) := by
  let hH : CSA.IsCentralDivision ℝ (Quaternion ℝ) := quaternion_isCentralDivision
  let hR : CSA.IsCentralDivision ℝ ℝ := ⟨inferInstance, inferInstance⟩
  let r : BrauerGroup.{0, 0} ℝ := classOf (divisionCSA hR)
  let q : BrauerGroup.{0, 0} ℝ := classOf (divisionCSA hH)
  change r = 0 ∧ q ≠ 0 ∧ (∀ c, c = r ∨ c = q) ∧
    2 • q = 0 ∧ ∃ e : BrauerGroup.{0, 0} ℝ ≃+ ZMod 2, e q = 1
  have hr : r = 0 := by
    rw [zero_eq_classOf_scalar]
    exact classOf_eq_of_algEquiv (ULift.algEquiv (R := ℝ)).symm
  have hq : q ≠ 0 := by
    rw [← hr]
    intro h
    obtain ⟨e⟩ := (classOf_division_eq_iff ℝ _ _ hH hR).mp h
    exact D07.Ch23.Frobenius.pairwiseNonisomorphic.2.1 ⟨e.symm⟩
  have hall (c : BrauerGroup.{0, 0} ℝ) : c = r ∨ c = q := by
    obtain ⟨D, _, _, hD, rfl⟩ := exists_division_representative ℝ c
    let : FiniteDimensional ℝ D := hD.2
    let : Algebra.IsCentral ℝ D := hD.1
    obtain ⟨n, hn, _⟩ := D07.Ch23.Frobenius.finiteDimensionalClassification D
    rcases hn with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
    · exact Or.inl (classOf_eq_of_algEquiv e.symm)
    · exact (complex_alternative_impossible e).elim
    · exact Or.inr (classOf_eq_of_algEquiv e.symm)
  have hneg : -q = q := by
    obtain ⟨e, _⟩ := quaternion_conjugation
    change -classOf (divisionCSA hH) = classOf (divisionCSA hH)
    rw [classOf_neg]
    exact classOf_eq_of_algEquiv e.symm
  have htwo : 2 • q = 0 := by
    calc
      2 • q = -q + q := by rw [two_nsmul, hneg]
      _ = 0 := neg_add_cancel q
  have hgen (c : BrauerGroup.{0, 0} ℝ) : c ∈ AddSubgroup.zmultiples q := by
    rcases hall c with hc | rfl
    · rw [hc, hr]
      exact AddSubgroup.zero_mem _
    · exact ⟨1, one_zsmul q⟩
  have hcard : Nat.card (BrauerGroup.{0, 0} ℝ) = 2 := by
    have huniv : (Set.univ : Set (BrauerGroup.{0, 0} ℝ)) = {r, q} := by
      ext c
      simpa only [Set.mem_univ, true_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using hall c
    rw [← Set.ncard_univ, huniv, Set.ncard_pair (hr.trans_ne hq.symm)]
  exact ⟨hr, hq, hall, htwo, (zmodAddEquivOfGenerator hgen hcard).symm,
    zmodAddEquivOfGenerator_symm_apply_generator hgen hcard⟩

theorem real_classification : Specs.RM03.Brauer.RealClassification :=
  ⟨quaternion_isCentralDivision, instAddCommGroup.{0, 0} ℝ,
    ⟨zero_eq_classOf_scalar ℝ, fun A B => ⟨tensorCSA A B, rfl, classOf_add A B⟩,
      fun A => ⟨oppositeCSA A, rfl, classOf_neg A⟩, classOf_eq_zero_iff_split⟩,
    real_classes⟩

end RM03.Brauer
