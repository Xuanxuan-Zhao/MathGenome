import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.ObstructionAndClassification
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.ProperSplitSolutions
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CyclicAndSplitExamples

namespace GaloisFormalization.IG.CyclicAndSplitExamples

open FiniteEmbeddingProblem
open scoped IsMulCommutative

noncomputable section

local notation "C₂" => Multiplicative (ZMod 2)
local notation "C₄" => Multiplicative (ZMod 4)
local notation "g₂" => (Multiplicative.ofAdd (1 : ZMod 2))

/-- The extension by reduction modulo two, with prescribed map the identity. -/
abbrev cyclicProblem := Specs.GaloisFormalization.IG.CyclicAndSplitExamples.cyclicProblem

/-- The extension by projection onto the first factor, with prescribed map the identity. -/
abbrev splitProblem := Specs.GaloisFormalization.IG.CyclicAndSplitExamples.splitProblem

/-- The weak solution given by the first-factor inclusion. -/
abbrev firstFactorSolution :=
  Specs.GaloisFormalization.IG.CyclicAndSplitExamples.firstFactorSolution

theorem cyclic_central : IsCentral cyclicProblem :=
  fun _ _ => Subgroup.mem_center_iff.mpr fun _ => mul_comm _ _

theorem cyclic_kernel (b : C₄) :
    b ∈ cyclicProblem.kernel ↔ b.toAdd = 0 ∨ b.toAdd = 2 := by
  change (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) b.toAdd = 0 ↔
    b.toAdd = 0 ∨ b.toAdd = 2
  generalize b.toAdd = a
  revert a
  decide

theorem cyclic_generator_fibre (b : C₄) :
    cyclicProblem.pi b = g₂ ↔ b.toAdd = 1 ∨ b.toAdd = 3 := by
  change (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) b.toAdd = 1 ↔
    b.toAdd = 1 ∨ b.toAdd = 3
  generalize b.toAdd = a
  revert a
  decide

private theorem generator_sq : g₂ ^ 2 = (1 : C₂) := by decide

private theorem lift_sq (b : C₄) (hb : cyclicProblem.pi b = g₂) :
    b ^ 2 = Multiplicative.ofAdd (2 : ZMod 4) := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  change b.toAdd + b.toAdd = 2
  rcases (cyclic_generator_fibre b).mp hb with h | h <;> rw [h] <;> decide

theorem cyclic_generator_lift_order (b : C₄) (hb : cyclicProblem.pi b = g₂) :
    orderOf b = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · change b ^ 2 ≠ 1
    rw [lift_sq b hb]
    decide
  · change b ^ (2 * 2) = 1
    rw [pow_mul, lift_sq b hb]
    decide

theorem cyclic_no_weak_solution : ¬ Nonempty cyclicProblem.WeakSolution := by
  rintro ⟨sol⟩
  have hb : cyclicProblem.pi (sol.lift g₂) = g₂ := WeakSolution.commutes_apply sol g₂
  have hs : sol.lift g₂ ^ 2 = 1 := by rw [← map_pow, generator_sq, map_one]
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [cyclic_generator_lift_order _ hb] at hd
  exact (by decide : ¬ (4 ∣ 2)) hd

theorem cyclic_factor_set_value (s : NormalizedSection cyclicProblem) :
    ((factorSet cyclicProblem s g₂ g₂).toMul.val : C₄).toAdd = (2 : ZMod 4) := by
  have hg : g₂ * g₂ = (1 : C₂) := (pow_two g₂).symm.trans generator_sq
  rw [factorSet_coe, hg, s.map_one, inv_one, mul_one, ← pow_two,
    lift_sq (s g₂) (s.rightInverse g₂)]
  rfl

local notation "A" => Additive cyclicProblem.kernel

local instance : IsMulCommutative cyclicProblem.kernel := inferInstance
local instance : DistribMulAction C₂ A := quotientKernelAction cyclicProblem

private theorem kernel_double (a : A) : 2 • a = 0 := by
  rw [two_nsmul]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (a.toMul.val : C₄).toAdd + (a.toMul.val : C₄).toAdd = 0
  rcases (cyclic_kernel a.toMul.val).mp a.toMul.property with h | h <;> rw [h] <;> decide

theorem cyclic_normalized_differential (z : GH.continuousCochains C₂ A 1)
    (hz : z.val ![1] = 0) :
    (GH.continuousDifferential C₂ A 1 z).val ![g₂, g₂] = 2 • z.val ![g₂] ∧
    2 • z.val ![g₂] = 0 := by
  refine ⟨?_, kernel_double _⟩
  rw [GH.differential_one, ← pow_two, generator_sq, hz, sub_zero,
    quotientKernelAction_eq_self_of_isCentral cyclicProblem cyclic_central, two_nsmul]

theorem cyclic_nonzero_classes :
    continuousExtensionClass cyclicProblem ≠ 0 ∧
    extensionClass cyclicProblem ≠ 0 ∧ weakLiftObstruction cyclicProblem ≠ 0 := by
  have hcontinuous : continuousExtensionClass cyclicProblem ≠ 0 := by
    intro h
    let s := normalizedSection cyclicProblem
    let c := factorCocycle cyclicProblem s
    have hc : GH.continuousClass C₂ A 2 c = GH.continuousClass C₂ A 2 0 := by
      rw [show GH.continuousClass C₂ A 2 c = continuousExtensionClass cyclicProblem from
        continuousClass_of_section cyclicProblem s, h, map_zero]
    obtain ⟨z, hz⟩ := (GH.continuousClass_succ_eq_iff (n := 1) c 0).mp hc
    change GH.continuousDifferential C₂ A 1 z = c.val - 0 at hz
    rw [sub_zero] at hz
    have hδ (q r : C₂) :
        (GH.continuousDifferential C₂ A 1 z).val ![q, r] = factorSet cyclicProblem s q r := by
      rw [hz]
      exact factorCocycle_apply cyclicProblem s q r
    have hz₀ : z.val ![1] = 0 := by
      simpa only [GH.differential_one, one_smul, mul_one, add_sub_cancel_right,
        (factorSet_normalized cyclicProblem s).1] using hδ 1 1
    obtain ⟨heval, hdouble⟩ := cyclic_normalized_differential z hz₀
    have hzero : factorSet cyclicProblem s g₂ g₂ = 0 :=
      (hδ g₂ g₂).symm.trans (heval.trans hdouble)
    have htwo := cyclic_factor_set_value s
    rw [hzero] at htwo
    exact (by decide : (0 : ZMod 4) ≠ 2) htwo
  refine ⟨hcontinuous, ?_, ?_⟩
  · obtain ⟨e, _, he⟩ := ordinaryClass_comparison cyclicProblem
    rw [← he, map_ne_zero_iff e e.injective]
    exact hcontinuous
  · exact fun h => cyclic_no_weak_solution
      ((weakLift_obstruction_and_classification cyclicProblem).1.mpr h)

theorem product_is_split : IsSplit splitProblem :=
  ⟨firstFactorSolution.lift.toMonoidHom, MonoidHom.ext fun _ => rfl⟩

theorem product_no_proper_solution :
    ¬ ∃ sol : splitProblem.WeakSolution, WeakSolution.IsProper sol := by
  rintro ⟨sol, hsol⟩
  have h := (WeakSolution.proper_iff_map_kernel sol).mp hsol
  change (MonoidHom.id C₂).ker.map sol.lift.toMonoidHom = splitProblem.kernel at h
  rw [MonoidHom.ker_id, Subgroup.map_bot] at h
  have hmem : ((1, g₂) : C₂ × C₂) ∈ splitProblem.kernel := by
    change splitProblem.pi (1, g₂) = 1
    rfl
  rw [← h, Subgroup.mem_bot] at hmem
  exact (by decide : g₂ ≠ (1 : C₂)) (congrArg Prod.snd hmem)

end
end GaloisFormalization.IG.CyclicAndSplitExamples
