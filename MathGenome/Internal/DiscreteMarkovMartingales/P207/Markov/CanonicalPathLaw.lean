import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.CanonicalPathLaw
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Interfaces
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.ProcessInterfaces

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

set_option linter.unusedSectionVars false

universe u v

namespace P207.Markov
noncomputable section

namespace CanonicalPathLaw
abbrev coordinate : CanonicalPathLawSpec.coordinateType.{u} := @P207.Markov.coordinate
abbrev prefixCylinder : CanonicalPathLawSpec.prefixCylinderType.{u} := @P207.Markov.prefixCylinder
abbrev coordinateFiltration : CanonicalPathLawSpec.coordinateFiltrationType.{u} :=
  @P207.Markov.coordinateFiltration
abbrev historyKernel : CanonicalPathLawSpec.historyKernelType.{u} := @P207.Markov.historyKernel
abbrev pathLaw : CanonicalPathLawSpec.pathLawType.{u} := @P207.Markov.pathLaw
abbrev statePathLaw : CanonicalPathLawSpec.statePathLawType.{u} := @P207.Markov.statePathLaw
abbrev pathKernel : CanonicalPathLawSpec.pathKernelType.{u} := @P207.Markov.pathKernel
abbrev stateExpectation : CanonicalPathLawSpec.stateExpectationType.{u} := @P207.Markov.stateExpectation
end CanonicalPathLaw

variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S]

 theorem pathLaw_probability (P : StochasticMatrix S) (ν : ProbabilityLaw S) :
    IsProbabilityMeasure (pathLaw P ν) := by
  unfold pathLaw
  infer_instance

theorem pathKernel_apply (P : StochasticMatrix S) (i : S) :
    pathKernel P i = statePathLaw P i := rfl

theorem pathKernel_markov (P : StochasticMatrix S) : IsMarkovKernel (pathKernel P) :=
  ⟨fun i => pathLaw_probability P (PMF.pure i)⟩

theorem measurable_statePathLaw (P : StochasticMatrix S) : Measurable (statePathLaw P) :=
  measurable_of_countable _

theorem measurableSet_prefixCylinder (n : ℕ) (x : ℕ → S) :
    MeasurableSet (prefixCylinder n x) := by
  have heq : prefixCylinder n x = ⋂ k, ⋂ (_ : k ≤ n), {ω : ℕ → S | ω k = x k} := by
    ext ω
    simp [prefixCylinder]
  rw [heq]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply k) measurable_const

 theorem coordinate_adapted : Adapted (coordinateFiltration (S := S)) coordinate :=
  P207.adapted_naturalFiltration _ _

 theorem coordinateFiltration_eq_comap (n : ℕ) :
    coordinateFiltration (S := S) n =
      MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ => S) n) inferInstance := by
  apply le_antisymm
  · refine iSup₂_le fun k hkn => ?_
    have hk : Measurable (fun x : (i : Finset.Iic n) → S => x ⟨k, Finset.mem_Iic.mpr hkn⟩) :=
      measurable_pi_apply _
    have hcomp : coordinate k =
        (fun x : (i : Finset.Iic n) → S => x ⟨k, Finset.mem_Iic.mpr hkn⟩) ∘
          Preorder.frestrictLe (π := fun _ => S) n := rfl
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hk.comap_le
  · have hm : @Measurable (ℕ → S) ((i : Finset.Iic n) → S)
        (coordinateFiltration n) inferInstance (Preorder.frestrictLe (π := fun _ => S) n) := by
      let : MeasurableSpace (ℕ → S) := coordinateFiltration n
      exact measurable_pi_iff.mpr fun k => (coordinate_adapted k).mono
        ((coordinateFiltration (S := S)).mono (Finset.mem_Iic.mp k.2)) le_rfl
    exact hm.comap_le

 theorem pathLaw_map_prefix_zero (P : StochasticMatrix S) (ν : ProbabilityLaw S) :
    (pathLaw P ν).map (Preorder.frestrictLe (π := fun _ => S) 0) =
      ν.toMeasure.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm := by
  rw [pathLaw, Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

 theorem pathLaw_map_zero (P : StochasticMatrix S) (ν : ProbabilityLaw S) :
    (pathLaw P ν).map (coordinate 0) = ν.toMeasure := by
  have h := congrArg (fun ρ => ρ.map
    (fun x : (i : Finset.Iic 0) → S => x ⟨0, by simp⟩))
    (pathLaw_map_prefix_zero P ν)
  have he : Measurable (fun x : (i : Finset.Iic 0) → S => x ⟨0, by simp⟩) :=
    measurable_pi_apply _
  rw [Measure.map_map he (Preorder.measurable_frestrictLe 0),
    Measure.map_map he (MeasurableEquiv.measurable _)] at h
  change (pathLaw P ν).map (fun ω : ℕ → S => ω 0) = ν.toMeasure
  simpa [Function.comp_def, Measure.map_id] using h

 theorem prefixCylinder_eq_preimage (n : ℕ) (x : ℕ → S) :
    prefixCylinder n x = (Preorder.frestrictLe (π := fun _ => S) n) ⁻¹' {Preorder.frestrictLe (π := fun _ => S) n x} := by
  ext ω
  simp only [prefixCylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext k
    exact h k (Finset.mem_Iic.mp k.2)
  · intro h k hk
    exact congrFun h ⟨k, Finset.mem_Iic.mpr hk⟩

 theorem pathLaw_prefix_zero (P : StochasticMatrix S) (ν : ProbabilityLaw S) (x : ℕ → S) :
    pathLaw P ν (prefixCylinder 0 x) = ν (x 0) := by
  have h := congrArg (fun ρ : Measure S => ρ {x 0}) (pathLaw_map_zero P ν)
  rw [Measure.map_apply (show Measurable (coordinate (S := S) 0) from measurable_pi_apply 0) (measurableSet_singleton _),
    law_measure_singleton] at h
  change (pathLaw P ν) {ω : ℕ → S | ω 0 = x 0} = _ at h
  have heq : prefixCylinder 0 x = {ω : ℕ → S | ω 0 = x 0} := by
    ext ω
    simp [prefixCylinder]
  rw [heq]
  exact h

 theorem pathLaw_prefix_succ (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (n : ℕ) (x : ℕ → S) :
    pathLaw P ν (prefixCylinder (n + 1) x) =
      pathLaw P ν (prefixCylinder n x) * P (x n) (x (n + 1)) := by
  have heq : prefixCylinder (n + 1) x =
      (fun ω : ℕ → S => (Preorder.frestrictLe (π := fun _ => S) n ω, ω (n + 1))) ⁻¹'
        ({Preorder.frestrictLe (π := fun _ => S) n x} ×ˢ {x (n + 1)}) := by
    ext ω
    have hh : (Preorder.frestrictLe (π := fun _ => S) n ω = Preorder.frestrictLe (π := fun _ => S) n x) ↔
        ∀ k ≤ n, ω k = x k := by
      exact (Set.ext_iff.mp (prefixCylinder_eq_preimage n x) ω).symm
    simp only [prefixCylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
      Set.mem_singleton_iff, hh]
    exact ⟨fun h => ⟨fun k hk => h k (Nat.le_succ_of_le hk), h _ le_rfl⟩,
      fun h k hk => (Nat.le_succ_iff_eq_or_le.mp hk).elim (fun he => he ▸ h.2) (h.1 k)⟩
  rw [heq, ← Measure.map_apply (by fun_prop)
      ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    pathLaw, ← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton]
  change (P (x n)).toMeasure {x (n + 1)} *
    (pathLaw P ν).map (Preorder.frestrictLe (π := fun _ => S) n) {Preorder.frestrictLe (π := fun _ => S) n x} = _
  rw [law_measure_singleton, Measure.map_apply (Preorder.measurable_frestrictLe n)
    (measurableSet_singleton _), ← prefixCylinder_eq_preimage, mul_comm]
  rfl

 theorem pathLaw_prefix (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (n : ℕ) (x : ℕ → S) :
    pathLaw P ν (prefixCylinder n x) =
      ν (x 0) * ∏ k ∈ Finset.range n, P (x k) (x (k + 1)) := by
  induction n with
  | zero => simpa using pathLaw_prefix_zero P ν x
  | succ n ih => rw [pathLaw_prefix_succ, ih, Finset.prod_range_succ, mul_assoc]

/-- Countability of finite histories upgrades agreement on atomic prefixes
into equality of measures on the full product sigma-algebra. -/
theorem pathMeasure_ext (μ ρ : Measure (ℕ → S)) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (h : ∀ n x, μ (prefixCylinder n x) = ρ (prefixCylinder n x)) : μ = ρ := by
  let Q : (I : Finset ℕ) → Measure ((i : I) → S) := fun I => ρ.map I.restrict
  have hQ : IsProjectiveMeasureFamily (α := fun _ => S) Q := by
    intro I J hJI
    dsimp [Q]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hρ : IsProjectiveLimit (α := fun _ => S) ρ Q := fun _ => rfl
  apply IsProjectiveLimit.unique (α := fun _ => S) (P := Q) _ hρ
  apply (isProjectiveLimit_nat_iff hQ μ).mpr
  intro n
  apply Measure.ext_of_singleton
  intro y
  let x : ℕ → S := fun k => if hk : k ≤ n then y ⟨k, Finset.mem_Iic.mpr hk⟩
    else Classical.choice (inferInstance : Nonempty S)
  have hx : Preorder.frestrictLe (π := fun _ => S) n x = y := by
    funext k
    simp only [Preorder.frestrictLe_apply, x, dite_eq_left (Finset.mem_Iic.mp k.2)]
  change μ.map (Preorder.frestrictLe n) {y} = ρ.map (Preorder.frestrictLe n) {y}
  rw [← hx, Measure.map_apply (Preorder.measurable_frestrictLe _) (measurableSet_singleton _),
    Measure.map_apply (Preorder.measurable_frestrictLe _) (measurableSet_singleton _),
    ← prefixCylinder_eq_preimage]
  exact h n x

 theorem pathLaw_unique (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (ρ : Measure (ℕ → S)) [IsProbabilityMeasure ρ]
    (h : ∀ n x, ρ (prefixCylinder n x) =
      ν (x 0) * ∏ k ∈ Finset.range n, P (x k) (x (k + 1))) : ρ = pathLaw P ν := by
  apply pathMeasure_ext
  intro n x
  rw [h n x, pathLaw_prefix]

 theorem coordinate_isMarkovChain (P : StochasticMatrix S) (ν : ProbabilityLaw S) :
    IsMarkovChain P ν coordinate coordinateFiltration (pathLaw P ν) := by
  refine ⟨coordinate_adapted, ?_, ?_⟩
  · intro i
    have h := congrArg (fun ρ : Measure S => ρ {i}) (pathLaw_map_zero P ν)
    rw [Measure.map_apply (show Measurable (coordinate (S := S) 0) from measurable_pi_apply 0)
      (measurableSet_singleton i), law_measure_singleton] at h
    exact h
  · intro n j
    have hc := condDistrib_ae_eq_condExp (μ := pathLaw P ν)
      (Preorder.measurable_frestrictLe (X := fun _ => S) n)
      (show Measurable (coordinate (S := S) (n + 1)) from measurable_pi_apply _)
      (measurableSet_singleton j)
    have hk := Kernel.condDistrib_trajMeasure (X := fun _ => S) (μ₀ := ν.toMeasure)
      (κ := historyKernel P) (a := n)
    have hk' := ae_of_ae_map (μ := pathLaw P ν)
      (Preorder.measurable_frestrictLe (X := fun _ => S) n).aemeasurable hk
    rw [coordinateFiltration_eq_comap]
    apply hc.symm.trans
    filter_upwards [hk'] with ω hω
    change ((condDistrib (coordinate (n + 1)) (Preorder.frestrictLe n)
      (pathLaw P ν)) (Preorder.frestrictLe n ω)).real {j} = _
    rw [show condDistrib (coordinate (n + 1)) (Preorder.frestrictLe n)
        (pathLaw P ν) (Preorder.frestrictLe n ω) =
        historyKernel P n (Preorder.frestrictLe n ω) from hω]
    change ((P (ω n)).toMeasure {j}).toReal = (P (ω n) j).toReal
    rw [law_measure_singleton]

/-- Prefix events are measurable for the chain's supplied filtration. -/
theorem measurableSet_processPrefix {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (hX : Adapted ℱ X) (n : ℕ) (x : ℕ → S) :
    MeasurableSet[ℱ n] {ω | ∀ k ≤ n, X k ω = x k} := by
  have heq : {ω | ∀ k ≤ n, X k ω = x k} =
      ⋂ k : Finset.Iic n, {ω | X k ω = x k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h k => h k (Finset.mem_Iic.mp k.2),
      fun h k hk => h ⟨k, Finset.mem_Iic.mpr hk⟩⟩
  rw [heq]
  let : MeasurableSpace Ω := ℱ n
  exact MeasurableSet.iInter fun k => measurableSet_eq_fun
    ((hX k).mono (ℱ.mono (Finset.mem_Iic.mp k.2)) le_rfl) measurable_const

/-- The conditional expectation identity gives the prefix recursion even
when the preceding prefix has probability zero. -/
theorem chain_prefix_succ {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (n : ℕ) (x : ℕ → S) :
    μ {ω | ∀ k ≤ n + 1, X k ω = x k} =
      μ {ω | ∀ k ≤ n, X k ω = x k} * P (x n) (x (n + 1)) := by
  let A : Set Ω := {ω | ∀ k ≤ n, X k ω = x k}
  let B : Set Ω := {ω | X (n + 1) ω = x (n + 1)}
  have hA : MeasurableSet[ℱ n] A := measurableSet_processPrefix X ℱ h.1 n x
  have hAm : MeasurableSet A := (ℱ.le n) A hA
  have hB : MeasurableSet B := measurableSet_eq_fun (h.1.measurable (i := n + 1)) measurable_const
  have heq : {ω | ∀ k ≤ n + 1, X k ω = x k} = A ∩ B := by
    ext ω
    exact ⟨fun h => ⟨fun k hk => h k (Nat.le_succ_of_le hk), h _ le_rfl⟩,
      fun h k hk => (Nat.le_succ_iff_eq_or_le.mp hk).elim (fun he => he ▸ h.2) (h.1 k)⟩
  have hi : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hB
  have hcond : μ[B.indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      (fun ω => realMatrix P (X n ω) (x (n + 1))) := h.2.2 n (x (n + 1))
  have he : (μ (A ∩ B)).toReal = (μ A).toReal * (P (x n) (x (n + 1))).toReal := by
    calc
      (μ (A ∩ B)).toReal = ∫ ω in A, B.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        rw [setIntegral_indicator hB, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = ∫ ω in A, μ[B.indicator (fun _ => (1 : ℝ)) | ℱ n] ω ∂μ :=
        (setIntegral_condExp (ℱ.le n) hi hA).symm
      _ = ∫ ω in A, realMatrix P (X n ω) (x (n + 1)) ∂μ :=
        setIntegral_congr_ae hAm (hcond.mono fun ω hω _ => hω)
      _ = ∫ _ in A, (P (x n) (x (n + 1))).toReal ∂μ :=
        setIntegral_congr_fun hAm fun ω hω => by
          change (P (X n ω) (x (n + 1))).toReal = _
          rw [hω n le_rfl]
      _ = (μ A).toReal * (P (x n) (x (n + 1))).toReal := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
  rw [heq]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (entry_ne_top P _ _))).mp
  simpa only [ENNReal.toReal_mul] using he

 theorem chain_prefix {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (n : ℕ) (x : ℕ → S) :
    μ {ω | ∀ k ≤ n, X k ω = x k} =
      ν (x 0) * ∏ k ∈ Finset.range n, P (x k) (x (k + 1)) := by
  induction n with
  | zero => simpa using h.2.1 (x 0)
  | succ n ih => rw [chain_prefix_succ P ν X ℱ μ h, ih, Finset.prod_range_succ, mul_assoc]

 theorem chain_pathLaw {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) :
    μ.map (fun ω n => X n ω) = pathLaw P ν := by
  have hm : Measurable (fun ω n => X n ω) := measurable_pi_iff.mpr (fun _ => h.1.measurable)
  have : IsProbabilityMeasure (μ.map (fun ω n => X n ω)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply pathLaw_unique
  intro n x
  rw [Measure.map_apply hm (measurableSet_prefixCylinder n x)]
  exact chain_prefix P ν X ℱ μ h n x

end
end P207.Markov
