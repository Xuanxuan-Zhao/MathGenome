import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology

open Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction NNReal

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- The test-function LF topology, defined using all compact subsets. -/
@[instance_reducible]
noncomputable def lfTopology (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) : TopologicalSpace (Tests 𝕜 Ω) :=
  TestFunction.topologicalSpace Ω 𝕜 ⊤

/-- The continuous scalar-linear dual of scalar-valued test functions. -/
def distributionSpace (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) : Type := Tests 𝕜 Ω →L[𝕜] 𝕜

/-- Compact cofinality follows from interior nesting and the open cover theorem. -/
theorem Exhaustion.cofinal (e : Exhaustion Ω) (K : Compacts (Domain d))
    (hK : (K : Set (Domain d)) ⊆ Ω) : ∃ j, (K : Set (Domain d)) ⊆ e.compact j := by
  have hm : Monotone (fun j => (e.compact j : Set (Domain d))) :=
    monotone_nat_of_le_succ fun j => (e.nested j).trans interior_subset
  have hc : ∀ x ∈ K, ∃ j, x ∈ interior (e.compact j : Set (Domain d)) := by
    intro x hx
    have : x ∈ ⋃ j, (e.compact j : Set (Domain d)) := by rw [e.covers]; exact hK hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp this
    exact ⟨j + 1, e.nested j hj⟩
  obtain ⟨j, hj⟩ := K.isCompact.elim_directed_cover
    (fun j => interior (e.compact j : Set (Domain d))) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr (hc x hx))
    (Monotone.directed_le fun _ _ h => interior_mono (hm h))
  exact ⟨j, hj.trans interior_subset⟩

/-- A compact-step map factors through any larger step, without altering its function. -/
theorem inclusion_factor {K L : Compacts (Domain d)} (hK : (K : Set (Domain d)) ⊆ Ω)
    (hL : (L : Set (Domain d)) ⊆ Ω) (hKL : K ≤ L) :
    (TestFunction.ofSupportedIn hK : Step 𝕜 K → Tests 𝕜 Ω) =
    TestFunction.ofSupportedIn hL ∘
      (ContDiffMapSupportedIn.monoCLM 𝕜 : Step 𝕜 K →L[𝕜] Step 𝕜 L) := by
  funext φ
  apply TestFunction.ext
  intro x
  simp [ContDiffMapSupportedIn.monoCLM_apply, hKL]

/-- The final topology before locally convex modification is already
independent of restricting the indexing system to an exhaustion. -/
theorem exhaustionOriginal_eq (e : Exhaustion Ω) :
    exhaustionOriginal (𝕜 := 𝕜) e = TestFunction.originalTop Ω 𝕜 ⊤ := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    exact le_iSup₂_of_le (e.compact j) (e.inside j) le_rfl
  · refine iSup₂_le fun K hK => ?_
    obtain ⟨j, hj⟩ := e.cofinal K hK
    rw [← continuous_iff_coinduced_le]
    rw [inclusion_factor hK (e.inside j) hj]
    have hc : @Continuous (Step 𝕜 (e.compact j)) (Tests 𝕜 Ω) inferInstance
        (exhaustionOriginal (𝕜 := 𝕜) e) (TestFunction.ofSupportedIn (e.inside j)) := by
      rw [continuous_iff_coinduced_le]
      exact le_iSup_of_le j le_rfl
    let : TopologicalSpace (Tests 𝕜 Ω) := exhaustionOriginal (𝕜 := 𝕜) e
    exact hc.comp (ContDiffMapSupportedIn.monoCLM 𝕜).continuous

theorem exhaustion_eq : Specs.ExpandedFA.Distributions.TestFunctionLFTopology.exhaustionEqualityType := by
  intro 𝕜 _ d Ω e
  simp only [exhaustionTopology, exhaustionOriginal_eq, TestFunction.topologicalSpace]

theorem exhaustion_independent :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.exhaustionIndependenceType := by
  intro 𝕜 _ d Ω e f
  rw [exhaustion_eq 𝕜 d Ω e, exhaustion_eq 𝕜 d Ω f]

theorem union_steps : Specs.ExpandedFA.Distributions.TestFunctionLFTopology.unionType := by
  intro 𝕜 _ d Ω e φ
  obtain ⟨j, hj⟩ := e.cofinal ⟨tsupport φ, φ.hasCompactSupport⟩ φ.tsupport_subset
  refine ⟨j, ContDiffMapSupportedIn.of_support_subset φ.contDiff (subset_closure.trans hj), ?_⟩
  rfl

theorem topology_properties : Specs.ExpandedFA.Distributions.TestFunctionLFTopology.topologyType := by
  intro 𝕜 _ d Ω
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ hK => TestFunction.continuous_ofSupportedIn hK⟩

theorem finest_topology : Specs.ExpandedFA.Distributions.TestFunctionLFTopology.finestType := by
  intro 𝕜 _ d Ω e t ht₁ ht₂ ht₃ hc
  let := ht₁
  let := ht₂
  let := ht₃
  apply TestFunction.topologicalSpace_le_iff.mpr
  rw [← exhaustionOriginal_eq e]
  exact iSup_le fun j => continuous_iff_coinduced_le.mp (hc j)

/-- Existence uses a compact exhaustion of the open subtype and its open embedding
into the ambient finite-dimensional real space. -/
theorem exists_exhaustion :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.existsExhaustionType := by
  intro d Ω
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let k := CompactExhaustion.choice Ω
  let c : ℕ → Compacts (Domain d) := fun j =>
    ⟨Subtype.val '' k j, (k.isCompact j).image continuous_subtype_val⟩
  refine ⟨⟨c, ?_, ?_, ?_⟩⟩
  · rintro j x ⟨y, _, rfl⟩
    exact y.property
  · rintro j x ⟨y, hy, rfl⟩
    exact Ω.isOpen.isOpenMap_subtype_val.image_interior_subset (k (j + 1))
      ⟨y, k.subset_interior_succ j hy, rfl⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨j, y, _, rfl⟩ := mem_iUnion.mp hx
      exact y.property
    · intro hx
      obtain ⟨j, hj⟩ := k.exists_mem ⟨x, hx⟩
      exact mem_iUnion.mpr ⟨j, ⟨⟨x, hx⟩, hj, rfl⟩⟩

/-- The universal property can be tested on just the exhaustion steps. -/
theorem continuous_linear_iff_steps {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] (e : Exhaustion Ω) (u : Tests 𝕜 Ω →ₗ[ℝ] V) :
    Continuous u ↔ ∀ j, Continuous (u ∘ TestFunction.ofSupportedIn (e.inside j)) := by
  constructor
  · exact fun hu j => hu.comp (TestFunction.continuous_ofSupportedIn (e.inside j))
  · intro hu
    apply (TestFunction.continuous_iff_continuous_comp u).mpr
    intro K hK
    obtain ⟨j, hj⟩ := e.cofinal K hK
    rw [inclusion_factor hK (e.inside j) hj, ← Function.comp_assoc]
    exact (hu j).comp (ContDiffMapSupportedIn.monoCLM 𝕜).continuous

theorem dual_criterion : Specs.ExpandedFA.Distributions.TestFunctionLFTopology.dualCriterionType := by
  intro 𝕜 _ d Ω e u
  exact continuous_linear_iff_steps e (u.restrictScalars ℝ)

/-- Passing to the seminormed topology turns a seminorm into the norm of
a linear map. This obtains the seminorm criterion from the linear one. -/
theorem seminorm_criterion :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.seminormCriterionType := by
  intro 𝕜 _ d Ω e p
  constructor
  · exact fun hp j => hp.comp (TestFunction.continuous_ofSupportedIn (e.inside j))
  · intro hp
    let : SeminormedAddCommGroup (Tests 𝕜 Ω) := p.toSeminormedAddCommGroup
    let : NormedSpace ℝ (Tests 𝕜 Ω) :=
      { norm_smul_le := fun a b => le_of_eq (map_smul_eq_mul p a b) }
    let : TopologicalSpace (Tests 𝕜 Ω) := p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
    have hi : @Continuous (Tests 𝕜 Ω) (Tests 𝕜 Ω)
        (TestFunction.topologicalSpace Ω 𝕜 ⊤) inferInstance (LinearMap.id : Tests 𝕜 Ω →ₗ[ℝ] Tests 𝕜 Ω) := by
      apply (TestFunction.continuous_iff_continuous_comp (LinearMap.id : Tests 𝕜 Ω →ₗ[ℝ] Tests 𝕜 Ω)).mpr
      intro K hK
      obtain ⟨j, hj⟩ := e.cofinal K hK
      have hstep : @Continuous (Step 𝕜 (e.compact j)) (Tests 𝕜 Ω) inferInstance inferInstance
          (TestFunction.ofSupportedIn (e.inside j)) := by
        let u : Step 𝕜 (e.compact j) →ₗ[ℝ] Tests 𝕜 Ω :=
          { toFun := TestFunction.ofSupportedIn (e.inside j)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        apply (norm_withSeminorms ℝ (Tests 𝕜 Ω)).continuous_of_continuous_comp u
        intro i
        exact hp j
      rw [show (LinearMap.id : Tests 𝕜 Ω →ₗ[ℝ] Tests 𝕜 Ω) ∘
        TestFunction.ofSupportedIn hK = TestFunction.ofSupportedIn hK from rfl]
      rw [inclusion_factor hK (e.inside j) hj]
      exact hstep.comp (ContDiffMapSupportedIn.monoCLM 𝕜).continuous
    exact @Continuous.norm _ _ p.toSeminormedAddCommGroup.toSeminormedAddGroup
      (TestFunction.topologicalSpace Ω 𝕜 ⊤) _ hi

@[simp] theorem coordinateDerivative_apply {k : ℕ} (K : Compacts (Domain d))
    (a : Fin k → Fin d) (φ : Step 𝕜 K) (x : Domain d) :
    coordinateDerivative 𝕜 K a φ x =
      iteratedFDeriv ℝ k φ x (fun j => coordinateVector (a j)) := by
  change ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k φ x _ = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]

@[simp] theorem coordinateSeminorm_apply {k : ℕ} (K : Compacts (Domain d))
    (a : Fin k → Fin d) (φ : Step 𝕜 K) :
    coordinateSeminorm 𝕜 K a φ = ‖coordinateDerivative 𝕜 K a φ‖ := rfl

/-- Each member of the finite maximum is bounded by that maximum. -/
theorem coordinate_le_stepSeminorm {k m : ℕ} (K : Compacts (Domain d))
    (a : Fin k → Fin d) (hk : k ≤ m) :
    coordinateSeminorm 𝕜 K a ≤ stepSeminorm 𝕜 K m := by
  unfold stepSeminorm
  apply le_trans (Finset.le_sup (Finset.mem_univ a))
  exact Finset.le_sup (f := fun i => Finset.univ.sup (coordinateSeminorm (k := i) 𝕜 K))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem step_seminorm_formula :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.stepSeminormFormulaType := by
  intro 𝕜 _ d K m φ C hC
  constructor
  · intro h k hk a x
    calc
      _ ≤ ‖coordinateDerivative 𝕜 K a φ‖ := by
        rw [← coordinateDerivative_apply]
        exact BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ stepSeminorm 𝕜 K m φ := coordinate_le_stepSeminorm K a hk φ
      _ ≤ C := h
  · intro h
    apply Seminorm.finset_sup_apply_le hC
    intro k hk
    apply Seminorm.finset_sup_apply_le hC
    intro a _
    rw [coordinateSeminorm_apply, BoundedContinuousFunction.norm_le hC]
    intro x
    simpa only [coordinateDerivative_apply] using h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) a x

/-- The elementary finite-coordinate estimate for a multilinear map. Expanding
each argument in the standard basis handles every d and every derivative order,
including empty coordinate types. -/
theorem norm_multilinear_le_coordinate_bound {k : ℕ}
    (A : (Domain d) [×k]→L[ℝ] 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ a : Fin k → Fin d, ‖A (fun j => coordinateVector (a j))‖ ≤ C) :
    ‖A‖ ≤ (d : ℝ) ^ k * C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hC)
  intro v
  have hexp : A v = ∑ a : Fin k → Fin d,
      (∏ j, v j (a j)) • A (fun j => coordinateVector (a j)) := by
    calc
      A v = A (fun j => ∑ i, v j i • coordinateVector i) := by
        congr 1
        funext j
        exact pi_eq_sum_univ' (v j)
      _ = ∑ a : Fin k → Fin d, A (fun j => v j (a j) • coordinateVector (a j)) :=
        A.toMultilinearMap.map_sum (fun j i => v j i • coordinateVector i)
      _ = _ := by congr 1; funext a; exact A.map_smul_univ _ _
  rw [hexp]
  calc
    ‖∑ a : Fin k → Fin d, (∏ j, v j (a j)) • A (fun j => coordinateVector (a j))‖
      ≤ ∑ a : Fin k → Fin d, ‖(∏ j, v j (a j)) • A (fun j => coordinateVector (a j))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : Fin k → Fin d, (∏ j, ‖v j‖) * C := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => norm_le_pi_norm (v j) (a j))) (hA a) (norm_nonneg _) (by positivity)
    _ = (d : ℝ) ^ k * C * ∏ j, ‖v j‖ := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Coordinate sup norms are controlled by the derivative operator sup norm. -/
theorem coordinateSeminorm_le {k : ℕ} (K : Compacts (Domain d))
    (a : Fin k → Fin d) :
    coordinateSeminorm 𝕜 K a ≤ ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K k := by
  intro φ
  rw [coordinateSeminorm_apply]
  apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
  intro x
  rw [coordinateDerivative_apply]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k φ x‖ * ∏ j, ‖coordinateVector (a j)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ k φ x‖ := by simp [coordinateVector, Pi.norm_single]
    _ ≤ _ := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜

/-- Conversely, the operator seminorm is controlled by the displayed p_k. -/
theorem operatorSeminorm_le (K : Compacts (Domain d)) (k : ℕ) :
    ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K k ≤
      ((d : ℝ≥0) ^ k) • stepSeminorm 𝕜 K k := by
  intro φ
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜 (by positivity) k φ).mpr
  intro x _
  apply norm_multilinear_le_coordinate_bound _ _ (apply_nonneg _ _)
  intro a
  calc
    _ = ‖coordinateDerivative 𝕜 K a φ x‖ := by rw [coordinateDerivative_apply]
    _ ≤ ‖coordinateDerivative 𝕜 K a φ‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
    _ ≤ stepSeminorm 𝕜 K k φ := coordinate_le_stepSeminorm K a le_rfl φ

theorem step_seminorm_topology :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.stepSeminormTopologyType := by
  intro 𝕜 _ d K
  apply (ContDiffMapSupportedIn.withSeminorms 𝕜 (Domain d) 𝕜 ⊤ K).congr
  · intro m
    refine ⟨Finset.range (m + 1), 1, ?_⟩
    rw [one_smul]
    change stepSeminorm 𝕜 K m ≤ _
    apply Finset.sup_le
    intro k hk
    apply Finset.sup_le
    intro a _
    exact (coordinateSeminorm_le K a).trans (Finset.le_sup hk)
  · intro k
    refine ⟨{k}, (d : ℝ≥0) ^ k, ?_⟩
    rw [Finset.sup_singleton]
    exact operatorSeminorm_le K k

theorem scalar_seminorm_criterion :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.scalarSeminormCriterionType := by
  intro 𝕜 _ d Ω e p
  exact seminorm_criterion 𝕜 d Ω e (p.restrictScalars ℝ)

/-- The native real LF topology is also a topological vector space over the
function's scalar field. This is essential for complex-valued tests. -/
theorem scalar_continuousSMul : ContinuousSMul 𝕜 (Tests 𝕜 Ω) := by
  let T : Tests 𝕜 Ω →ₗ[ℝ] Tests 𝕜 Ω :=
    ((RCLike.I : 𝕜) • (LinearMap.id : Tests 𝕜 Ω →ₗ[𝕜] Tests 𝕜 Ω)).restrictScalars ℝ
  have hT : Continuous T := by
    apply (TestFunction.continuous_iff_continuous_comp T).mpr
    intro K hK
    have h := (TestFunction.continuous_ofSupportedIn (F := 𝕜) (n := ⊤) hK).comp
      (continuous_id.const_smul (RCLike.I : 𝕜) :
        Continuous (fun φ : Step 𝕜 K => (RCLike.I : 𝕜) • φ))
    exact h
  constructor
  have h : Continuous (fun z : 𝕜 × Tests 𝕜 Ω =>
      RCLike.re z.1 • z.2 + RCLike.im z.1 • T z.2) :=
    ((RCLike.continuous_re.comp continuous_fst).smul continuous_snd).add
      ((RCLike.continuous_im.comp continuous_fst).smul (hT.comp continuous_snd))
  apply h.congr
  intro z
  change RCLike.re z.1 • z.2 + RCLike.im z.1 • ((RCLike.I : 𝕜) • z.2) = _
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜),
    smul_smul, ← add_smul, RCLike.re_add_im]

theorem scalar_topology :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.scalarTopologyType := by
  intro 𝕜 _ d Ω
  exact scalar_continuousSMul

/-- The topology is explicitly generated by all seminorms continuous on the steps. -/
theorem generating_seminorms :
    Specs.ExpandedFA.Distributions.TestFunctionLFTopology.generatingSeminormsType := by
  intro 𝕜 _ d Ω e
  let eqv : {p : Seminorm ℝ (Tests 𝕜 Ω) //
      ∀ j, Continuous (p ∘ TestFunction.ofSupportedIn (e.inside j))} ≃
      {p : Seminorm ℝ (Tests 𝕜 Ω) // Continuous p} :=
    Equiv.subtypeEquivRight (fun p => (seminorm_criterion 𝕜 d Ω e p).symm)
  exact (PolynormableSpace.withSeminorms ℝ (Tests 𝕜 Ω)).congr_equiv eqv

end ExpandedFA.Distributions
