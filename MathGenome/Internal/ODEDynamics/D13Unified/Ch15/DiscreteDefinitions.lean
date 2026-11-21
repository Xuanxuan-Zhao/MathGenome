import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions

/-! Canonical interface and definitional bridges for Chapter 15 discrete dynamics. -/
namespace D13Unified.Ch15.DiscreteDefinitions

universe u v
open Filter Set Function
open scoped Topology

/-- A discrete system is a self-map, with no topology required. -/
abbrev DiscreteSystem : Specs.D13Unified.Ch15.DiscreteDefinitions.DiscreteSystemType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.DiscreteSystem

/-- Use the native natural-number iterate throughout. -/
abbrev iterate : Specs.D13Unified.Ch15.DiscreteDefinitions.iterateType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.iterate

/-- The forward orbit as a sequence, including time zero. -/
abbrev forwardOrbit : Specs.D13Unified.Ch15.DiscreteDefinitions.forwardOrbitType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.forwardOrbit

/-- The set of values of the forward orbit. -/
abbrev orbitSet : Specs.D13Unified.Ch15.DiscreteDefinitions.orbitSetType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.orbitSet

/-- Positive invariance is image inclusion. -/
abbrev PositivelyInvariant : Specs.D13Unified.Ch15.DiscreteDefinitions.PositivelyInvariantType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.PositivelyInvariant

/-- Invariance requires equality of the image and the set. -/
abbrev Invariant : Specs.D13Unified.Ch15.DiscreteDefinitions.InvariantType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.Invariant

/-- Least period is positive and excludes every smaller positive return. -/
abbrev HasLeastPeriod : Specs.D13Unified.Ch15.DiscreteDefinitions.HasLeastPeriodType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.HasLeastPeriod

/-- Signed iterates require a specified invertible map, never an arbitrary self-map. -/
abbrev integerIterate : Specs.D13Unified.Ch15.DiscreteDefinitions.integerIterateType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.integerIterate

/-- A specified homeomorphism conjugates F to G. -/
abbrev IsConjugacy : Specs.D13Unified.Ch15.DiscreteDefinitions.IsConjugacyType.{u, v} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.IsConjugacy

/-- Existence of a topological conjugacy. -/
abbrev TopologicallyConjugate : Specs.D13Unified.Ch15.DiscreteDefinitions.TopologicallyConjugateType.{u, v} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.TopologicallyConjugate

/-- A semiconjugacy is continuous and surjective; injectivity is not required. -/
abbrev IsSemiconjugacy : Specs.D13Unified.Ch15.DiscreteDefinitions.IsSemiconjugacyType.{u, v} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.IsSemiconjugacy

/-- The epsilon-delta orbit condition used for fixed points of continuous maps. -/
abbrev LyapunovStable : Specs.D13Unified.Ch15.DiscreteDefinitions.LyapunovStableType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.LyapunovStable

/-- Every point of some ball converges to p; convergence is pointwise in x. -/
abbrev AttractsNeighborhood : Specs.D13Unified.Ch15.DiscreteDefinitions.AttractsNeighborhoodType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.AttractsNeighborhood

/-- Asymptotic stability includes Lyapunov stability and local attraction. -/
abbrev AsymptoticallyStable : Specs.D13Unified.Ch15.DiscreteDefinitions.AsymptoticallyStableType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.AsymptoticallyStable

/-- The original quantitative bound on a neighborhood, for every natural n. -/
abbrev LocallyExponentiallyStable : Specs.D13Unified.Ch15.DiscreteDefinitions.LocallyExponentiallyStableType.{u} :=
  Specs.D13Unified.Ch15.DiscreteDefinitions.LocallyExponentiallyStable

theorem iterate_zero :
  ∀ {X : Type u} (F : X → X), iterate F 0 = id := by
  intro X F
  rfl

theorem iterate_succ :
  ∀ {X : Type u} (F : X → X) (n : ℕ),
  iterate F (n + 1) = F ∘ iterate F n := by
  intro X F n
  exact Function.iterate_succ' F n

theorem forwardOrbit_zero :
  ∀ {X : Type u} (F : X → X) (x : X), forwardOrbit F x 0 = x := by
  intro X F x
  rfl

theorem forwardOrbit_succ :
  ∀ {X : Type u} (F : X → X) (x : X) (n : ℕ),
  forwardOrbit F x (n + 1) = F (forwardOrbit F x n) := by
  intro X F x n
  exact Function.iterate_succ_apply' F n x

theorem mem_orbitSet :
  ∀ {X : Type u} (F : X → X) (x y : X),
  y ∈ orbitSet F x ↔ ∃ n : ℕ, F^[n] x = y := by
  intro X F x y
  rfl

theorem positivelyInvariant_iff_mapsTo :
  ∀ {X : Type u} (F : X → X) (A : Set X),
  PositivelyInvariant F A ↔ Set.MapsTo F A A := by
  intro X F A
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h hx

theorem hasLeastPeriod_iff :
  ∀ {X : Type u} (F : X → X) (x : X) (p : ℕ),
  HasLeastPeriod F x p ↔ 0 < p ∧ F^[p] x = x ∧
    ∀ m : ℕ, 0 < m → m < p → F^[m] x ≠ x := by
  intro X F x p
  rfl

theorem hasLeastPeriod_iff_minimalPeriod :
  ∀ {X : Type u} (F : X → X) (x : X) (p : ℕ),
  HasLeastPeriod F x p ↔ 0 < p ∧ Function.minimalPeriod F x = p := by
  intro X F x p
  constructor
  · rintro ⟨hp, hfix, hleast⟩
    refine ⟨hp, le_antisymm (hfix.minimalPeriod_le hp) ?_⟩
    exact le_of_not_gt (fun hlt => hleast (Function.minimalPeriod F x)
      (hfix.minimalPeriod_pos hp) hlt (Function.isPeriodicPt_minimalPeriod F x))
  · rintro ⟨hp, hperiod⟩
    refine ⟨hp, ?_, ?_⟩
    · simpa only [hperiod] using Function.isPeriodicPt_minimalPeriod F x
    · intro m hm hmp hfix
      have hle := hfix.minimalPeriod_le hm
      rw [hperiod] at hle
      exact (Nat.not_le_of_lt hmp) hle

theorem integerIterate_ofNat :
  ∀ {X : Type u} (F : X ≃ X) (n : ℕ),
  integerIterate F (n : ℤ) = (F : X → X)^[n] := by
  intro X F n
  rfl

theorem integerIterate_negSucc :
  ∀ {X : Type u} (F : X ≃ X) (n : ℕ),
  integerIterate F (Int.negSucc n) = (F.symm : X → X)^[n + 1] := by
  intro X F n
  rfl

theorem inverse_iterate_cancel :
  ∀ {X : Type u} (F : X ≃ X) (n : ℕ) (x : X),
  (F.symm : X → X)^[n] ((F : X → X)^[n] x) = x ∧
    (F : X → X)^[n] ((F.symm : X → X)^[n] x) = x := by
  intro X F n x
  exact ⟨(Function.LeftInverse.iterate F.left_inv n) x,
    (Function.LeftInverse.iterate F.right_inv n) x⟩

theorem isConjugacy_iff :
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (F : X → X) (G : Y → Y) (h : X ≃ₜ Y),
  IsConjugacy F G h ↔ (h : X → Y) ∘ F = G ∘ (h : X → Y) := by
  intro X Y _ _ F G h
  exact Function.semiconj_iff_comp_eq

theorem isSemiconjugacy_iff :
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (F : X → X) (G : Y → Y) (h : X → Y),
  IsSemiconjugacy F G h ↔ Continuous h ∧ Function.Surjective h ∧ h ∘ F = G ∘ h := by
  intro X Y _ _ F G h
  change (Continuous h ∧ Function.Surjective h ∧ Function.Semiconj h F G) ↔ _
  rw [Function.semiconj_iff_comp_eq]

theorem lyapunovStable_iff_neighborhoods :
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (p : X),
  LyapunovStable F p ↔ ∀ V ∈ 𝓝 p, ∃ U ∈ 𝓝 p,
    ∀ x ∈ U, ∀ n : ℕ, F^[n] x ∈ V := by
  intro X _ F p
  constructor
  · intro h V hV
    rcases Metric.mem_nhds_iff.mp hV with ⟨ε, hε, hball⟩
    rcases h ε hε with ⟨δ, hδ, hδbound⟩
    refine ⟨Metric.ball p δ, Metric.ball_mem_nhds p hδ, ?_⟩
    intro x hx n
    exact hball (hδbound x hx n)
  · intro h ε hε
    rcases h (Metric.ball p ε) (Metric.ball_mem_nhds p hε) with ⟨U, hU, hiter⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hball⟩
    exact ⟨δ, hδ, fun x hx n => hiter x (hball hx) n⟩

theorem attractsNeighborhood_iff :
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (p : X),
  AttractsNeighborhood F p ↔ ∃ U ∈ 𝓝 p,
    ∀ x ∈ U, Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 p) := by
  intro X _ F p
  constructor
  · rintro ⟨δ, hδ, hattract⟩
    exact ⟨Metric.ball p δ, Metric.ball_mem_nhds p hδ, hattract⟩
  · rintro ⟨U, hU, hattract⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hball⟩
    exact ⟨δ, hδ, fun x hx => hattract x (hball hx)⟩

theorem asymptoticallyStable_iff_neighborhoods :
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (p : X),
  AsymptoticallyStable F p ↔ LyapunovStable F p ∧ ∃ U ∈ 𝓝 p,
    ∀ x ∈ U, Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 p) := by
  intro X _ F p
  change (LyapunovStable F p ∧ AttractsNeighborhood F p) ↔ _
  rw [attractsNeighborhood_iff]

theorem locallyExponentiallyStable_iff_neighborhoods :
  ∀ {E : Type u} [NormedAddCommGroup E] (F : E → E) (p : E),
  LocallyExponentiallyStable F p ↔
    ∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ U ∈ 𝓝 p,
      ∀ x ∈ U, ∀ n : ℕ, ‖F^[n] x - p‖ ≤ C * q ^ n * ‖x - p‖ := by
  intro E _ F p
  constructor
  · rintro ⟨C, hC, q, hq, hq1, δ, hδ, hbound⟩
    refine ⟨C, hC, q, hq, hq1, Metric.ball p δ, Metric.ball_mem_nhds p hδ, ?_⟩
    intro x hx n
    exact hbound x ((dist_eq_norm x p) ▸ hx) n
  · rintro ⟨C, hC, q, hq, hq1, U, hU, hbound⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hball⟩
    refine ⟨C, hC, q, hq, hq1, δ, hδ, ?_⟩
    intro x hx n
    apply hbound x (hball ?_) n
    show dist x p < δ
    rwa [dist_eq_norm]

end D13Unified.Ch15.DiscreteDefinitions
