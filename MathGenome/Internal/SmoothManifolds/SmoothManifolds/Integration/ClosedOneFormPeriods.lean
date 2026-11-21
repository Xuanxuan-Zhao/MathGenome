import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClosedOneFormPeriods
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.PeriodCriterion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.ClosedOneFormLocalPrimitives
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalPrimitiveHomotopy

/-! M10.07: closed one-form periods under continuous fixed-endpoint homotopy.
Local primitives and cancellation on a grid prove invariance for arbitrary
continuous square homotopies, including in half-space charts. The global period
criterion then gives exactness, also componentwise and on empty bases.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.ClosedOneFormPeriods
open ModelData AtlasData CovectorData BundleOperationsData PathIntegrationData
  PeriodData ClosedOneFormPeriodData Set
universe u

variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]

abbrev EndpointHomotopic := @ClosedOneFormPeriodData.EndpointHomotopic
abbrev HomotopyInvariant := @ClosedOneFormPeriodData.HomotopyInvariant

/-- Normalize a continuous path on any increasing interval, including a point. -/
def intervalPath (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) : Path (γ a) (γ b) where
  toFun t := γ (a + (b-a) * t.val)
  continuous_toFun := hγ.comp_continuous
    (continuous_const.add (continuous_const.mul continuous_subtype_val)) (by
      intro t
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hab) t.property.1)
      · have h := mul_le_mul_of_nonneg_left t.property.2 (sub_nonneg.mpr hab)
        linarith)
  source' := by simp
  target' := by simp

/-- The four-edge condition implies equality of the original endpoints. -/
theorem endpointHomotopic_endpoints (γ η : ℝ → M) (a b c d : ℝ)
    (h : EndpointHomotopic γ η a b c d) : γ a = η c ∧ γ b = η d := by
  obtain ⟨H, _, _, h₁, hleft, hright⟩ := h
  constructor
  · simpa using (hleft 1).symm.trans (h₁ 0)
  · simpa using (hright 1).symm.trans (h₁ 1)

/-- Every exact form has homotopy invariant integrals, by the fundamental theorem
and the actual endpoint conditions of a continuous square. -/
theorem exact_homotopy_invariance :
    Specs.SmoothManifolds.Integration.ClosedOneFormPeriods.exact_homotopy_invarianceType.{u} := by
  intro n k M _ S α he γ η a b c d hγ hη hH
  have hend := endpointHomotopic_endpoints γ η a b c d hH
  exact PeriodCriterion.exact_implies_path_independent
    (fun S => PathIntegration.integral_dFunction S) S α he
    γ η a b c d hγ hη hend.1 hend.2

/-- Closedness supplies local potentials, whose increments cancel on a grid
subordinate to the continuous homotopy. This argument needs no regularity of
the homotopy beyond continuity and works directly at boundary points. -/
theorem homotopy_invariance :
    Specs.SmoothManifolds.Integration.ClosedOneFormPeriods.homotopy_invarianceType.{u} := by
  intro n k M _ S C α hclosed γ η a b c d hγ hη hH
  obtain ⟨H, hH, h0, h1, hs0, hs1⟩ := hH
  apply LocalPrimitiveHomotopy.homotopy_invariance S α.field _
    γ η a b c d hγ.1 hη.1 hγ hη H hH h0 h1 hs0 hs1
  intro p
  obtain ⟨U, f, hf, hU, hp, hdf⟩ :=
    ClosedOneFormLocalPrimitives.local_primitives S C α hclosed p
  exact ⟨U, hU, hp, f, hf, hdf⟩

/-- Nullhomotopy of a normalized loop is precisely a usable continuous square.
The second path traverses the singleton [a,a], so its integral is zero without
any velocity or reparametrization claim at a degenerate interval. -/
theorem endpointHomotopic_singleton_of_nullhomotopic
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hnull : ∀ (p : M) (δ : Path p p), Path.Homotopic δ (Path.refl p)) :
    EndpointHomotopic γ γ a b a a := by
  let δ : Path (γ a) (γ a) := (intervalPath γ a b hab hγ).cast rfl hclosed
  obtain ⟨H⟩ := hnull (γ a) δ
  refine ⟨H, H.continuous, ?_, ?_, ?_, ?_⟩
  · intro s
    exact H.map_zero_left s
  · intro s
    simpa using H.map_one_left s
  · intro t
    exact Path.Homotopy.source H t
  · intro t
    exact (Path.Homotopy.target H t).trans hclosed

/-- Homotopy invariant integrals have zero periods whenever all loops are null.
This is a genuine conditional assembly lemma, not the closed-form theorem. -/
theorem zero_periods_of_homotopy_invariant (S : SmoothManifold n k M)
    (α : CovectorField S)
    (hnull : ∀ (p : M) (γ : Path p p), Path.Homotopic γ (Path.refl p))
    (hi : HomotopyInvariant S α) : ZeroPeriods S α := by
  intro γ a b hγ hclosed
  have h := hi γ γ a b a a hγ
    (PeriodCriterion.piecewiseSmoothOn_singleton S γ a)
    (endpointHomotopic_singleton_of_nullhomotopic γ a b hγ.1 hγ.2.1 hclosed hnull)
  simpa [PathIntegrationData.pathIntegral] using h

/-- Apply the already established global period criterion componentwise. -/
theorem exact_of_homotopy_invariant :
    Specs.SmoothManifolds.Integration.ClosedOneFormPeriods.exact_of_homotopy_invariantType.{u} := by
  intro n k M _ S C α hnull hi
  exact PeriodCriterion.zero_periods_exact S C α
    (zero_periods_of_homotopy_invariant S α.field hnull hi)

/-- A form with homotopy invariant integral is exact on a simply connected base. -/
theorem exact_of_homotopy_invariant_of_simplyConnected
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    [SimplyConnectedSpace M] (hi : HomotopyInvariant S α.field) : Exact S α.field :=
  exact_of_homotopy_invariant S C α
    (fun _ γ => SimplyConnectedSpace.paths_homotopic γ (Path.refl _)) hi

/-- A loop remains in the connected component of its basepoint. -/
theorem loop_mem_component {p : M} (γ : Path p p) (t : unitInterval) :
    γ t ∈ connectedComponent p := by
  exact (isConnected_range γ.continuous).subset_connectedComponent
    ⟨0, γ.source⟩ ⟨t, rfl⟩

/-- Componentwise simple connectedness gives the precise topological hypothesis
used in the period argument, also on an empty manifold. -/
theorem loops_nullhomotopic_of_components
    (hcomp : ∀ p : M, SimplyConnectedSpace (connectedComponent p))
    (p : M) (γ : Path p p) : Path.Homotopic γ (Path.refl p) := by
  let q : connectedComponent p := ⟨p, mem_connectedComponent⟩
  let δ : Path q q := {
    toFun := fun t => ⟨γ t, loop_mem_component γ t⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext γ.source
    target' := Subtype.ext γ.target }
  letI := hcomp p
  have h := SimplyConnectedSpace.paths_homotopic δ (Path.refl q)
  have hh := h.map (⟨Subtype.val, continuous_subtype_val⟩ :
    ContinuousMap (connectedComponent p) M)
  convert hh using 1
  · ext t
    rfl
  · ext t
    rfl

/-- The final exactness assembly does not require the whole base to be connected. -/
theorem exact_of_homotopy_invariant_of_components
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (hcomp : ∀ p : M, SimplyConnectedSpace (connectedComponent p))
    (hi : HomotopyInvariant S α.field) : Exact S α.field :=
  exact_of_homotopy_invariant S C α (loops_nullhomotopic_of_components hcomp) hi

/-- On a simply connected manifold, every smooth closed one-form has a global
smooth primitive. -/
theorem simply_connected_exact :
    Specs.SmoothManifolds.Integration.ClosedOneFormPeriods.simply_connected_exactType.{u} := by
  intro n k M _ S C α hsimply hclosed
  letI := hsimply
  exact exact_of_homotopy_invariant_of_simplyConnected S C α
    (homotopy_invariance S C α hclosed)

/-- The same conclusion holds when every connected component is simply
connected; components have independent primitive constants. -/
theorem componentwise_simply_connected_exact :
    Specs.SmoothManifolds.Integration.ClosedOneFormPeriods.componentwise_simply_connected_exactType.{u} := by
  intro n k M _ S C α hcomp hclosed
  exact exact_of_homotopy_invariant_of_components S C α hcomp
    (homotopy_invariance S C α hclosed)

end SmoothManifolds.ClosedOneFormPeriods
