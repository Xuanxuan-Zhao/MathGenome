import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ShiftSpectra
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Prod

/-! Independent statements for paper.tex 6211–6232. The scalar field is real
or complex and inner products are conjugate-linear in the first variable.
The net is indexed by ALL finite-dimensional subspaces and positive integers,
ordered by inclusion and the usual integer order. No separability is imposed. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.OperatorTopology.Boundaries.Spec
universe u v

abbrev FiniteSubspace (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :=
  {M : Submodule 𝕜 H // FiniteDimensional 𝕜 M}

instance (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : Nonempty (FiniteSubspace 𝕜 H) :=
  ⟨⟨⊥, inferInstance⟩⟩

instance (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : IsDirectedOrder (FiniteSubspace 𝕜 H) := by
  constructor
  intro M N
  let := M.property
  let := N.property
  refine ⟨⟨M.val ⊔ N.val, inferInstance⟩, ?_, ?_⟩
  · change M.val ≤ M.val ⊔ N.val
    exact le_sup_left
  · change N.val ≤ M.val ⊔ N.val
    exact le_sup_right

abbrev NetIndex (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] := FiniteSubspace 𝕜 H × ℕ+

instance (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : IsDirectedOrder (NetIndex 𝕜 H) := by
  constructor
  intro i j
  obtain ⟨M, hi, hj⟩ := exists_ge_ge i.1 j.1
  exact ⟨(M, max i.2 j.2), ⟨hi, le_max_left _ _⟩, ⟨hj, le_max_right _ _⟩⟩

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Exactly S_(M,n) x = (1/n) ⟪e,x⟫ u_M. -/
def netS (e : H) (u : FiniteSubspace 𝕜 H → H) (i : NetIndex 𝕜 H) : H →L[𝕜] H :=
  ((i.2 : ℕ) : 𝕜)⁻¹ • InnerProductSpace.rankOne 𝕜 (u i.1) e

/-- Exactly T_(M,n) x = n ⟪u_M,x⟫ e. -/
def netT (e : H) (u : FiniteSubspace 𝕜 H → H) (i : NetIndex 𝕜 H) : H →L[𝕜] H :=
  ((i.2 : ℕ) : 𝕜) • InnerProductSpace.rankOne 𝕜 e (u i.1)

def UnitOrthogonalFamily (u : FiniteSubspace 𝕜 H → H) : Prop :=
  ∀ M, ‖u M‖ = 1 ∧ u M ∈ M.val.orthogonal

def UnitVectorsExist : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ¬ FiniteDimensional 𝕜 H →
    ∃ e : H, ‖e‖ = 1 ∧ ∃ u : FiniteSubspace 𝕜 H → H, UnitOrthogonalFamily u

def NetIdentities : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (e : H) (u : FiniteSubspace 𝕜 H → H),
    ‖e‖ = 1 → UnitOrthogonalFamily u → ∀ i : NetIndex 𝕜 H,
    ‖netS e u i‖ = (((i.2 : ℕ) : ℝ))⁻¹ ∧
    ‖netT e u i‖ = ((i.2 : ℕ) : ℝ) ∧
    (netT e u i).comp (netS e u i) = InnerProductSpace.rankOne 𝕜 e e

def NetConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (e : H) (u : FiniteSubspace 𝕜 H → H),
    ‖e‖ = 1 → UnitOrthogonalFamily u →
    Tendsto (netS e u) atTop (𝓝 0) ∧
    Tendsto (netT e u) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 H H) 0) ∧
    ¬ Tendsto (fun i => (netT e u i).comp (netS e u i)) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 H H) 0)

def StrongCompositionNotContinuous : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H], ¬ FiniteDimensional 𝕜 H →
    letI := OperatorTopology.Spec.StrongTopologyValue 𝕜 H H
    ¬ Continuous (fun p : (H →L[𝕜] H) × (H →L[𝕜] H) => p.1.comp p.2)

def AdjointWOTContinuous : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    letI := OperatorTopology.Spec.WeakTopologyValue 𝕜 H H
    Continuous (ContinuousLinearMap.adjoint : (H →L[𝕜] H) → (H →L[𝕜] H))

/-- The canonical scalar ℓ², with its existing norm and Hilbert structure.
Native coordinate zero is manuscript coordinate one. -/
abbrev SequenceHilbert (𝕜 : Type u) [RCLike 𝕜] :=
  ExpandedFA.P1.C01SequenceSpaces.SequenceLp 𝕜 2

def shiftSequence {𝕜 : Type u} [RCLike 𝕜] (x : SequenceHilbert 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => x n

private theorem shift_mem {𝕜 : Type u} [RCLike 𝕜] (x : SequenceHilbert 𝕜) :
    Memℓp (shiftSequence x) 2 := by
  apply memℓp_gen
  apply (summable_nat_add_iff 1).mp
  simpa only [shiftSequence] using (lp.memℓp x).summable (by norm_num)

private def shiftLinear (𝕜 : Type u) [RCLike 𝕜] :
    SequenceHilbert 𝕜 →ₗ[𝕜] SequenceHilbert 𝕜 where
  toFun x := ⟨shiftSequence x, shift_mem x⟩
  map_add' x y := by
    apply lp.ext; funext n
    change shiftSequence (x + y) n = shiftSequence x n + shiftSequence y n
    cases n <;> simp [shiftSequence]
  map_smul' a x := by
    apply lp.ext; funext n
    cases n <;> simp [shiftSequence]

private theorem shift_norm {𝕜 : Type u} [RCLike 𝕜] (x : SequenceHilbert 𝕜) :
    ‖shiftLinear 𝕜 x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  change (∑' n, ‖shiftSequence x n‖ ^ (2 : ℝ≥0∞).toReal) = _
  rw [((shift_mem x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).tsum_eq_zero_add]
  simp [shiftSequence]

def ShiftType := ∀ (𝕜 : Type u) [RCLike 𝕜],
  SequenceHilbert 𝕜 →L[𝕜] SequenceHilbert 𝕜

def ShiftValue : ShiftType := fun 𝕜 _ =>
  (⟨shiftLinear 𝕜, shift_norm⟩ : SequenceHilbert 𝕜 →ₗᵢ[𝕜] SequenceHilbert 𝕜).toContinuousLinearMap

def ShiftCoordinates : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceHilbert 𝕜),
  ShiftValue 𝕜 x 0 = 0 ∧ (∀ n, ShiftValue 𝕜 x (n + 1) = x n) ∧
  (∀ n, (ShiftValue 𝕜).adjoint x n = x (n + 1))

/-- The complex specialization is the already shared ℓᵖ shift at p=2,
and its Hilbert adjoint is the already shared backward shift. -/
def ShiftComplexIdentification : Prop :=
  ShiftValue ℂ = ExpandedFA.BanachAlgebra.ShiftSpectra.Spec.ForwardValue 2 (by norm_num) ∧
  (ShiftValue ℂ).adjoint = ExpandedFA.BanachAlgebra.ShiftSpectra.Spec.BackwardValue 2 (by norm_num)

def ShiftLimits : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  let V := ShiftValue 𝕜
  Tendsto (fun n : ℕ => V ^ n) atTop
    (@nhds _ (OperatorTopology.Spec.WeakTopologyValue 𝕜 _ _) 0) ∧
  Tendsto (fun n : ℕ => V.adjoint ^ n) atTop
    (@nhds _ (OperatorTopology.Spec.WeakTopologyValue 𝕜 _ _) 0) ∧
  Tendsto (fun n : ℕ => V.adjoint ^ n) atTop
    (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 _ _) 0) ∧
  ¬ Tendsto (fun n : ℕ => V ^ n) atTop
    (@nhds _ (OperatorTopology.Spec.StrongTopologyValue 𝕜 _ _) 0) ∧
  (∀ n : ℕ, (V.adjoint ^ n).comp (V ^ n) = ContinuousLinearMap.id 𝕜 _) ∧
  ¬ Tendsto (fun n : ℕ => (V.adjoint ^ n).comp (V ^ n)) atTop
    (@nhds _ (OperatorTopology.Spec.WeakTopologyValue 𝕜 _ _) 0)

def WeakCompositionNotContinuous : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  letI := OperatorTopology.Spec.WeakTopologyValue 𝕜 (SequenceHilbert 𝕜) (SequenceHilbert 𝕜)
  ¬ Continuous (fun p : (SequenceHilbert 𝕜 →L[𝕜] SequenceHilbert 𝕜) ×
    (SequenceHilbert 𝕜 →L[𝕜] SequenceHilbert 𝕜) => p.1.comp p.2)

def AdjointSOTNotContinuous : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  letI := OperatorTopology.Spec.StrongTopologyValue 𝕜 (SequenceHilbert 𝕜) (SequenceHilbert 𝕜)
  ¬ Continuous (ContinuousLinearMap.adjoint :
    (SequenceHilbert 𝕜 →L[𝕜] SequenceHilbert 𝕜) → _)

end ExpandedFA.OperatorTopology.Boundaries.Spec
