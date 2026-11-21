import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Basic

/-!
Canonical interval paths and integral chains (paper.tex, D12.03.01).
A total real function represents a function on [a,b]; all regularity and
trace conditions are restricted to that interval. Values outside it have no
mathematical role. Neither paths nor chains are identified by their traces.
`ContDiffOn ℝ 1` on each closed nondegenerate piece includes the one-sided
endpoint derivatives and continuity of these derivatives. No nonzero-speed
condition is imposed. A zero-piece partition represents a degenerate interval.

The integral uses the real-parameter complex-valued interval integral, i.e.
the Bochner integral in the two-dimensional real space ℂ. Its real/imaginary
coordinate interpretation and independence of the chosen partition belong to
the subsequent path-operations obligation. The integral is totalized on all
integrands; the basic contour integral is used for functions continuous on the
trace. Chains have finitely supported integer coefficients, and cycles are
chains supported on closed paths, so they reuse the very same path objects.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace D12Complex

/-- A continuous complex path on an arbitrary nonempty compact real interval. -/
structure ComplexPath where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  toFun : ℝ → ℂ
  continuousOn : ContinuousOn toFun (Icc a b)

instance : CoeFun ComplexPath (fun _ => ℝ → ℂ) := ⟨ComplexPath.toFun⟩

namespace ComplexPath

def trace (γ : ComplexPath) : Set ℂ := γ '' Icc γ.a γ.b

def source (γ : ComplexPath) : ℂ := γ γ.a

def target (γ : ComplexPath) : ℂ := γ γ.b

def IsClosed (γ : ComplexPath) : Prop := γ.target = γ.source

/-- Includes a=b; no strict inequality is imposed. -/
def const (a b : ℝ) (hab : a ≤ b) (z : ℂ) : ComplexPath :=
  ⟨a, b, hab, fun _ => z, continuousOn_const⟩

/-- Restrict the total representative to its intrinsic compact domain. -/
def onInterval (γ : ComplexPath) : C(Icc γ.a γ.b, ℂ) :=
  ⟨fun t => γ t, γ.continuousOn.domRestrict⟩

/-- Every continuous map on a compact interval has a path representative.
The auxiliary extension clamps to the endpoints and is globally continuous. -/
def ofContinuousMap (a b : ℝ) (hab : a ≤ b) (g : C(Icc a b, ℂ)) : ComplexPath :=
  ⟨a, b, hab, IccExtend hab g, g.continuous.Icc_extend'.continuousOn⟩

end ComplexPath

/-- A finite strictly ordered C1 partition, including its endpoint regularity. -/
structure C1Partition (γ : ComplexPath) where
  count : ℕ
  node : Fin (count + 1) → ℝ
  strictMono : StrictMono node
  first : node 0 = γ.a
  last : node (Fin.last count) = γ.b
  smooth : ∀ i : Fin count,
    ContDiffOn ℝ 1 γ (Icc (node i.castSucc) (node i.succ))

namespace C1Partition

def pieceSet {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count) : Set ℝ :=
  Icc (P.node i.castSucc) (P.node i.succ)

/-- The one-piece partition for a C1 path, or the empty partition if a=b. -/
def single (γ : ComplexPath) (h : ContDiffOn ℝ 1 γ (Icc γ.a γ.b)) :
    C1Partition γ := by
  by_cases hab : γ.a < γ.b
  · exact {
      count := 1
      node := ![γ.a, γ.b]
      strictMono := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
      first := rfl
      last := rfl
      smooth := by intro i; fin_cases i; exact h }
  · have heq : γ.a = γ.b := le_antisymm γ.ordered (le_of_not_gt hab)
    exact {
      count := 0
      node := fun _ => γ.a
      strictMono := by intro i j hij; fin_cases i; fin_cases j; exact (lt_irrefl _ hij).elim
      first := rfl
      last := heq
      smooth := fun i => Fin.elim0 i }

/-- Sum of integrals of f(γ(t))γ'(t) over the specified smooth pieces. -/
def integral {γ : ComplexPath} (P : C1Partition γ) (f : ℂ → ℂ) : ℂ :=
  ∑ i : Fin P.count, ∫ t in P.node i.castSucc..P.node i.succ,
    f (γ t) * derivWithin γ (P.pieceSet i) t

end C1Partition

def IsPiecewiseC1 (γ : ComplexPath) : Prop := Nonempty (C1Partition γ)

/-- Regularity is a property, not additional traversal/partition data. -/
def PiecewiseC1Path := {γ : ComplexPath // IsPiecewiseC1 γ}

namespace PiecewiseC1Path

def path (γ : PiecewiseC1Path) : ComplexPath := γ.val

instance : CoeFun PiecewiseC1Path (fun _ => ℝ → ℂ) := ⟨fun γ => γ.path⟩

def trace (γ : PiecewiseC1Path) : Set ℂ := γ.path.trace

def IsClosed (γ : PiecewiseC1Path) : Prop := γ.path.IsClosed

def partition (γ : PiecewiseC1Path) : C1Partition γ.path := Classical.choice γ.property

/-- Totalized formula; continuity of f on γ.trace is the basic contour hypothesis. -/
def integral (γ : PiecewiseC1Path) (f : ℂ → ℂ) : ℂ := γ.partition.integral f

def const (a b : ℝ) (hab : a ≤ b) (z : ℂ) : PiecewiseC1Path :=
  ⟨ComplexPath.const a b hab z, ⟨C1Partition.single _ contDiffOn_const⟩⟩

end PiecewiseC1Path

/-- Finite integral combinations of the canonical piecewise C1 paths. -/
abbrev IntegralChain := PiecewiseC1Path →₀ ℤ

namespace IntegralChain

/-- Only nonzero coefficients contribute to the active trace. -/
def trace (Γ : IntegralChain) : Set ℂ :=
  {z | ∃ γ ∈ Γ.support, z ∈ γ.trace}

def integral (Γ : IntegralChain) (f : ℂ → ℂ) : ℂ :=
  Γ.sum (fun γ m => (m : ℂ) * γ.integral f)

/-- This definition imposes closedness on each active path, as in the source. -/
def IsCycle (Γ : IntegralChain) : Prop :=
  ∀ γ ∈ Γ.support, γ.IsClosed

end IntegralChain

/-- A cycle reuses chains and their integral and active trace. -/
def IntegralCycle := {Γ : IntegralChain // Γ.IsCycle}

namespace IntegralCycle

def zero : IntegralCycle := ⟨0, by simp [IntegralChain.IsCycle]⟩

instance : Zero IntegralCycle := ⟨zero⟩

def chain (Γ : IntegralCycle) : IntegralChain := Γ.val

def trace (Γ : IntegralCycle) : Set ℂ := Γ.chain.trace

def integral (Γ : IntegralCycle) (f : ℂ → ℂ) : ℂ := Γ.chain.integral f

end IntegralCycle
end D12Complex

namespace Specs.D12Complex.Ch03.PathsChains
open _root_.D12Complex

-- Exact type/value specifications for the candidate-owned exports follow.

def ComplexPath_type := Type
def ComplexPath_value : ComplexPath_type := _root_.D12Complex.ComplexPath

def pathTrace_type := ComplexPath → Set ℂ
def pathTrace_value : pathTrace_type := _root_.D12Complex.ComplexPath.trace

def pathSource_type := ComplexPath → ℂ
def pathSource_value : pathSource_type := _root_.D12Complex.ComplexPath.source

def pathTarget_type := ComplexPath → ℂ
def pathTarget_value : pathTarget_type := _root_.D12Complex.ComplexPath.target

def IsClosedPath_type := ComplexPath → Prop
def IsClosedPath_value : IsClosedPath_type := _root_.D12Complex.ComplexPath.IsClosed

def constantPath_type := (a b : ℝ) → a ≤ b → ℂ → ComplexPath
def constantPath_value : constantPath_type := _root_.D12Complex.ComplexPath.const

def C1Partition_type := ComplexPath → Type
def C1Partition_value : C1Partition_type := _root_.D12Complex.C1Partition

def partitionPiece_type := {γ : ComplexPath} → (P : C1Partition γ) → Fin P.count → Set ℝ
def partitionPiece_value : partitionPiece_type := _root_.D12Complex.C1Partition.pieceSet

def partitionIntegral_type := {γ : ComplexPath} → C1Partition γ → (ℂ → ℂ) → ℂ
def partitionIntegral_value : partitionIntegral_type := _root_.D12Complex.C1Partition.integral

def IsPiecewiseC1_type := ComplexPath → Prop
def IsPiecewiseC1_value : IsPiecewiseC1_type := _root_.D12Complex.IsPiecewiseC1

def PiecewiseC1Path_type := Type
def PiecewiseC1Path_value : PiecewiseC1Path_type := _root_.D12Complex.PiecewiseC1Path

def piecewisePath_type := PiecewiseC1Path → ComplexPath
def piecewisePath_value : piecewisePath_type := _root_.D12Complex.PiecewiseC1Path.path

def piecewiseTrace_type := PiecewiseC1Path → Set ℂ
def piecewiseTrace_value : piecewiseTrace_type := _root_.D12Complex.PiecewiseC1Path.trace

def IsClosedPiecewisePath_type := PiecewiseC1Path → Prop
def IsClosedPiecewisePath_value : IsClosedPiecewisePath_type := _root_.D12Complex.PiecewiseC1Path.IsClosed

def chosenPartition_type := (γ : PiecewiseC1Path) → C1Partition γ.path
def chosenPartition_value : chosenPartition_type := _root_.D12Complex.PiecewiseC1Path.partition

def contourIntegral_type := PiecewiseC1Path → (ℂ → ℂ) → ℂ
def contourIntegral_value : contourIntegral_type := _root_.D12Complex.PiecewiseC1Path.integral

def constantPiecewisePath_type := (a b : ℝ) → a ≤ b → ℂ → PiecewiseC1Path
def constantPiecewisePath_value : constantPiecewisePath_type := _root_.D12Complex.PiecewiseC1Path.const

def IntegralChain_type := Type
def IntegralChain_value : IntegralChain_type := _root_.D12Complex.IntegralChain

def chainTrace_type := IntegralChain → Set ℂ
def chainTrace_value : chainTrace_type := _root_.D12Complex.IntegralChain.trace

def chainIntegral_type := IntegralChain → (ℂ → ℂ) → ℂ
def chainIntegral_value : chainIntegral_type := _root_.D12Complex.IntegralChain.integral

def IsCycle_type := IntegralChain → Prop
def IsCycle_value : IsCycle_type := _root_.D12Complex.IntegralChain.IsCycle

def IntegralCycle_type := Type
def IntegralCycle_value : IntegralCycle_type := _root_.D12Complex.IntegralCycle

def cycleChain_type := IntegralCycle → IntegralChain
def cycleChain_value : cycleChain_type := _root_.D12Complex.IntegralCycle.chain

def cycleTrace_type := IntegralCycle → Set ℂ
def cycleTrace_value : cycleTrace_type := _root_.D12Complex.IntegralCycle.trace

def cycleIntegral_type := IntegralCycle → (ℂ → ℂ) → ℂ
def cycleIntegral_value : cycleIntegral_type := _root_.D12Complex.IntegralCycle.integral


def intervalMap_type := (γ : ComplexPath) → C(Icc γ.a γ.b, ℂ)
def intervalMap_value : intervalMap_type := _root_.D12Complex.ComplexPath.onInterval

def ofContinuousMap_type := (a b : ℝ) → (hab : a ≤ b) → C(Icc a b, ℂ) → ComplexPath
def ofContinuousMap_value : ofContinuousMap_type := _root_.D12Complex.ComplexPath.ofContinuousMap

def smoothPartition_type := (γ : ComplexPath) → ContDiffOn ℝ 1 γ (Icc γ.a γ.b) → C1Partition γ
def smoothPartition_value : smoothPartition_type := _root_.D12Complex.C1Partition.single

def zeroCycle_type := IntegralCycle
def zeroCycle_value : zeroCycle_type := _root_.D12Complex.IntegralCycle.zero

def isPiecewiseC1_of_contDiffOn_type : Prop :=
  ∀ (γ : ComplexPath), ContDiffOn ℝ 1 γ (Icc γ.a γ.b) → IsPiecewiseC1 γ

def isPiecewiseC1_of_degenerate_type : Prop :=
  ∀ (γ : ComplexPath), γ.a = γ.b → IsPiecewiseC1 γ

def C1Partition_piece_lt_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count),
  P.node i.castSucc < P.node i.succ

def C1Partition_piece_subset_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count),
  P.pieceSet i ⊆ Icc γ.a γ.b

def C1Partition_piece_c1_iff_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count),
  ContDiffOn ℝ 1 γ (P.pieceSet i) ↔ DifferentiableOn ℝ γ (P.pieceSet i) ∧
    ContinuousOn (derivWithin γ (P.pieceSet i)) (P.pieceSet i)

def C1Partition_piece_integrable_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ) (f : ℂ → ℂ),
  ContinuousOn f γ.trace → ∀ i : Fin P.count,
  IntervalIntegrable (fun t => f (γ t) * derivWithin γ (P.pieceSet i) t)
    volume (P.node i.castSucc) (P.node i.succ)

def C1Partition_count_eq_zero_of_degenerate_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ),
  γ.a = γ.b → P.count = 0

def C1Partition_integral_degenerate_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ),
  γ.a = γ.b → ∀ f : ℂ → ℂ, P.integral f = 0

def C1Partition_integral_of_constant_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ) (z : ℂ),
  (∀ t ∈ Icc γ.a γ.b, γ t = z) → ∀ f : ℂ → ℂ, P.integral f = 0

def ComplexPath_ofContinuousMap_apply_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (g : C(Icc a b, ℂ)) (t : Icc a b),
  ComplexPath.ofContinuousMap a b hab g t = g t

def ComplexPath_onInterval_ofContinuousMap_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (g : C(Icc a b, ℂ)),
  (ComplexPath.ofContinuousMap a b hab g).onInterval = g

def ComplexPath_trace_nonempty_type : Prop :=
  ∀ γ : ComplexPath, γ.trace.Nonempty

def ComplexPath_trace_compact_type : Prop :=
  ∀ γ : ComplexPath, IsCompact γ.trace

def ComplexPath_const_trace_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (z : ℂ),
  (ComplexPath.const a b hab z).trace = {z}

def PiecewiseC1Path_integral_degenerate_type : Prop :=
  ∀ γ : PiecewiseC1Path,
  γ.path.a = γ.path.b → ∀ f : ℂ → ℂ, γ.integral f = 0

def PiecewiseC1Path_integral_of_constant_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (z : ℂ),
  (∀ t ∈ Icc γ.path.a γ.path.b, γ t = z) → ∀ f : ℂ → ℂ, γ.integral f = 0

def PiecewiseC1Path_const_integral_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (z : ℂ) (f : ℂ → ℂ),
  (PiecewiseC1Path.const a b hab z).integral f = 0

def PiecewiseC1Path_const_closed_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (z : ℂ),
  (PiecewiseC1Path.const a b hab z).IsClosed

def IntegralChain_mem_trace_iff_type : Prop :=
  ∀ (Γ : IntegralChain) (z : ℂ),
  z ∈ Γ.trace ↔ ∃ γ : PiecewiseC1Path, Γ γ ≠ 0 ∧ z ∈ γ.trace

def IntegralChain_zero_trace_type : Prop :=
  (0 : IntegralChain).trace = ∅

def IntegralChain_zero_integral_type : Prop :=
  ∀ f : ℂ → ℂ, (0 : IntegralChain).integral f = 0

def IntegralChain_zero_isCycle_type : Prop :=
  (0 : IntegralChain).IsCycle

def IntegralCycle_zero_chain_type : Prop :=
  (0 : IntegralCycle).chain = 0

def IntegralCycle_zero_trace_type : Prop :=
  (0 : IntegralCycle).trace = ∅

def IntegralCycle_zero_integral_type : Prop :=
  ∀ f : ℂ → ℂ, (0 : IntegralCycle).integral f = 0

end Specs.D12Complex.Ch03.PathsChains
