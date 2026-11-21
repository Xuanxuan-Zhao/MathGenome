import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace D12Complex.PathsChains

abbrev ComplexPath : Specs.D12Complex.Ch03.PathsChains.ComplexPath_type :=
  _root_.D12Complex.ComplexPath

abbrev pathTrace : Specs.D12Complex.Ch03.PathsChains.pathTrace_type :=
  _root_.D12Complex.ComplexPath.trace

abbrev pathSource : Specs.D12Complex.Ch03.PathsChains.pathSource_type :=
  _root_.D12Complex.ComplexPath.source

abbrev pathTarget : Specs.D12Complex.Ch03.PathsChains.pathTarget_type :=
  _root_.D12Complex.ComplexPath.target

abbrev IsClosedPath : Specs.D12Complex.Ch03.PathsChains.IsClosedPath_type :=
  _root_.D12Complex.ComplexPath.IsClosed

abbrev constantPath : Specs.D12Complex.Ch03.PathsChains.constantPath_type :=
  _root_.D12Complex.ComplexPath.const

abbrev C1Partition : Specs.D12Complex.Ch03.PathsChains.C1Partition_type :=
  _root_.D12Complex.C1Partition

abbrev partitionPiece : Specs.D12Complex.Ch03.PathsChains.partitionPiece_type :=
  _root_.D12Complex.C1Partition.pieceSet

abbrev partitionIntegral : Specs.D12Complex.Ch03.PathsChains.partitionIntegral_type :=
  _root_.D12Complex.C1Partition.integral

abbrev IsPiecewiseC1 : Specs.D12Complex.Ch03.PathsChains.IsPiecewiseC1_type :=
  _root_.D12Complex.IsPiecewiseC1

abbrev PiecewiseC1Path : Specs.D12Complex.Ch03.PathsChains.PiecewiseC1Path_type :=
  _root_.D12Complex.PiecewiseC1Path

abbrev piecewisePath : Specs.D12Complex.Ch03.PathsChains.piecewisePath_type :=
  _root_.D12Complex.PiecewiseC1Path.path

abbrev piecewiseTrace : Specs.D12Complex.Ch03.PathsChains.piecewiseTrace_type :=
  _root_.D12Complex.PiecewiseC1Path.trace

abbrev IsClosedPiecewisePath : Specs.D12Complex.Ch03.PathsChains.IsClosedPiecewisePath_type :=
  _root_.D12Complex.PiecewiseC1Path.IsClosed

abbrev chosenPartition : Specs.D12Complex.Ch03.PathsChains.chosenPartition_type :=
  _root_.D12Complex.PiecewiseC1Path.partition

abbrev contourIntegral : Specs.D12Complex.Ch03.PathsChains.contourIntegral_type :=
  _root_.D12Complex.PiecewiseC1Path.integral

abbrev constantPiecewisePath : Specs.D12Complex.Ch03.PathsChains.constantPiecewisePath_type :=
  _root_.D12Complex.PiecewiseC1Path.const

abbrev IntegralChain : Specs.D12Complex.Ch03.PathsChains.IntegralChain_type :=
  _root_.D12Complex.IntegralChain

abbrev chainTrace : Specs.D12Complex.Ch03.PathsChains.chainTrace_type :=
  _root_.D12Complex.IntegralChain.trace

abbrev chainIntegral : Specs.D12Complex.Ch03.PathsChains.chainIntegral_type :=
  _root_.D12Complex.IntegralChain.integral

abbrev IsCycle : Specs.D12Complex.Ch03.PathsChains.IsCycle_type :=
  _root_.D12Complex.IntegralChain.IsCycle

abbrev IntegralCycle : Specs.D12Complex.Ch03.PathsChains.IntegralCycle_type :=
  _root_.D12Complex.IntegralCycle

abbrev cycleChain : Specs.D12Complex.Ch03.PathsChains.cycleChain_type :=
  _root_.D12Complex.IntegralCycle.chain

abbrev cycleTrace : Specs.D12Complex.Ch03.PathsChains.cycleTrace_type :=
  _root_.D12Complex.IntegralCycle.trace

abbrev cycleIntegral : Specs.D12Complex.Ch03.PathsChains.cycleIntegral_type :=
  _root_.D12Complex.IntegralCycle.integral


abbrev intervalMap : Specs.D12Complex.Ch03.PathsChains.intervalMap_type :=
  _root_.D12Complex.ComplexPath.onInterval

abbrev ofContinuousMap : Specs.D12Complex.Ch03.PathsChains.ofContinuousMap_type :=
  _root_.D12Complex.ComplexPath.ofContinuousMap

abbrev smoothPartition : Specs.D12Complex.Ch03.PathsChains.smoothPartition_type :=
  _root_.D12Complex.C1Partition.single

abbrev zeroCycle : Specs.D12Complex.Ch03.PathsChains.zeroCycle_type :=
  _root_.D12Complex.IntegralCycle.zero

end D12Complex.PathsChains

namespace D12Complex

theorem isPiecewiseC1_of_contDiffOn (γ : ComplexPath)
    (h : ContDiffOn ℝ 1 γ (Icc γ.a γ.b)) : IsPiecewiseC1 γ :=
  ⟨C1Partition.single γ h⟩

theorem isPiecewiseC1_of_degenerate (γ : ComplexPath) (hab : γ.a = γ.b) :
    IsPiecewiseC1 γ := by
  refine ⟨{
    count := 0
    node := fun _ => γ.a
    first := rfl
    last := hab
    strictMono := ?_
    smooth := fun i => Fin.elim0 i }⟩
  intro i j hij
  fin_cases i
  fin_cases j
  exact (lt_irrefl _ hij).elim

namespace C1Partition

theorem piece_lt {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count) :
    P.node i.castSucc < P.node i.succ :=
  P.strictMono (by simp)

theorem piece_subset {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count) :
    P.pieceSet i ⊆ Icc γ.a γ.b := by
  intro t ht
  constructor
  · rw [← P.first]
    exact (P.strictMono.monotone (Fin.zero_le _)).trans ht.1
  · rw [← P.last]
    exact ht.2.trans (P.strictMono.monotone (Fin.le_last _))

/-- The closed-piece derivative is continuous, including one-sided endpoints. -/
theorem piece_c1_iff {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count) :
    ContDiffOn ℝ 1 γ (P.pieceSet i) ↔
      DifferentiableOn ℝ γ (P.pieceSet i) ∧
        ContinuousOn (derivWithin γ (P.pieceSet i)) (P.pieceSet i) :=
  contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc (P.piece_lt i))

theorem piece_integrable {γ : ComplexPath} (P : C1Partition γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) (i : Fin P.count) :
    IntervalIntegrable (fun t => f (γ t) * derivWithin γ (P.pieceSet i) t)
      volume (P.node i.castSucc) (P.node i.succ) := by
  have hcomp : ContinuousOn (fun t => f (γ t)) (P.pieceSet i) :=
    hf.comp (γ.continuousOn.mono (P.piece_subset i))
      (fun t ht => ⟨t, P.piece_subset i ht, rfl⟩)
  have hd := ((P.piece_c1_iff i).mp (P.smooth i)).2
  exact (hcomp.mul hd).intervalIntegrable_of_Icc (P.piece_lt i).le

theorem count_eq_zero_of_degenerate {γ : ComplexPath} (P : C1Partition γ)
    (hab : γ.a = γ.b) : P.count = 0 := by
  by_contra hn
  have hlt : (0 : Fin (P.count + 1)) < Fin.last P.count := by
    show 0 < P.count
    exact Nat.pos_of_ne_zero hn
  have := P.strictMono hlt
  rw [P.first, P.last, hab] at this
  exact (lt_irrefl _ this)

theorem integral_degenerate {γ : ComplexPath} (P : C1Partition γ)
    (hab : γ.a = γ.b) (f : ℂ → ℂ) : P.integral f = 0 := by
  unfold integral
  have hn := P.count_eq_zero_of_degenerate hab
  have : IsEmpty (Fin P.count) := by rw [hn]; infer_instance
  exact Finset.sum_eq_zero (fun i _ => isEmptyElim i)

/-- Constancy only on the actual parameter interval suffices. -/
theorem integral_of_constant {γ : ComplexPath} (P : C1Partition γ) (z : ℂ)
    (hz : ∀ t ∈ Icc γ.a γ.b, γ t = z) (f : ℂ → ℂ) : P.integral f = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with t
  intro ht
  simp only [Set.uIoc_of_le (P.piece_lt i).le] at ht
  have hmem : t ∈ P.pieceSet i :=
    ⟨le_of_lt ht.1, ht.2⟩
  have hEq : Set.EqOn γ (fun _ => z) (P.pieceSet i) :=
    fun x hx => hz x (P.piece_subset i hx)
  have hd : derivWithin γ (P.pieceSet i) t = 0 := by
    rw [derivWithin_congr hEq (hEq hmem)]
    simp
  simp [hd]

end C1Partition

namespace ComplexPath

@[simp] theorem ofContinuousMap_apply (a b : ℝ) (hab : a ≤ b)
    (g : C(Icc a b, ℂ)) (t : Icc a b) :
    ofContinuousMap a b hab g t = g t := by
  exact Set.IccExtend_of_mem hab g t.property

@[simp] theorem onInterval_ofContinuousMap (a b : ℝ) (hab : a ≤ b)
    (g : C(Icc a b, ℂ)) : (ofContinuousMap a b hab g).onInterval = g := by
  ext t
  exact ofContinuousMap_apply a b hab g t

theorem trace_nonempty (γ : ComplexPath) : γ.trace.Nonempty :=
  ⟨γ γ.a, γ.a, ⟨le_rfl, γ.ordered⟩, rfl⟩

theorem trace_compact (γ : ComplexPath) : IsCompact γ.trace :=
  isCompact_Icc.image_of_continuousOn γ.continuousOn

theorem const_trace (a b : ℝ) (hab : a ≤ b) (z : ℂ) :
    (ComplexPath.const a b hab z).trace = {z} := by
  ext w
  simp only [trace, const, Set.mem_image, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, _, rfl⟩; rfl
  · rintro rfl; exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩

end ComplexPath

namespace PiecewiseC1Path

theorem integral_degenerate (γ : PiecewiseC1Path) (hab : γ.path.a = γ.path.b)
    (f : ℂ → ℂ) : γ.integral f = 0 :=
  γ.partition.integral_degenerate hab f

theorem integral_of_constant (γ : PiecewiseC1Path) (z : ℂ)
    (hz : ∀ t ∈ Icc γ.path.a γ.path.b, γ t = z) (f : ℂ → ℂ) :
    γ.integral f = 0 := γ.partition.integral_of_constant z hz f

theorem const_integral (a b : ℝ) (hab : a ≤ b) (z : ℂ) (f : ℂ → ℂ) :
    (PiecewiseC1Path.const a b hab z).integral f = 0 := by
  apply integral_of_constant _ z
  intro t _
  rfl

theorem const_closed (a b : ℝ) (hab : a ≤ b) (z : ℂ) :
    (PiecewiseC1Path.const a b hab z).IsClosed := rfl

end PiecewiseC1Path

namespace IntegralChain

theorem mem_trace_iff (Γ : IntegralChain) (z : ℂ) :
    z ∈ Γ.trace ↔ ∃ γ : PiecewiseC1Path, Γ γ ≠ 0 ∧ z ∈ γ.trace := by
  simp [trace, Finsupp.mem_support_iff]

@[simp] theorem zero_trace : (0 : IntegralChain).trace = ∅ := by
  ext z
  simp [trace]

@[simp] theorem zero_integral (f : ℂ → ℂ) :
    (0 : IntegralChain).integral f = 0 := by simp [integral]

@[simp] theorem zero_isCycle : (0 : IntegralChain).IsCycle := by
  simp [IsCycle]

end IntegralChain

namespace IntegralCycle

@[simp] theorem zero_chain : (0 : IntegralCycle).chain = 0 := rfl

@[simp] theorem zero_trace : (0 : IntegralCycle).trace = ∅ :=
  IntegralChain.zero_trace

@[simp] theorem zero_integral (f : ℂ → ℂ) : (0 : IntegralCycle).integral f = 0 :=
  IntegralChain.zero_integral f

end IntegralCycle
end D12Complex
