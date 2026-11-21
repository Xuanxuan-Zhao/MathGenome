import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.InvariantTensorPolarization
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.FirstCentralizer
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section
open scoped BigOperators
universe u v
namespace AdvancedFiniteGroupRepresentations

/-- Multilinearity makes an affine diagonal a continuous vector-valued polynomial.
The input vector space does not need any topology. -/
private theorem continuous_affine_diagonal
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    {E : Type v} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (n : ℕ) (f : MultilinearMap ℂ (fun _ : Fin n => W) E) (a b : W) :
    Continuous (fun t : ℂ => f (fun _ => a + t • b)) := by
  classical
  have expansion (t : ℂ) :
      f (fun _ => a + t • b) =
        ∑ s : Finset (Fin n), (∏ i : Fin n, if i ∈ s then (1 : ℂ) else t) •
          f (s.piecewise (fun _ => a) (fun _ => b)) := by
    rw [show (fun _ : Fin n => a + t • b) =
      (fun _ => a) + (fun _ => t • b) from rfl, f.map_add_univ]
    apply Finset.sum_congr rfl
    intro s _
    rw [← f.map_smul_univ]
    congr 1
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  simp_rw [expansion]
  apply continuous_finsetSum
  intro s _
  apply Continuous.smul
  · apply continuous_finsetProd
    intro i _
    change Continuous (fun t : ℂ => if i ∈ s then 1 else t)
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using (continuous_const : Continuous (fun _ : ℂ => (1 : ℂ)))
    · have he : (fun t : ℂ => if i ∈ s then 1 else t) = (id : ℂ → ℂ) := by
        funext t
        exact ite_eq_right hi
      rw [he]
      exact continuous_id
  · exact continuous_const

variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The finite spectrum leaves a dense set of invertible scalar shifts. Taking
limits in a finite-dimensional subspace gives the same conclusion as Lagrange
interpolation in the source proof. -/
theorem operatorPower_mem_diagonalSpan (n : ℕ) (T : Module.End ℂ V) :
    PiTensorProduct.map (fun _ : Fin n => T) ∈
      Submodule.span ℂ (Set.range (diagonalOperator V n)) := by
  classical
  let E := Module.End ℂ (TensorPower V n)
  let e := (Module.finBasis ℂ E).equivFun
  let : NormedAddCommGroup E := NormedAddCommGroup.induced E _ e e.injective
  let : NormedSpace ℂ E := NormedSpace.induced ℂ E _ e
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range (diagonalOperator V n))
  have hc : Continuous (fun t : ℂ => PiTensorProduct.map
      (fun _ : Fin n => T + t • (1 : Module.End ℂ V))) :=
    continuous_affine_diagonal n
      (PiTensorProduct.mapMultilinear ℂ (fun _ : Fin n => V) (fun _ => V)) T 1
  have hd : Dense (spectrum ℂ (-T))ᶜ :=
    (Module.End.finite_spectrum (-T)).countable.dense_compl ℂ
  have hclosed : IsClosed {t : ℂ | PiTensorProduct.map
      (fun _ : Fin n => T + t • (1 : Module.End ℂ V)) ∈ S} :=
    (Submodule.closed_of_finiteDimensional S).preimage hc
  have hmem : ∀ t ∈ (spectrum ℂ (-T))ᶜ,
      PiTensorProduct.map (fun _ : Fin n => T + t • (1 : Module.End ℂ V)) ∈ S := by
    intro t ht
    have hu : IsUnit (T + t • (1 : Module.End ℂ V)) := by
      simpa [Algebra.algebraMap_eq_smul_one, sub_neg_eq_add, add_comm] using
        (spectrum.notMem_iff.mp ht)
    obtain ⟨g, hg⟩ := hu
    apply Submodule.subset_span
    refine ⟨LinearMap.GeneralLinearGroup.toLinearEquiv g, ?_⟩
    change PiTensorProduct.map (fun _ : Fin n => (g : Module.End ℂ V)) = _
    rw [hg]
  have hzero : PiTensorProduct.map
      (fun _ : Fin n => T + (0 : ℂ) • (1 : Module.End ℂ V)) ∈ S :=
    hd.induction hmem hclosed 0
  simpa using hzero

/-- In degree zero the canonical tensor identification makes every operator scalar. -/
theorem tensorAlgebras_zero : tensorA V 0 = ⊤ ∧ tensorB V 0 = ⊤ := by
  have htop (S : Subalgebra ℂ (Module.End ℂ (TensorPower V 0))) : S = ⊤ := by
    apply top_unique
    intro F _
    obtain ⟨t, rfl⟩ := (endomorphismTensor_bijective V 0).2 F
    rw [endomorphismTensor_zero]
    exact S.smul_mem S.one_mem _
  exact ⟨htop _, htop _⟩

/-- These are the whole zero algebra, whose identity is its unique element. -/
theorem tensorAlgebras_zero_dimension (n : ℕ) (hn : 0 < n)
    (hd : Module.finrank ℂ V = 0) :
    (0 : Module.End ℂ (TensorPower V n)) = 1 ∧
      tensorA V n = ⊤ ∧ tensorB V n = ⊤ := by
  let := tensorPower_zero_dimension V n hn hd
  have htop (S : Subalgebra ℂ (Module.End ℂ (TensorPower V n))) : S = ⊤ := by
    apply top_unique
    intro F _
    rw [Subsingleton.elim F 0]
    exact S.zero_mem
  exact ⟨tensorEnd_zero_dimension V n hn hd, htop _, htop _⟩

/-- Schur--Weyl's first centralizer identity, including both boundary cases. -/
theorem firstCentralizer (n : ℕ) :
    Subalgebra.centralizer ℂ (tensorA V n : Set (Module.End ℂ (TensorPower V n))) =
      tensorB V n := by
  have hle : tensorB V n ≤ Subalgebra.centralizer ℂ (tensorA V n : Set _) := by
    intro F hF a ha
    exact tensor_subalgebras_commute V n a ha F hF
  apply le_antisymm ?_ hle
  intro F hF
  by_cases hn : n = 0
  · subst n
    rw [(tensorAlgebras_zero V).2]
    trivial
  by_cases hd : Module.finrank ℂ V = 0
  · rw [(tensorAlgebras_zero_dimension V n (Nat.pos_of_ne_zero hn) hd).2.2]
    trivial
  obtain ⟨t, rfl⟩ := (endomorphismTensor_bijective V n).2 F
  have ht := (endomorphismTensor_invariant_iff V n t).mpr hF
  have hs := (tensor_invariant_iff_mem_purePowerSpan (Module.End ℂ V) n t).mp ht
  clear hF ht
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    rw [endomorphismTensor_pure]
    have hp := operatorPower_mem_diagonalSpan V n T
    rw [← tensorB_span V n] at hp
    exact hp
  | zero =>
    rw [map_zero]
    exact (tensorB V n).zero_mem
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (tensorB V n).add_mem ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact (tensorB V n).smul_mem ih c

end AdvancedFiniteGroupRepresentations
