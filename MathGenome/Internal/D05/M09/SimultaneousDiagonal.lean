import MathGenome.Internal.Specs.D05.M09.SimultaneousDiagonal
import MathGenome.Internal.D05.M09.SimultaneousDiagonal.Finite
import MathGenome.Internal.D05.M03.HomDimension.FiniteOperatorSpan

/-! Simultaneous diagonalization for arbitrary families, by finite span
selection followed by the proved finite-family theorem. -/

noncomputable section

namespace D05.M09.SimultaneousDiagonal

def simultaneouslyDiagonalizable (K V ι : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : ι → Module.End K V) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) K V) (μ : ι → Fin d → K),
    ∀ i j, T i (b j) = μ i j • b j

/-- Having a given vector as an eigenvector (with zero allowed here) is
closed under linear combinations of operators. No spectral assumption
on those combinations is used. -/
theorem eigenvector_of_mem_span {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (S : Set (Module.End K V)) (v : V)
    (hS : ∀ A ∈ S, ∃ a : K, A v = a • v)
    (A : Module.End K V) (hA : A ∈ Submodule.span K S) :
    ∃ a : K, A v = a • v := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact hS A hA
  | zero => exact ⟨0, by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a + b, by simp only [LinearMap.add_apply, ha, hb, add_smul]⟩
  | smul c A _ hA =>
    obtain ⟨a, ha⟩ := hA
    exact ⟨c * a, by simp only [LinearMap.smul_apply, ha, smul_smul]⟩

theorem common_eigenbasis : Specs.D05.M09.SimultaneousDiagonal.common_eigenbasis := by
  intro K V ι _ _ _ _ T hC hD
  classical
  have hC_all (i j : ι) : Commute (T i) (T j) := by
    by_cases hij : i = j
    · rw [hij]
    · exact hC hij
  obtain ⟨s, hsF, hs, _, _, _⟩ :=
    M03.HomDimension.FiniteOperatorSpan.finite_operator_span
      (Module.finrank K V) rfl (Set.range T)
  let R : s → Module.End K V := fun A => A.val
  have hRC : Pairwise (fun i j => Commute (R i) (R j)) := by
    intro A B _
    obtain ⟨i, hi⟩ := hsF A.property
    obtain ⟨j, hj⟩ := hsF B.property
    simpa only [R, ← hi, ← hj] using hC_all i j
  have hRD : ∀ A, Specs.D05.M09.Diagonalizable.diagonalizable_value K V (R A) := by
    intro A
    obtain ⟨i, hi⟩ := hsF A.property
    simpa only [R, ← hi] using hD i
  obtain ⟨d, b, μ, hb⟩ := Finite.finite_common_eigenbasis R hRC hRD
  have hEigen (i : ι) (j : Fin d) : ∃ a : K, T i (b j) = a • b j := by
    refine eigenvector_of_mem_span (s : Set (Module.End K V)) (b j) ?_ (T i) ?_
    · intro A hA
      exact ⟨μ ⟨A, hA⟩ j, hb ⟨A, hA⟩ j⟩
    · rw [hs]
      exact Submodule.subset_span ⟨i, rfl⟩
  choose ν hν using hEigen
  exact ⟨d, b, ν, hν⟩

theorem common_eigenbasis_converse :
    Specs.D05.M09.SimultaneousDiagonal.common_eigenbasis_converse := by
  intro K V ι _ _ _ _ T h
  obtain ⟨d, b, μ, hb⟩ := h
  refine ⟨(fun i => ⟨d, b, μ i, hb i⟩), ?_⟩
  intro i j _
  apply b.ext
  intro k
  change T i (T j (b k)) = T j (T i (b k))
  rw [hb j k, hb i k, map_smul, map_smul, hb i k, hb j k,
    smul_smul, smul_smul, mul_comm]

theorem simultaneous_iff_diagonalizable_and_commute :
    Specs.D05.M09.SimultaneousDiagonal.simultaneous_iff_diagonalizable_and_commute := by
  intro K V ι _ _ _ _ T
  exact ⟨common_eigenbasis_converse T, fun h => common_eigenbasis T h.2 h.1⟩

theorem commute_iff_simultaneous :
    Specs.D05.M09.SimultaneousDiagonal.commute_iff_simultaneous := by
  intro K V ι _ _ _ _ T hD
  exact ⟨fun hC => common_eigenbasis T hC hD,
    fun h => (common_eigenbasis_converse T h).2⟩

theorem set_common_eigenbasis : Specs.D05.M09.SimultaneousDiagonal.set_common_eigenbasis := by
  intro K V _ _ _ _ F hC hD
  obtain ⟨d, b, μ, hb⟩ := common_eigenbasis (fun A : F => A.val)
    (fun {A B} _ => hC A.val A.property B.val B.property)
    (fun A => hD A.val A.property)
  exact ⟨d, b, fun A hA => ⟨μ ⟨A, hA⟩, hb ⟨A, hA⟩⟩⟩

theorem empty_family_common_eigenbasis :
    Specs.D05.M09.SimultaneousDiagonal.empty_family_common_eigenbasis := by
  intro K V ι _ _ _ _ _ T
  exact Finite.empty_family_common_eigenbasis T

theorem zero_space_common_eigenbasis :
    Specs.D05.M09.SimultaneousDiagonal.zero_space_common_eigenbasis := by
  intro K V ι _ _ _ _ T
  exact ⟨Module.Basis.empty V, (fun _ j => Fin.elim0 j), fun _ j => Fin.elim0 j⟩

end D05.M09.SimultaneousDiagonal
