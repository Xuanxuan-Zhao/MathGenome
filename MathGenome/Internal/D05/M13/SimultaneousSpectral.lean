import MathGenome.Internal.Specs.D05.M13.SimultaneousSpectral
import MathGenome.Internal.D05.M13.NormalBasic
import MathGenome.Internal.D05.M13.NormalReducing
import MathGenome.Internal.D05.M13.SelfAdjoint
import MathGenome.Internal.D05.M12.Orthonormal
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! Common orthonormal eigenbases for arbitrary commuting families.
The symmetric joint-eigenspace theorem is dimension-based and requires no
finite index set. For complex normal maps, apply it to the commuting family
of all real and imaginary self-adjoint parts. -/

noncomputable section
namespace D05.M13.SimultaneousSpectral
open Module.End

/-- Collect orthonormal bases of the mutually orthogonal joint eigenspaces. -/
theorem symmetric_common_basis {F V ι : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V]
    (T : ι → Module.End F V) (hT : ∀ i, (T i).IsSymmetric)
    (hC : ∀ i j, Commute (T i) (T j)) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank F V)) F V,
      ∃ μ : ι → Fin (Module.finrank F V) → F,
        ∀ i k, T i (b k) = μ i k • b k := by
  classical
  let W (χ : ι → F) : Submodule F V := ⨅ i, (T i).eigenspace (χ i)
  have hfull := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT
    (fun i j _ => hC i j)
  letI : Fintype {χ : ι → F // W χ ≠ ⊥} :=
    hfull.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have ho := (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT).comp
    (f := fun χ : {χ : ι → F // W χ ≠ ⊥} => χ.val) Subtype.val_injective
  have hi : DirectSum.IsInternal (fun χ : {χ : ι → F // W χ ≠ ⊥} => W χ) :=
    DirectSum.isInternal_ne_bot_iff.mpr hfull
  refine ⟨hi.subordinateOrthonormalBasis rfl ho,
    fun i k => (hi.subordinateOrthonormalBasisIndex rfl k ho).val i, ?_⟩
  intro i k
  exact mem_eigenspace_iff.mp
    ((Submodule.mem_iInf _).mp (hi.subordinateOrthonormalBasis_subordinate rfl k ho) i)

theorem real_common_orthonormal_eigenbasis :
    Specs.D05.M13.SimultaneousSpectral.real_common_orthonormal_eigenbasis := by
  intro V _ _ _ ι T hT hC
  obtain ⟨b, μ, hb⟩ := symmetric_common_basis T
    (fun i => (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric (T i)).mp (hT i))
    (fun i j => show Commute (T i) (T j) from hC i j)
  exact ⟨b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal, μ, hb⟩

/-- All four combinations of a pair of maps and their adjoints commute. -/
theorem commute_adjoints {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (S T : Module.End ℂ V) (hS : D05.normalOperator S)
    (hT : D05.normalOperator T) (hST : Commute S T) :
    Commute S T.adjoint ∧ Commute S.adjoint T ∧ Commute S.adjoint T.adjoint := by
  have h1 : Commute S T.adjoint :=
    D05.M13.NormalReducing.commutes_adjoint T S hT hST.eq
  have h2 : Commute S.adjoint T :=
    (show Commute T S.adjoint from
      D05.M13.NormalReducing.commutes_adjoint S T hS hST.symm.eq).symm
  have h3 : Commute S.adjoint T.adjoint := by
    have h : (S.comp T).adjoint = (T.comp S).adjoint :=
      congrArg LinearMap.adjoint hST.eq
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp] at h
    exact h.symm
  exact ⟨h1, h2, h3⟩

theorem complex_common_orthonormal_eigenbasis :
    Specs.D05.M13.SimultaneousSpectral.complex_common_orthonormal_eigenbasis := by
  intro V _ _ _ ι T hT hC
  let A (i : ι) := (2 : ℂ)⁻¹ • (T i + (T i).adjoint)
  let B (i : ι) := (2 * Complex.I)⁻¹ • (T i - (T i).adjoint)
  let P : ι × Bool → Module.End ℂ V := fun p => if p.2 then B p.1 else A p.1
  have hs : ∀ p, (P p).IsSymmetric := by
    rintro ⟨i, b⟩
    apply (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric _).mp
    cases b
    · exact D05.M13.NormalBasic.real_part_selfAdjoint (T i)
    · exact D05.M13.NormalBasic.imag_part_selfAdjoint (T i)
  have hc : ∀ p q, Commute (P p) (P q) := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    have hij : Commute (T i) (T j) := hC i j
    obtain ⟨h1, h2, h3⟩ := commute_adjoints (T i) (T j) (hT i) (hT j) hij
    cases a <;> cases b <;> dsimp [P, A, B]
    · exact ((hij.add_right h1).add_left (h2.add_right h3)).smul_left _ |>.smul_right _
    · exact ((hij.sub_right h1).add_left (h2.sub_right h3)).smul_left _ |>.smul_right _
    · exact ((hij.add_right h1).sub_left (h2.add_right h3)).smul_left _ |>.smul_right _
    · exact ((hij.sub_right h1).sub_left (h2.sub_right h3)).smul_left _ |>.smul_right _
  obtain ⟨b, μ, hb⟩ := symmetric_common_basis P hs hc
  refine ⟨b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal,
    fun i k => μ (i, false) k + Complex.I * μ (i, true) k, ?_⟩
  intro i k
  have ha : A i (b k) = μ (i, false) k • b k := hb (i, false) k
  have hd : B i (b k) = μ (i, true) k • b k := hb (i, true) k
  rw [D05.M13.NormalBasic.complex_decomposition (T i)]
  change A i (b k) + Complex.I • B i (b k) = _
  rw [ha, hd, smul_smul, add_smul]
  rfl

theorem real_normal_diagonalizable_selfAdjoint :
    Specs.D05.M13.SimultaneousSpectral.real_normal_diagonalizable_selfAdjoint := by
  intro V _ _ _ T hT ⟨b, μ, hb⟩
  apply b.ext
  intro k
  have ha := (D05.M13.NormalBasic.eigenvector_equation_iff T hT (μ k) (b k)).mp (hb k)
  simpa using (hb k).trans ha.symm

theorem real_normal_diagonalizable_common_basis :
    Specs.D05.M13.SimultaneousSpectral.real_normal_diagonalizable_common_basis := by
  intro V _ _ _ ι T hT hd hC
  exact real_common_orthonormal_eigenbasis T
    (fun i => real_normal_diagonalizable_selfAdjoint (T i) (hT i) (hd i)) hC

end D05.M13.SimultaneousSpectral
