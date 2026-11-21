import MathGenome.Internal.Specs.D05.M10.Nilpotent
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M10.KernelStabilization

/-! K05.10.nilpotent: positive nilpotency index, dimension bound, and eigenvalues. -/

noncomputable section

namespace D05.M10.Nilpotent

/-- Canonical nilpotence of the endomorphism in its composition algebra. -/
abbrev nilpotent := Specs.D05.M10.Nilpotent.nilpotent_value

/-- The paper's index counts positive exponents even on the zero space. -/
abbrev nilpotencyIndex := Specs.D05.M10.Nilpotent.nilpotencyIndex_value

theorem nilpotent_iff_positive_power :
    Specs.D05.M10.Nilpotent.nilpotent_iff_positive_power := by
  intro K V _ _ _ N
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r + 1, Nat.succ_pos r, by rw [pow_succ, hr, zero_mul]⟩
  · rintro ⟨r, _, hr⟩
    exact ⟨r, hr⟩

theorem index_spec : Specs.D05.M10.Nilpotent.index_spec := by
  intro K V _ _ _ N hN
  have hpos := (nilpotent_iff_positive_power N).mp hN
  have hmem := Nat.sInf_mem hpos
  exact ⟨hmem.1, hmem.2, fun r hr hpow => Nat.sInf_le ⟨hr, hpow⟩⟩

theorem kernel_pow_dimension : Specs.D05.M10.Nilpotent.kernel_pow_dimension := by
  intro K V _ _ _ _ N n hn hN
  obtain ⟨r, hr⟩ := hN
  have hpow : N ^ (n + r) = 0 := by rw [pow_add, hr, mul_zero]
  exact (KernelStabilization.kernel_stabilization N n hn r).trans
    (LinearMap.ker_eq_top.mpr hpow)

theorem pow_dimension_eq_zero : Specs.D05.M10.Nilpotent.pow_dimension_eq_zero := by
  intro K V _ _ _ _ N n hn hN
  exact LinearMap.ker_eq_top.mp (kernel_pow_dimension N n hn hN)

theorem index_le_dimension : Specs.D05.M10.Nilpotent.index_le_dimension := by
  intro K V _ _ _ _ N n hn hpos hN
  exact (index_spec N hN).2.2 n hpos (pow_dimension_eq_zero N n hn hN)

theorem zero_dimensional : Specs.D05.M10.Nilpotent.zero_dimensional := by
  intro K V _ _ _ _ N hdim
  have hz := (D05.M02.Dimension.dimension_zero_iff_zero_space (K := K) (V := V)).mp hdim
  have hp : ∀ r : ℕ, N ^ r = 0 := by
    intro r
    ext x
    exact hz _
  have hN : IsNilpotent N := ⟨1, hp 1⟩
  exact ⟨hp, Nat.le_antisymm ((index_spec N hN).2.2 1 Nat.one_pos (hp 1))
    (index_spec N hN).1⟩

theorem eigenvector_scalar_eq_zero :
    Specs.D05.M10.Nilpotent.eigenvector_scalar_eq_zero := by
  intro K V _ _ _ N μ x hN hx heq
  have hv : N.HasEigenvector μ x := ⟨Module.End.mem_eigenspace_iff.mpr heq, hx⟩
  exact ((Module.End.hasEigenvalue_of_hasEigenvector hv).isNilpotent_of_isNilpotent hN).eq_zero

theorem eigenvalues : Specs.D05.M10.Nilpotent.eigenvalues := by
  intro K V _ _ _ _ _ N hN μ
  constructor
  · intro hμ
    obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    exact eigenvector_scalar_eq_zero N μ x hN hx.2 hx.apply_eq_smul
  · rintro rfl
    -- A trivial kernel would make all power kernels trivial, contradicting nilpotence.
    change N.eigenspace 0 ≠ ⊥
    rw [Module.End.eigenspace_zero]
    intro hker
    obtain ⟨r, hr⟩ := hN
    have hcon : LinearMap.ker (N ^ 0) = LinearMap.ker (N ^ (0 + 1)) := by
      change LinearMap.ker (LinearMap.id : Module.End K V) = LinearMap.ker N
      rw [LinearMap.ker_id, hker]
    have hstable := KernelStabilization.kernel_eq_of_consecutive N 0 hcon r
    simp only [Nat.zero_add] at hstable
    have hbot : (⊥ : Submodule K V) = ⊤ :=
      (KernelStabilization.initial_terms N).1.symm.trans
        (hstable.trans (LinearMap.ker_eq_top.mpr hr))
    exact bot_ne_top hbot

end D05.M10.Nilpotent
