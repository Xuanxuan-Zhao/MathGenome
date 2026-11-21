import MathGenome.Internal.Specs.D05.M13.UnitarySpectrum.Cayley
import MathGenome.Internal.D05.M13.UnitarySpectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace D05.M13.UnitarySpectrum.Cayley

open Module.End

abbrev cayley : Specs.D05.M13.UnitarySpectrum.Cayley.transform_type :=
  Specs.D05.M13.UnitarySpectrum.Cayley.cayley_value

abbrev inverseCayley : Specs.D05.M13.UnitarySpectrum.Cayley.transform_type :=
  Specs.D05.M13.UnitarySpectrum.Cayley.inverseCayley_value

abbrev alternate : Specs.D05.M13.UnitarySpectrum.Cayley.transform_type :=
  Specs.D05.M13.UnitarySpectrum.Cayley.alternate_value

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/- A diagonal map is invertible when all its diagonal entries are nonzero.
The inverse is constructed on the same basis, also for an empty basis. -/
omit [FiniteDimensional ℂ V] in
theorem isUnit_of_diagonal {ι : Type*} (b : Module.Basis ι ℂ V)
    (A : Module.End ℂ V) (μ : ι → ℂ) (hA : ∀ i, A (b i) = μ i • b i)
    (hμ : ∀ i, μ i ≠ 0) : IsUnit A := by
  let B : Module.End ℂ V := b.constr ℂ (fun i => (μ i)⁻¹ • b i)
  have hB (i : ι) : B (b i) = (μ i)⁻¹ • b i := b.constr_basis ℂ _ i
  have hAB : A * B = 1 := by
    apply b.ext
    intro i
    simp [Module.End.mul_apply, hB, hA, smul_smul, hμ i]
  have hBA : B * A = 1 := by
    apply b.ext
    intro i
    simp [Module.End.mul_apply, hB, hA, smul_smul, hμ i]
  exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

omit [FiniteDimensional ℂ V] in
theorem inverse_on_eigenvector (A : Module.End ℂ V) (hA : IsUnit A)
    {v : V} {μ : ℂ} (hv : A v = μ • v) (hμ : μ ≠ 0) :
    Ring.inverse A v = μ⁻¹ • v := by
  have he : Ring.inverse A (A v) = v :=
    DFunLike.congr_fun (Ring.inverse_mul_cancel A hA) v
  calc
    Ring.inverse A v = Ring.inverse A (μ⁻¹ • A v) := by
      rw [hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • v := by rw [map_smul, he]

theorem normal_of_diagonal (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
    (A : Module.End ℂ V) (μ : Fin (Module.finrank ℂ V) → ℂ) (hA : ∀ i, A (b i) = μ i • b i) :
    D05.normalOperator A :=
  D05.M13.ComplexSpectral.orthonormal_eigenbasis_normal A b.toBasis
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal) ⟨μ, hA⟩

theorem unitary_of_diagonal (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
    (A : Module.End ℂ V) (μ : Fin (Module.finrank ℂ V) → ℂ) (hA : ∀ i, A (b i) = μ i • b i)
    (hμ : ∀ i, ‖μ i‖ = 1) : D05.IsUnitaryMap A := by
  have hn := normal_of_diagonal b A μ hA
  apply (D05.M13.Unitary.endomorphism_isometry_iff_unitary A).mp
  apply (D05.M13.Unitary.isometry_iff_adjoint_comp A).mpr
  apply b.toBasis.ext
  intro i
  change LinearMap.adjoint A (A (b i)) = b i
  rw [hA, map_smul, D05.M13.UnitarySpectrum.adjoint_eigenvector A hn (hA i), smul_smul]
  have he : μ i * starRingEnd ℂ (μ i) = 1 := by
    rw [Complex.mul_conj', hμ i]
    norm_num
  rw [he, one_smul]

theorem selfAdjoint_of_diagonal (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
    (A : Module.End ℂ V) (μ : Fin (Module.finrank ℂ V) → ℂ) (hA : ∀ i, A (b i) = μ i • b i)
    (hμ : ∀ i, (μ i).im = 0) : D05.selfAdjoint A := by
  have hn := normal_of_diagonal b A μ hA
  apply b.toBasis.ext
  intro i
  change A (b i) = LinearMap.adjoint A (b i)
  rw [hA, D05.M13.UnitarySpectrum.adjoint_eigenvector A hn (hA i)]
  congr 1
  apply Complex.ext <;> simp [hμ i]

/-- Scalar calculations for the two fractional linear transformations. -/
theorem scalar_forward (t : ℂ) (ht : t.im = 0) :
    t + Complex.I ≠ 0 ∧ ‖(t - Complex.I) / (t + Complex.I)‖ = 1 ∧
      1 - (t - Complex.I) / (t + Complex.I) ≠ 0 := by
  have hd : t + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [ht] at this
  refine ⟨hd, ?_, ?_⟩
  · rw [norm_div]
    have hn : ‖t - Complex.I‖ = ‖t + Complex.I‖ := by
      simp [Complex.norm_def, Complex.normSq_apply, ht]
    rw [hn, div_self (norm_ne_zero_iff.mpr hd)]
  · intro h
    have he : (t - Complex.I) / (t + Complex.I) = 1 := (sub_eq_zero.mp h).symm
    have he' := (div_eq_iff hd).mp he
    have := congrArg Complex.im he'
    simp [ht] at this
    linarith

theorem scalar_backward (z : ℂ) (hz : ‖z‖ = 1) :
    (Complex.I * ((1 + z) / (1 - z))).im = 0 := by
  have hs : z.re * z.re + z.im * z.im = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hz
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    simpa using h
  rw [← mul_div_assoc, Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, zero_sub]
  rw [← sub_div, div_eq_zero_iff]
  left
  nlinarith

theorem scalar_left_inverse (t : ℂ) (ht : t.im = 0) :
    Complex.I * ((1 + (t - Complex.I) / (t + Complex.I)) /
      (1 - (t - Complex.I) / (t + Complex.I))) = t := by
  obtain ⟨hd, _, he⟩ := scalar_forward t ht
  field_simp
  ring

theorem scalar_right_inverse (z : ℂ) (hz : z ≠ 1) :
    (Complex.I * ((1 + z) / (1 - z)) - Complex.I) /
      (Complex.I * ((1 + z) / (1 - z)) + Complex.I) = z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have he : Complex.I * ((1 + z) / (1 - z)) + Complex.I ≠ 0 := by
    intro h
    have hh : (2 : ℂ) * Complex.I = 0 := by
      field_simp at h
      linear_combination h
    exact (mul_ne_zero (by norm_num) Complex.I_ne_zero) hh
  field_simp
  ring


theorem scalar_alternate (t : ℂ) (ht : t.im = 0) :
    1 + Complex.I * t ≠ 0 ∧ ‖(1 - Complex.I * t) / (1 + Complex.I * t)‖ = 1 ∧
      1 + (1 - Complex.I * t) / (1 + Complex.I * t) ≠ 0 := by
  have hd : 1 + Complex.I * t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [ht] at this
  refine ⟨hd, ?_, ?_⟩
  · rw [norm_div]
    have hn : ‖1 - Complex.I * t‖ = ‖1 + Complex.I * t‖ := by
      simp [Complex.norm_def, Complex.normSq_apply, ht]
    rw [hn, div_self (norm_ne_zero_iff.mpr hd)]
  · intro h
    have he : (1 - Complex.I * t) / (1 + Complex.I * t) = -1 := by
      linear_combination h
    have he' := (div_eq_iff hd).mp he
    have := congrArg Complex.re he'
    simp [ht] at this
    linarith

/- The forward transform acts by the scalar fractional linear map. -/
omit [FiniteDimensional ℂ V] in
theorem cayley_on_eigenvector (T : Module.End ℂ V)
    (hD : IsUnit (T + Complex.I • 1)) {v : V} {t : ℂ}
    (hv : T v = t • v) (ht : t + Complex.I ≠ 0) :
    cayley T v = ((t - Complex.I) / (t + Complex.I)) • v := by
  have hd : (T + Complex.I • 1) v = (t + Complex.I) • v := by
    simp [hv, add_smul]
  have hn : (T - Complex.I • 1) v = (t - Complex.I) • v := by
    simp [hv, sub_smul]
  change (T - Complex.I • 1) (Ring.inverse (T + Complex.I • 1) v) = _
  rw [inverse_on_eigenvector _ hD hd ht, map_smul, hn, smul_smul]
  congr 1
  simp [div_eq_mul_inv, mul_comm]

omit [FiniteDimensional ℂ V] in
theorem inverseCayley_on_eigenvector (U : Module.End ℂ V)
    (hD : IsUnit (1 - U)) {v : V} {z : ℂ}
    (hv : U v = z • v) (hz : 1 - z ≠ 0) :
    inverseCayley U v = (Complex.I * ((1 + z) / (1 - z))) • v := by
  have hd : (1 - U) v = (1 - z) • v := by simp [hv, sub_smul]
  have hn : (1 + U) v = (1 + z) • v := by simp [hv, add_smul]
  change Complex.I • ((1 + U) (Ring.inverse (1 - U) v)) = _
  rw [inverse_on_eigenvector _ hD hd hz, map_smul, hn, smul_smul, smul_smul]
  congr 1
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

omit [FiniteDimensional ℂ V] in
theorem nonzero_diagonal_of_unit {ι : Type*} (b : Module.Basis ι ℂ V)
    (A : Module.End ℂ V) (hA : IsUnit A) (μ : ι → ℂ)
    (hd : ∀ i, A (b i) = μ i • b i) : ∀ i, μ i ≠ 0 := by
  intro i hi
  apply b.ne_zero i
  apply ((Module.End.isUnit_iff A).mp hA).1
  simp [hd, hi]

theorem selfAdjoint_eigenbasis (T : Module.End ℂ V) (hT : D05.selfAdjoint T) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∃ t : Fin (Module.finrank ℂ V) → ℂ,
        (∀ i, T (b i) = t i • b i) ∧ ∀ i, (t i).im = 0 := by
  have hn := D05.M13.SelfAdjoint.selfAdjoint_implies_normal T hT
  obtain ⟨b, t, hb⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis T hn
  refine ⟨b, t, hb, fun i => ?_⟩
  exact (D05.M13.UnitarySpectrum.selfAdjoint_iff_real_eigenvalues T hn).mp hT (t i)
    (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hb i), b.toBasis.ne_zero i⟩)

theorem unitary_eigenbasis (U : Module.End ℂ V) (hU : D05.IsUnitaryMap U) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∃ z : Fin (Module.finrank ℂ V) → ℂ,
        (∀ i, U (b i) = z i • b i) ∧ ∀ i, ‖z i‖ = 1 := by
  obtain ⟨hl, hr⟩ := (D05.M13.Unitary.unitary_iff_adjoint_identities U).mp hU
  have hn : D05.normalOperator U := hr.trans hl.symm
  obtain ⟨b, z, hb⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis U hn
  refine ⟨b, z, hb, fun i => ?_⟩
  exact (D05.M13.UnitarySpectrum.unitary_iff_norm_eigenvalues U hn).mp hU (z i)
    (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hb i), b.toBasis.ne_zero i⟩)

theorem forward : Specs.D05.M13.UnitarySpectrum.Cayley.forward := by
  intro V _ _ _ T hT
  obtain ⟨b, t, hb, ht⟩ := selfAdjoint_eigenbasis T hT
  have hd (i) : (T + Complex.I • 1) (b i) = (t i + Complex.I) • b i := by
    simp [hb, add_smul]
  have hu : IsUnit (T + Complex.I • 1) :=
    isUnit_of_diagonal b.toBasis _ _ hd (fun i => (scalar_forward (t i) (ht i)).1)
  have hc (i) := cayley_on_eigenvector T hu (hb i) (scalar_forward (t i) (ht i)).1
  refine ⟨hu, unitary_of_diagonal b _ _ hc (fun i => (scalar_forward (t i) (ht i)).2.1), ?_⟩
  apply isUnit_of_diagonal b.toBasis (1 - cayley T)
    (fun i => 1 - (t i - Complex.I) / (t i + Complex.I))
  · intro i
    simp [hc, sub_smul]
  · intro i
    exact (scalar_forward (t i) (ht i)).2.2

theorem backward : Specs.D05.M13.UnitarySpectrum.Cayley.backward := by
  intro V _ _ _ U hU hD
  obtain ⟨b, z, hb, hz⟩ := unitary_eigenbasis U hU
  have hd (i) : (1 - U) (b i) = (1 - z i) • b i := by simp [hb, sub_smul]
  have hne := nonzero_diagonal_of_unit b.toBasis _ hD _ hd
  exact selfAdjoint_of_diagonal b _ _
    (fun i => inverseCayley_on_eigenvector U hD (hb i) (hne i))
    (fun i => scalar_backward (z i) (hz i))

theorem left_inverse : Specs.D05.M13.UnitarySpectrum.Cayley.left_inverse := by
  intro V _ _ _ T hT
  obtain ⟨b, t, hb, ht⟩ := selfAdjoint_eigenbasis T hT
  obtain ⟨hD, _, hE⟩ := forward T hT
  apply b.toBasis.ext
  intro i
  have hs := scalar_forward (t i) (ht i)
  change inverseCayley (cayley T) (b i) = T (b i)
  rw [inverseCayley_on_eigenvector _ hE (cayley_on_eigenvector T hD (hb i) hs.1) hs.2.2,
    scalar_left_inverse (t i) (ht i), hb]

theorem right_inverse : Specs.D05.M13.UnitarySpectrum.Cayley.right_inverse := by
  intro V _ _ _ U hU hD
  obtain ⟨b, z, hb, hz⟩ := unitary_eigenbasis U hU
  have hd (i) : (1 - U) (b i) = (1 - z i) • b i := by simp [hb, sub_smul]
  have hne := nonzero_diagonal_of_unit b.toBasis _ hD _ hd
  have hT := backward U hU hD
  have hE := (forward _ hT).1
  apply b.toBasis.ext
  intro i
  change cayley (inverseCayley U) (b i) = U (b i)
  rw [cayley_on_eigenvector _ hE
    (inverseCayley_on_eigenvector U hD (hb i) (hne i))
    (scalar_forward _ (scalar_backward (z i) (hz i))).1,
    scalar_right_inverse (z i) (fun h => hne i (by simp [h])), hb]

theorem bijection : Specs.D05.M13.UnitarySpectrum.Cayley.bijection := by
  intro V _ _ _
  let e : {T : Module.End ℂ V // D05.selfAdjoint T} ≃
      {U : Module.End ℂ V // D05.IsUnitaryMap U ∧ IsUnit (1 - U)} :=
    { toFun := fun T => ⟨cayley T.val, (forward T.val T.property).2⟩
      invFun := fun U => ⟨inverseCayley U.val, backward U.val U.property.1 U.property.2⟩
      left_inv := fun T => Subtype.ext (left_inverse T.val T.property)
      right_inv := fun U => Subtype.ext (right_inverse U.val U.property.1 U.property.2) }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

/- The second convention uses its own denominator and excluded value. -/
omit [FiniteDimensional ℂ V] in
theorem alternate_on_eigenvector (T : Module.End ℂ V)
    (hD : IsUnit (1 + Complex.I • T)) {v : V} {t : ℂ}
    (hv : T v = t • v) (ht : 1 + Complex.I * t ≠ 0) :
    alternate T v = ((1 - Complex.I * t) / (1 + Complex.I * t)) • v := by
  have hd : (1 + Complex.I • T) v = (1 + Complex.I * t) • v := by
    simp [hv, add_smul, smul_smul]
  have hn : (1 - Complex.I • T) v = (1 - Complex.I * t) • v := by
    simp [hv, sub_smul, smul_smul]
  change (1 - Complex.I • T) (Ring.inverse (1 + Complex.I • T) v) = _
  rw [inverse_on_eigenvector _ hD hd ht, map_smul, hn, smul_smul]
  congr 1
  simp [div_eq_mul_inv, mul_comm]

theorem alternate_forward : Specs.D05.M13.UnitarySpectrum.Cayley.alternate_forward := by
  intro V _ _ _ T hT
  obtain ⟨b, t, hb, ht⟩ := selfAdjoint_eigenbasis T hT
  have hd (i) : (1 + Complex.I • T) (b i) = (1 + Complex.I * t i) • b i := by
    simp [hb, add_smul, smul_smul]
  have hu : IsUnit (1 + Complex.I • T) :=
    isUnit_of_diagonal b.toBasis _ _ hd (fun i => (scalar_alternate (t i) (ht i)).1)
  have hc (i) := alternate_on_eigenvector T hu (hb i) (scalar_alternate (t i) (ht i)).1
  refine ⟨hu, unitary_of_diagonal b _ _ hc (fun i => (scalar_alternate (t i) (ht i)).2.1), ?_⟩
  apply isUnit_of_diagonal b.toBasis (1 + alternate T)
    (fun i => 1 + (1 - Complex.I * t i) / (1 + Complex.I * t i))
  · intro i
    simp [hc, add_smul]
  · intro i
    exact (scalar_alternate (t i) (ht i)).2.2

theorem excluded_eigenvalues : Specs.D05.M13.UnitarySpectrum.Cayley.excluded_eigenvalues := by
  intro V _ _ _ T hT
  constructor
  · intro he
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hi := ((Module.End.isUnit_iff (1 - cayley T)).mp (forward T hT).2.2).1
    apply hv.2
    apply hi
    simp [hv.apply_eq_smul]
  · intro he
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hi := ((Module.End.isUnit_iff (1 + alternate T)).mp (alternate_forward T hT).2.2).1
    apply hv.2
    apply hi
    simp [hv.apply_eq_smul]

end D05.M13.UnitarySpectrum.Cayley
