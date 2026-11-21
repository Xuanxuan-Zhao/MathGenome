import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions

/-!
Banach-algebra conventions for the manuscript.

Native algebra, norm and operator structures are retained. Algebraic spectrum
and resolvent work without completeness or nonzero hypotheses, including on
bounded operators on an incomplete normed space. In particular an operator's
inverse witness below is itself a bounded, everywhere-defined operator on X.
The point and approximate point spectra use the same scalar field as X.

Nonunital spectra use the native ℓ¹ unitization. Characters are algebraic,
nonzero scalar-linear multiplicative maps; they have no boundedness assumption.
-/

namespace ExpandedFA.BanachAlgebra

open Specs.ExpandedFA.BanachAlgebra.Conventions

universe u v

abbrev IsBanachAlgebra : IsBanachAlgebraType.{u} :=
  IsBanachAlgebraValue

abbrev IsUnitalBanachAlgebra : IsUnitalBanachAlgebraType.{u} :=
  IsUnitalBanachAlgebraValue

abbrev AlgebraInvertible : AlgebraInvertibleType.{u} :=
  AlgebraInvertibleValue

abbrev algebraResolventSet : AlgebraScalarSetType.{u, v} :=
  fun 𝕜 _ _ _ _ a => _root_.resolventSet 𝕜 a

abbrev algebraSpectrum : AlgebraScalarSetType.{u, v} :=
  fun 𝕜 _ _ _ _ a => _root_.spectrum 𝕜 a

/-- `algebraResolvent 𝕜 A a z` denotes R(z,a), with zero extension off ρ(a). -/
noncomputable abbrev algebraResolvent : AlgebraResolventType.{u, v} :=
  fun _ _ _ _ _ a z => _root_.resolvent a z

noncomputable abbrev algebraSpectralRadius : AlgebraSpectralRadiusType.{u, v} :=
  AlgebraSpectralRadiusValue

abbrev L1Unitization : UnitizationType.{u} :=
  UnitizationValue

abbrev unitizationInclusion : UnitizationInclusionType.{u} :=
  UnitizationInclusionValue

abbrev nonunitalSpectrum : NonunitalSpectrumType.{u} :=
  NonunitalSpectrumValue

noncomputable abbrev nonunitalResolvent : NonunitalResolventType.{u} :=
  NonunitalResolventValue

noncomputable abbrev nonunitalSpectralRadius : NonunitalSpectralRadiusType.{u} :=
  NonunitalSpectralRadiusValue

abbrev pointSpectrum : OperatorScalarSetType.{u, v} :=
  PointSpectrumValue

abbrev approximatePointSpectrum : OperatorScalarSetType.{u, v} :=
  ApproximatePointSpectrumValue

/-- A set of linear maps, with nonzeroness and multiplicativity only. -/
abbrev characterSpace : CharacterSpaceType.{u, v} :=
  CharacterSpaceValue

abbrev Character : CharacterType.{u, v} :=
  CharacterValue

theorem invertible_iff_two_sided_inverse : InvertibleTwoSidedInverse.{u} := by
  intro A _ a
  exact isUnit_iff_exists

theorem mem_algebraSpectrum_iff : SpectrumMembership.{u, v} := by
  intro 𝕜 A _ _ _ a z
  change (¬ IsUnit (algebraMap 𝕜 A z - a)) ↔ _
  rw [Algebra.algebraMap_eq_smul_one]

theorem algebraResolvent_inverse : ResolventInverse.{u, v} := by
  intro 𝕜 A _ _ _ a z hz
  have hu : IsUnit (algebraMap 𝕜 A z - a) := hz
  simpa only [AlgebraResolventValue, Algebra.algebraMap_eq_smul_one] using
    And.intro (Ring.mul_inverse_cancel _ hu) (Ring.inverse_mul_cancel _ hu)

theorem operator_resolvent_iff_bounded_inverse : OperatorResolventBoundedInverse.{u, v} := by
  intro 𝕜 X _ _ _ T z
  change IsUnit (algebraMap 𝕜 (X →L[𝕜] X) z - T) ↔ _
  rw [Algebra.algebraMap_eq_smul_one, isUnit_iff_exists]
  constructor
  · rintro ⟨S, hright, hleft⟩
    refine ⟨S, ?_, ?_⟩
    · intro x
      simpa using congrArg (fun U : X →L[𝕜] X => U x) hleft
    · intro x
      simpa using congrArg (fun U : X →L[𝕜] X => U x) hright
  · rintro ⟨S, hleft, hright⟩
    refine ⟨S, ?_, ?_⟩
    · ext x
      simpa using hright x
    · ext x
      simpa using hleft x

theorem operator_spectrum_iff_no_bounded_inverse : OperatorSpectrumNoBoundedInverse.{u, v} := by
  intro 𝕜 X _ _ _ T z
  exact not_congr (operator_resolvent_iff_bounded_inverse 𝕜 X T z)

theorem zero_space_spectra : ZeroSpaceSpectra.{u, v} := by
  intro 𝕜 X _ _ _ _ T
  refine ⟨_root_.spectrum.of_subsingleton T, ?_, ?_⟩
  · ext z
    change (∃ x : X, x ≠ 0 ∧ T x = z • x) ↔ False
    simp only [Subsingleton.elim _ (0 : X), ne_eq, not_true_eq_false, false_and, exists_false]
  · ext z
    change (∀ ε : ℝ, 0 < ε → ∃ x : X, ‖x‖ = 1 ∧ ‖T x - z • x‖ < ε) ↔ False
    constructor
    · intro h
      obtain ⟨x, hx, _⟩ := h 1 zero_lt_one
      simp only [Subsingleton.elim x (0 : X), norm_zero, zero_ne_one] at hx
    · exact False.elim

/-! Convenience accessors for algebraic characters. -/

namespace Character

variable {𝕜 : Type u} {A : Type v} [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A]

instance : FunLike (Character 𝕜 A) A 𝕜 where
  coe χ := χ.val
  coe_injective _χ _ψ h := Subtype.ext (LinearMap.ext fun a => congrFun h a)

instance : LinearMapClass (Character 𝕜 A) 𝕜 A 𝕜 where
  map_add χ := χ.val.map_add
  map_smulₛₗ χ := χ.val.map_smul

@[simp] theorem map_mul (χ : Character 𝕜 A) (a b : A) : χ (a * b) = χ a * χ b :=
  χ.property.2 a b

theorem nonzero (χ : Character 𝕜 A) : χ.val ≠ 0 := χ.property.1

end Character

end ExpandedFA.BanachAlgebra
