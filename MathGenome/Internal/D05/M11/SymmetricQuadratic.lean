import MathGenome.Internal.D05.M11.Bilinear
import MathGenome.Internal.Specs.D05.M11.SymmetricQuadratic

/-! K05.11.symmetric_quadratic: symmetry, quadratic diagonals and the characteristic-two guard. -/

namespace D05.M11.SymmetricQuadratic

/-- The canonical symmetry predicate on a bilinear form. -/
abbrev symmetric {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : Prop := B.IsSymm

/-- The canonical space of quadratic forms, in every characteristic. -/
abbrev quadraticForm (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  QuadraticForm K V

/-- The diagonal of any bilinear form is quadratic. -/
def diagonal {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : QuadraticForm K V := B.toQuadraticMap

theorem symmetric_iff : Specs.D05.M11.SymmetricQuadratic.symmetric_iff := by
  intro K V _ _ _ B
  exact LinearMap.BilinForm.isSymm_def

theorem quadratic_iff_axioms : Specs.D05.M11.SymmetricQuadratic.quadratic_iff_axioms := by
  intro K V _ _ _ q
  constructor
  · rintro ⟨Q, hQ⟩
    constructor
    · intro a x
      simpa only [hQ, pow_two, smul_eq_mul] using Q.map_smul a x
    · exact ⟨Q.polarBilin, fun x y => by
        simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQ]⟩
  · rintro ⟨hsmul, P, hP⟩
    refine ⟨{ toFun := q, toFun_smul := ?_, exists_companion' := ?_ }, fun _ => rfl⟩
    · intro a x
      simpa only [pow_two, smul_eq_mul] using hsmul a x
    · refine ⟨P, fun x y => ?_⟩
      rw [hP]
      abel

theorem diagonal_apply : Specs.D05.M11.SymmetricQuadratic.diagonal_apply := by
  intro K V _ _ _ B x
  rfl

theorem diagonal_homogeneous : Specs.D05.M11.SymmetricQuadratic.diagonal_homogeneous := by
  intro K V _ _ _ B a x
  simpa only [Specs.D05.M11.SymmetricQuadratic.diagonal_value, pow_two, smul_eq_mul] using
    B.toQuadraticMap.map_smul a x

theorem diagonal_polar : Specs.D05.M11.SymmetricQuadratic.diagonal_polar := by
  intro K V _ _ _ B x y
  exact LinearMap.BilinMap.polar_toQuadraticMap (B := B) x y

theorem diagonal_polar_bilinear :
    Specs.D05.M11.SymmetricQuadratic.diagonal_polar_bilinear := by
  intro K V _ _ _ B
  exact LinearMap.BilinMap.polarBilin_toQuadraticMap (B := B)

theorem quadratic_polar : Specs.D05.M11.SymmetricQuadratic.quadratic_polar := by
  intro K V _ _ _ Q
  exact ⟨fun _ _ => rfl, ⟨QuadraticMap.polar_comm Q⟩⟩

theorem scalar_examples_apply : Specs.D05.M11.SymmetricQuadratic.scalar_examples_apply := by
  intro K _ x
  exact ⟨rfl, (pow_two x).symm⟩

theorem characteristic_two_polar :
    Specs.D05.M11.SymmetricQuadratic.characteristic_two_polar := by
  intro K _ _
  constructor
  · apply LinearMap.ext₂
    intro x y
    simp [QuadraticMap.polarBilin, QuadraticMap.polar]
  · apply LinearMap.ext₂
    intro x y
    change (x + y) * (x + y) - x * x - y * y = 0
    calc
      _ = (2 : K) * (x * y) := by ring
      _ = 0 := by rw [CharTwo.two_eq_zero, zero_mul]

theorem characteristic_two_distinct :
    Specs.D05.M11.SymmetricQuadratic.characteristic_two_distinct := by
  intro K _ _
  constructor
  · change (1 : K) * 1 = 1
    exact one_mul 1
  · intro h
    have h1 := congrArg (fun Q : QuadraticForm K K => Q 1) h
    change (0 : K) = 1 * 1 at h1
    exact zero_ne_one (h1.trans (mul_one 1))

theorem characteristic_two_not_injective :
    Specs.D05.M11.SymmetricQuadratic.characteristic_two_not_injective := by
  intro K _ _ hinj
  obtain ⟨hzero, hsq⟩ := characteristic_two_polar (K := K)
  exact (characteristic_two_distinct (K := K)).2 (hinj (hzero.trans hsq.symm))

end D05.M11.SymmetricQuadratic
