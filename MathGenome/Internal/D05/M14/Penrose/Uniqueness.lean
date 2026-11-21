import MathGenome.Internal.Specs.D05.M14.Penrose.Uniqueness
import MathGenome.Internal.D05.M14.Pseudoinverse
import MathGenome.Internal.D05.M06.Projection
import MathGenome.Internal.D05.M13.AdjointLaws

/-! K05.14.penrose: uniqueness from the four Penrose identities. -/

noncomputable section
namespace D05.M14.Penrose.Uniqueness

/-- The residual of an idempotent lies in its kernel. Self-adjointness
identifies that kernel with the perpendicular of its range. -/
theorem self_adjoint_idempotent_projection :
    Specs.D05.M14.Penrose.Uniqueness.self_adjoint_idempotent_projection := by
  intro F V _ _ _ _ P hP hsa
  have horth : P.range.orthogonal = P.ker := by
    rw [LinearMap.orthogonal_range, hsa]
  constructor
  · apply LinearMap.ext
    intro v
    symm
    apply (D05.M12.Projection.component_characterization P.range v (P v)).mpr
    refine ⟨LinearMap.mem_range_self P v, ?_⟩
    rw [horth]
    change P (v - P v) = 0
    have hPv : P (P v) = P v := DFunLike.congr_fun hP v
    rw [map_sub, hPv, sub_self]
  · rw [LinearMap.orthogonal_ker, hsa]

theorem candidate_range_projection :
    Specs.D05.M14.Penrose.Uniqueness.candidate_range_projection := by
  intro F V W _ _ _ _ _ _ _ T X hTXT hsa
  have hid : (T.comp X).comp (T.comp X) = T.comp X := by
    rw [← LinearMap.comp_assoc, hTXT]
  have hr : (T.comp X).range = T.range := by
    apply le_antisymm
    · rintro y ⟨w, rfl⟩
      exact LinearMap.mem_range_self T (X w)
    · rintro y ⟨v, rfl⟩
      refine ⟨T v, ?_⟩
      exact DFunLike.congr_fun hTXT v
  have hp := (self_adjoint_idempotent_projection (T.comp X) hid hsa).1
  simpa only [hr] using hp

theorem candidate_kernel_projection :
    Specs.D05.M14.Penrose.Uniqueness.candidate_kernel_projection := by
  intro F V W _ _ _ _ _ _ _ T X hTXT hsa
  have hid : (X.comp T).comp (X.comp T) = X.comp T := by
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc T X T, hTXT]
  have hk : (X.comp T).ker = T.ker := by
    ext v
    change X (T v) = 0 ↔ T v = 0
    constructor
    · intro hv
      calc
        T v = T (X (T v)) := (DFunLike.congr_fun hTXT v).symm
        _ = 0 := by rw [hv, map_zero]
    · intro hv
      rw [hv, map_zero]
  obtain ⟨hp, hr⟩ := self_adjoint_idempotent_projection (X.comp T) hid hsa
  simpa only [hr, hk] using hp

theorem candidate_characterization :
    Specs.D05.M14.Penrose.Uniqueness.candidate_characterization := by
  intro F V W _ _ _ _ _ _ _ T X hTXT hXTX hTXsa hXTsa w
  have hp := candidate_kernel_projection T X hTXT hXTsa
  have hXw : (X.comp T) (X w) = X w := DFunLike.congr_fun hXTX w
  constructor
  · rw [hp] at hXw
    exact ((D05.M12.Projection.component_characterization
      T.ker.orthogonal (X w) (X w)).mp hXw).1
  · exact DFunLike.congr_fun (candidate_range_projection T X hTXT hTXsa) w

theorem uniqueness : Specs.D05.M14.Penrose.Uniqueness.uniqueness := by
  intro F V W _ _ _ _ _ _ _ T X hTXT hXTX hTXsa hXTsa
  apply LinearMap.ext
  intro w
  exact (D05.M14.Pseudoinverse.characterization T w (X w)).mpr
    (candidate_characterization T X hTXT hXTX hTXsa hXTsa w)

end D05.M14.Penrose.Uniqueness
