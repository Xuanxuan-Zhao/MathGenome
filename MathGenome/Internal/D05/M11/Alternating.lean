import MathGenome.Internal.D05.M11.Bilinear
import MathGenome.Internal.Specs.D05.M11.Alternating
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! K05.11.alternating: characteristic-sensitive skew-symmetry, explicit
symmetric/alternating decomposition, and its diagonal-function bridge. -/

namespace D05.M11.Alternating

open Specs.D05.M11.Alternating (symmetricPart alternatingPart)

theorem alternating_iff_diagonal : Specs.D05.M11.Alternating.alternating_iff_diagonal := by
  intro K V _ _ _ B
  rfl

theorem alternating_implies_skew : Specs.D05.M11.Alternating.alternating_implies_skew := by
  intro K V _ _ _ B h u v
  exact (h.neg_eq v u).symm

theorem skew_diagonal_two_mul : Specs.D05.M11.Alternating.skew_diagonal_two_mul := by
  intro K V _ _ _ B h v
  rw [two_mul]
  exact eq_neg_iff_add_eq_zero.mp (h v v)

theorem alternating_iff_skew : Specs.D05.M11.Alternating.alternating_iff_skew := by
  intro K V _ _ _ h2 B
  constructor
  · exact alternating_implies_skew B
  · intro h v
    exact (mul_eq_zero.mp (skew_diagonal_two_mul B h v)).resolve_left h2

theorem characteristic_two_counterexample :
    Specs.D05.M11.Alternating.characteristic_two_counterexample := by
  intro K _ h2
  have hneg (z : K) : z = -z := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [← two_mul, h2, zero_mul]
  refine ⟨LinearMap.mul K K, Module.finrank_self K, (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro x y
    change x * y = -(y * x)
    rw [mul_comm y x]
    exact hneg _
  · change (1 : K) * 1 = 1
    exact one_mul 1
  · intro h
    have hz := h.self_eq_zero (1 : K)
    change (1 : K) * 1 = 0 at hz
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa only [one_mul] using hz)

theorem part_formulas : Specs.D05.M11.Alternating.part_formulas := by
  intro K V _ _ _ B u v
  constructor
  · change (2 : K)⁻¹ * (B u v + B v u) = _
    rw [div_eq_mul_inv, mul_comm]
  · change (2 : K)⁻¹ * (B u v - B v u) = _
    rw [div_eq_mul_inv, mul_comm]

theorem part_properties : Specs.D05.M11.Alternating.part_properties := by
  intro K V _ _ _ B
  have hs : (symmetricPart B).IsSymm := by
    constructor
    intro u v
    rw [(part_formulas B u v).1, (part_formulas B v u).1, add_comm]
  have ha : (alternatingPart B).IsAlt := by
    intro v
    rw [(part_formulas B v v).2, sub_self, zero_div]
  exact ⟨hs, ha, alternating_implies_skew _ ha⟩

theorem decomposition : Specs.D05.M11.Alternating.decomposition := by
  intro K V _ _ _ h2 B
  ext u v
  change B u v = symmetricPart B u v + alternatingPart B u v
  rw [(part_formulas B u v).1, (part_formulas B u v).2]
  field_simp [h2]
  ring

theorem symmetric_alternating_eq_zero :
    Specs.D05.M11.Alternating.symmetric_alternating_eq_zero := by
  intro K V _ _ _ h2 B hs ha
  ext u v
  change B u v = 0
  have hz : (2 : K) * B u v = 0 := by
    rw [two_mul]
    apply eq_neg_iff_add_eq_zero.mp
    exact (hs.eq u v).trans (alternating_implies_skew B ha v u)
  exact (mul_eq_zero.mp hz).resolve_left h2

theorem diagonal_eq_symmetricPart :
    Specs.D05.M11.Alternating.diagonal_eq_symmetricPart := by
  intro K V _ _ _ h2 B v
  have h := LinearMap.BilinForm.congr_fun (decomposition h2 B) v v
  change B v v = symmetricPart B v v + alternatingPart B v v at h
  rw [(part_properties B).2.1.self_eq_zero v, add_zero] at h
  exact h

theorem decomposition_unique : Specs.D05.M11.Alternating.decomposition_unique := by
  intro K V _ _ _ h2 B S A hs ha heq
  let : NeZero (2 : K) := ⟨h2⟩
  have hS : S = symmetricPart B := by
    apply LinearMap.BilinForm.ext_of_isSymm hs (part_properties B).1
    intro v
    rw [← diagonal_eq_symmetricPart h2 B v, heq]
    change S v v = S v v + A v v
    rw [ha.self_eq_zero v, add_zero]
  refine ⟨hS, ?_⟩
  have h := (decomposition h2 B).symm.trans heq
  rw [hS] at h
  ext u v
  have hv := LinearMap.BilinForm.congr_fun h u v
  change symmetricPart B u v + alternatingPart B u v = symmetricPart B u v + A u v at hv
  exact (add_left_cancel hv).symm

theorem exists_unique_decomposition :
    Specs.D05.M11.Alternating.exists_unique_decomposition := by
  intro K V _ _ _ h2 B
  refine ⟨(symmetricPart B, alternatingPart B),
    ⟨(part_properties B).1, (part_properties B).2.1, decomposition h2 B⟩, ?_⟩
  rintro ⟨S, A⟩ ⟨hs, ha, heq⟩
  exact Prod.ext (decomposition_unique h2 B S A hs ha heq).1
    (decomposition_unique h2 B S A hs ha heq).2

theorem exists_unique_symmetric_representative :
    Specs.D05.M11.Alternating.exists_unique_symmetric_representative := by
  intro K V _ _ _ h2 B
  let : NeZero (2 : K) := ⟨h2⟩
  refine ⟨symmetricPart B, ⟨(part_properties B).1,
    fun v => (diagonal_eq_symmetricPart h2 B v).symm⟩, ?_⟩
  rintro S ⟨hs, hd⟩
  apply LinearMap.BilinForm.ext_of_isSymm hs (part_properties B).1
  intro v
  exact (hd v).trans (diagonal_eq_symmetricPart h2 B v)

end D05.M11.Alternating
