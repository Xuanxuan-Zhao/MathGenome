import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.BasicRepresentation
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.Integrability
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Batteries.Tactic.OpenPrivate

/-! The level-one basic representation of the untwisted affine algebra. -/

noncomputable section

open UniversalEnvelopingAlgebra (ι)

universe u

namespace RepTheorySurvey.Affine

open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)
open _root_.Specs.RepTheorySurvey.Affine.BasicRepresentation
open _root_.Specs.RepTheorySurvey.Affine.Integrability (coe_affineSimpleCoroot)
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces (coordinates sideDegrees)
open _root_.Specs.RepTheorySurvey.Affine.VermaWeightSpaces
open _root_.Specs.RepTheorySurvey.Affine.VermaModules (centralCartanElement)

open private coordinates_homogeneous coordinates_K coordinates_d homogeneous_mem_components
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
open private enveloping_commutator from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.Integrability

abbrev basicWeight := @basicWeight_value

theorem basicWeightCoordinates : basicWeightCoordinates_type.{u} := by
  intro G _ _ B H
  refine ⟨?_, ?_, ?_⟩
  · change (coordinates B (K B)).1.2 = 1
    rw [coordinates_K]
  · intro x hx
    change (coordinates B x.1).1.2 = 0
    rw [hx, coordinates_d]
  · intro h x hx
    change (coordinates B x.1).1.2 = 0
    rw [hx, coordinates_homogeneous]

theorem basicWeightCoroots : basicWeightCoroots_type.{u} := by
  intro G _ _ _ B H φ θ i
  change (coordinates B (affineSimpleCoroot B H θ i : AffineAlgebra B)).1.2 = _
  rw [coe_affineSimpleCoroot]
  cases i with
  | none =>
    change (coordinates B (K B - homogeneous B 0 _)).1.2 = 1
    rw [map_sub, coordinates_K, coordinates_homogeneous]
    change (1 : ℂ) - 0 = 1
    exact sub_zero 1
  | some i =>
    change (coordinates B (homogeneous B 0 _)).1.2 = 0
    rw [coordinates_homogeneous]

/-- The bracket identity expressed on a left enveloping module. -/
private theorem act_commutator {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    {V : Type u} [AddCommGroup V] [Module (U L) V] (a b : L) (x : V) :
    ι ℂ a • (ι ℂ b • x) = ι ℂ b • (ι ℂ a • x) + ι ℂ ⁅a, b⁆ • x := by
  rw [← enveloping_commutator, sub_smul, mul_smul, mul_smul]
  abel

theorem basicRepresentationStrings : basicRepresentationStrings_type.{u} := by
  intro G _ _ _ _ B H _ φ D hB hφ χ hχ v hv hvne h hh
  let a : Carrier D := homogeneous B 1 h
  let b : Carrier D := homogeneous B (-1) h
  let t : Carrier D := d B
  let k : Carrier D := K B
  let c := B.form (h : G) (h : G)
  let w := fun n : ℕ => (ι ℂ b) ^ n • v
  change (∀ n, w n ≠ 0 ∧ ι ℂ t • w n = (-(n : ℂ)) • w n) ∧
    Function.Injective (fun n : ℕ => -(n : ℂ)) ∧ LinearIndependent ℂ w
  have hab : ⁅a, b⁆ = c • k := by
    change ⁅homogeneous B 1 h, homogeneous B (-1) h⁆ = c • K B
    rw [homogeneousBracket]
    simp [c]
  have htb : ⁅t, b⁆ = (-1 : ℂ) • b := by
    change ⁅d B, homogeneous B (-1) h⁆ = (-1 : ℂ) • homogeneous B (-1) h
    rw [degreeBracket]
    norm_num
  have hamem : a ∈ positive D := by
    change homogeneous B 1 h ∈ affinePositive B H φ
    exact homogeneous_mem_components B (by norm_num [sideDegrees])
  have hav : ι ℂ a • v = 0 := hv.2 ⟨a, hamem⟩
  have htv : ι ℂ t • v = 0 := by
    have hd := hv.1 ⟨t, (cartanD B H).property⟩
    change ι ℂ t • v = basicWeight B H (cartanD B H) • v at hd
    rw [(basicWeightCoordinates B H).2.1 _ rfl, zero_smul] at hd
    exact hd
  have hk (x : affineSimple D χ) : ι ℂ k • x = x := by
    have hx := (affineLevelAction B H φ D hB hφ _ χ hχ).2 x
    change ι ℂ k • x = basicWeight B H (centralCartanElement B H) • x at hx
    rwa [(basicWeightCoordinates B H).1, one_smul] at hx
  have hcomm (x : affineSimple D χ) :
      ι ℂ a • (ι ℂ b • x) = ι ℂ b • (ι ℂ a • x) + c • x := by
    rw [act_commutator, hab, map_smul, smul_assoc, hk]
  have hdegree (x : affineSimple D χ) :
      ι ℂ t • (ι ℂ b • x) = ι ℂ b • (ι ℂ t • x) + (-1 : ℂ) • (ι ℂ b • x) := by
    rw [act_commutator, htb, map_smul, smul_assoc]
  have hw0 : w 0 = v := by simp [w]
  have hwstep (n : ℕ) : w (n + 1) = ι ℂ b • w n := by
    exact (by rw [pow_succ', mul_smul] : (ι ℂ b) ^ (n + 1) • v = _)
  have hraise (n : ℕ) : ι ℂ a • w (n + 1) = (((n : ℂ) + 1) * c) • w n := by
    induction n with
    | zero => rw [hwstep, hw0, hcomm, hav]; simp
    | succ n ih =>
      rw [hwstep (n + 1), hcomm, ih, smul_comm (ι ℂ b), ← hwstep, ← add_smul]
      congr 1
      push_cast
      ring
  have hnz (n : ℕ) : w n ≠ 0 := by
    induction n with
    | zero => rwa [hw0]
    | succ n ih =>
      intro hzero
      have hs := hraise n
      rw [hzero, smul_zero, eq_comm] at hs
      exact ih ((smul_eq_zero.mp hs).resolve_left (mul_ne_zero (Nat.cast_add_one_ne_zero n) hh))
  have heig (n : ℕ) : ι ℂ t • w n = (-(n : ℂ)) • w n := by
    induction n with
    | zero => simpa only [hw0, Nat.cast_zero, neg_zero, zero_smul] using htv
    | succ n ih =>
      rw [hwstep, hdegree, ih, smul_comm (ι ℂ b), ← add_smul]
      congr 1
      push_cast
      ring
  have hinj : Function.Injective (fun n : ℕ => -(n : ℂ)) :=
    fun _ _ hn => Nat.cast_injective (neg_injective hn : (_ : ℂ) = _)
  refine ⟨fun n => ⟨hnz n, heig n⟩, hinj, ?_⟩
  let degree : Module.End ℂ (affineSimple D χ) := Algebra.lsmul ℂ ℂ _ (ι ℂ t)
  exact degree.eigenvectors_linearIndependent' _ hinj w
    (fun n => ⟨Module.End.mem_eigenspace_iff.mpr (heig n), hnz n⟩)

theorem basicRepresentation : basicRepresentation_type.{u} := by
  intro G _ _ _ _ B H _ φ D hB hφ
  refine ⟨affineVermaCharacter B H φ D hB hφ (basicWeight B H), ?_⟩
  intro χ hχ
  refine ⟨?_, ?_⟩
  · intro θ hθ T S
    apply (affineSimpleIntegrable B H φ D hB hφ θ hθ T S _ χ hχ).2
    intro i
    rw [basicWeightCoroots B H φ θ i]
    cases i with
    | none => exact ⟨1, by norm_num⟩
    | some i => exact ⟨0, by norm_num⟩
  · obtain ⟨_, hvne, hv, _⟩ :=
      affineSimpleHighestWeight B H φ D hB hφ _ χ hχ
    have := cartanNontrivial (G := G) H
    have hnd := cartanNondegenerate H B hB.1
    obtain ⟨h, hh⟩ : ∃ h : H, B.form (h : G) (h : G) ≠ 0 := by
      by_contra! hz
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      apply hx
      apply hnd.1 x
      intro y
      change B.form (x : G) (y : G) = 0
      rw [B.symmetric.polarization, ← Submodule.coe_add, hz, hz, hz]
      simp
    have hli := (basicRepresentationStrings B H φ D hB hφ χ hχ _ hv hvne h hh).2.2
    intro hfinite
    exact Module.Finite.not_linearIndependent_of_infinite _ hli

end RepTheorySurvey.Affine
