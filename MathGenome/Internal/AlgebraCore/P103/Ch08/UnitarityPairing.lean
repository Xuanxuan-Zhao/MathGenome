import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.UnitarityPairing
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section
universe u v w
namespace P103.Ch08

def functionPairing : UnitaritySpecs.functionPairingType :=
  @UnitaritySpecs.functionPairingValue

namespace PositiveHermitianForm

/-- The ordinary coordinate form, including on the zero-dimensional space. -/
def coordinate (ι : Type*) [Fintype ι] : PositiveHermitianForm (ι → ℂ) where
  toFun x y := ∑ i, x i * star (y i)
  add_left x y z := by simp [add_mul, Finset.sum_add_distrib]
  smul_left c x y := by simp [mul_assoc, Finset.mul_sum]
  conj_symm x y := by simp [star_sum, mul_comm]
  nonneg x := by
    simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  positive x hx := by
    simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    have hi : ∃ i, x i ≠ 0 := by
      by_contra hi
      apply hx
      ext i
      simpa using (not_exists.mp hi i)
    obtain ⟨i, hi⟩ := hi
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _,
      Complex.normSq_pos.mpr hi⟩

def comap {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (h : PositiveHermitianForm W)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) : PositiveHermitianForm V where
  toFun x y := h.toFun (f x) (f y)
  add_left x y z := by simp [h.add_left]
  smul_left c x y := by simp [h.smul_left]
  conj_symm x y := h.conj_symm _ _
  nonneg x := h.nonneg _
  positive x hx := h.positive _ (fun hfx => hx (hf (by simpa using hfx)))

/-- Multiplication by a strictly positive real number preserves positivity. -/
def scale {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : PositiveHermitianForm V) (c : ℝ) (hc : 0 < c) : PositiveHermitianForm V where
  toFun x y := (c : ℂ) * h.toFun x y
  add_left x y z := by rw [h.add_left, mul_add]
  smul_left a x y := by rw [h.smul_left]; ring
  conj_symm x y := by simp [h.conj_symm]
  nonneg x := by simpa using mul_nonneg hc.le (h.nonneg x)
  positive x hx := by simpa using mul_pos hc (h.positive x hx)

/-- Averaging a form requires no preassigned norm or topology on V. -/
def average {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (h : PositiveHermitianForm V)
    (ρ : Representation ℂ G V) : PositiveHermitianForm V where
  toFun x y := ∑ g : G, h.toFun (ρ g x) (ρ g y)
  add_left x y z := by simp [h.add_left, Finset.sum_add_distrib]
  smul_left c x y := by simp [h.smul_left, Finset.mul_sum]
  conj_symm x y := by simp [star_sum, h.conj_symm]
  nonneg x := by
    simp only [Complex.re_sum]
    exact Finset.sum_nonneg fun g _ => h.nonneg _
  positive x hx := by
    simp only [Complex.re_sum]
    apply Finset.sum_pos' (fun g _ => h.nonneg _)
    exact ⟨1, Finset.mem_univ _, by simpa using h.positive x hx⟩

theorem average_invariant {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (h : PositiveHermitianForm V)
    (ρ : Representation ℂ G V) (g : G) (x y : V) :
    (h.average ρ).toFun (ρ g x) (ρ g y) = (h.average ρ).toFun x y := by
  change (∑ a : G, h.toFun (ρ a (ρ g x)) (ρ a (ρ g y))) = _
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

theorem add_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : PositiveHermitianForm V) (x y z : V) :
    h.toFun x (y + z) = h.toFun x y + h.toFun x z := by
  rw [← h.conj_symm x (y + z), h.add_left, star_add, h.conj_symm, h.conj_symm]

theorem smul_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : PositiveHermitianForm V) (c : ℂ) (x y : V) :
    h.toFun x (c • y) = star c * h.toFun x y := by
  rw [← h.conj_symm x (c • y), h.smul_left, star_mul, h.conj_symm]
  exact mul_comm _ _

/-- Reverse the arguments to match Mathlib's second-variable linear convention. -/
@[instance_reducible] def core {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : PositiveHermitianForm V) : InnerProductSpace.Core ℂ V where
  inner x y := h.toFun y x
  conj_inner_symm x y := h.conj_symm y x
  re_inner_nonneg := h.nonneg
  add_left x y z := h.add_right z x y
  smul_left x y c := h.smul_right c y x
  definite x hx := by
    by_contra hn
    have hp := h.positive x hn
    rw [hx] at hp
    simp at hp

end PositiveHermitianForm

theorem existsInvariantHermitian : UnitaritySpecs.existsInvariantHermitianType := by
  intro G _ _ V _ _ _ ρ
  let e := (Module.finBasis ℂ V).equivFun
  let h := (PositiveHermitianForm.coordinate (Fin (Module.finrank ℂ V))).comap
    e.toLinearMap e.injective
  exact ⟨h.average ρ, h.average_invariant ρ⟩

theorem functionPairing_positive : UnitaritySpecs.functionPairingPositiveType := by
  intro G _ _
  let h := (PositiveHermitianForm.coordinate G).scale (Fintype.card G : ℝ)⁻¹ (by positivity)
  refine ⟨h, ?_⟩
  ext f k
  simp [h, PositiveHermitianForm.scale, PositiveHermitianForm.coordinate,
    UnitaritySpecs.functionPairingValue]

/-- An invariant form identifies the inverse operator with the adjoint; taking
its trace in an orthonormal basis gives complex conjugation. -/
theorem character_inverse_conjugate : UnitaritySpecs.characterInverseConjugateType := by
  intro G _ _ V _ _ _ ρ g
  obtain ⟨h, hinv⟩ := existsInvariantHermitian ρ
  letI : InnerProductSpace.Core ℂ V := h.core
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  let b := stdOrthonormalBasis ℂ V
  change LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g))
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  change h.toFun (ρ g⁻¹ (b i)) (b i) = star (h.toFun (ρ g (b i)) (b i))
  rw [h.conj_symm]
  have hh := hinv g (ρ g⁻¹ (b i)) (b i)
  simpa using hh.symm

private theorem characterPairing_left {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue σ) = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) := by
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have ht := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ
  unfold UnitaritySpecs.functionPairingValue
  simp_rw [← character_inverse_conjugate σ]
  simpa only [Fintype.card_eq_nat_card, Representation.character,
    CharacterSpecs.characterValue] using ht

private theorem functionPairing_conj_symm {G : Type*} [Fintype G] (f h : G → ℂ) :
    star (UnitaritySpecs.functionPairingValue h f) =
      UnitaritySpecs.functionPairingValue f h := by
  simp [UnitaritySpecs.functionPairingValue, star_sum, mul_comm]

theorem character_pairing : UnitaritySpecs.characterPairingType := by
  intro G _ _ V _ _ _ W _ _ _ ρ σ
  have h₁ := characterPairing_left ρ σ
  have h₂ := characterPairing_left σ ρ
  refine ⟨h₁, ?_⟩
  have hs := functionPairing_conj_symm (CharacterSpecs.characterValue σ)
    (CharacterSpecs.characterValue ρ)
  rw [h₁, h₂] at hs
  simpa using hs

end P103.Ch08
