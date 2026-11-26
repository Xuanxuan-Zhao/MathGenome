import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.HermitianMatrixGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.HermitianMatrixGeneration

open Specs.HermitianMatrixGeneration Specs.UnitaryRankOne
open Matrix
open scoped Matrix
open private conj_conj conj_eq_iff trace_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {W : Type w} [AddCommGroup W] [Module E W]

local notation "σ" => quadraticConjugation F E

variable (h : HermitianForm (F := F) (E := E) (W := W) (quadraticConjugation F E))

@[local simp] private theorem pairing_add_right (x y z : W) :
    h.pairing x (y + z) = h.pairing x y + h.pairing x z :=
  (h.linear_second x).map_add _ _

@[local simp] private theorem pairing_smul_right (x y : W) (c : E) :
    h.pairing x (c • y) = c * h.pairing x y :=
  (h.linear_second x).map_smul _ _

@[local simp] private theorem pairing_zero_right (x : W) : h.pairing x 0 = 0 :=
  (h.linear_second x).map_zero

@[local simp] private theorem pairing_add_left (x y z : W) :
    h.pairing (x + y) z = h.pairing x z + h.pairing y z := by
  rw [← h.hermitian z (x + y), pairing_add_right, map_add, h.hermitian, h.hermitian]

@[local simp] private theorem pairing_smul_left (x y : W) (c : E) :
    h.pairing (c • x) y = σ c * h.pairing x y := by
  rw [← h.hermitian y (c • x), pairing_smul_right, map_mul, h.hermitian]

@[local simp] private theorem pairing_zero_left (x : W) : h.pairing 0 x = 0 := by
  rw [← h.hermitian x 0, pairing_zero_right, map_zero]

@[local simp] private theorem pairing_sub_right (x y z : W) :
    h.pairing x (y - z) = h.pairing x y - h.pairing x z :=
  (h.linear_second x).mk' _ |>.map_sub _ _

@[local simp] private theorem pairing_sub_left (x y z : W) :
    h.pairing (x - y) z = h.pairing x z - h.pairing y z := by
  rw [← h.hermitian z (x - y), pairing_sub_right, map_sub, h.hermitian, h.hermitian]

/-- The elementary shear for two vector space blocks. -/
private def shear {X Y : Type*} [AddCommGroup X] [Module E X]
    [AddCommGroup Y] [Module E Y] (f : Y →ₗ[E] X) : (X × Y) ≃ₗ[E] (X × Y) where
  toFun p := (p.1 + f p.2, p.2)
  invFun p := (p.1 - f p.2, p.2)
  left_inv := fun p => by simp
  right_inv := fun p => by simp
  map_add' := fun p r => by simp [add_add_add_comm]
  map_smul' := fun c p => by simp [smul_add]

@[local simp] private theorem shear_apply {X Y : Type*} [AddCommGroup X] [Module E X]
    [AddCommGroup Y] [Module E Y] (f : Y →ₗ[E] X) (p : X × Y) :
    shear f p = (p.1 + f p.2, p.2) := rfl

private theorem det_shear {X Y : Type*} [AddCommGroup X] [Module E X]
    [AddCommGroup Y] [Module E Y] [FiniteDimensional E X] [FiniteDimensional E Y]
    (f : Y →ₗ[E] X) : LinearEquiv.det (shear f) = 1 := by
  classical
  let b := Module.finBasis E X
  let c := Module.finBasis E Y
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c) (shear f).toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix c b f) 0 1 := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_one]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one]

private def upperEquiv (z : W) (b : E) : (Space E W) ≃ₗ[E] (Space E W) :=
  (shear ((-(h.linear z)).coprod (LinearMap.mulLeft E b))).trans
    ((LinearEquiv.refl E E).prodCongr (shear (LinearMap.toSpanSingleton E W z)))

@[local simp] private theorem upperEquiv_apply (z : W) (b : E) (p : (Space E W)) :
    upperEquiv h z b p = upperAction h z b p := by
  rcases p with ⟨x, w, y⟩
  simp [upperEquiv, upperAction, HermitianForm.linear, sub_eq_add_neg, add_assoc]

private def swapLines : (Space E W) ≃ₗ[E] (Space E W) where
  toFun p := (p.2.2, p.2.1, p.1)
  invFun p := (p.2.2, p.2.1, p.1)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private def lowerEquiv (z : W) (b : E) : (Space E W) ≃ₗ[E] (Space E W) :=
  ((swapLines.symm).trans (upperEquiv h z b)).trans swapLines

@[local simp] private theorem lowerEquiv_apply (z : W) (b : E) (p : (Space E W)) :
    lowerEquiv h z b p = lowerAction h z b p := by
  change ((upperEquiv h z b (p.2.2, p.2.1, p.1)).2.2,
    (upperEquiv h z b (p.2.2, p.2.1, p.1)).2.1,
    (upperEquiv h z b (p.2.2, p.2.1, p.1)).1) = _
  rw [upperEquiv_apply]
  rfl

private theorem upper_preserves (z : W) (b : E) (hb : b + σ b = -(h.pairing z z))
    (p r : (Space E W)) : hyperbolicPairing h (upperEquiv h z b p) (upperEquiv h z b r) = hyperbolicPairing h p r := by
  simp only [upperEquiv_apply, hyperbolicPairing, upperAction, map_add, map_sub, map_mul,
    pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right, h.hermitian]
  linear_combination (σ p.2.2 * r.2.2) * hb

private theorem swap_preserves (p r : (Space E W)) : hyperbolicPairing h (swapLines p) (swapLines r) = hyperbolicPairing h p r := by
  change σ p.2.2 * r.1 + h.pairing p.2.1 r.2.1 + σ p.1 * r.2.2 = _
  simp only [hyperbolicPairing]
  ring

variable [FiniteDimensional E W]

private theorem det_prodCongr {X Y : Type*} [AddCommGroup X] [Module E X]
    [AddCommGroup Y] [Module E Y] [FiniteDimensional E X] [FiniteDimensional E Y]
    (a : X ≃ₗ[E] X) (b : Y ≃ₗ[E] Y) :
    LinearEquiv.det (a.prodCongr b) = LinearEquiv.det a * LinearEquiv.det b := by
  apply Units.ext
  simp only [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, Units.val_mul]

private theorem det_upperEquiv (z : W) (b : E) : LinearEquiv.det (upperEquiv h z b) = 1 := by
  simp [upperEquiv, det_prodCongr, det_shear]

private theorem upper_mem_specialUnitary (z : W) (b : E)
    (hb : b + σ b = -(h.pairing z z)) : upperEquiv h z b ∈ specialUnitary h :=
  ⟨det_upperEquiv h z b, upper_preserves h z b hb⟩

private theorem lower_mem_specialUnitary (z : W) (b : E)
    (hb : b + σ b = -(h.pairing z z)) : lowerEquiv h z b ∈ specialUnitary h := by
  refine ⟨by simp [lowerEquiv, det_upperEquiv], ?_⟩
  intro p r
  change hyperbolicPairing h (swapLines (upperEquiv h z b (swapLines p)))
    (swapLines (upperEquiv h z b (swapLines r))) = hyperbolicPairing h p r
  rw [swap_preserves, upper_preserves h z b hb, swap_preserves]

omit [FiniteDimensional E W] in
private theorem upper_mem_closure (z : W) (b : E) (hb : b + σ b = -(h.pairing z z)) :
    upperEquiv h z b ∈ (Subgroup.closure (radicalGenerators h)) :=
  Subgroup.subset_closure ⟨z, b, hb, Or.inl (upperEquiv_apply h z b)⟩

omit [FiniteDimensional E W] in
private theorem lower_mem_closure (z : W) (b : E) (hb : b + σ b = -(h.pairing z z)) :
    lowerEquiv h z b ∈ (Subgroup.closure (radicalGenerators h)) :=
  Subgroup.subset_closure ⟨z, b, hb, Or.inr (lowerEquiv_apply h z b)⟩

theorem radicalClosure_le_specialUnitary :
    (Subgroup.closure (radicalGenerators h)) ≤ specialUnitary h := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨z, b, hb, hg | hg⟩
  · have eq : g = upperEquiv h z b :=
      LinearEquiv.ext fun p => (hg p).trans (upperEquiv_apply h z b p).symm
    rw [eq]
    exact upper_mem_specialUnitary h z b hb
  · have eq : g = lowerEquiv h z b :=
      LinearEquiv.ext fun p => (hg p).trans (lowerEquiv_apply h z b p).symm
    rw [eq]
    exact lower_mem_specialUnitary h z b hb


private def lineCoordinate (z : W) : W →ₗ[E] E :=
  (h.pairing z z)⁻¹ • h.linear z

omit [FiniteDimensional E W] in
@[local simp] private theorem lineCoordinate_apply (z w : W) :
    lineCoordinate h z w = h.pairing z w / h.pairing z z := by
  simp [lineCoordinate, HermitianForm.linear, div_eq_inv_mul]

omit [FiniteDimensional E W] in
private theorem lineCoordinate_self (z : W) (hz : h.pairing z z ≠ 0) :
    lineCoordinate h z z = 1 := by simp [hz]

/-- Split off a nonisotropic complementary line, keeping its perpendicular
space as a separate summand on which the rank-one group acts trivially. -/
private def rankOneCoordinates (z : W) (hz : h.pairing z z ≠ 0) :
    Space E W ≃ₗ[E] ((Fin 3 → E) × LinearMap.ker (lineCoordinate h z)) where
  toFun p := (![p.1, lineCoordinate h z p.2.1, p.2.2],
    ⟨p.2.1 - lineCoordinate h z p.2.1 • z, by
      change lineCoordinate h z (p.2.1 - lineCoordinate h z p.2.1 • z) = 0
      simp only [map_sub, map_smul, lineCoordinate_self h z hz, smul_eq_mul, mul_one, sub_self]⟩)
  invFun p := (p.1 0, p.2.val + p.1 1 • z, p.1 2)
  left_inv p := by simp
  right_inv p := by
    have hp : lineCoordinate h z p.2.val = 0 := p.2.property
    have hc : lineCoordinate h z (p.2.val + p.1 1 • z) = p.1 1 := by
      rw [map_add, hp, map_smul, lineCoordinate_self h z hz, smul_eq_mul, mul_one, zero_add]
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Fin.reduceFinMk, hc]
    · apply Subtype.ext
      dsimp only
      rw [hc, add_sub_cancel_right]
  map_add' p r := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Fin.reduceFinMk, add_div]
    · apply Subtype.ext
      change p.2.1 + r.2.1 - lineCoordinate h z (p.2.1 + r.2.1) • z =
        (p.2.1 - lineCoordinate h z p.2.1 • z) + (r.2.1 - lineCoordinate h z r.2.1 • z)
      rw [map_add, add_smul, add_sub_add_comm]
  map_smul' c p := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Fin.reduceFinMk]
    · apply Subtype.ext
      change c • p.2.1 - lineCoordinate h z (c • p.2.1) • z =
        c • (p.2.1 - lineCoordinate h z p.2.1 • z)
      rw [map_smul, smul_sub, smul_assoc]

private def rankOneEmbed (z : W) (hz : h.pairing z z ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 3) E →* (Space E W ≃ₗ[E] Space E W) where
  toFun g := ((rankOneCoordinates h z hz).trans
    ((Matrix.SpecialLinearGroup.toLin' g).prodCongr (LinearEquiv.refl E _))).trans
      (rankOneCoordinates h z hz).symm
  map_one' := by ext p <;> simp
  map_mul' g d := by
    apply LinearEquiv.ext
    intro p
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]

omit [FiniteDimensional E W] in
private theorem rankOneEmbed_apply (z : W) (hz : h.pairing z z ≠ 0)
    (g : Matrix.SpecialLinearGroup (Fin 3) E) (p : Space E W) :
    let c := lineCoordinate h z p.2.1
    let r := g.val *ᵥ ![p.1, c, p.2.2]
    rankOneEmbed h z hz g p = (r 0, (p.2.1 - c • z) + r 1 • z, r 2) := rfl

omit [FiniteDimensional E W] in
private theorem rankOne_middle (z w : W) (c d : E) :
    (w - c • z) + d • z = w + (d - c) • z := by
  rw [sub_smul]
  abel

private theorem rankOne_radical_mem (z : W) (hz : h.pairing z z ≠ 0)
    (g : Matrix.SpecialLinearGroup (Fin 3) E)
    (hg : g ∈ unitaryRadicalGenerators σ (h.pairing z z)) :
    rankOneEmbed h z hz g ∈ Subgroup.closure (radicalGenerators h) := by
  let q := h.pairing z z
  have hq : σ q = q := h.hermitian z z
  obtain ⟨a, b, hab, hg | hg⟩ := hg
  · let c := -(σ a) / q
    have hc : σ c = -a / q := by simp [c, hq, conj_conj]
    have hb : b + σ b = -(h.pairing (c • z) (c • z)) := by
      simp only [pairing_smul_left, pairing_smul_right, hc, c]
      change b + σ b = _ at hab ⊢
      rw [hab]
      field_simp [q, hz]
      ring
    apply Subgroup.subset_closure
    refine ⟨c • z, b, hb, Or.inl fun p => ?_⟩
    simp [rankOneEmbed_apply, hg, upper, mulVec, dotProduct, Fin.sum_univ_three,
      
      Matrix.of_apply, zero_mul, one_mul, add_zero, zero_add, rankOne_middle,
      upperAction, pairing_smul_left, hc, lineCoordinate_apply]
    constructor
    · dsimp only [q]
      ring
    · rw [smul_smul, mul_comm p.2.2]
  · let c := σ a / q
    have hc : σ c = a / q := by simp [c, hq, conj_conj]
    have hb : b + σ b = -(h.pairing (c • z) (c • z)) := by
      simp only [pairing_smul_left, pairing_smul_right, hc, c]
      change b + σ b = _ at hab ⊢
      rw [hab]
      field_simp [q, hz]
      ring
    apply Subgroup.subset_closure
    refine ⟨c • z, b, hb, Or.inr fun p => ?_⟩
    simp [rankOneEmbed_apply, hg, lower, mulVec, dotProduct, Fin.sum_univ_three,
      
      Matrix.of_apply, zero_mul, one_mul, add_zero, rankOne_middle,
      lowerAction, pairing_smul_left, hc, lineCoordinate_apply]
    constructor
    · rw [smul_smul, mul_comm p.1]
    · dsimp only [q]
      ring

private theorem rankOne_closure_mem (z : W) (hz : h.pairing z z ≠ 0)
    (g : Matrix.SpecialLinearGroup (Fin 3) E)
    (hg : g ∈ Subgroup.closure (unitaryRadicalGenerators σ (h.pairing z z))) :
    rankOneEmbed h z hz g ∈ Subgroup.closure (radicalGenerators h) := by
  have comap_le : Subgroup.closure (unitaryRadicalGenerators σ (h.pairing z z)) ≤
      (Subgroup.closure (radicalGenerators h)).comap (rankOneEmbed h z hz) :=
    (Subgroup.closure_le _).mpr (fun g hg => rankOne_radical_mem h z hz g hg)
  exact comap_le hg

omit [FiniteDimensional E W] in
variable [Infinite F] in
private theorem rankOne_words (z : W) (hz : h.pairing z z ≠ 0) :
    let q := h.pairing z z
    let K := Subgroup.closure (unitaryRadicalGenerators σ q)
    (∀ s : Eˣ, RepresentedIn (unitaryDiagonal σ (s : E)) K) ∧
      RepresentedIn (unitaryWeyl E) K ∧
      (∀ η : E, η * σ η = 1 → ∃ s : Eˣ, σ (s : E) / (s : E) = η) := by
  obtain ⟨a, ha⟩ := (conj_eq_iff (h.pairing z z)).mp (h.hermitian z z)
  have ha₀ : a ≠ 0 := by
    intro eq
    exact hz (by simpa [eq] using ha.symm)
  obtain ⟨_, hd, hw, hr⟩ := LinearAlgebraicGroups.Arithmetic.UnitaryRankOne.unitaryTorusAndWeylWords (E := E) (Units.mk0 a ha₀)
  change algebraMap F E (↑(Units.mk0 a ha₀) : F) = h.pairing z z at ha
  rw [ha] at hd hw
  exact ⟨fun s => (hd s).1, hw, hr⟩

variable [Infinite F] in
private theorem lifted_diagonal (z : W) (hz : h.pairing z z ≠ 0) (s : Eˣ) :
    ∃ g ∈ Subgroup.closure (radicalGenerators h), ∀ p : Space E W,
      g p = ((s : E) * p.1, h.reflectionAction z (σ (s : E) / (s : E)) p.2.1,
        (σ (s : E))⁻¹ * p.2.2) := by
  obtain ⟨g, hg, hval⟩ := (rankOne_words h z hz).1 s
  refine ⟨rankOneEmbed h z hz g, rankOne_closure_mem h z hz g hg, fun p => ?_⟩
  simp [rankOneEmbed_apply, hval, unitaryDiagonal, mulVec_diagonal,
    rankOne_middle,
    HermitianForm.reflectionAction, lineCoordinate_apply]
  rw [sub_mul, one_mul]

theorem rankOneDiagonalWords : RankOneDiagonalWords.{u,v,w} := by
  intro F E _ _ _ _ _ _ W _ _ _ h z hz s
  exact lifted_diagonal h z hz s

variable [Infinite F] in
private theorem lifted_weyl (z : W) (hz : h.pairing z z ≠ 0) :
    ∃ g ∈ Subgroup.closure (radicalGenerators h), ∀ p : Space E W,
      g p = (p.2.2, h.reflectionAction z (-1) p.2.1, p.1) := by
  obtain ⟨g, hg, hval⟩ := (rankOne_words h z hz).2.1
  refine ⟨rankOneEmbed h z hz g, rankOne_closure_mem h z hz g hg, fun p => ?_⟩
  simp [rankOneEmbed_apply, hval, unitaryWeyl, mulVec, dotProduct, Fin.sum_univ_three,
    
    Matrix.of_apply, zero_mul, one_mul, add_zero, zero_add,
    HermitianForm.reflectionAction, lineCoordinate_apply]
  rw [sub_mul, one_mul, neg_one_mul, sub_smul, neg_smul]
  abel


omit [FiniteDimensional E W] in
private theorem exists_nonisotropic [Nontrivial W] (hn : h.Nondegenerate) :
    ∃ z : W, h.pairing z z ≠ 0 := by
  by_contra! hnrm
  have hnonfixed : ∃ c : E, σ c ≠ c := by
    by_contra! hc
    exact quadraticConjugation_ne_one F E (AlgEquiv.ext hc)
  obtain ⟨c, hc⟩ := hnonfixed
  have hpolar (x y : W) : h.pairing x y + h.pairing y x = 0 := by
    simpa only [pairing_add_right, pairing_add_left, hnrm x, hnrm y, zero_add, add_zero, add_comm]
      using hnrm (x + y)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  apply hw
  apply hn
  intro z
  have h₁ := hpolar z w
  have h₂ : c * h.pairing z w + σ c * h.pairing w z = 0 := by
    simpa only [pairing_smul_right, pairing_smul_left] using hpolar z (c • w)
  have hm : (c - σ c) * h.pairing z w = 0 := by
    linear_combination h₂ - σ c * h₁
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hc.symm)

omit [FiniteDimensional E W] in
private theorem exists_admissible (z : W) : ∃ b : E, b + σ b = -(h.pairing z z) := by
  obtain ⟨a, ha⟩ := (conj_eq_iff (h.pairing z z)).mp (h.hermitian z z)
  have hdim := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdim ▸ Nat.zero_lt_succ 1)
  obtain ⟨b, hb⟩ := Algebra.trace_surjective (K := F) (L := E) (-a)
  refine ⟨b, ?_⟩
  rw [← trace_eq, hb, map_neg, ha]

omit [FiniteDimensional E W] in
private theorem upper_eliminate (x : E) (w : W) (y : E) (hy : y ≠ 0)
    (hi : hyperbolicPairing h (x, w, y) (x, w, y) = 0) :
    ∃ g ∈ Subgroup.closure (radicalGenerators h),
      g (x, w, y) = (0, 0, y) ∧ ∀ t : E, g (t, 0, 0) = (t, 0, 0) := by
  let z := -(y⁻¹) • w
  let b := σ (x / y)
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy
  change σ x * y + h.pairing w w + σ y * x = 0 at hi
  have hb : b + σ b = -(h.pairing z z) := by
    simp only [b, z, conj_conj, pairing_smul_left, pairing_smul_right,
      map_neg, map_inv₀, map_div₀]
    field_simp
    linear_combination hi
  refine ⟨upperEquiv h z b, upper_mem_closure h z b hb, ?_, ?_⟩
  · rw [upperEquiv_apply]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · change x - h.pairing z w + b * y = 0
      simp only [b, z, pairing_smul_left, map_neg, map_inv₀, map_div₀]
      field_simp
      linear_combination hi
    · change w + y • z = 0
      rw [show y • z = -w by simp [z, smul_smul, hy]]
      exact add_neg_cancel w
  · intro t
    simp [upperAction]

private def firstVector : Space E W := (1, 0, 0)
private def lastVector : Space E W := (0, 0, 1)

omit [FiniteDimensional E W] [Module E W] in
private theorem firstVector_ne_zero : (firstVector : Space E W) ≠ 0 := by
  intro eq
  exact one_ne_zero (congrArg Prod.fst eq)

variable [Infinite F] in
private theorem move_to_first_line (hn : h.Nondegenerate)
    (z : W) (hz : h.pairing z z ≠ 0)
    (p : Space E W) (hp : p ≠ 0) (hi : hyperbolicPairing h p p = 0) :
    ∃ g ∈ Subgroup.closure (radicalGenerators h), ∃ t : E, t ≠ 0 ∧ g p = (t, 0, 0) := by
  let H := Subgroup.closure (radicalGenerators h)
  obtain ⟨n, hnH, hnp⟩ := lifted_weyl h z hz
  have hmove (p : Space E W) (hy : p.2.2 ≠ 0) (hi : hyperbolicPairing h p p = 0) :
      ∃ g ∈ H, ∃ t : E, t ≠ 0 ∧ g p = (t, 0, 0) := by
    rcases p with ⟨x, w, y⟩
    obtain ⟨g, hg, hgp, _⟩ := upper_eliminate h x w y hy hi
    refine ⟨n * g, H.mul_mem hnH hg, y, hy, ?_⟩
    rw [LinearEquiv.mul_apply, hgp, hnp]
    simp [HermitianForm.reflectionAction]
  by_cases hy : p.2.2 = 0
  · by_cases hx : p.1 = 0
    · have hw : p.2.1 ≠ 0 := by
        rintro hw
        exact hp (Prod.ext hx (Prod.ext hw hy))
      obtain ⟨r, hr⟩ : ∃ r, h.pairing r p.2.1 ≠ 0 := by
        by_contra! hh
        exact hw (hn _ hh)
      obtain ⟨b, hb⟩ := exists_admissible h r
      let l := lowerEquiv h r b
      have hl := lower_mem_closure h r b hb
      have hlp : (l p).2.2 ≠ 0 := by
        simpa [l, lowerAction, hx, hy] using hr
      obtain ⟨g, hg, t, ht, he⟩ :=
        hmove (l p) hlp (((lower_mem_specialUnitary h r b hb).2 p p).trans hi)
      exact ⟨g * l, H.mul_mem hg hl, t, ht, he⟩
    · have hnp₃ : (n p).2.2 ≠ 0 := by rw [hnp]; exact hx
      obtain ⟨g, hg, t, ht, he⟩ :=
        hmove (n p) hnp₃ (((radicalClosure_le_specialUnitary h hnH).2 p p).trans hi)
      exact ⟨g * n, H.mul_mem hg hnH, t, ht, he⟩
  · exact hmove p hy hi

omit [FiniteDimensional E W] in
private theorem apply_blocks (g : Space E W ≃ₗ[E] Space E W) (x : E) (w : W) (y : E) :
    g (x, w, y) = x • g firstVector + g (0, w, 0) + y • g lastVector := by
  have heq : (x, w, y) = x • (firstVector : Space E W) + (0, w, 0) + y • lastVector := by
    simp [firstVector, lastVector]
  calc
    g (x, w, y) = g (x • firstVector + (0, w, 0) + y • lastVector) := congrArg g heq
    _ = _ := by rw [map_add, map_add, map_smul, map_smul]

omit [FiniteDimensional E W] in
private theorem upper_coordinates (g : Space E W ≃ₗ[E] Space E W)
    (hg : g ∈ specialUnitary h) (hu : UpperUnitriangular g) :
    ∃ (z : W) (b : E), b + σ b = -(h.pairing z z) ∧
      ∀ p, g p = upperAction h z b p := by
  obtain ⟨he, hmid, hy⟩ := hu
  let z := (g lastVector).2.1
  let b := (g lastVector).1
  have hf : g lastVector = (b, z, 1) := Prod.ext rfl (Prod.ext rfl hy)
  have hn := hg.2 lastVector lastVector
  rw [hf] at hn
  have hb : b + σ b = -(h.pairing z z) := by
    simp [hyperbolicPairing, lastVector] at hn
    linear_combination hn
  have hm (w : W) : g (0, w, 0) = (-(h.pairing z w), w, 0) := by
    have h₀ : g (0, w, 0) = ((g (0, w, 0)).1, w, 0) := Prod.ext rfl (hmid w)
    have hp := hg.2 lastVector (0, w, 0)
    rw [hf, h₀] at hp
    simp [hyperbolicPairing, lastVector] at hp
    apply Prod.ext _ (hmid w)
    linear_combination hp
  refine ⟨z, b, hb, ?_⟩
  rintro ⟨x, w, y⟩
  change g firstVector = firstVector at he
  rw [apply_blocks, he, hm, hf]
  simp [firstVector, upperAction, sub_eq_add_neg, mul_comm]

theorem unitriangularCoordinates : UnitriangularCoordinates.{u,v,w} := by
  intro F E _ _ _ _ _ W _ _ _ h g
  constructor
  · intro hg
    refine ⟨radicalClosure_le_specialUnitary h (Subgroup.subset_closure hg), ?_⟩
    obtain ⟨z, b, _, hu | hl⟩ := hg
    · exact Or.inl ⟨by simp [hu, upperAction], by simp [hu, upperAction],
        by simp [hu, upperAction]⟩
    · exact Or.inr ⟨by simp [hl, lowerAction], by simp [hl, lowerAction],
        by simp [hl, lowerAction]⟩
  · rintro ⟨hg, hu | hl⟩
    · obtain ⟨z, b, hb, he⟩ := upper_coordinates h g hg hu
      exact ⟨z, b, hb, Or.inl he⟩
    · let s : Space E W ≃ₗ[E] Space E W := swapLines
      let a := (s.symm.trans g).trans s
      have ha (p : Space E W) : a p = s (g (s p)) := rfl
      have haSU : a ∈ specialUnitary h := by
        refine ⟨(LinearEquiv.det_conj g s).trans hg.1, ?_⟩
        intro p r
        rw [ha, ha, swap_preserves, hg.2, swap_preserves]
      obtain ⟨hf, hw, he⟩ := hl
      have hau : UpperUnitriangular a := by
        refine ⟨?_, ?_, ?_⟩
        · change s (g (0, 0, 1)) = _
          rw [hf]
          rfl
        · intro w
          change ((g (0, w, 0)).2.1, (g (0, w, 0)).1) = (w, 0)
          exact congrArg Prod.swap (hw w)
        · exact he
      obtain ⟨z, b, hb, hza⟩ := upper_coordinates h a haSU hau
      refine ⟨z, b, hb, Or.inr fun p => ?_⟩
      have hp := congrArg s (hza (s p))
      exact hp

/-- The line-pair stabilizer acts by the conjugate-inverse scales on the
outer coordinates and by a linear automorphism on the central block. -/
private def levi (τ : E ≃ₐ[F] E) (t : Eˣ) (A : W ≃ₗ[E] W) : Space E W ≃ₗ[E] Space E W :=
  (Units.mulLeftLinearEquiv E E t).prodCongr
    (A.prodCongr (Units.mulLeftLinearEquiv E E (Units.map τ.toMonoidHom t)⁻¹))

omit [FiniteDimensional E W] in
@[local simp] private theorem levi_apply (t : Eˣ) (A : W ≃ₗ[E] W) (p : Space E W) :
    levi σ t A p = ((t : E) * p.1, A p.2.1, (σ (t : E))⁻¹ * p.2.2) := by
  change ((t : E) * p.1, A p.2.1, (↑((Units.map (σ).toMonoidHom t)⁻¹) : E) * p.2.2) = _
  rw [Units.val_inv_eq_inv_val]
  rfl

omit [FiniteDimensional E W] in
private theorem levi_mul (s t : Eˣ) (A B : W ≃ₗ[E] W) :
    levi σ (s * t) (A * B) = levi σ s A * levi σ t B := by
  apply LinearEquiv.ext
  intro p
  simp [mul_comm, mul_left_comm]

omit [FiniteDimensional E W] in
private theorem levi_one : levi σ (1 : Eˣ) (1 : W ≃ₗ[E] W) = 1 := by
  apply LinearEquiv.ext
  intro p
  simp

omit [FiniteDimensional E W] in
private theorem levi_inv (t : Eˣ) (A : W ≃ₗ[E] W) :
    (levi σ t A)⁻¹ = levi σ t⁻¹ A⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  rw [← levi_mul, inv_mul_cancel, inv_mul_cancel, levi_one]

private theorem levi_classify (g : Space E W ≃ₗ[E] Space E W)
    (hg : g ∈ specialUnitary h) (t r : E) (ht : t ≠ 0)
    (he : g firstVector = (t, 0, 0)) (hf : g lastVector = (0, 0, r)) :
    ∃ A ∈ h.unitaryGroup, g = levi σ (Units.mk0 t ht) A := by
  have hp := hg.2 firstVector lastVector
  rw [he, hf] at hp
  have hr : σ t * r = 1 := by
    simpa [hyperbolicPairing, firstVector, lastVector] using hp
  have hσt : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  have hr₀ : r ≠ 0 := right_ne_zero_of_mul (hr.trans_ne one_ne_zero)
  have hre : r = (σ t)⁻¹ := by
    apply mul_left_cancel₀ hσt
    simpa [hσt] using hr
  have hmid (w : W) : g (0, w, 0) = (0, (g (0, w, 0)).2.1, 0) := by
    have h₁ := hg.2 lastVector (0, w, 0)
    have h₂ := hg.2 firstVector (0, w, 0)
    rw [hf] at h₁
    rw [he] at h₂
    have h₁' : σ r * (g (0, w, 0)).1 = 0 := by
      simpa [hyperbolicPairing, lastVector] using h₁
    have h₂' : σ t * (g (0, w, 0)).2.2 = 0 := by
      simpa [hyperbolicPairing, firstVector] using h₂
    exact Prod.ext ((mul_eq_zero.mp h₁').resolve_left ((map_ne_zero σ).mpr hr₀))
      (Prod.ext rfl ((mul_eq_zero.mp h₂').resolve_left hσt))
  let L : W →ₗ[E] W :=
    (LinearMap.fst E W E).comp ((LinearMap.snd E E (W × E)).comp
      (g.toLinearMap.comp ((LinearMap.inr E E (W × E)).comp (LinearMap.inl E W E))))
  have hL (w : W) : g (0, w, 0) = (0, L w, 0) := hmid w
  have hinj : Function.Injective L := by
    intro x y hxy
    have hxy' : g (0, x, 0) = g (0, y, 0) := by rw [hL, hL, hxy]
    exact congrArg (fun p : Space E W => p.2.1) (g.injective hxy')
  let A := LinearEquiv.ofInjectiveEndo L hinj
  have hA (w : W) : g (0, w, 0) = (0, A w, 0) := hL w
  refine ⟨A, ?_, ?_⟩
  · intro x y
    have hp := hg.2 (0, x, 0) (0, y, 0)
    rw [hA, hA] at hp
    simpa [hyperbolicPairing] using hp
  · apply LinearEquiv.ext
    rintro ⟨x, w, y⟩
    rw [apply_blocks, he, hf, hA, levi_apply, hre]
    simp [smul_eq_mul, mul_comm]

private theorem det_levi_trivial (t : Eˣ) :
    (LinearEquiv.det (levi σ t (1 : W ≃ₗ[E] W)) : E) =
      (t : E) * (σ (t : E))⁻¹ := by
  rw [levi, det_prodCongr, det_prodCongr]
  simp [Units.val_inv_eq_inv_val, LinearEquiv.coe_det]

variable [Infinite F] in
private theorem levi_mem_closure
    (href : ∀ A ∈ h.unitaryGroup, A ∈ Subgroup.closure h.reflections)
    (z : W) (hz : h.pairing z z ≠ 0) (t : Eˣ) (A : W ≃ₗ[E] W)
    (hA : A ∈ h.unitaryGroup) (hlevi : levi σ t A ∈ specialUnitary h) :
    levi σ t A ∈ Subgroup.closure (radicalGenerators h) := by
  let H := Subgroup.closure (radicalGenerators h)
  have liftReflection (B : W ≃ₗ[E] W) (hB : B ∈ h.reflections) :
      ∃ s : Eˣ, levi σ s B ∈ H := by
    obtain ⟨c, η, hc, hη, he⟩ := hB
    obtain ⟨s, hs⟩ := (rankOne_words h c hc).2.2 η hη
    obtain ⟨g, hg, hgp⟩ := lifted_diagonal h c hc s
    have heq : g = levi σ s B := LinearEquiv.ext (by
      intro p
      rw [hgp, levi_apply, hs, he])
    exact ⟨s, heq ▸ hg⟩
  have liftLevi : ∃ s : Eˣ, levi σ s A ∈ H := by
    refine Subgroup.closure_induction (p := fun B _ => ∃ s : Eˣ, levi σ s B ∈ H)
      liftReflection ⟨1, by rw [levi_one]; exact H.one_mem⟩ ?_ ?_ (href A hA)
    · rintro B C _ _ ⟨s, hs⟩ ⟨r, hr⟩
      exact ⟨s * r, by rw [levi_mul]; exact H.mul_mem hs hr⟩
    · rintro B _ ⟨s, hs⟩
      exact ⟨s⁻¹, by rw [← levi_inv]; exact H.inv_mem hs⟩
  obtain ⟨s, hs⟩ := liftLevi
  let d := s⁻¹ * t
  have hprod : (levi σ s A)⁻¹ * levi σ t A =
      levi σ d (1 : W ≃ₗ[E] W) := by
    rw [levi_inv, ← levi_mul, inv_mul_cancel]
  have hscale : levi σ d (1 : W ≃ₗ[E] W) ∈ specialUnitary h := by
    rw [← hprod]
    exact (specialUnitary h).mul_mem
      ((specialUnitary h).inv_mem (radicalClosure_le_specialUnitary h hs)) hlevi
  have hdet : (d : E) * (σ (d : E))⁻¹ = 1 := by
    rw [← det_levi_trivial (F := F) (W := W), hscale.1, Units.val_one]
  have hσd : σ (d : E) ≠ 0 := (map_ne_zero σ).mpr d.ne_zero
  have hfixed : (d : E) = σ (d : E) := by
    have hd := (div_eq_iff hσd).mp (by simpa [div_eq_mul_inv] using hdet)
    simpa using hd
  obtain ⟨g, hg, hgp⟩ := lifted_diagonal h z hz d
  have hdiag : levi σ d (1 : W ≃ₗ[E] W) = g := by
    apply LinearEquiv.ext
    intro p
    rw [levi_apply, hgp, ← hfixed]
    simp [d.ne_zero, HermitianForm.reflectionAction]
  have hdH : levi σ d (1 : W ≃ₗ[E] W) ∈ H := hdiag.symm ▸ hg
  rw [← hprod] at hdH
  exact (H.mul_mem_cancel_left (H.inv_mem hs)).mp hdH

/-- Generation of the full special unitary point group from the two
unitriangular groups when the orthogonal complement is nonzero. -/
theorem hermitianMatrixGeneration :
    Generation.{u,v,w} := by
  intro F E _ _ _ _ _ _ W _ _ _ _ h hn href
  let H := Subgroup.closure (radicalGenerators h)
  apply le_antisymm (radicalClosure_le_specialUnitary h)
  intro g hg
  obtain ⟨z, hz⟩ := exists_nonisotropic h hn
  have he₀ : g firstVector ≠ 0 := by
    intro eq
    exact firstVector_ne_zero (g.injective (eq.trans (map_zero g).symm))
  have heiso : hyperbolicPairing h (g firstVector) (g firstVector) = 0 := by
    rw [hg.2]
    simp [firstVector, hyperbolicPairing]
  obtain ⟨a, ha, t, ht, he⟩ := move_to_first_line h hn z hz (g firstVector) he₀ heiso
  let k := a * g
  have hk : k ∈ specialUnitary h :=
    (specialUnitary h).mul_mem (radicalClosure_le_specialUnitary h ha) hg
  have hke : k firstVector = (t, 0, 0) := he
  have hpair := hk.2 firstVector lastVector
  rw [hke] at hpair
  have hy : (k lastVector).2.2 ≠ 0 := by
    have hm : quadraticConjugation F E t * (k lastVector).2.2 = 1 := by
      simpa [hyperbolicPairing, firstVector, lastVector] using hpair
    exact right_ne_zero_of_mul (hm.trans_ne one_ne_zero)
  have hfiso : hyperbolicPairing h (k lastVector) (k lastVector) = 0 := by
    rw [hk.2]
    simp [lastVector, hyperbolicPairing]
  obtain ⟨b, hb, hbf, hbe⟩ := upper_eliminate h (k lastVector).1 (k lastVector).2.1
    (k lastVector).2.2 hy hfiso
  have hbk : b * k ∈ specialUnitary h :=
    (specialUnitary h).mul_mem (radicalClosure_le_specialUnitary h hb) hk
  have hbe' : (b * k) firstVector = (t, 0, 0) := by
    rw [LinearEquiv.mul_apply, hke, hbe]
  have hbf' : (b * k) lastVector = (0, 0, (k lastVector).2.2) := hbf
  obtain ⟨A, hA, heq⟩ := levi_classify h (b * k) hbk t (k lastVector).2.2 ht hbe' hbf'
  have hlevi : b * k ∈ H := by
    rw [heq]
    exact levi_mem_closure h href z hz _ A hA (heq ▸ hbk)
  have hkH : k ∈ H := (H.mul_mem_cancel_left hb).mp hlevi
  exact (H.mul_mem_cancel_left ha).mp hkH

/-- The coordinate model applies to any prescribed normalized hyperbolic pair. -/
theorem hyperbolicCoordinates : HyperbolicCoordinates.{u,v,w} := by
  intro F E _ _ _ _ _ W _ _ h e f hee hff hef
  let P := h.hyperbolicComplement e f
  have hfe : h.pairing f e = 1 := by rw [← h.hermitian e f, hef, map_one]
  have orth (x : P) : h.pairing e x.val = 0 ∧ h.pairing f x.val = 0 := x.property
  have orth' (x : P) : h.pairing x.val e = 0 ∧ h.pairing x.val f = 0 := by
    rw [← h.hermitian e x.val, ← h.hermitian f x.val, (orth x).1, (orth x).2, map_zero]
    exact ⟨rfl, rfl⟩
  let residual (x : W) : P :=
    ⟨x - h.pairing f x • e - h.pairing e x • f, by
      change h.pairing e _ = 0 ∧ h.pairing f _ = 0
      simp [hee, hff, hef, hfe]⟩
  let c : Space E P ≃ₗ[E] W :=
    { toFun p := p.1 • e + p.2.1.val + p.2.2 • f
      invFun x := (h.pairing f x, residual x, h.pairing e x)
      left_inv p := by
        have hf : h.pairing f (p.1 • e + p.2.1.val + p.2.2 • f) = p.1 := by
          simp [hfe, hff, (orth p.2.1).2]
        have he : h.pairing e (p.1 • e + p.2.1.val + p.2.2 • f) = p.2.2 := by
          simp [hee, hef, (orth p.2.1).1]
        refine Prod.ext hf (Prod.ext (Subtype.ext ?_) he)
        dsimp only [residual]
        rw [hf, he]
        abel
      right_inv x := by
        dsimp only [residual]
        abel
      map_add' p r := by
        change (p.1 + r.1) • e + (p.2.1.val + r.2.1.val) + (p.2.2 + r.2.2) • f = _
        rw [add_smul, add_smul]
        abel
      map_smul' a p := by
        change (a * p.1) • e + a • p.2.1.val + (a * p.2.2) • f =
          a • (p.1 • e + p.2.1.val + p.2.2 • f)
        simp only [smul_add, smul_smul] }
  have hc (p : Space E P) : c p = p.1 • e + p.2.1.val + p.2.2 • f := rfl
  have hpair (p r : Space E P) :
      h.pairing (c p) (c r) = hyperbolicPairing (h.restrict P) p r := by
    rw [hc, hc]
    simp [hyperbolicPairing, HermitianForm.restrict, hee, hff, hef, hfe,
      (orth r.2.1).1, (orth r.2.1).2, (orth' p.2.1).1, (orth' p.2.1).2,
      mul_comm, add_comm, add_left_comm, add_assoc]
  refine ⟨?_, c, hc, hpair⟩
  intro hn x hx
  apply Subtype.ext
  change x.val = 0
  apply hn x.val
  intro y
  obtain ⟨p, rfl⟩ := c.surjective y
  have e₀ : c (0, x, 0) = x.val := by simp [hc]
  have hp := hpair p (0, x, 0)
  rw [e₀] at hp
  have hzero := hx p.2.1
  change (h.restrict P).pairing p.2.1 x = 0 at hzero
  simpa [hyperbolicPairing, hzero] using hp

theorem generationForHyperbolicPair : GenerationForHyperbolicPair.{u,v,w} := by
  intro F E _ _ _ _ _ _ W _ _ _ h e f hee hff hef
  dsimp only
  intro _ hn href
  let P := h.hyperbolicComplement e f
  let hP := h.restrict P
  obtain ⟨hnP, c, hc, hpair⟩ := hyperbolicCoordinates h e f hee hff hef
  have hgen := hermitianMatrixGeneration hP (hnP hn) href
  let φ : (Space E P ≃ₗ[E] Space E P) →* (W ≃ₗ[E] W) :=
    { toFun g := (c.symm.trans g).trans c
      map_one' := by
        apply LinearEquiv.ext
        intro x
        simp
      map_mul' g a := by
        apply LinearEquiv.ext
        intro x
        simp }
  have hφ (g : Space E P ≃ₗ[E] Space E P) (x : W) : φ g x = c (g (c.symm x)) := rfl
  have hdet (g : Space E P ≃ₗ[E] Space E P) : LinearEquiv.det (φ g) = LinearEquiv.det g :=
    LinearEquiv.det_conj g c
  have hsurj : Function.Surjective φ := by
    intro g
    refine ⟨(c.trans g).trans c.symm, ?_⟩
    apply LinearEquiv.ext
    intro x
    simp [hφ]
  have hmem (g : Space E P ≃ₗ[E] Space E P) :
      φ g ∈ h.unitaryGroup ⊓ LinearEquiv.det.ker ↔ g ∈ specialUnitary hP := by
    constructor
    · intro hg
      refine ⟨(hdet g).symm.trans hg.2, ?_⟩
      intro p r
      have hp := hg.1 (c p) (c r)
      simpa only [hφ, LinearEquiv.symm_apply_apply, hpair] using hp
    · intro hg
      refine ⟨?_, (hdet g).trans hg.1⟩
      intro x y
      have he : h.pairing (c (c.symm x)) (c (c.symm y)) =
          hyperbolicPairing hP (c.symm x) (c.symm y) := hpair _ _
      rw [c.apply_symm_apply, c.apply_symm_apply] at he
      rw [hφ, hφ, hpair]
      exact (hg.2 (c.symm x) (c.symm y)).trans he.symm
  refine ⟨c, hc, ?_⟩
  change Subgroup.closure (φ '' radicalGenerators hP) = _
  rw [← MonoidHom.map_closure, hgen]
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hmem a).2 ha
  · intro hg
    obtain ⟨a, rfl⟩ := hsurj g
    exact ⟨a, (hmem a).1 hg, rfl⟩

end LinearAlgebraicGroups.Arithmetic.HermitianMatrixGeneration
