import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
import Mathlib.RingTheory.TensorProduct.Maps
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.Tactic.Module

/-!
# Quaternionic isotropy for nontrialitarian spin groups

Quaternionic line congruence and the local quadratic bound yield isotropic
projectors. Inverse scaling on adjoint projectors lifts through the spin cover
and rules out isotropic models for compact real factors.
-/

universe u v

namespace LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy

open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinIsotropy
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (SkewHermitianPairing)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (Involution antiValue)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels (quaternionConjugate)
open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision degree)
open LocalQuadraticSplitting (local_division_unique real_division)
open MulOpposite

open private quaternion_central quaternion_norm_formula from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
open private quaternion_isUnit_of_norm_ne_zero from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

noncomputable section

private def conjugationLinear {F : Type u} {B : Type v} [Field F] [Ring B] [Algebra F B]
    (s : Involution F B) : B →ₗ[F] B :=
  (MulOpposite.opLinearEquiv F).symm.toLinearMap.comp s.anti.toLinearMap

section Pure

variable {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
variable {hB : isCentralSimple F B} (s : Involution F B) (hs : IsCanonical hB s)

private theorem two_ne_zero_coeff (h₂ : (2 : F) ≠ 0) : (2 : B) ≠ 0 := by
  intro h
  apply h₂
  apply (algebraMap F B).injective
  simpa only [map_ofNat, map_zero] using h

private theorem conjugate_scalar (r : F) :
    antiValue s.anti (algebraMap F B r) = algebraMap F B r := by
  rw [antiValue, s.anti.commutes]
  rfl

private theorem conjugate_mul (x y : B) :
    antiValue s.anti (x * y) = antiValue s.anti y * antiValue s.anti x := by
  simp [antiValue]

private theorem conjugate_add (x y : B) :
    antiValue s.anti (x + y) = antiValue s.anti x + antiValue s.anti y :=
  (conjugationLinear s).map_add x y

private theorem conjugate_smul (r : F) (x : B) :
    antiValue s.anti (r • x) = r • antiValue s.anti x :=
  (conjugationLinear s).map_smul r x

include hs in
private theorem fixed_is_scalar (h₂ : (2 : F) ≠ 0)
    {x : B} (hx : antiValue s.anti x = x) : ∃ c : F, x = algebraMap F B c := by
  have ht := hs x
  rw [hx, quaternionConjugate, eq_sub_iff_add_eq] at ht
  refine ⟨LocalDivisionNormTraceReduction.reducedTrace hB x / 2, ?_⟩
  have h₂' : algebraMap F B 2 ≠ 0 := fun hz =>
    h₂ ((algebraMap F B).injective (hz.trans (map_zero _).symm))
  apply mul_left_cancel₀ h₂'
  rw [← map_mul, mul_comm 2, div_mul_cancel₀ _ h₂, ← ht, map_ofNat, two_mul]

private theorem pure_ne_scalar (h₂ : (2 : F) ≠ 0)
    {q : B} (hq : q ≠ 0) (hp : antiValue s.anti q = -q) (r : F) :
    q ≠ algebraMap F B r := by
  intro hr
  have he : q = -q := by
    have h := conjugate_scalar s r
    rwa [← hr, hp, eq_comm] at h
  have h0 : (2 : B) * q = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp he
  exact hq ((mul_eq_zero.mp h0).resolve_left (two_ne_zero_coeff h₂))

include hs

private theorem pure_square (h₂ : (2 : F) ≠ 0)
    {q : B} (hq : q ≠ 0) (hp : antiValue s.anti q = -q) :
    ∃ d : F, q * q = algebraMap F B d ∧ ¬ IsSquare d := by
  obtain ⟨d, hd⟩ := fixed_is_scalar s hs h₂ (x := q * q) (by
    rw [conjugate_mul, hp, neg_mul_neg])
  refine ⟨d, hd, ?_⟩
  rintro ⟨r, hr⟩
  have he : (q - algebraMap F B r) * (q + algebraMap F B r) = 0 := by
    rw [sub_mul, mul_add, mul_add, hd, hr, map_mul, Algebra.commutes r q]
    abel
  rcases mul_eq_zero.mp he with hl | hr'
  · exact pure_ne_scalar s h₂ hq hp r (sub_eq_zero.mp hl)
  · exact pure_ne_scalar s h₂ hq hp (-r)
      ((eq_neg_of_add_eq_zero_left hr').trans (map_neg _ _).symm)

private theorem canonical_commutes (x : B) : Commute x (antiValue s.anti x) := by
  rw [hs, quaternionConjugate]
  have hc : Commute (algebraMap F B (LocalDivisionNormTraceReduction.reducedTrace hB x)) x :=
    Algebra.commutes _ _
  exact hc.symm.sub_right (Commute.refl x)

private theorem anticommuting_square_scalar_is_pure (h₂ : (2 : F) ≠ 0)
    {q z : B} (hq : q ≠ 0) (hz : z ≠ 0)
    (hanti : z * q = -(q * z)) {t : F} (hzsq : z * z = algebraMap F B t) :
    antiValue s.anti z = -z := by
  let w := antiValue s.anti z
  have hw : w * w = z * z := by
    change antiValue s.anti z * antiValue s.anti z = _
    rw [← conjugate_mul, hzsq, conjugate_scalar]
  have he : (w - z) * (w + z) = 0 := by
    rw [sub_mul, mul_add, mul_add, hw, (canonical_commutes s hs z).eq]
    abel
  rcases mul_eq_zero.mp he with hl | hr
  · obtain ⟨r, hzr⟩ := fixed_is_scalar s hs h₂ (sub_eq_zero.mp hl)
    have hc : z * q = q * z := by rw [hzr]; exact Algebra.commutes _ _
    have h0 : (2 : B) * (q * z) = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp (hc.symm.trans hanti)
    exact False.elim ((mul_ne_zero (two_ne_zero_coeff h₂) (mul_ne_zero hq hz)) h0)
  · exact eq_neg_of_add_eq_zero_left hr

omit hs

/-- A parameter outside the quadratic norm group gives a division algebra
in the cyclic quaternion presentation. -/
private theorem cyclic_units {d t : F} (hd : ¬ IsSquare d)
    (hn : ¬ ∃ x y : F, x * x - d * (y * y) = t)
    (z : QuaternionAlgebra F d 0 t) : IsUnit z ∨ z = 0 := by
  let : Fact (¬ IsSquare d) := ⟨hd⟩
  let E := QuadraticAlgebra F d 0
  let a : E := ⟨z.re, z.imI⟩
  let b : E := ⟨z.imJ, z.imK⟩
  have value (x : E) : QuadraticAlgebra.norm x = x.re * x.re - d * (x.im * x.im) := by
    simp [QuadraticAlgebra.norm_def]
    ring
  by_cases hzero : (z * star z).re = 0
  · have hnorm : QuadraticAlgebra.norm a = t * QuadraticAlgebra.norm b := by
      rw [quaternion_norm_formula] at hzero
      rw [value, value]
      simp only [a, b]
      dsimp [LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy.pureNorm] at hzero
      linear_combination hzero
    by_cases hb : b = 0
    · have ha : a = 0 := QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (by simpa [hb] using hnorm)
      right
      exact QuaternionAlgebra.ext (congrArg QuadraticAlgebra.re ha) (congrArg QuadraticAlgebra.im ha)
        (congrArg QuadraticAlgebra.re hb) (congrArg QuadraticAlgebra.im hb)
    · let x : E := a / b
      have he : QuadraticAlgebra.norm x = t := by
        change QuadraticAlgebra.norm (a / b) = t
        apply mul_right_cancel₀ (fun h => hb (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h))
        rw [← map_mul, div_mul_cancel₀ _ hb, hnorm]
      exact False.elim (hn ⟨x.re, x.im, (value x).symm.trans he⟩)
  · exact Or.inl (quaternion_isUnit_of_norm_ne_zero hzero)

include hs

/-- Uniqueness of the division quaternion algebra gives the pure-line
congruence by comparing cyclic algebras for the nonnorm scalars. -/
private theorem pureLine_of_unique (h₂ : (2 : F) ≠ 0)
    (unique : ∀ (D : Type u) [DivisionRing D] [Algebra F D],
      isCentralDivision F D → degree F D = 2 → Nonempty (D ≃ₐ[F] B)) :
    PureLine s := by
  intro q hq hp t ht
  obtain ⟨d, hdq, hd⟩ := pure_square s hs h₂ hq hp
  by_cases hn : ∃ x y : F, x * x - d * (y * y) = t
  · obtain ⟨x, y, hxy⟩ := hn
    let a : B := x • (1 : B) + y • q
    have ha : antiValue s.anti a = x • (1 : B) - y • q := by
      dsimp [a]
      rw [conjugate_add, conjugate_smul, conjugate_smul, hp, smul_neg, ← sub_eq_add_neg]
      simp [antiValue]
    have hprod : antiValue s.anti a * a = algebraMap F B t := by
      rw [ha, Algebra.algebraMap_eq_smul_one, ← hxy]
      dsimp [a]
      simp only [sub_mul, mul_add, smul_mul_smul, mul_one, one_mul, hdq,
        Algebra.algebraMap_eq_smul_one, smul_smul, sub_smul]
      rw [mul_comm y x, mul_comm (y * y) d]
      abel
    have hne : a ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hprod
      exact ht ((algebraMap F B).injective (hprod.symm.trans (map_zero _).symm))
    refine ⟨Units.mk0 a hne, ?_⟩
    have hc : Commute q a := by
      change q * (x • (1 : B) + y • q) = (x • (1 : B) + y • q) * q
      simp [mul_add, add_mul]
    change antiValue s.anti a * q * a = _
    rw [mul_assoc, hc.eq, ← mul_assoc, hprod, Algebra.smul_def]
  · let D := QuaternionAlgebra F d 0 t
    let : DivisionRing D := DivisionRing.ofIsUnitOrEqZero (cyclic_units hd hn)
    have hd0 : d ≠ 0 := fun h => hd ⟨0, by simp [h]⟩
    have hD : isCentralDivision F D := ⟨quaternion_central h₂ hd0, inferInstance⟩
    have hdeg : degree F D = 2 := by
      change Nat.sqrt (Module.finrank F (QuaternionAlgebra F d 0 t)) = 2
      rw [QuaternionAlgebra.finrank_eq_four]
      exact Nat.sqrt_eq' 2
    obtain ⟨e⟩ := unique D hD hdeg
    let i : D := ⟨0, 1, 0, 0⟩
    let j : D := ⟨0, 0, 1, 0⟩
    let p := e i
    let z := e j
    have hi : i * i = algebraMap F D d := by ext <;> simp [i, D, QuaternionAlgebra.algebraMap_eq]
    have hj : j * j = algebraMap F D t := by ext <;> simp [j, D, QuaternionAlgebra.algebraMap_eq]
    have hij : j * i = -(i * j) := by ext <;> simp [i, j, D]
    have hpq : p * p = q * q := by
      change e i * e i = q * q
      rw [hdq, ← e.commutes, ← map_mul, hi]
    have hz : z ≠ 0 := by
      intro hz
      exact one_ne_zero (congrArg QuaternionAlgebra.imJ (e.injective (hz.trans (map_zero e).symm)))
    have hzz : z * z = algebraMap F B t := by
      change e j * e j = _
      rw [← e.commutes, ← map_mul, hj]
    have hzp : z * p = -(p * z) := by
      change e j * e i = -(e i * e j)
      rw [← map_mul, hij, map_neg, map_mul]
    obtain ⟨w, hw, hwp⟩ : ∃ w : B, w ≠ 0 ∧ w * p = q * w := by
      by_cases hsum : q + p = 0
      · refine ⟨z, hz, ?_⟩
        rw [eq_neg_of_add_eq_zero_left hsum, neg_mul, hzp]
      · refine ⟨q + p, hsum, ?_⟩
        rw [add_mul, mul_add, hpq, add_comm]
    have hwcomm : w * p * w⁻¹ = q := by
      rw [hwp, mul_assoc, mul_inv_cancel₀ hw, mul_one]
    let f : B →+* B :=
      { toFun := fun x => w * x * w⁻¹
        map_zero' := by simp
        map_one' := by simp [hw]
        map_add' := by intro x y; rw [mul_add, add_mul]
        map_mul' := by
          intro x y
          calc
            w * (x * y) * w⁻¹ = (w * x) * (w⁻¹ * w) * y * w⁻¹ := by
              rw [inv_mul_cancel₀ hw, mul_one, mul_assoc w x y]
            _ = (w * x * w⁻¹) * (w * y * w⁻¹) := by simp only [mul_assoc] }
    have hf (x : B) : f x = w * x * w⁻¹ := rfl
    let b := f z
    have hfp : f p = q := hwcomm
    have hbsq : b * b = algebraMap F B t := by
      change f z * f z = _
      rw [← map_mul, hzz, hf, ← Algebra.commutes t w, mul_assoc, mul_inv_cancel₀ hw, mul_one]
    have hb : b ≠ 0 := by
      intro hb
      rw [hb, zero_mul] at hbsq
      exact ht ((algebraMap F B).injective (hbsq.symm.trans (map_zero _).symm))
    have hanti : b * q = -(q * b) := by
      change f z * q = -(q * f z)
      rw [← hfp, ← map_mul, hzp, map_neg, map_mul]
    refine ⟨Units.mk0 b hb, ?_⟩
    change antiValue s.anti b * q * b = t • q
    rw [anticommuting_square_scalar_is_pure s hs h₂ hq hb hanti hbsq,
      neg_mul, hanti, neg_neg, mul_assoc, hbsq, ← Algebra.commutes, Algebra.smul_def]

end Pure

/-- Every nonzero scalar multiple of a pure quaternion is realized by congruence. -/
theorem pureLines : LocalPureLines.{u,v} := by
  constructor
  · intro F _ _ _ _ h₂ B _ _ hB hd s hs
    exact pureLine_of_unique s hs h₂ fun D _ _ hD hdD =>
      local_division_unique hD hdD hB.2 hd
  · intro B _ _ hB hd s hs
    apply pureLine_of_unique s hs (by norm_num)
    intro D _ _ hD hdD
    obtain ⟨⟨f⟩, _⟩ := real_division hD hdD
    obtain ⟨⟨g⟩, _⟩ := real_division hB.2 hd
    exact ⟨f.trans g.symm⟩

section Skew

variable {F : Type u} {B V : Type v} [Field F] [DivisionRing B] [Algebra F B]
variable [AddCommGroup V] [Module Bᵐᵒᵖ V]
variable {s : Involution F B} (h : SkewHermitianPairing (V := V) s)

private def rightValue (x : V) : V →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun y := op (h.value x y)
  map_add' y z := congrArg op (h.add_right x y z)
  map_smul' a y := congrArg op (h.smul_right x y (unop a))

private theorem value_right_sum {ι : Type*} [Fintype ι] (x : V) (y : ι → V) :
    h.value x (∑ i, y i) = ∑ i, h.value x (y i) := by
  let f : V →+ B :=
    MulOpposite.opAddEquiv.symm.toAddMonoidHom.comp (rightValue h x).toAddMonoidHom
  exact map_sum f y Finset.univ

private theorem value_left_sum {ι : Type*} [Fintype ι] (x : ι → V) (y : V) :
    h.value (∑ i, x i) y = ∑ i, h.value (x i) y := by
  simp_rw [h.skew y, value_right_sum]
  change -(conjugationLinear s) (∑ i, h.value y (x i)) =
    ∑ i, -(conjugationLinear s) (h.value y (x i))
  rw [map_sum, Finset.sum_neg_distrib]

private theorem value_left_smul (a : B) (x y : V) :
    h.value (op a • x) y = antiValue s.anti a * h.value x y := by
  rw [h.skew y, h.smul_right, conjugate_mul, ← mul_neg, ← h.skew y x]

private theorem exists_orthogonal_family (n : ℕ) (hn : n ≤ Module.finrank Bᵐᵒᵖ V) :
    ∃ e : Fin n → V, (∀ i, e i ≠ 0) ∧ Pairwise (fun i j => h.value (e i) (e j) = 0) := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨e, he, heo⟩ := ih (Nat.le_of_succ_le hn)
    let f : V →ₗ[Bᵐᵒᵖ] (Fin n → Bᵐᵒᵖ) := LinearMap.pi fun i => rightValue h (e i)
    have hker : f.ker ≠ ⊥ := by
      intro hbot
      have hr := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hbot)
      simp at hr
      omega
    obtain ⟨z, hz, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have horth (i : Fin n) : h.value (e i) z = 0 :=
      op_injective (congrFun (LinearMap.mem_ker.mp hz) i)
    refine ⟨Fin.snoc e z, Fin.lastCases (by simpa using hne) (fun i => by simpa using he i), ?_⟩
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases (fun hj => (hj rfl).elim) (fun j _ => ?_) j
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [h.skew, horth]
      change -(conjugationLinear s) 0 = 0
      simp
    · refine Fin.lastCases (fun _ => by simpa using horth i) (fun j hij => ?_) j
      simp only [Fin.snoc_castSucc]
      exact heo (fun hEq => hij (congrArg Fin.castSucc hEq))

private theorem skew_isotropy_of_pureLine {hB : isCentralSimple F B}
    (hd : degree F B = 2) (h₂ : (2 : F) ≠ 0)
    (hline : PureLine s) (hr : 4 ≤ Module.finrank Bᵐᵒᵖ V) :
    ∃ x : V, x ≠ 0 ∧ h.value x x = 0 := by
  classical
  by_contra! anisotropic
  obtain ⟨e, he, horth⟩ := exists_orthogonal_family h 4 hr
  let q : Fin 4 → B := fun i => h.value (e i) (e i)
  have hq (i : Fin 4) : q i ≠ 0 := anisotropic _ (he i)
  have hp (i : Fin 4) : antiValue s.anti (q i) = -q i := by
    have hi := h.skew (e i) (e i)
    exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans (eq_neg_iff_add_eq_zero.mp hi))
  let p : Submodule F B := (conjugationLinear s + LinearMap.id).ker
  let qp : Fin 4 → p := fun i => ⟨q i, by
    change antiValue s.anti (q i) + q i = 0
    rw [hp, neg_add_cancel]⟩
  let : FiniteDimensional F B := hB.2.2
  have hproper : p ≠ ⊤ := by
    intro ht
    have h1 : (1 : B) ∈ p := ht ▸ Submodule.mem_top
    change antiValue s.anti (1 : B) + 1 = 0 at h1
    exact two_ne_zero_coeff h₂ (by simpa [antiValue, one_add_one_eq_two] using h1)
  have hdB : Module.finrank F B = 4 := by
    have h := RM03.CSA.finrank_eq_degree_sq hB
    change Module.finrank F B = (degree F B) ^ 2 at h
    simpa [hd] using h
  have hdim := Submodule.finrank_lt hproper
  rw [hdB] at hdim
  have hdep : ¬ LinearIndependent F qp := by
    intro hi
    have hle := hi.fintype_card_le_finrank
    rw [Fintype.card_fin] at hle
    omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hcB : ∑ j, c j • q j = 0 := by
    simpa [qp] using congrArg p.subtype hc
  have represent (j : Fin 4) :
      ∃ a : B, antiValue s.anti a * q j * a = c j • q j := by
    by_cases hcj : c j = 0
    · exact ⟨0, by simp [hcj]⟩
    · obtain ⟨a, ha⟩ := hline (q j) (hq j) (hp j) (c j) hcj
      exact ⟨a, ha⟩
  choose a ha using represent
  let x : V := ∑ j, op (a j) • e j
  have hx (j : Fin 4) : h.value (e j) x = q j * a j := by
    dsimp [x]
    rw [value_right_sum]
    simp only [h.smul_right]
    exact Finset.sum_eq_single j (fun l _ hlj => by rw [horth hlj.symm, zero_mul]) (by simp)
  have hxx : h.value x x = 0 := calc
    h.value x x = ∑ j, h.value (op (a j) • e j) x := value_left_sum h _ x
    _ = ∑ j, c j • q j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [value_left_smul, hx, ← mul_assoc, ha]
    _ = 0 := hcB
  have hzero : x = 0 := by
    by_contra hn
    exact anisotropic x hn hxx
  have hzeroValue : h.value (e i) (0 : V) = 0 :=
    op_injective ((rightValue h (e i)).map_zero)
  have hai : a i = 0 := by
    have heq := hx i
    rw [hzero, hzeroValue] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (hq i)
  have hci : c i • q i = 0 := by rw [← ha, hai, mul_zero]
  exact hi ((smul_eq_zero.mp hci).resolve_right (hq i))

private theorem skew_partner (h₂ : (2 : F) ≠ 0)
    {x : V} (hx : x ≠ 0) (hxx : h.value x x = 0) : HasHyperbolicPair h := by
  obtain ⟨y, hy⟩ := NontrialitarianSpinModels.hyperbolicPartner.{u,v} h₂ s h x hx hxx
  exact ⟨x, y, hx, hxx, hy⟩

end Skew

/-- Regular skew-Hermitian forms in quaternion dimension at least four have a hyperbolic pair. -/
theorem skewIsotropy : LocalSkewIsotropy.{u,v} := by
  constructor
  · intro F _ _ _ _ h₂ B _ _ hB hd s hs V _ _ hr h
    obtain ⟨x, hx, hxx⟩ := skew_isotropy_of_pureLine h (hB := hB) hd h₂
      (pureLines.{u,v}.1 F h₂ B hB hd s hs) hr
    exact skew_partner h h₂ hx hxx
  · intro B _ _ hB hd s hs V _ _ hr h
    have h₂ : (2 : ℝ) ≠ 0 := by norm_num
    obtain ⟨x, hx, hxx⟩ := skew_isotropy_of_pureLine h (hB := hB) hd h₂
      (pureLines.{u,v}.2 B hB hd s hs) hr
    exact skew_partner h h₂ hx hxx

open LinearAlgebraicGroups.Specs.Arithmetic
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (dagger hermitianValue)

private theorem rightColumn_finrank {B : Type u} [DivisionRing B] (r : ℕ) :
    Module.finrank Bᵐᵒᵖ (Fin r → B) = r := by
  let e : (Fin r → B) ≃ₗ[Bᵐᵒᵖ] (Fin r → Bᵐᵒᵖ) :=
    { toFun := fun x i => op (x i)
      invFun := fun x i => unop (x i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq]
  simp

/-- Both local matrix models of the orthogonal involution are isotropic. -/
theorem finiteModelIsotropy : FiniteModelIsotropy.{u} := by
  classical
  intro F A _ _ _ _ _ _ h₂ hA n hn hdegree s hortho
  obtain ⟨B, _, _, r, hB, hr, ⟨e⟩, hsplit | hdeg⟩ := NontrialitarianSpinModels.nonarchimedeanDivision h₂ hA s
  · obtain ⟨iso⟩ := hsplit
    let E := e.trans iso.mapMatrix
    have hdF : degree F F = 1 := by
      change Nat.sqrt (Module.finrank F F) = 1
      simp
    have hsize : r = 2 * n := by
      have heq := RM03.CSA.degree_matrix_division hA
        (show isCentralDivision F F from ⟨inferInstance, inferInstance⟩) hr E
      change degree F A = r * degree F F at heq
      simpa [hdF, hdegree] using heq.symm
    obtain ⟨H, q, hsymm, hpolar, hreg, hadjoint⟩ := NontrialitarianSpinModels.fieldOrthogonalModel r h₂ hA s hortho E
    left
    refine ⟨r, E, H, q, hsize, hsymm, hpolar, hreg, hadjoint, ?_⟩
    apply LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy.local_isotropy h₂ q
    · exact LinearMap.separatingLeft_iff_ker_eq_bot.mp hreg.1
    · simpa using (show 5 ≤ r by omega)
  · right
    have hsize : r = n := by
      have heq := RM03.CSA.degree_matrix_division hA hB.2 hr e
      change degree F A = r * degree F B at heq
      rw [hdegree, hdeg] at heq
      omega
    obtain ⟨b, H, hcanon, hskew, hadjoint, ⟨h, hh⟩, _, _⟩ :=
      NontrialitarianSpinModels.quaternionSkewModel r h₂ hA s hortho hB hdeg e
    refine ⟨B, inferInstance, inferInstance, hB, r, e, b, H, h, hdeg, hsize,
      hcanon, hskew, hadjoint, hh, ?_⟩
    have hdim : 4 ≤ Module.finrank Bᵐᵒᵖ (Fin r → B) := by
      simpa [rightColumn_finrank, hsize] using hn
    obtain ⟨x, hx, hxx⟩ := skew_isotropy_of_pureLine h (hB := hB) hdeg h₂
      (pureLines.{u,u}.1 F h₂ B hB hdeg b hcanon) hdim
    exact skew_partner h h₂ hx hxx


end

section SpinComparison

open Algebra.TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (dagger extendAnti hermitianValue)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent (coefficientHom tensorMap tensorMap_involution)
open Matrix
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open scoped CategoryTheory.MonObj Matrix TensorProduct

open private scalarMatrixBaseChange scalarMatrixBaseChange_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

set_option linter.style.haveILetI false

section ScalarExtension



noncomputable section

private theorem extendAnti_apply {k A L : Type u} [Field k] [Ring A] [Algebra k A]
    [CommRing L] [Algebra k L] (s : SymplecticIsometryDescent.Involution k A) (z : L ⊗[k] A) :
    antiValue (extendAnti (toDivisionInvolution s).anti L) z = (s.baseChange L).toLinearMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul l a => rfl
  | add x y hx hy => simpa only [antiValue, map_add, MulOpposite.unop_add] using congrArg₂ (· + ·) hx hy
-- Adapted from Mathlib/RingTheory/TensorProduct/Maps.lean (Algebra.TensorProduct.cancelBaseChange). Copyright (c) 2020 Kim Morrison. All rights reserved. Released under Apache 2.0, see LICENSE. MathGenome adapts tensor base-change cancellation to the local scalar tower.
private def tensorCancel (k F L A : Type u) [CommRing k] [CommRing F] [CommRing L]
    [Ring A] [Algebra k F] [Algebra k L] [Algebra k A] [Algebra F L] [IsScalarTower k F L] :
    (L ⊗[F] (F ⊗[k] A)) ≃ₐ[L] L ⊗[k] A :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k F L L A).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp)

@[simp] private theorem tensorCancel_tmul {k F L A : Type u} [CommRing k] [CommRing F] [CommRing L]
    [Ring A] [Algebra k F] [Algebra k L] [Algebra k A] [Algebra F L] [IsScalarTower k F L]
    (l : L) (f : F) (a : A) :
    tensorCancel k F L A (l ⊗ₜ[F] (f ⊗ₜ[k] a)) = (f • l) ⊗ₜ[k] a :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul k F L l a f

private theorem cancelBaseChange_involution {k F L A : Type u} [Field k] [CommRing F] [CommRing L]
    [Ring A] [Algebra k F] [Algebra k L] [Algebra k A] [Algebra F L] [IsScalarTower k F L]
    (s : SymplecticIsometryDescent.Involution k A) (z : L ⊗[F] (F ⊗[k] A)) :
    tensorCancel k F L A (((s.baseChange F).baseChange L).toLinearMap z) =
      (s.baseChange L).toLinearMap (tensorCancel k F L A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul l z =>
    induction z using TensorProduct.inductionOn with
    | tmul f a => simp [SymplecticIsometryDescent.Involution.baseChange, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem scalarExtendOrthogonal {k F A : Type u} [Field k] [Field F] [Ring A]
    [Algebra k F] [Algebra k A] (s : SymplecticIsometryDescent.Involution k A)
    (h : IsOrthogonal (toDivisionInvolution s)) :
    IsOrthogonal (toDivisionInvolution (s.baseChange F)) := by
  classical
  obtain ⟨d, e, H, hH, he⟩ := h
  let K := AlgebraicClosure k
  let L := AlgebraicClosure F
  let i : K →ₐ[k] L := IsAlgClosed.lift
  letI : Algebra K L := i.toRingHom.toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let E₀ : (L ⊗[K] (K ⊗[k] A)) ≃ₐ[L] Matrix (Fin d) (Fin d) L :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans
        (scalarMatrixBaseChange (F := K) (R := L) (Fin d))
  let E : (L ⊗[k] A) ≃ₐ[L] Matrix (Fin d) (Fin d) L := (tensorCancel k K L A).symm.trans E₀
  let H' := Units.map ((algebraMap K L).mapMatrix.toMonoidHom) H
  have ht (l : L) (a : K ⊗[k] A) : E₀ (l ⊗ₜ[K] a) = l • (e a).map (algebraMap K L) := by
    change scalarMatrixBaseChange (Fin d) (l ⊗ₜ[K] e a) = _
    exact scalarMatrixBaseChange_tmul l (e a)
  have hE₀ (w : L ⊗[K] (K ⊗[k] A)) :
      E₀ (((s.baseChange K).baseChange L).toLinearMap w) = gramAdjoint H' (E₀ w) := by
    induction w using TensorProduct.inductionOn with
    | tmul l a =>
      have ha := he a
      rw [extendAnti_apply] at ha
      rw [show ((s.baseChange K).baseChange L).toLinearMap (l ⊗ₜ[K] a) =
        l ⊗ₜ[K] (s.baseChange K).toLinearMap a from rfl, ht, ht, ha]
      change l • (gramAdjoint H (e a)).map (algebraMap K L) =
        (H.inv.map (algebraMap K L)) * (l • (e a).map (algebraMap K L)).transpose *
          (H.val.map (algebraMap K L))
      simp [gramAdjoint, Matrix.transpose_smul, Matrix.transpose_map, Matrix.map_mul]
    | add x y hx hy =>
      simpa only [map_add, gramAdjoint, Matrix.transpose_add, Matrix.mul_add,
        Matrix.add_mul] using congrArg₂ (· + ·) hx hy
  have hE (z : L ⊗[k] A) :
      E ((s.baseChange L).toLinearMap z) = gramAdjoint H' (E z) := by
    obtain ⟨w, rfl⟩ := (tensorCancel k K L A).surjective z
    rw [← cancelBaseChange_involution]
    simpa [E] using hE₀ w
  refine ⟨d, (tensorCancel k F L A).trans E, H', ?_, ?_⟩
  · change (H.val.map (algebraMap K L)).transpose = H.val.map (algebraMap K L)
    simpa only [RingHom.mapMatrix_apply, Matrix.transpose_map] using congrArg
      (fun M : Matrix (Fin d) (Fin d) K => M.map (algebraMap K L)) hH
  · intro x
    rw [extendAnti_apply]
    change E (tensorCancel k F L A (((s.baseChange F).baseChange L).toLinearMap x)) =
      gramAdjoint H' (E (tensorCancel k F L A x))
    rw [cancelBaseChange_involution]
    exact hE _

end


end ScalarExtension
section HyperbolicProjectors



noncomputable section

private theorem isotropicProjector {F A B : Type u} {J : Type*} [Field F] [Ring A] [Algebra F A]
    [DivisionRing B] [Algebra F B] [Fintype J] [DecidableEq J]
    (s : SymplecticIsometryDescent.Involution F A) (b : Specs.SymplecticDivisionForms.Involution F B)
    (E : A ≃ₐ[F] Matrix J J B) (H : (Matrix J J B)ˣ)
    (hadj : ∀ z, E (s.toLinearMap z) = H.inv * dagger b.anti (E z) * H.val)
    (x : J → B) (hx : x ≠ 0) (hxx : hermitianValue b.anti H.val x x = 0) :
    ∃ p : A, p ≠ 0 ∧ p * p = p ∧ s.toLinearMap p * p = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    contrapose! hx
    ext i
    exact hx i
  let r : J → B := Pi.single j (x j)⁻¹
  have hr : r ⬝ᵥ x = 1 := by
    simp [r, single_dotProduct, hj]
  let P : Matrix J J B := vecMulVec x r
  have hP : P ≠ 0 := by
    apply Matrix.vecMulVec_ne_zero hx
    intro h
    have hh := congrFun h j
    simp [r, hj] at hh
  have he : P * P = P := by
    simp [P, vecMulVec_mul_vecMulVec, hr]
  have hdag : dagger b.anti P =
      vecMulVec (fun i => antiValue b.anti (r i)) (fun i => antiValue b.anti (x i)) := by
    ext i j
    simp [dagger, P, vecMulVec_apply, antiValue, MulOpposite.unop_mul]
  let p := E.symm P
  refine ⟨p, fun h => hP (by simpa [p] using congrArg E h), ?_, ?_⟩
  · apply E.injective
    simpa [p] using he
  · apply E.injective
    rw [map_mul, map_zero, hadj, show E p = P by simp [p]]
    have hH : H.val * P = vecMulVec (H.val *ᵥ x) r := mul_vecMulVec _ _ _
    have hzero : dagger b.anti P * (H.val * P) = 0 := by
      rw [hH, hdag, vecMulVec_mul_vecMulVec]
      rw [show (fun i => antiValue b.anti (x i)) ⬝ᵥ (H.val *ᵥ x) = 0 from hxx]
      simp
    rw [mul_assoc H.inv, mul_assoc H.inv, mul_assoc (dagger b.anti P), hzero, mul_zero]

/-- An isotropic projector can be corrected to an idempotent orthogonal to its adjoint. -/
private theorem orthogonalProjectors {F A : Type u} [Field F] [Ring A] [Algebra F A]
    (s : SymplecticIsometryDescent.Involution F A) (h₂ : (2 : F) ≠ 0)
    {p : A} (hp : p ≠ 0) (hpp : p * p = p) (hsp : s.toLinearMap p * p = 0) :
    ∃ e : A, e ≠ 0 ∧ e * e = e ∧ e * s.toLinearMap e = 0 ∧ s.toLinearMap e * e = 0 := by
  let q := s.toLinearMap p
  let c : F := 2⁻¹
  have hqq : q * q = q := by
    dsimp [q]
    rw [← s.map_mul, hpp]
  have hqp : q * p = 0 := hsp
  have hcc : c + c = 1 := by
    dsimp [c]
    rw [← two_mul, mul_inv_cancel₀ h₂]
  let e := p - c • (p * q)
  have hse : s.toLinearMap e = q - c • (p * q) := by
    change s.toLinearMap (p - c • (p * q)) = _
    rw [map_sub, map_smul, s.map_mul, show s.toLinearMap q = p from s.involutive p]
  have hpqp : p * q * p = 0 := by rw [mul_assoc, hqp, mul_zero]
  have hppq : p * (p * q) = p * q := by rw [← mul_assoc, hpp]
  have hpqq : (p * q) * q = p * q := by rw [mul_assoc, hqq]
  have hqpq : q * (p * q) = 0 := by rw [← mul_assoc, hqp, zero_mul]
  have hpqpq : (p * q) * (p * q) = 0 := by rw [← mul_assoc, hpqp, zero_mul]
  have hep : e * p = p := by simp [e, sub_mul, hpp, hpqp]
  refine ⟨e, fun he => hp (by simpa [he] using hep.symm), ?_, ?_, ?_⟩
  · rw [show e * e = e * (p - c • (p * q)) by rfl, mul_sub,
      ← mul_smul_comm, ← mul_assoc, hep]
    simp only [e, mul_smul_comm]
  · rw [hse]
    change (p - c • (p * q)) * (q - c • (p * q)) = 0
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hppq,
      hpqq, hpqpq, smul_zero, sub_zero]
    rw [sub_sub, ← add_smul, hcc, one_smul, sub_self]
  · rw [hse]
    change (q - c • (p * q)) * (p - c • (p * q)) = 0
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hqp,
      hpqp, hqpq, hpqpq, smul_zero, sub_self]

end


end HyperbolicProjectors
section CentralCover


open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

variable {k : Type u} [Field k]

private theorem kernelElement {G H : GroupScheme k} {π : G ⟶ H}
    {N : ClosedSubgroup G} (hN : IsSchemeKernel π N) {T : SchemeOver k}
    {a : T ⟶ G.X} (ha : a ≫ π.hom.hom = 1) :
    ∃ n : T ⟶ N.group.X, n ≫ N.inclusion.hom.hom = a :=
  ⟨hN.lift a (toUnit _) ha, hN.lift_fst _ _ _⟩

private theorem square_eq_of_projection_eq {G H : GroupScheme k} {π : G ⟶ H}
    (hπ : CentralIsogenies.IsCentralIsogeny π)
    {N : ClosedSubgroup G} (hN : IsSchemeKernel π N)
    (hpow : (𝟙 N.group.X : N.group.X ⟶ N.group.X) ^ 2 = 1)
    {T : SchemeOver k} {a b : T ⟶ G.X} (hab : a ≫ π.hom.hom = b ≫ π.hom.hom) :
    a ^ 2 = b ^ 2 := by
  obtain ⟨Z, hZ, hcen⟩ := hπ.2.2.2
  let d := a * b⁻¹
  have hd : d ≫ π.hom.hom = 1 := by
    simp [d, MonObj.mul_comp, GrpObj.inv_comp, hab]
  obtain ⟨n, hn⟩ := kernelElement hN hd
  obtain ⟨z, hz⟩ := kernelElement hZ hd
  have hc : Commute d b := by
    simpa only [show (𝟙 G : G ⟶ G).hom.hom = 𝟙 G.X from rfl, Category.comp_id, hz] using
      (centralizes_iff (𝟙 G) Z.inclusion.hom.hom).mp hcen T z b
  have hd2 : d ^ 2 = 1 := by
    have hn2 : n ^ 2 = 1 := by
      simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using
        congrArg (n ≫ ·) hpow
    rw [← hn, ← MonObj.pow_comp, hn2, MonObj.one_comp]
  have ha : d * b = a := by simp [d, mul_assoc]
  rw [← ha, hc.mul_pow, hd2, one_mul]

/-- The square map descends along a faithfully flat central cover with kernel of exponent two. -/
private theorem descendSquare {G H : AffineAlgebraicGroup k} {π : G.val ⟶ H.val}
    (hπ : CentralIsogenies.IsCentralIsogeny π)
    {N : ClosedSubgroup G.val} (hN : IsSchemeKernel π N)
    (hpow : (𝟙 N.group.X : N.group.X ⟶ N.group.X) ^ 2 = 1) :
    ∃ s : H.val.X ⟶ G.val.X, π.hom.hom ≫ s = (𝟙 G.val.X : G.val.X ⟶ G.val.X) ^ 2 ∧
      s ≫ π.hom.hom = (𝟙 H.val.X : H.val.X ⟶ H.val.X) ^ 2 := by
  let p := π.hom.hom
  let q : G.val.X ⟶ G.val.X := (𝟙 G.val.X : G.val.X ⟶ G.val.X) ^ 2
  letI : Flat p.left := hπ.2.1
  letI : Surjective p.left := hπ.2.2.1
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine H.val.X.left := H.property.1
  letI : IsRegularEpi p.left := isRegularEpi_of_flat_of_surjective_of_isAffine p.left
  let a := pullback.fst p.left p.left
  let b := pullback.snd p.left p.left
  let X : SchemeOver k := Over.mk (a ≫ G.val.X.hom)
  let a' : X ⟶ G.val.X := Over.homMk a
  let b' : X ⟶ G.val.X := Over.homMk b (by
    dsimp [X]
    rw [← Over.w p, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ H.val.X.hom)
      (pullback.condition (f := p.left) (g := p.left)).symm)
  have hab : a' ≫ p = b' ≫ p := Over.OverMorphism.ext (by exact pullback.condition)
  have heq : a ≫ q.left = b ≫ q.left := by
    have hcomp : a' ≫ q = b' ≫ q := by
      simpa only [q, MonObj.comp_pow, Category.comp_id] using
        square_eq_of_projection_eq hπ hN hpow hab
    exact congrArg (fun f : X ⟶ G.val.X => f.left) hcomp
  obtain ⟨s, hs⟩ := IsRegularEpi.exists_of_isKernelPair p.left
    (IsPullback.of_hasPullback p.left p.left) q.left heq
  have hs' : s ≫ G.val.X.hom = H.val.X.hom := by
    rw [← cancel_epi p.left, ← Category.assoc, hs, Over.w q, Over.w p]
  let s' : H.val.X ⟶ G.val.X := Over.homMk s hs'
  have hfac : p ≫ s' = q := Over.OverMorphism.ext hs
  refine ⟨s', hfac, ?_⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi p.left]
  change (p ≫ s' ≫ p).left = (p ≫ ((𝟙 H.val.X : H.val.X ⟶ H.val.X) ^ 2)).left
  congr 1
  rw [← Category.assoc, hfac]
  simp only [q, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]


private theorem fourth_power_of_commuting_images {G H : GroupScheme k} {π : G ⟶ H}
    (hπ : CentralIsogenies.IsCentralIsogeny π)
    {N : ClosedSubgroup G} (hN : IsSchemeKernel π N)
    (hpow : (𝟙 N.group.X : N.group.X ⟶ N.group.X) ^ 2 = 1)
    {T : SchemeOver k} {a b c : T ⟶ G.X}
    (hc : c ≫ π.hom.hom = (a ≫ π.hom.hom) * (b ≫ π.hom.hom))
    (hab : Commute (a ≫ π.hom.hom) (b ≫ π.hom.hom)) :
    c ^ 4 = a ^ 4 * b ^ 4 := by
  let p := π.hom.hom
  have hconj : (a * b * a⁻¹) ≫ p = b ≫ p := by
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hab.eq]
    simp [p, mul_assoc]
  have hcom : Commute a (b ^ 2) := by
    apply (mul_inv_eq_iff_eq_mul).1
    have h := square_eq_of_projection_eq hπ hN hpow hconj
    simpa only [show (a * b * a⁻¹) ^ 2 = a * b ^ 2 * a⁻¹ by simp [pow_two, mul_assoc]] using h
  have hsq : (c ^ 2) ≫ p = (a ^ 2 * b ^ 2) ≫ p := by
    rw [MonObj.pow_comp]
    change (c ≫ π.hom.hom) ^ 2 = _
    rw [hc, hab.mul_pow, MonObj.mul_comp, MonObj.pow_comp, MonObj.pow_comp]
  have hh := square_eq_of_projection_eq hπ hN hpow hsq
  rw [(hcom.pow_left 2).mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hh
  exact hh

end


end CentralCover
section ReducedNorm


noncomputable section

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}

open private pairReducedNorm_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

private theorem norm_of_isometry_square
    (D : DescendedQuadraticPair ρ)
    {d : ℕ} (b : Module.Basis (Fin d) k ρ.fixedSubalgebra)
    (R : TestAlgebra k) (a : R ⊗[k] ρ.fixedSubalgebra)
    (ha : (D.involution.baseChange R).toLinearMap a * a = 1) :
    MvPolynomial.eval₂ (algebraMap k R) (fun j => (b.baseChange R).repr (a * a) j)
      (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) = 1 := by
  classical
  let A := ρ.fixedSubalgebra
  let S := K ⊗[k] R
  let f : R →ₐ[k] S := includeRight
  let R' : TestAlgebra k := CommAlgCat.of k S
  let f' : R ⟶ R' := CommAlgCat.ofHom f
  have hf : Function.Injective f := by
    change Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)
    exact Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨E, hE, hstar, _⟩ := NontrialitarianSpinModels.quadraticPairScalarExtension D S
  apply hf
  change f'.hom (MvPolynomial.eval₂ (algebraMap k R)
    (fun j => (b.baseChange R).repr (a * a) j)
    (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b)) = f'.hom 1
  rw [pairReducedNorm_natural D f' b (a * a), map_one,
    NontrialitarianSpinModels.pairReducedNormScalarExtension D S E hE d b (tensorMap f' (a * a))]
  let J := hyperbolicGram I S
  have hJ : J * J = 1 := by
    change Matrix.fromBlocks (0 : Matrix I I S) 1 1 0 *
      Matrix.fromBlocks (0 : Matrix I I S) 1 1 0 = 1
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  let X := E (tensorMap f' a)
  have hX : (J * X.transpose * J) * X = 1 := by
    have hh := congrArg (fun z => E (tensorMap f' z)) ha
    simp only [map_mul, map_one, tensorMap_involution] at hh
    change E ((D.involution.baseChange S).toLinearMap (tensorMap f' a)) * X = 1 at hh
    rw [hstar] at hh
    exact hh
  have hJdet : J.det * J.det = 1 := by
    rw [← Matrix.det_mul, hJ, Matrix.det_one]
  have hXdet : X.det * X.det = 1 := by
    have hh := congrArg Matrix.det hX
    simp only [Matrix.det_one, Matrix.det_mul, Matrix.det_transpose] at hh
    calc
      X.det * X.det = (J.det * J.det) * (X.det * X.det) := by rw [hJdet, one_mul]
      _ = 1 := by rw [← hh]; ac_rfl
  rw [map_mul, map_mul, Matrix.det_mul]
  exact hXdet

end


end ReducedNorm
section DiagonalScales


noncomputable section

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

private def diagonalValue (e f : A) (t : Rˣ) : A :=
  1 + ((t : R) - 1) • e + ((↑t⁻¹ : R) - 1) • f

private theorem diagonalValue_one (e f : A) : diagonalValue e f (1 : Rˣ) = 1 := by
  simp [diagonalValue]

private theorem diagonalValue_mul {e f : A}
    (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (t s : Rˣ) :
    diagonalValue e f t * diagonalValue e f s = diagonalValue e f (t * s) := by
  simp only [diagonalValue, add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    he, hf, hef, hfe, smul_zero, add_zero,
    one_mul, mul_one, Units.val_mul, _root_.mul_inv_rev]
  module

private def diagonalUnits {e f : A}
    (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    Rˣ →* Aˣ where
  toFun t :=
    { val := diagonalValue e f t
      inv := diagonalValue e f t⁻¹
      val_inv := by rw [diagonalValue_mul he hf hef hfe, mul_inv_cancel, diagonalValue_one]
      inv_val := by rw [diagonalValue_mul he hf hef hfe, inv_mul_cancel, diagonalValue_one] }
  map_one' := Units.ext (diagonalValue_one e f)
  map_mul' t s := Units.ext (diagonalValue_mul he hf hef hfe t s).symm

private theorem diagonalValue_involution (s : SymplecticIsometryDescent.Involution R A) (e : A) (t : Rˣ) :
    s.toLinearMap (diagonalValue e (s.toLinearMap e) t) =
      diagonalValue e (s.toLinearMap e) t⁻¹ := by
  simp [diagonalValue, s.map_one, show s.toLinearMap (s.toLinearMap e) = e from s.involutive e, add_assoc, add_comm]

private theorem diagonalValue_mul_projector {e f : A} (he : e * e = e) (hfe : f * e = 0)
    (t : Rˣ) : diagonalValue e f t * e = (t : R) • e := by
  simp only [diagonalValue, add_mul, smul_mul_assoc, one_mul, he, hfe, smul_zero, add_zero]
  module

section

variable {k F A : Type u} [Field k] [Field F] [Algebra k F] [Ring A] [Algebra k A]

private def liftProjector (R : TestAlgebra F) (e : F ⊗[k] A) :
    ((restrictTestAlgebra k F).obj R) ⊗[k] A :=
  tensorMap (coefficientHom R) e

private theorem liftProjector_involution (s : SymplecticIsometryDescent.Involution k A)
    (R : TestAlgebra F) (e : F ⊗[k] A) :
    (s.baseChange ((restrictTestAlgebra k F).obj R)).toLinearMap (liftProjector R e) =
      liftProjector R ((s.baseChange F).toLinearMap e) := by
  exact (tensorMap_involution s (coefficientHom R) e).symm

private theorem liftProjector_natural (R S : TestAlgebra F) (a : R ⟶ S)
    (e : F ⊗[k] A) :
    tensorMap ((restrictTestAlgebra k F).map a) (liftProjector R e) = liftProjector S e := by
  induction e using TensorProduct.inductionOn with
  | tmul t x =>
    exact congrArg (fun v : (restrictTestAlgebra k F).obj S => v ⊗ₜ[k] x)
      (a.hom.commutes t)
  | add x y hx hy =>
    simp only [liftProjector, map_add] at hx hy ⊢
    rw [hx, hy]

end

end


end DiagonalScales
section RealField


open private matrixBaseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

noncomputable section

private def cancelFieldEquiv {F L A : Type*} [Field F] [Field L] [Ring A] [Algebra F A]
    (R : F ≃+* L) :
    letI : Algebra F L := R.toRingHom.toAlgebra
    (L ⊗[F] A) ≃ₐ[F] A := by
  letI : Algebra F L := R.toRingHom.toAlgebra
  let l : L →ₐ[F] A :=
    { toRingHom := (algebraMap F A).comp R.symm.toRingHom
      commutes' := fun r => congrArg (algebraMap F A) (R.symm_apply_apply r) }
  let f := Algebra.TensorProduct.lift l (AlgHom.id F A)
    (fun b a => Algebra.commutes (R.symm b) a)
  refine AlgEquiv.ofAlgHom f includeRight ?_ ?_
  · apply AlgHom.ext
    intro a
    change f (1 ⊗ₜ[F] a) = a
    simp [f, l, Algebra.TensorProduct.lift_tmul]
  · apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change includeRight (f (a ⊗ₜ[F] b)) = a ⊗ₜ[F] b
      rw [show f (a ⊗ₜ[F] b) = algebraMap F A (R.symm a) * b from
        Algebra.TensorProduct.lift_tmul ..]
      change (1 : L) ⊗ₜ[F] (algebraMap F A (R.symm a) * b) = _
      rw [← Algebra.smul_def, TensorProduct.tmul_smul]
      change ((R (R.symm a)) * 1) ⊗ₜ[F] b = _
      rw [R.apply_symm_apply, mul_one]
    | add x y hx hy =>
      simp only [AlgHom.comp_apply, AlgHom.id_apply, map_add] at hx hy ⊢
      rw [hx, hy]

private theorem cancelFieldEquiv_tmul {F L A : Type*} [Field F] [Field L] [Ring A] [Algebra F A]
    (R : F ≃+* L) :
    letI : Algebra F L := R.toRingHom.toAlgebra
    ∀ a b, cancelFieldEquiv (A := A) R (a ⊗ₜ[F] b) = R.symm a • b := by
  letI : Algebra F L := R.toRingHom.toAlgebra
  intro a b
  let l : L →ₐ[F] A :=
    { toRingHom := (algebraMap F A).comp R.symm.toRingHom
      commutes' := fun r => congrArg (algebraMap F A) (R.symm_apply_apply r) }
  exact (Algebra.TensorProduct.lift_tmul l (AlgHom.id F A)
    (fun b a => Algebra.commutes (R.symm b) a) a b).trans (Algebra.smul_def (R.symm a) b).symm

private def transferFieldPresentation {F L A B : Type*} [Field F] [Field L]
    [Ring A] [Algebra F A] [Ring B] [Algebra L B] (R : F ≃+* L) :
    letI : Algebra F L := R.toRingHom.toAlgebra
    letI : Algebra L F := R.symm.toRingHom.toAlgebra
    (L ⊗[F] A ≃ₐ[L] B) → (A ≃ₐ[F] F ⊗[L] B) := by
  letI : Algebra F L := R.toRingHom.toAlgebra
  letI : Algebra L F := R.symm.toRingHom.toAlgebra
  intro E
  let e := (cancelFieldEquiv (A := A) R).symm.toRingEquiv.trans
    (E.toRingEquiv.trans (cancelFieldEquiv (A := B) R.symm).symm.toRingEquiv)
  apply AlgEquiv.ofRingEquiv (f := e)
  intro r
  apply (cancelFieldEquiv (A := B) R.symm).injective
  change (cancelFieldEquiv (A := B) R.symm)
    ((cancelFieldEquiv (A := B) R.symm).symm (E ((cancelFieldEquiv (A := A) R).symm
      (algebraMap F A r)))) = _
  rw [AlgEquiv.apply_symm_apply]
  change E ((1 : L) ⊗ₜ[F] algebraMap F A r) =
    cancelFieldEquiv (A := B) R.symm (r ⊗ₜ[L] (1 : B))
  have hx : ((1 : L) ⊗ₜ[F] algebraMap F A r) = algebraMap L (L ⊗[F] A) (R r) := by
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
    change ((R r) * 1) ⊗ₜ[F] (1 : A) = R r ⊗ₜ[F] (1 : A)
    rw [mul_one]
  rw [hx, AlgEquiv.commutes, cancelFieldEquiv_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

private abbrev divisionRingOfEquiv {A B : Type*} [Ring A] [DivisionRing B] (e : A ≃+* B) :
    DivisionRing A := by
  letI : Nontrivial A := e.toEquiv.nontrivial
  refine DivisionRing.ofIsUnitOrEqZero (fun a => ?_)
  by_cases h : a = 0
  · exact Or.inr h
  · have ha : e a ≠ 0 := fun h0 => h (e.injective (h0.trans e.map_zero.symm))
    exact Or.inl (by simpa using (isUnit_iff_ne_zero.mpr ha).map e.symm.toMonoidHom)

private theorem realDivisionPresentation {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    (R : F ≃+* ℝ) (hB : isCentralDivision F B) (hd : degree F B = 2) :
    letI : Algebra ℝ F := R.symm.toRingHom.toAlgebra
    Nonempty (B ≃ₐ[F] F ⊗[ℝ] Quaternion ℝ) := by
  letI : Algebra F ℝ := R.toRingHom.toAlgebra
  letI : Algebra ℝ F := R.symm.toRingHom.toAlgebra
  let A := ℝ ⊗[F] B
  let e := (cancelFieldEquiv (A := B) R).toRingEquiv
  letI : DivisionRing A := divisionRingOfEquiv e
  have h₀ := _root_.RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  have hA : isCentralSimple ℝ A := _root_.RM03.CSA.isCentralSimple_baseChange h₀
  have hd' : degree ℝ A = 2 :=
    (congrArg Nat.sqrt (_root_.RM03.CSA.finrank_baseChange (L := ℝ) h₀)).trans hd
  obtain ⟨⟨E⟩, _⟩ := LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting.real_division (B := A) hA.2 hd'
  exact ⟨transferFieldPresentation R E⟩

end


end RealField
noncomputable section
section Spin

open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

set_option maxHeartbeats 850000

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup k} {D : DescendedQuadraticPair ρ}

private def vectorPoint (M : SpinModel G D) (R : TestAlgebra k) (a : Points G.val.X R) :
    (R ⊗[k] ρ.fixedSubalgebra)ˣ :=
  M.fullPoints R (a ≫ M.projection.hom.hom ≫ M.inclusion.hom.hom)

private theorem neutralPoints_injective (M : SpinModel G D) (R : TestAlgebra k) :
    Function.Injective (fun a : Points M.neutral.val.X R =>
      M.fullPoints R (a ≫ M.inclusion.hom.hom)) := by
  letI : IsOpenImmersion M.inclusion.hom.hom.left := M.openImmersion
  letI : Mono M.inclusion.hom.hom.left := inferInstance
  letI : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  intro x y h
  exact (cancel_mono M.inclusion.hom.hom).mp (M.fullFaithful R h)

private theorem spinKernel_square (M : SpinModel G D) :
    (𝟙 M.kernel.group.X : M.kernel.group.X ⟶ M.kernel.group.X) ^ 2 = 1 := by
  apply hom_ext_of_points (Unipotent.closedSubgroupAlgebraicGroup M.kernel).property.1
  intro R a
  change Points M.kernel.group.X R at a
  have ha : a ^ 2 = 1 := by
    apply (M.kernelPoints R).injective
    rw [map_pow, map_one]
    exact Subtype.ext ((mem_rootsOfUnity 2 (M.kernelPoints R a).val).mp (M.kernelPoints R a).property)
  calc
    a ≫ ((𝟙 M.kernel.group.X : M.kernel.group.X ⟶ M.kernel.group.X) ^ 2) = a ^ 2 := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = 1 := ha
    _ = a ≫ (1 : M.kernel.group.X ⟶ M.kernel.group.X) := (MonObj.comp_one a).symm

private def IsOrthogonalProjector {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (s : SymplecticIsometryDescent.Involution R A) (e : A) : Prop :=
  e * e = e ∧ e * s.toLinearMap e = 0 ∧ s.toLinearMap e * e = 0

private def projectorUnits {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    {s : SymplecticIsometryDescent.Involution R A} {e : A} (he : IsOrthogonalProjector s e) :
    Rˣ →* Aˣ :=
  diagonalUnits he.1 (by rw [← s.map_mul, he.1]) he.2.1 he.2.2

private theorem projectorUnits_isometry {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    {s : SymplecticIsometryDescent.Involution R A} {e : A} (he : IsOrthogonalProjector s e)
    (t : Rˣ) : s.toLinearMap (projectorUnits he t).val * (projectorUnits he t).val = 1 := by
  change s.toLinearMap (diagonalValue e (s.toLinearMap e) t) *
    diagonalValue e (s.toLinearMap e) t = 1
  rw [diagonalValue_involution]
  exact (projectorUnits he t).inv_val

private theorem projectorUnits_tensorMap {R S : TestAlgebra k} (a : R ⟶ S)
    {e : R ⊗[k] ρ.fixedSubalgebra} {e' : S ⊗[k] ρ.fixedSubalgebra}
    (he : IsOrthogonalProjector (D.involution.baseChange R) e)
    (he' : IsOrthogonalProjector (D.involution.baseChange S) e')
    (h : SymplecticIsometryDescent.tensorMap a e = e') (t : Rˣ) :
    Units.map (SymplecticIsometryDescent.tensorMap a).toMonoidHom (projectorUnits he t) =
      projectorUnits he' (Units.map a.hom.toMonoidHom t) := by
  apply Units.ext
  change SymplecticIsometryDescent.tensorMap a (diagonalValue e ((D.involution.baseChange R).toLinearMap e) t) =
    diagonalValue e' ((D.involution.baseChange S).toLinearMap e') (Units.map a.hom.toMonoidHom t)
  have hs (r : R) (x : R ⊗[k] ρ.fixedSubalgebra) :
      SymplecticIsometryDescent.tensorMap a (r • x) = a.hom r • SymplecticIsometryDescent.tensorMap a x := by
    induction x using TensorProduct.inductionOn with
    | tmul t x =>
      rw [TensorProduct.smul_tmul']
      change (a.hom (r * t)) ⊗ₜ[k] x = a.hom r • ((a.hom t) ⊗ₜ[k] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add x y hx hy =>
      rw [smul_add, map_add, map_add, smul_add, hx, hy]
  rw [diagonalValue, diagonalValue, map_add, map_add, map_one, hs, hs,
    SymplecticIsometryDescent.tensorMap_involution, h]
  simp only [map_sub, map_one, ← map_inv, Units.coe_map]
  rfl

private theorem neutralScalePoint (M : SpinModel G D)
    (h₂ : (2 : k) ≠ 0)
    (R : TestAlgebra k) {e : R ⊗[k] ρ.fixedSubalgebra}
    (he : IsOrthogonalProjector (D.involution.baseChange R) e) (t : Rˣ) :
    ∃ a : Points M.neutral.val.X R,
      M.fullPoints R (a ≫ M.inclusion.hom.hom) = projectorUnits he (t ^ 2) := by
  obtain ⟨d, b, hb⟩ := M.reducedNormOne h₂
  apply (hb R _).mpr
  refine ⟨projectorUnits_isometry he _, ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, pow_two]
  exact norm_of_isometry_square D b R _ (projectorUnits_isometry he t)

/-- Inverse scales on the two adjoint projectors give a natural family of spin points.
Squaring the scales puts them in the neutral isometries. The descended square
map and fourth powers then give a multiplicative lift through the spin cover. -/
private theorem spinScaling (M : SpinModel G D)
    (h₂ : (2 : k) ≠ 0) :
    ∃ g : ∀ (R : TestAlgebra k) {e : R ⊗[k] ρ.fixedSubalgebra},
        IsOrthogonalProjector (D.involution.baseChange R) e → Rˣ →* Points G.val.X R,
      (∀ (R : TestAlgebra k) e he (t : Rˣ), vectorPoint M R (g R (e := e) he t) = projectorUnits he (t ^ 16)) ∧
      ∀ (R S : TestAlgebra k) (a : R ⟶ S) {e e'} (he : IsOrthogonalProjector (D.involution.baseChange R) e)
        (he' : IsOrthogonalProjector (D.involution.baseChange S) e')
        (_h : SymplecticIsometryDescent.tensorMap a e = e') (t : Rˣ),
        mapPoints a (g R he t) = g S he' (Units.map a.hom.toMonoidHom t) := by
  classical
  let n (R : TestAlgebra k) {e} (he : IsOrthogonalProjector (D.involution.baseChange R) e) (t : Rˣ) :=
    (neutralScalePoint M h₂ R he t).choose
  have hn (R : TestAlgebra k) {e} (he : IsOrthogonalProjector (D.involution.baseChange R) e) (t : Rˣ) :
      M.fullPoints R (n R he t ≫ M.inclusion.hom.hom) = projectorUnits he (t ^ 2) :=
    (neutralScalePoint M h₂ R he t).choose_spec
  have hn1 (R : TestAlgebra k) {e} (he : IsOrthogonalProjector (D.involution.baseChange R) e) :
      n R he 1 = 1 := by
    apply neutralPoints_injective M R
    dsimp only
    rw [hn, one_pow, map_one, MonObj.one_comp, map_one]
  have hnm (R : TestAlgebra k) {e} (he : IsOrthogonalProjector (D.involution.baseChange R) e) (t u : Rˣ) :
      n R he (t * u) = n R he t * n R he u := by
    apply neutralPoints_injective M R
    dsimp only
    rw [hn, MonObj.mul_comp, map_mul, hn, hn, mul_pow, map_mul]
  let s := M.centralIsogeny
  have hpow := spinKernel_square M
  obtain ⟨c, hc₁, hc₂⟩ := descendSquare s M.isKernel hpow
  let g (R : TestAlgebra k) {e} (he : IsOrthogonalProjector (D.involution.baseChange R) e) :
      Rˣ →* Points G.val.X R :=
    { toFun := fun t => (n R he t ≫ c) ^ 4
      map_one' := by
        have h : (1 : Points M.neutral.val.X R) ≫ c = 1 := by
          calc
            _ = (1 : Points G.val.X R) ≫ (M.projection.hom.hom ≫ c) := by
              rw [← Category.assoc, MonObj.one_comp M.projection.hom.hom]
            _ = 1 := by rw [hc₁, MonObj.comp_pow, Category.comp_id, one_pow]
        change (n R he 1 ≫ c) ^ 4 = 1
        rw [hn1, h, one_pow]
      map_mul' := by
        intro t u
        change (n R he (t * u) ≫ c) ^ 4 = (n R he t ≫ c) ^ 4 * (n R he u ≫ c) ^ 4
        have hcomm : Commute (n R he t) (n R he u) := by
          change n R he t * n R he u = n R he u * n R he t
          rw [← hnm R he t u, ← hnm R he u t, mul_comm t u]
        apply fourth_power_of_commuting_images s M.isKernel hpow
        · simp only [Category.assoc, hc₂, MonObj.comp_pow, Category.comp_id]
          rw [hnm, hcomm.mul_pow]
        · simp only [Category.assoc, hc₂, MonObj.comp_pow, Category.comp_id]
          exact hcomm.pow_pow 2 2 }
  refine ⟨g, ?_, ?_⟩
  · intro R e he t
    rw [vectorPoint]
    change M.fullPoints R (((n R he t ≫ c) ^ 4) ≫ M.projection.hom.hom ≫ M.inclusion.hom.hom) = _
    rw [← Category.assoc, MonObj.pow_comp, Category.assoc (n R he t) c, hc₂,
      MonObj.comp_pow, Category.comp_id, ← pow_mul, MonObj.pow_comp, map_pow, hn, ← map_pow, ← pow_mul]
  · intro R S a e e' he he' h t
    have hna : mapPoints a (n R he t) = n S he' (Units.map a.hom.toMonoidHom t) := by
      apply neutralPoints_injective M S
      change M.fullPoints S (mapPoints a (n R he t ≫ M.inclusion.hom.hom)) =
        M.fullPoints S (n S he' (Units.map a.hom.toMonoidHom t) ≫ M.inclusion.hom.hom)
      rw [M.fullNatural, hn, hn, ← map_pow]
      exact projectorUnits_tensorMap a he he' h _
    change mapPoints a ((n R he t ≫ c) ^ 4) = (n S he' (Units.map a.hom.toMonoidHom t) ≫ c) ^ 4
    change ((testSpec k).map a.op ≫ (n R he t ≫ c) ^ 4) = _
    rw [MonObj.comp_pow, ← Category.assoc]
    exact congrArg (fun b : Points M.neutral.val.X S => (b ≫ c) ^ 4) hna

end Spin

section FiniteSpin

open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinIsotropy
open LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint mapPoints_unitPoint)
open private unitEquiv unitEquiv_unitPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem scalarIsotropicProjector {F A : Type u} {J : Type*} [Field F] [Ring A] [Algebra F A]
    [Fintype J] [DecidableEq J] (s : SymplecticIsometryDescent.Involution F A)
    (E : A ≃ₐ[F] Matrix J J F) (H : (Matrix J J F)ˣ) (q : QuadraticForm F (J → F))
    (hadj : ∀ z, E (s.toLinearMap z) = gramAdjoint H (E z))
    (hpolar : q.polarBilin = Matrix.toLinearMap₂' F H.val) (hq : IsIsotropic q) :
    ∃ p : A, p ≠ 0 ∧ p * p = p ∧ s.toLinearMap p * p = 0 := by
  let b : Specs.SymplecticDivisionForms.Involution F F :=
    ⟨AlgEquiv.toOpposite F F, fun _ => rfl⟩
  obtain ⟨x, hx, hxx⟩ := hq
  apply isotropicProjector s b E H (fun z => hadj z) x hx
  change x ⬝ᵥ (H.val *ᵥ x) = 0
  rw [← Matrix.toLinearMap₂'_apply', ← hpolar, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, hxx, smul_zero]

private theorem tensorMap_injective {k A : Type u} [Field k] [Ring A] [Algebra k A]
    {R S : TestAlgebra k} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (SymplecticIsometryDescent.tensorMap (A := A) f) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := A) f.hom.toLinearMap hf

private theorem spinCocharacterOfProjector {k K I F : Type u} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] [Field F] [Algebra k F]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup k} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D) (h₂ : (2 : k) ≠ 0)
    {e : F ⊗[k] ρ.fixedSubalgebra} (he₀ : e ≠ 0)
    (he : IsOrthogonalProjector (D.involution.baseChange F) e)
    (t : Fˣ) (ht : (t : F) ^ 16 ≠ 1) :
    ∃ c : Cocharacter ((groupBaseChange k F).obj G.val), c ≠ 0 := by
  classical
  let G' := (groupBaseChange k F).obj G.val
  let gm := specGroup (groupAlgebra F IntegerCharacters)
  let T := restrictTestAlgebra k F
  obtain ⟨g, hg, hgn⟩ := spinScaling M h₂
  let e' (R : TestAlgebra F) : (T.obj R) ⊗[k] ρ.fixedSubalgebra := liftProjector R e
  have he' (R : TestAlgebra F) :
      IsOrthogonalProjector (D.involution.baseChange (T.obj R)) (e' R) := by
    rcases he with ⟨hee, heσ, hσe⟩
    refine ⟨?_, ?_, ?_⟩
    · change e' R * e' R = e' R
      simpa only [e', liftProjector, map_mul] using congrArg
        (SymplecticIsometryDescent.tensorMap (SymplecticIsometryDescent.coefficientHom (k := k) R)) hee
    · change e' R * (D.involution.baseChange (T.obj R)).toLinearMap (e' R) = 0
      rw [show (D.involution.baseChange (T.obj R)).toLinearMap (e' R) =
        liftProjector R ((D.involution.baseChange F).toLinearMap e) from liftProjector_involution D.involution R e]
      simpa only [e', liftProjector, map_mul, map_zero] using congrArg
        (SymplecticIsometryDescent.tensorMap (SymplecticIsometryDescent.coefficientHom (k := k) R)) heσ
    · change (D.involution.baseChange (T.obj R)).toLinearMap (e' R) * e' R = 0
      rw [show (D.involution.baseChange (T.obj R)).toLinearMap (e' R) =
        liftProjector R ((D.involution.baseChange F).toLinearMap e) from liftProjector_involution D.involution R e]
      simpa only [e', liftProjector, map_mul, map_zero] using congrArg
        (SymplecticIsometryDescent.tensorMap (SymplecticIsometryDescent.coefficientHom (k := k) R)) hσe
  let α : (groupPointsFunctor F).obj gm ⟶ (groupPointsFunctor F).obj G' :=
    { app := fun R => GrpCat.ofHom
        (((baseChangePointGroupEquiv F G.val R).symm.toMonoidHom.comp (g (T.obj R) (he' R))).comp
          (unitEquiv R).toMonoidHom)
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        apply (baseChangePointGroupEquiv F G.val S).injective
        change (baseChangePointGroupEquiv F G.val S)
          ((baseChangePointGroupEquiv F G.val S).symm (g (T.obj S) (he' S) (unitEquiv S (mapPoints a x)))) =
          baseChangePoint k F G.val.X S (mapPoints a
            ((baseChangePointGroupEquiv F G.val R).symm (g (T.obj R) (he' R) (unitEquiv R x))))
        rw [MulEquiv.apply_symm_apply]
        rw [baseChangePointsNaturality (k := k) (K := F) (X := G.val.X) a]
        change g (T.obj S) (he' S) (unitEquiv S (mapPoints a x)) =
          mapPoints (T.map a) ((baseChangePointGroupEquiv F G.val R)
            ((baseChangePointGroupEquiv F G.val R).symm (g (T.obj R) (he' R) (unitEquiv R x))))
        rw [MulEquiv.apply_symm_apply, hgn (T.obj R) (T.obj S) (T.map a)
          (he' R) (he' S) (liftProjector_natural R S a e)]
        have hx : unitPoint R (unitEquiv R x) = x :=
          (unitEquiv R).injective (unitEquiv_unitPoint R _)
        conv_lhs => rw [← hx, mapPoints_unitPoint, unitEquiv_unitPoint]
        rfl }
  have hgm : IsAffine gm.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters))))
  obtain ⟨c, hc⟩ := (groupHomComparison F gm G' hgm).surjective α
  refine ⟨c, ?_⟩
  intro hzero
  let R := CommAlgCat.of F F
  have hzeroPoint : α.app R (unitPoint R t) = 1 := by
    rw [← hc, hzero]
    change unitPoint R t ≫ (1 : gm.X ⟶ G'.X) = 1
    exact MonObj.comp_one _
  have hz : g (T.obj R) (he' R) t = 1 := by
    have hy := congrArg (baseChangePointGroupEquiv F G.val R) hzeroPoint
    change (baseChangePointGroupEquiv F G.val R)
      ((baseChangePointGroupEquiv F G.val R).symm
        (g (T.obj R) (he' R) (unitEquiv R (unitPoint R t)))) =
      (baseChangePointGroupEquiv F G.val R) 1 at hy
    simpa only [MulEquiv.apply_symm_apply, map_one, unitEquiv_unitPoint] using hy
  have hv := hg (T.obj R) (e' R) (he' R) t
  rw [hz, vectorPoint, MonObj.one_comp, map_one] at hv
  let f := SymplecticIsometryDescent.coefficientHom (k := k) R
  let scalarMap := (SymplecticIsometryDescent.tensorMap (A := ρ.fixedSubalgebra) f).toMonoidHom
  have hinj : Function.Injective scalarMap :=
    tensorMap_injective f (fun _ _ h => h)
  have ht' : Units.map f.hom.toMonoidHom (t ^ 16) = t ^ 16 := Units.ext rfl
  have hz' := projectorUnits_tensorMap (D := D) f he (he' R) rfl (t ^ 16)
  rw [ht'] at hz'
  have hv' : (1 : (F ⊗[k] ρ.fixedSubalgebra)ˣ) = projectorUnits he (t ^ 16) := by
    apply Units.ext
    apply hinj
    have hh := hv.trans hz'.symm
    have hh' := congrArg Units.val hh
    simpa only [Units.val_one, Units.coe_map, map_one] using hh'
  have hcoef := congrArg (fun w : (F ⊗[k] ρ.fixedSubalgebra)ˣ => w.val * e) hv'
  change 1 * e =
    diagonalValue e ((D.involution.baseChange F).toLinearMap e) (t ^ 16) * e at hcoef
  rw [diagonalValue_mul_projector he.1 he.2.2, one_mul] at hcoef
  let z : F := ↑(t ^ 16)
  change e = z • e at hcoef
  have hz1 : z = 1 := by
    have h : z • e = (1 : F) • e := hcoef.symm.trans (one_smul F _).symm
    exact smul_left_injective F he₀ h
  exact ht (by simpa [z] using hz1)

/-- Every finite factor in characteristic different from two has positive split rank. -/
theorem finiteSpinIsotropy : FiniteSpinIsotropy.{u} := by
  classical
  intro k K I _ _ _ _ _ ρ G D M hn ho F _ _ _ _ _ h₂
  let A := F ⊗[k] ρ.fixedSubalgebra
  let σ := D.involution.baseChange F
  let s := toDivisionInvolution σ
  have hs : IsOrthogonal s := scalarExtendOrthogonal (F := F) D.involution ho
  have hk2 : (2 : k) ≠ 0 := fun h => h₂ (by simpa only [map_ofNat, map_zero] using congrArg (algebraMap k F) h)
  have hA : _root_.Specs.RM03.CSA.isCentralSimple F A :=
    _root_.RM03.CSA.isCentralSimple_baseChange D.centralSimple
  have hdeg : _root_.Specs.RM03.CSA.degree F A = 2 * Fintype.card I :=
    (congrArg Nat.sqrt (_root_.RM03.CSA.finrank_baseChange (L := F) D.centralSimple)).trans D.degree
  have hp : ∃ p : A, p ≠ 0 ∧ p * p = p ∧ σ.toLinearMap p * p = 0 := by
    rcases finiteModelIsotropy h₂ hA (Fintype.card I)
      hn hdeg s hs with h | h
    · obtain ⟨r, E, H, q, _, _, hpolar, _, hadj, hi⟩ := h
      exact scalarIsotropicProjector σ E H q hadj hpolar hi
    · obtain ⟨B, _, _, _, r, E, b, H, h, _, _, _, _, hadj, hvalue, ⟨x, y, hx, hxx, _⟩⟩ := h
      exact isotropicProjector σ b E H hadj x hx (by rw [← hvalue]; exact hxx)
  obtain ⟨p, hp₀, hpp, hσp⟩ := hp
  obtain ⟨e, he₀, hee, heσ, hσe⟩ := orthogonalProjectors σ h₂ hp₀ hpp hσp
  obtain ⟨a, ha, hval⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation F)
  refine spinCocharacterOfProjector M hk2 he₀ ⟨hee, heσ, hσe⟩ (Units.mk0 a ha) ?_
  intro h
  have hh := pow_lt_one₀ (show 0 ≤ ValuativeRel.valuation F a from zero_le) hval (by decide : (16 : ℕ) ≠ 0)
  rw [← map_pow, show a ^ 16 = 1 from h, map_one] at hh
  exact hh.false

end FiniteSpin

section RealSpin

open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinIsotropy
open LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic)
open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision degree)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn asMatrix)
open private matrixPresentation continuous_glEvaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private scalarMatrixBaseChange matrixBaseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open Opposite Topology

set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false

private theorem isTopologicalRing_of_realEquiv {F : Type u} [Field F] (R : F ≃+* ℝ) :
    letI : TopologicalSpace F := TopologicalSpace.induced R inferInstance
    IsTopologicalRing F := by
  letI : TopologicalSpace F := TopologicalSpace.induced R inferInstance
  have h : IsInducing R := ⟨rfl⟩
  refine { continuous_add := ?_, continuous_mul := ?_, continuous_neg := ?_ }
  · apply h.continuous_iff.mpr
    change Continuous (fun p : F × F => R (p.1 + p.2))
    simp only [map_add]
    exact (h.continuous.comp continuous_fst).add (h.continuous.comp continuous_snd)
  · apply h.continuous_iff.mpr
    change Continuous (fun p : F × F => R (p.1 * p.2))
    simp only [map_mul]
    exact (h.continuous.comp continuous_fst).mul (h.continuous.comp continuous_snd)
  · apply h.continuous_iff.mpr
    change Continuous (fun x : F => R (-x))
    simp only [map_neg]
    exact h.continuous.neg

section

variable {k K I F : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  [Field F] [Algebra k F] {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup k} {D : DescendedQuadraticPair ρ}

private theorem continuous_vectorPoint_linear [TopologicalSpace F] [IsTopologicalRing F]
    (M : SpinModel G D) (i : MatrixRealization G)
    (ℓ : (F ⊗[k] ρ.fixedSubalgebra) →ₗ[F] F) :
    Continuous (fun g : PointsIn i F => ℓ (vectorPoint M (CommAlgCat.of k F) g).val) := by
  classical
  let : FiniteDimensional k ρ.fixedSubalgebra := D.centralSimple.2.2
  let b := Module.finBasis k ρ.fixedSubalgebra
  obtain ⟨C, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.property.1
  obtain ⟨a, ha, hm⟩ := matrixPresentation C.unop e i
  let R := CommAlgCat.of k F
  let evaluate : PointsIn i F → (C.unop ⟶ R) := fun g => coordinateMap (k := k) (g ≫ e.inv)
  let z := (vectorPoint M C.unop e.hom).val
  have heval (g : PointsIn i F) : g = mapPoints (evaluate g) e.hom := by
    have heq : (testSpec k).map (evaluate g).op = g ≫ e.inv := coordinateMap_spec _
    change g = (testSpec k).map (evaluate g).op ≫ e.hom
    rw [heq]
    simp
  have hval (g : PointsIn i F) :
      (vectorPoint M R g).val = SymplecticIsometryDescent.tensorMap (evaluate g) z := by
    conv_lhs => rw [heval g]
    change (M.fullPoints R (mapPoints (evaluate g)
      (e.hom ≫ M.projection.hom.hom ≫ M.inclusion.hom.hom))).val = _
    rw [M.fullNatural]
    rfl
  have hrepr (g : PointsIn i F) :
      ℓ (vectorPoint M R g).val =
        ∑ j, (evaluate g).hom ((b.baseChange C.unop).repr z j) * ℓ (1 ⊗ₜ[k] b j) := by
    conv_lhs => rw [hval g, ← (b.baseChange C.unop).sum_repr z, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    let c := (evaluate g).hom ((b.baseChange C.unop).repr z j)
    change ℓ (c ⊗ₜ[k] b j) = c * ℓ (1 ⊗ₜ[k] b j)
    have heq : c ⊗ₜ[k] b j = c • ((1 : F) ⊗ₜ[k] b j) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [heq, map_smul, smul_eq_mul]
  change Continuous (fun g : PointsIn i F => ℓ (vectorPoint M R g).val)
  rw [funext hrepr]
  refine continuous_finsetSum _ fun j _ => Continuous.mul_const ?_ _
  obtain ⟨c, hc⟩ := ha ((b.baseChange C.unop).repr z j)
  have hex (g : PointsIn i F) :
      (evaluate g).hom ((b.baseChange C.unop).repr z j) = glEvaluation (asMatrix i F g) c := by
    have h := DFunLike.congr_fun (hm F g) c
    change glEvaluation (asMatrix i F g) c = (evaluate g).hom (a.hom c) at h
    rw [hc] at h
    exact h.symm
  simp_rw [hex]
  exact (continuous_glEvaluation c).comp continuous_induced_dom

private theorem noOrthogonalProjector_of_compact
    (M : SpinModel G D) (h₂ : (2 : k) ≠ 0)
    (R : F ≃+* ℝ) (i : MatrixRealization G) :
    letI : TopologicalSpace F := TopologicalSpace.induced R inferInstance
    IsCompact (Set.univ : Set (PointsIn i F)) →
      ∀ {e : F ⊗[k] ρ.fixedSubalgebra},
        IsOrthogonalProjector (D.involution.baseChange F) e → e = 0 := by
  letI : TopologicalSpace F := TopologicalSpace.induced R inferInstance
  letI : IsTopologicalRing F := isTopologicalRing_of_realEquiv R
  intro hc e he
  by_contra he₀
  classical
  obtain ⟨d, b, _⟩ := M.reducedNormOne h₂
  let β := b.baseChange F
  obtain ⟨j, hj⟩ : ∃ j, β.repr e j ≠ 0 := by
    by_contra! h
    apply he₀
    apply β.repr.injective
    ext i
    simpa using h i
  let l : (F ⊗[k] ρ.fixedSubalgebra) →ₗ[F] F := (β.repr e j)⁻¹ • β.coord j
  have hl : l e = 1 := inv_mul_cancel₀ hj
  let ℓ := l.comp (LinearMap.mulRight F e)
  let f (g : PointsIn i F) := R (ℓ (vectorPoint M (CommAlgCat.of k F) g).val)
  have hfc : Continuous f :=
    (show Continuous R from continuous_induced_dom).comp (continuous_vectorPoint_linear M i ℓ)
  obtain ⟨m, hm⟩ := (hc.image hfc).bddAbove
  let t₀ := max (m + 1) (2 : ℝ)
  have h₁ : 1 ≤ t₀ := le_trans (by norm_num) (le_max_right _ _)
  have ht₀ : t₀ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h₁)
  let t : Fˣ := Units.mk0 (R.symm t₀) (fun hh => ht₀ (by simpa using congrArg R hh))
  obtain ⟨g, hg, _⟩ := spinScaling M h₂
  let p : PointsIn i F := g (CommAlgCat.of k F) he t
  have hp : f p = t₀ ^ 16 := by
    change R (l ((vectorPoint M (CommAlgCat.of k F) p).val * e)) = _
    rw [hg (CommAlgCat.of k F) e he t]
    change R (l (diagonalValue e ((D.involution.baseChange F).toLinearMap e) (t ^ 16) * e)) = _
    rw [diagonalValue_mul_projector he.1 he.2.2, map_smul, hl, smul_eq_mul, mul_one]
    simp [t, Units.val_pow_eq_pow_val]
  have hle : f p ≤ m := hm ⟨p, Set.mem_univ p, rfl⟩
  rw [hp] at hle
  apply (not_lt_of_ge hle)
  calc
    m < t₀ := lt_of_lt_of_le (lt_add_one m) (le_max_left _ _)
    _ ≤ t₀ ^ 16 := by
      simpa only [pow_one] using pow_le_pow_right₀ h₁ (by decide : (1 : ℕ) ≤ 16)

end

private theorem definite_of_real_anisotropic {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
    (R : F ≃+* ℝ) (q : QuadraticForm F V) (hq : ¬ IsIsotropic q) :
    (∀ x, x ≠ 0 → 0 < R (q x)) ∨ (∀ x, x ≠ 0 → R (q x) < 0) := by
  have hnone (x : V) (hx : x ≠ 0) : R (q x) ≠ 0 := by
    intro h0
    exact hq ⟨x, hx, R.injective (by simpa only [map_zero] using h0)⟩
  by_cases hpos : ∀ x, x ≠ 0 → 0 < R (q x)
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨y, hy, hy'⟩ := hpos
    have hny : R (q y) < 0 := lt_of_le_of_ne hy' (hnone y hy)
    intro x hx
    by_contra! hnx
    have hpx : 0 < R (q x) := lt_of_le_of_ne hnx (Ne.symm (hnone x hx))
    obtain ⟨p, hp⟩ := q.exists_companion
    let f (t : ℝ) := R (q (R.symm (1 - t) • x + R.symm t • y))
    have hformula (t : ℝ) :
        f t = (1 - t) ^ 2 * R (q x) + t ^ 2 * R (q y) +
          ((1 - t) * t) * R (p x y) := by
      dsimp [f]
      rw [hp, q.map_smul, q.map_smul, LinearMap.map_smul₂, map_smul]
      simp only [smul_eq_mul, map_add, map_mul, R.apply_symm_apply, pow_two]
      ring
    have hf : Continuous f := by
      rw [funext hformula]
      fun_prop
    have hz : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
      simpa [f] using And.intro hny.le hpx.le
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf.continuousOn hz
    let a := R.symm (1 - t)
    let b := R.symm t
    have hzero : q (a • x + b • y) = 0 := R.injective (by simpa only [map_zero] using ht)
    have hv : a • x + b • y = 0 := by
      by_contra hn
      exact hq ⟨_, hn, hzero⟩
    have hb : b ≠ 0 := by
      intro h
      have ht0 : t = 0 := R.symm.injective (by simpa only [map_zero] using h)
      exact hx (by simpa [a, b, ht0] using hv)
    have hby : b • y = -(a • x) := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hv)
    have hv' := congrArg (fun z : V => b⁻¹ • z) hby
    change b⁻¹ • (b • y) = b⁻¹ • (-(a • x)) at hv'
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul, smul_neg, smul_smul] at hv'
    have heq := congrArg (fun z : V => R (q z)) hv'
    change R (q y) = R (q (-((b⁻¹ * a) • x))) at heq
    rw [q.map_neg, q.map_smul, smul_eq_mul, map_mul, map_mul] at heq
    rw [heq] at hny
    exact (mul_nonneg (mul_self_nonneg _) hpx.le).not_gt hny

/-- At a compact real factor the descended algebra is split and its form is definite. -/
theorem compactRealModel : CompactRealModel.{u} := by
  classical
  intro k K I _ _ _ _ _ ρ G D M hn ho F _ _ R i hc
  letI : Algebra F ℝ := R.toRingHom.toAlgebra
  letI : Algebra ℝ F := R.symm.toRingHom.toAlgebra
  let A := F ⊗[k] ρ.fixedSubalgebra
  let AF := ℝ ⊗[F] A
  let σ := D.involution.baseChange F
  let s := toDivisionInvolution σ
  have hs : IsOrthogonal s := scalarExtendOrthogonal (F := F) D.involution ho
  have h₂ : (2 : F) ≠ 0 := fun h =>
    (by norm_num : (2 : ℝ) ≠ 0) (by simpa only [map_ofNat, map_zero] using congrArg R h)
  have hk₂ : (2 : k) ≠ 0 := fun h => h₂ (by simpa only [map_ofNat, map_zero] using congrArg (algebraMap k F) h)
  have hA : isCentralSimple F A := _root_.RM03.CSA.isCentralSimple_baseChange D.centralSimple
  have hdeg : degree F A = 2 * Fintype.card I :=
    (congrArg Nat.sqrt (_root_.RM03.CSA.finrank_baseChange (L := F) D.centralSimple)).trans D.degree
  have hAF : isCentralSimple ℝ AF := _root_.RM03.CSA.isCentralSimple_baseChange hA
  have hno : ¬ ∃ p : A, p ≠ 0 ∧ p * p = p ∧ σ.toLinearMap p * p = 0 := by
    rintro ⟨p, hp, hpp, hσp⟩
    obtain ⟨e, he, hee, heσ, hσe⟩ := orthogonalProjectors σ h₂ hp hpp hσp
    exact he (noOrthogonalProjector_of_compact M hk₂ R i hc ⟨hee, heσ, hσe⟩)
  obtain ⟨r, hr, h | h⟩ := NontrialitarianSpinModels.archimedeanDivision.1 hAF
  · obtain ⟨E⟩ := h
    let e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F :=
      (transferFieldPresentation R E).trans (scalarMatrixBaseChange (F := ℝ) (R := F) (Fin r))
    have hsize : r = 2 * Fintype.card I := by
      have hdF : degree F F = 1 := by change Nat.sqrt (Module.finrank F F) = 1; simp
      have hdim := _root_.RM03.CSA.degree_matrix_division hA
        (show isCentralDivision F F from ⟨inferInstance, inferInstance⟩) hr e
      change degree F A = r * degree F F at hdim
      simpa only [hdeg, hdF, mul_one] using hdim.symm
    obtain ⟨H, q, hsymm, hpolar, hreg, hadj⟩ := NontrialitarianSpinModels.fieldOrthogonalModel r h₂ hA s hs e
    refine ⟨r, e, H, q, hsize, hsymm, hpolar, hreg, hadj, definite_of_real_anisotropic R q ?_⟩
    intro hq
    exact hno (scalarIsotropicProjector σ e H q hadj hpolar hq)
  · obtain ⟨E⟩ := h
    let B := F ⊗[ℝ] Quaternion ℝ
    letI : DivisionRing B := divisionRingOfEquiv (cancelFieldEquiv R.symm).toRingEquiv
    have hH : isCentralSimple ℝ (Quaternion ℝ) := _root_.RM03.CSA.isCentralSimple_of_isCentralDivision
      ℝ (Quaternion ℝ) _root_.RM03.Brauer.QuaternionSplitting.hamilton_central_division
    have hB : isCentralSimple F B := _root_.RM03.CSA.isCentralSimple_baseChange hH
    have hdB : degree F B = 2 := by
      change Nat.sqrt (Module.finrank F B) = 2
      rw [_root_.RM03.CSA.finrank_baseChange hH, Quaternion.finrank_eq_four]
      exact Nat.sqrt_eq' 2
    let e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B :=
      (transferFieldPresentation R E).trans (matrixBaseChange (F := ℝ) (R := F) (Fin r))
    have hsize : r = Fintype.card I := by
      have hd := _root_.RM03.CSA.degree_matrix_division hA hB.2 hr e
      change degree F A = r * degree F B at hd
      rw [hdeg, hdB] at hd
      omega
    obtain ⟨b, H, hb, _, hadj, ⟨h, hh⟩, _, _⟩ := NontrialitarianSpinModels.quaternionSkewModel r h₂ hA s hs hB hdB e
    have hlines : PureLine b :=
      pureLine_of_unique b (hB := hB) hb h₂ (fun C _ _ hC hdC => realDivisionPresentation R hC hdC)
    have hdim : 4 ≤ Module.finrank Bᵐᵒᵖ (Fin r → B) := by
      simpa [rightColumn_finrank, hsize] using hn
    obtain ⟨x, hx, hxx⟩ := skew_isotropy_of_pureLine h (hB := hB) hdB h₂ hlines hdim
    exact (hno (isotropicProjector σ b e H hadj x hx (by rw [← hh]; exact hxx))).elim

end RealSpin

end

end SpinComparison

end LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
