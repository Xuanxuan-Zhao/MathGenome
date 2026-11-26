import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicTypeC
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

open MulOpposite
open scoped TensorProduct Matrix

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.IsotropicTypeC

open LinearAlgebraicGroups.Specs.IsotropicTypeC
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels
open LocalDivisionNormTraceReduction (reducedTrace)
open _root_.Specs.RM03.CSA (isCentralSimple degree)

variable {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]

local notation "ι" => algebraMap F B

@[simp] private theorem conjugate_zero (s : AntiAutomorphism F B) :
    conjugate s 0 = 0 := by simp [conjugate]

@[simp] private theorem conjugate_one (s : AntiAutomorphism F B) :
    conjugate s 1 = 1 := by simp [conjugate]

@[simp] private theorem conjugate_add (s : AntiAutomorphism F B) (x y : B) :
    conjugate s (x + y) = conjugate s x + conjugate s y := by simp [conjugate]

@[simp] private theorem conjugate_sub (s : AntiAutomorphism F B) (x y : B) :
    conjugate s (x - y) = conjugate s x - conjugate s y := by simp [conjugate]

@[simp] private theorem conjugate_neg (s : AntiAutomorphism F B) (x : B) :
    conjugate s (-x) = -conjugate s x := by simp [conjugate]

@[simp] private theorem conjugate_mul (s : AntiAutomorphism F B) (x y : B) :
    conjugate s (x * y) = conjugate s y * conjugate s x := by simp [conjugate]

@[simp] private theorem conjugate_scalar (s : AntiAutomorphism F B) (x : F) :
    conjugate s (ι x) = ι x := by simp [conjugate, s.commutes]

private theorem conjugate_ne_zero (s : AntiAutomorphism F B) {x : B} (hx : x ≠ 0) :
    conjugate s x ≠ 0 := by
  intro h
  apply hx
  exact s.injective (unop_injective (h.trans (conjugate_zero s).symm))

private theorem eq_inv_of_mul (x y : B) (h : x * y = 1) : y = x⁻¹ := by
  have hx : x ≠ 0 := fun hx => by simp [hx] at h
  calc
    y = x⁻¹ * (x * y) := by rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
    _ = x⁻¹ := by rw [h, mul_one]

@[simp] private theorem conjugate_inv (s : AntiAutomorphism F B) (x : B) :
    conjugate s x⁻¹ = (conjugate s x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  apply eq_inv_of_mul
  rw [← conjugate_mul, inv_mul_cancel₀ hx, conjugate_one]

private theorem trace_eq (hB : isCentralSimple F B) (s : AntiAutomorphism F B)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x) (x : B) :
    x + conjugate s x = ι (reducedTrace hB x) := by
  rw [hs, quaternionConjugate]
  abel

private noncomputable def traceLinear (hB : isCentralSimple F B) (s : AntiAutomorphism F B)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x) : B →ₗ[F] F where
  toFun := reducedTrace hB
  map_add' x y := by
    apply (algebraMap F B).injective
    rw [map_add, ← trace_eq hB s hs, ← trace_eq hB s hs, ← trace_eq hB s hs, conjugate_add]
    abel
  map_smul' d x := by
    apply (algebraMap F B).injective
    change ι (reducedTrace hB (d • x)) = ι (d * reducedTrace hB x)
    rw [map_mul, ← trace_eq hB s hs, ← trace_eq hB s hs, Algebra.smul_def,
      conjugate_mul, conjugate_scalar, mul_add, Algebra.commutes d (conjugate s x)]

private theorem conjugate_involutive (hB : isCentralSimple F B) (s : AntiAutomorphism F B)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x) (x : B) :
    conjugate s (conjugate s x) = x := by
  conv_lhs => rw [hs x, quaternionConjugate, conjugate_sub, conjugate_scalar, hs x,
    quaternionConjugate]
  abel

open private split_quaternion_conjugate from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

private theorem norm_scalar (hB : isCentralSimple F B) (hd : degree F B = 2)
    (s : AntiAutomorphism F B) (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (x : B) :
    x * conjugate s x = ι (_root_.Specs.RM03.CSA.reducedNorm hB x) ∧
      conjugate s x * x = ι (_root_.Specs.RM03.CSA.reducedNorm hB x) := by
  let L := AlgebraicClosure F
  have hd' : RM03.CSA.degree F B = 2 := hd
  have hnmap (e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) :
      algebraMap F L (_root_.Specs.RM03.CSA.reducedNorm hB x) =
        (e (1 ⊗ₜ[F] x)).det := by
    revert e
    rw [← hd']
    exact fun e => RM03.CSA.reducedNorm_map hB x e
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hB
  let e₂ : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L := hd' ▸ e
  let T : B →ₐ[F] Matrix (Fin 2) (Fin 2) L :=
    (e₂.restrictScalars F).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hT : Function.Injective T :=
    e₂.injective.comp (Algebra.TensorProduct.includeRight_injective
      (B := B) (algebraMap F L).injective)
  have hbar : T (conjugate s x) = (T x).adjugate := by
    rw [hs]
    exact split_quaternion_conjugate hB hd e₂ x
  have hn : algebraMap F L (_root_.Specs.RM03.CSA.reducedNorm hB x) = (T x).det :=
    hnmap e₂
  have hscalar : T (ι (_root_.Specs.RM03.CSA.reducedNorm hB x)) =
      (T x).det • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [T.commutes, IsScalarTower.algebraMap_apply F L (Matrix (Fin 2) (Fin 2) L), hn,
      Algebra.algebraMap_eq_smul_one]
  constructor <;> apply hT <;> rw [map_mul, hbar, hscalar]
  · exact Matrix.mul_adjugate _
  · exact Matrix.adjugate_mul _

private theorem normOne_quotient_conjugate (hB : isCentralSimple F B) (hd : degree F B = 2)
    (s : AntiAutomorphism F B) (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (a : B) (ha : a ≠ 0) :
    (a * (conjugate s a)⁻¹) * conjugate s (a * (conjugate s a)⁻¹) = 1 := by
  rw [conjugate_mul, conjugate_inv, conjugate_involutive hB s hs]
  have hcomm : Commute a (conjugate s a) :=
    (norm_scalar hB hd s hs a).1.trans (norm_scalar hB hd s hs a).2.symm
  rw [mul_assoc, ← mul_assoc ((conjugate s a)⁻¹), hcomm.inv_right₀.inv_left₀.eq.symm,
    mul_assoc a⁻¹, inv_mul_cancel₀ (conjugate_ne_zero s ha), mul_one, mul_inv_cancel₀ ha]

theorem shearIsometries : ShearIsometries.{u,v} := by
  intro F B _ _ _ s hs q a b hab
  let Q := algebraMap F B (↑q⁻¹ : F)
  let q₀ := algebraMap F B (q : F)
  let w : Matrix (Fin 3) (Fin 3) B := !![0, 0, 1; 0, -1, 0; 1, 0, 0]
  have hQeq : algebraMap F B ((q : F)⁻¹) = Q :=
    congrArg (algebraMap F B) (Units.val_inv_eq_inv_val q).symm
  have hqeq : algebraMap F B (q : F) = q₀ := rfl
  have hQQ : Q * q₀ = 1 := by
    change algebraMap F B (↑q⁻¹ : F) * algebraMap F B (q : F) = 1
    rw [← map_mul, Units.inv_mul, map_one]
  have hqQ : q₀ * Q = 1 := (Algebra.commutes (q : F) Q).trans hQQ
  have hcomm (x : B) : Q * x = x * Q := Algebra.commutes _ _
  have hbum : b + conjugate s b + a * (conjugate s a * Q) = 0 := by
    rw [← mul_assoc, show b + conjugate s b = -(a * conjugate s a * Q) from hab]
    abel
  have hu : IsUnit (upper s q a b) := by
    refine ⟨⟨upper s q a b, upper s q (-a) (conjugate s b), ?_, ?_⟩, rfl⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [upper, Matrix.mul_apply, Fin.sum_univ_three, hQeq, -map_inv₀]
    all_goals (convert hbum using 1; abel)
  have hadj : QuaternionHermitianCocharacters.adjoint s.toAlgHom (upper s q a b) =
      !![1, 0, 0; conjugate s a, 1, 0; conjugate s b, -(Q * a), 1] := by
    ext i j
    change conjugate s (upper s q a b j i) = _
    fin_cases i <;> fin_cases j <;> simp [upper, hQeq, -map_inv₀, hs a, Q]
  have hh : gram (B := B) q * upper s q a b =
      !![0, 0, 1; 0, q₀, -conjugate s a; 1, a, b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, upper, Matrix.mul_apply, Fin.sum_univ_three, hQeq, hqeq, -map_inv₀]
    rw [← hcomm (conjugate s a), ← mul_assoc, hqQ, one_mul]
  have hpres : QuaternionHermitianCocharacters.adjoint s.toAlgHom (upper s q a b) *
      gram q * upper s q a b = gram q := by
    rw [mul_assoc, hh, hadj]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_three, hqeq]
    · rw [hcomm a, mul_assoc, hQQ, mul_one, neg_add_cancel]
    · rw [hcomm a, mul_assoc, hcomm (conjugate s a)]
      convert hbum using 1; abel
  have hw : w * w = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w, Matrix.mul_apply, Fin.sum_univ_three]
  have hj : QuaternionHermitianCocharacters.adjoint s.toAlgHom w * gram q * w = gram q := by
    have hwa : QuaternionHermitianCocharacters.adjoint s.toAlgHom w = w := by
      ext i j
      change conjugate s (w j i) = _
      fin_cases i <;> fin_cases j <;> simp [w]
    rw [hwa]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gram, w, Matrix.mul_apply, Fin.sum_univ_three]
  have heq : lower s q a b = w * upper s q a b * w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower, upper, w, Matrix.mul_apply, Fin.sum_univ_three]
  have hw' : IsUnit w := ⟨⟨w, w, hw, hw⟩, rfl⟩
  refine ⟨hu, hpres, ?_, ?_⟩
  · rw [heq]
    exact (hw'.mul hu).mul hw'
  · rw [heq]
    let adj : Matrix (Fin 3) (Fin 3) B → Matrix (Fin 3) (Fin 3) B :=
      QuaternionHermitianCocharacters.adjoint s.toAlgHom
    have hmul (x y : Matrix (Fin 3) (Fin 3) B) : adj (x * y) = adj y * adj x :=
      QuaternionHermitianCocharacters.adjoint_mul s.toAlgHom x y
    change adj (w * upper s q a b * w) * gram q * (w * upper s q a b * w) = _
    rw [hmul, hmul]
    calc
      _ = adj w * (adj (upper s q a b) * (adj w * gram q * w) * upper s q a b) * w := by
        simp only [mul_assoc]
      _ = gram q := by rw [hj, hpres, hj]

theorem threeFactorInterchange : ThreeFactorInterchange.{u,v} := by
  intro F B _ _ _ hB _ s hs q a b hab hb
  let k := (conjugate s b)⁻¹
  let Q := algebraMap F B (↑q⁻¹ : F)
  let d := b⁻¹ * a
  let e := k * a
  have hQeq : algebraMap F B ((q : F)⁻¹) = Q := by simp only [Q, Units.val_inv_eq_inv_val]
  have hk : conjugate s b ≠ 0 := conjugate_ne_zero s hb
  have hkb : k * conjugate s b = 1 := inv_mul_cancel₀ hk
  have hbk : conjugate s b * k = 1 := mul_inv_cancel₀ hk
  have hbi : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  have hib : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  have hbQ (x : B) : Q * x = x * Q := Algebra.commutes _ x
  have hbarK : conjugate s k = b⁻¹ := by simp [k, conjugate_involutive hB s hs]
  have hbarD : conjugate s d = conjugate s a * k := by simp [d, k]
  have hbarE : conjugate s e = conjugate s a * b⁻¹ := by simp [e, hbarK]
  have hA : a * conjugate s a * Q = -(b + conjugate s b) := by
    exact (neg_eq_iff_eq_neg.mpr hab).symm
  have hAd (x y : B) :
      -(x * a * (conjugate s a * y) * Q) = x * (b + conjugate s b) * y := by
    calc
      _ = x * (-(a * conjugate s a * Q)) * y := by
        rw [mul_assoc (x * a) (conjugate s a * y) Q,
          mul_assoc (conjugate s a) y Q, ← hbQ y]
        noncomm_ring
      _ = _ := by rw [hA, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · change k + conjugate s k = -(e * conjugate s e * Q)
    rw [hbarK, hbarE, hAd]
    rw [mul_add, add_mul, mul_assoc k b, hbi, mul_one, hkb, one_mul]
  · change k + conjugate s k = -(d * conjugate s d * Q)
    rw [hbarK, hbarD, hAd]
    rw [mul_add, add_mul, hib, one_mul, mul_assoc b⁻¹, hbk, mul_one]
  change lower s q e k * upper s q a b * lower s q d k = _
  have h00 : 1 + a * (conjugate s a * k * Q) + b * k = 0 := by
    have heq : a * (conjugate s a * k * Q) = (a * conjugate s a * Q) * k := by
      rw [mul_assoc (conjugate s a) k Q, ← hbQ k]
      noncomm_ring
    rw [heq, hA, neg_mul, add_mul, hbk]
    abel
  have h01 : a + -(b * d) = 0 := by
    change a + -(b * (b⁻¹ * a)) = 0
    rw [← mul_assoc, hbi, one_mul, add_neg_cancel]
  have h11 : (conjugate s a * Q) * d = conjugate s a * b⁻¹ * a * Q := by
    rw [mul_assoc (conjugate s a), hbQ d, ← mul_assoc]
    change conjugate s a * (b⁻¹ * a) * Q = _
    rw [← mul_assoc]
  have hright : upper s q a b * lower s q d k =
      !![0, 0, b; 0, 1 + conjugate s a * b⁻¹ * a * Q, -(conjugate s a * Q); k, -d, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_three, hbarD, hQeq, -map_inv₀]
    · exact h00
    · exact h01
    · rw [mul_assoc (conjugate s a) k Q, ← hbQ k, ← mul_assoc, add_neg_cancel]
    · exact h11
  have h20 : e * (conjugate s a * Q) = -(k * b + 1) := by
    calc
      _ = k * (a * conjugate s a * Q) := by change (k * a) * _ = _; noncomm_ring
      _ = _ := by rw [hA, mul_neg, mul_add, hkb]
  have h21 : -(e * (1 + conjugate s a * b⁻¹ * a * Q)) + -d = 0 := by
    rw [mul_add, mul_one]
    have heq : e * (conjugate s a * b⁻¹ * a * Q) = k * (a * conjugate s a * Q) * b⁻¹ * a := by
      change (k * a) * _ = _
      simp only [mul_assoc]
      rw [← hbQ a, ← mul_assoc b⁻¹ Q a, ← hbQ b⁻¹, mul_assoc Q b⁻¹ a]
    rw [heq, hA, mul_neg, neg_mul, neg_mul, mul_add, add_mul, mul_assoc k b, hbi,
      mul_one, hkb, one_mul, add_mul]
    change -((k * a) + -(k * a + d)) + -d = 0
    abel
  rw [mul_assoc, hright]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, interchange, Matrix.mul_apply, Fin.sum_univ_three, hbarE, hQeq, -map_inv₀]
  · have heq : (conjugate s a * b⁻¹ * Q) * b = conjugate s a * Q := by
      rw [mul_assoc (conjugate s a * b⁻¹), hbQ b, ← mul_assoc, mul_assoc (conjugate s a),
        hib, mul_one]
    rw [heq, add_neg_cancel]
  · rfl
  · exact h21
  · rw [h20]
    abel

theorem traceZeroRatios : TraceZeroRatios.{u,v} := by
  intro F B _ _ _ hB hd t
  obtain ⟨s, hs, _, _, _⟩ :=
    SymplecticInvolutionModels.quaternionConjugation.{u,v,u} hB hd
  let tr := traceLinear hB s hs
  let m : B →ₗ[F] B :=
    { toFun := fun x => (t : B) * x
      map_add' := fun x y => mul_add _ _ _
      map_smul' := by
        intro d x
        change (t : B) * (d • x) = d • ((t : B) * x)
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc,
          (Algebra.commutes d (t : B)).symm, mul_assoc] }
  let f := tr.prod (tr.comp m)
  have hdim : Module.finrank F B = 4 := by
    rw [RM03.CSA.finrank_eq_degree_sq hB]
    rw [show RM03.CSA.degree F B = 2 from hd]
    rfl
  obtain ⟨c, hcz, hc⟩ : ∃ c : B, f c = 0 ∧ c ≠ 0 := by
    by_contra! h
    have hinj : Function.Injective f :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr h)
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hdim, Module.finrank_prod, Module.finrank_self] at hle
    omega
  let d := Units.mk0 c hc
  refine ⟨t * d, d, ?_, ?_, ?_⟩
  · exact congrArg Prod.snd hcz
  · exact congrArg Prod.fst hcz
  · simp

theorem normOneMiddleEntries : NormOneMiddleEntries.{u,v} := by
  intro F B _ _ _ hB hd s hs q r hr
  let Q := algebraMap F B (↑q⁻¹ : F)
  by_cases h : r = 1
  · obtain ⟨_, b, _, htr, _⟩ := traceZeroRatios hB hd (1 : Bˣ)
    refine ⟨0, b, Units.ne_zero b, ?_, ?_, fun _ => rfl⟩
    · change _ = -(0 * conjugate s 0 * Q)
      simp [trace_eq hB s hs, htr]
    · simp [interchange, h]
  · let x := 1 - r
    have hx : x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hQ : Q ≠ 0 := (map_ne_zero (algebraMap F B)).mpr (Units.ne_zero q⁻¹)
    let b := -(x⁻¹ * Q)
    have hb : b ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hx) hQ)
    have hbQ : Commute Q x := Algebra.commutes _ _
    have hxb : x * b = -Q := by
      dsimp only [b]
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    have hbx : b * x = -Q := by
      dsimp only [b]
      rw [neg_mul, mul_assoc, hbQ.eq, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
    have hbarx : conjugate s x * r = -x := by
      dsimp only [x]
      rw [conjugate_sub, conjugate_one, sub_mul, one_mul,
        eq_inv_of_mul _ _ hr, inv_mul_cancel₀]
      · abel
      · intro hzero
        simp [hzero] at hr
    have hbarb : conjugate s b = -(r * b) := by
      have heq := congrArg (conjugate s) hbx
      simp only [conjugate_mul, conjugate_neg] at heq
      rw [show conjugate s Q = Q from conjugate_scalar s _] at heq
      have hxbar := conjugate_ne_zero s hx
      apply mul_left_cancel₀ hxbar
      rw [heq, mul_neg, ← mul_assoc, hbarx, neg_mul, hxb, neg_neg]
    have hm : b⁻¹ * Q = -x := by
      apply mul_left_cancel₀ hb
      rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul, mul_neg, hbx, neg_neg]
    refine ⟨1, b, hb, ?_, ?_, fun hh => (h hh).elim⟩
    · change b + conjugate s b = -(1 * conjugate s 1 * Q)
      rw [conjugate_one, one_mul, hbarb, ← sub_eq_add_neg]
      exact (by simpa only [sub_mul, one_mul, x] using hxb)
    · change 1 + conjugate s 1 * b⁻¹ * 1 * Q = r
      rw [conjugate_one, one_mul, mul_one, hm]
      dsimp only [x]
      abel

theorem traceOnNormOne : TraceOnNormOne.{u,v} := by
  intro F B _ _ _ hB hd s hs c hc
  obtain ⟨_, _, _, _, hsurj⟩ :=
    SymplecticInvolutionModels.quaternionConjugation.{u,v,u} hB hd
  by_cases htrc : reducedTrace hB c = 0
  · obtain ⟨x, hx⟩ := hsurj 1
    obtain ⟨y, hy⟩ := hsurj 1
    let tr := traceLinear hB s hs
    let z := c⁻¹ * y
    have hcz : c * z = y := by simp [z, ← mul_assoc, mul_inv_cancel₀ hc]
    obtain ⟨b, htrb, htrcb⟩ : ∃ b : B, tr b ≠ 0 ∧ tr (c * b) ≠ 0 := by
      have hz : tr (c * z) ≠ 0 := by
        change reducedTrace hB (c * z) ≠ 0
        rw [hcz, hy]
        exact one_ne_zero
      have hx₁ : tr x ≠ 0 := by
        change reducedTrace hB x ≠ 0
        rw [hx]
        exact one_ne_zero
      by_cases hx₂ : tr (c * x) = 0
      · by_cases hz₁ : tr z = 0
        · refine ⟨x + z, ?_, ?_⟩
          · simpa [map_add, hz₁] using hx₁
          · simpa [mul_add, map_add, hx₂] using hz
        · exact ⟨z, hz₁, hz⟩
      · exact ⟨x, hx₁, hx₂⟩
    have hb : b ≠ 0 := fun hb => htrb (by simp [hb])
    have hbar : conjugate s b ≠ 0 := conjugate_ne_zero s hb
    let n := _root_.Specs.RM03.CSA.reducedNorm hB b
    have hn := (norm_scalar hB hd s hs b).1
    have hn₀ : n ≠ 0 := by
      intro h
      have hn' : b * conjugate s b = algebraMap F B n := hn
      rw [h, map_zero] at hn'
      exact (mul_ne_zero hb hbar) hn'
    let r := b * (conjugate s b)⁻¹
    have hrr : r * conjugate s r = 1 := normOne_quotient_conjugate hB hd s hs b hb
    refine ⟨r, hrr, ?_⟩
    have hscale : (conjugate s b)⁻¹ = b * algebraMap F B n⁻¹ := by
      apply (eq_inv_of_mul _ _ ?_).symm
      rw [← mul_assoc, (norm_scalar hB hd s hs b).2, ← map_mul, mul_inv_cancel₀ hn₀, map_one]
    have hlin : r = (reducedTrace hB b / n) • b - 1 := by
      dsimp [r]
      rw [hscale, ← mul_assoc, show b * b = algebraMap F B (reducedTrace hB b) * b - algebraMap F B n by
        rw [← trace_eq hB s hs, add_mul, (norm_scalar hB hd s hs b).2]
        simp [n]]
      rw [sub_mul, ← map_mul (algebraMap F B) n n⁻¹, mul_inv_cancel₀ hn₀, map_one, Algebra.smul_def,
        div_eq_mul_inv, map_mul, mul_assoc, ← Algebra.commutes n⁻¹ b, ← mul_assoc]
    change tr (c * r) ≠ 0
    rw [hlin, mul_sub, mul_one, Algebra.mul_smul_comm,
      map_sub, map_smul, show tr c = 0 from htrc, sub_zero, smul_eq_mul]
    exact mul_ne_zero (div_ne_zero htrb hn₀) htrcb
  · exact ⟨1, by simp, by simpa using htrc⟩

private theorem conjugate_eq_neg_of_traceZero (hB : isCentralSimple F B)
    (s : AntiAutomorphism F B) (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (b : B) (hb : reducedTrace hB b = 0) :
    conjugate s b = -b := by rw [hs, quaternionConjugate, hb, map_zero, zero_sub]

private theorem traceZero_of_conjugate_eq_neg (hB : isCentralSimple F B)
    (s : AntiAutomorphism F B) (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (b : B) (hb : conjugate s b = -b) :
    reducedTrace hB b = 0 := by
  apply (algebraMap F B).injective
  rw [← trace_eq hB s hs, hb, add_neg_cancel, map_zero]

private theorem planeInterchange_eq (b : B) (hb : b ≠ 0) :
    planeInterchange b = !![0, b; -b⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeInterchange, planeUpper, planeLower, Matrix.mul_apply, Fin.sum_univ_two,
      mul_inv_cancel₀ hb, inv_mul_cancel₀ hb]

theorem purePlaneWords : PurePlaneWords.{u,v} := by
  intro F B _ _ _ hB hd s hs
  have htr (b : B) (hb : reducedTrace hB b = 0) : reducedTrace hB (-b⁻¹) = 0 := by
    apply traceZero_of_conjugate_eq_neg hB s hs
    rw [conjugate_neg, conjugate_inv, conjugate_eq_neg_of_traceZero hB s hs b hb, inv_neg]
  refine ⟨fun b hb => ⟨htr b hb, ?_⟩, ?_⟩
  · rw [planeInterchange_eq _ (Units.ne_zero b),
      conjugate_eq_neg_of_traceZero hB s hs b hb, inv_neg]
  · intro t
    obtain ⟨b, c, hb, hc, ht⟩ := traceZeroRatios hB hd t
    refine ⟨b, c, hb, hc, ?_⟩
    have hbc : (t : B) = (b : B) * (c : B)⁻¹ := by
      rw [ht, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [planeInterchange_eq _ (Units.ne_zero b),
      planeInterchange_eq _ (neg_ne_zero.mpr (Units.ne_zero c)), inv_neg, neg_neg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hbc,
        conjugate_eq_neg_of_traceZero hB s hs b hb, conjugate_eq_neg_of_traceZero hB s hs c hc]

private theorem interchange_mem_words (hB : isCentralSimple F B) (hd : degree F B = 2)
    (s : AntiAutomorphism F B) (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (q : Fˣ) (a b : B) (hab : Admissible s q a b) (hb : b ≠ 0) :
    interchange s q a b ∈ radicalWords s q := by
  obtain ⟨h₁, h₂, heq⟩ := threeFactorInterchange hB hd s hs q a b hab hb
  rw [← heq]
  apply (radicalWords s q).mul_mem
  · exact (radicalWords s q).mul_mem
      (Submonoid.subset_closure ⟨_, _, h₁, Or.inr rfl⟩)
      (Submonoid.subset_closure ⟨_, _, hab, Or.inl rfl⟩)
  · exact Submonoid.subset_closure ⟨_, _, h₂, Or.inr rfl⟩

private theorem pureInterchange_mem_words (hB : isCentralSimple F B) (hd : degree F B = 2)
    (s : AntiAutomorphism F B) (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (q : Fˣ) (b : B) (hb : b ≠ 0) (hbtr : conjugate s b = -b) :
    interchange s q 0 b ∈ radicalWords s q := by
  apply interchange_mem_words hB hd s hs _ _ _ _ hb
  simp [Admissible, hbtr]

private theorem interchange_mul_pure (s : AntiAutomorphism F B) (q : Fˣ)
    (a b c : B) (hc : conjugate s c = -c) :
    interchange s q a b * interchange s q 0 (-c) =
      Matrix.diagonal ![b * c⁻¹, interchange s q a b 1 1,
        (conjugate s (b * c⁻¹))⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [interchange, Matrix.mul_apply, Fin.sum_univ_three, hc]

theorem lineAndPairScaleWords : LineAndPairScaleWords.{u,v} := by
  intro F B _ _ _ hB hd s hs q t r hr
  have hscale (t : Bˣ) :
      Matrix.diagonal ![(t : B), (1 : B), (conjugate s t)⁻¹] ∈ radicalWords s q := by
    obtain ⟨b, c, hb, hc, ht⟩ := traceZeroRatios hB hd t
    have hbc : (t : B) = (b : B) * (c : B)⁻¹ := by
      rw [ht, Units.val_mul, Units.val_inv_eq_inv_val]
    have hbp := conjugate_eq_neg_of_traceZero hB s hs b hb
    have hcp := conjugate_eq_neg_of_traceZero hB s hs c hc
    have hword := (radicalWords s q).mul_mem
      (pureInterchange_mem_words hB hd s hs q b (Units.ne_zero _) hbp)
      (pureInterchange_mem_words hB hd s hs q (-(c : B))
        (neg_ne_zero.mpr (Units.ne_zero _)) (by simp [hcp]))
    rw [interchange_mul_pure _ _ _ _ _ hcp, ← hbc] at hword
    simpa [interchange] using hword
  obtain ⟨a, b, hb, hab, hmiddle, _⟩ := normOneMiddleEntries hB hd s hs q r hr
  obtain ⟨_, c, _, hct, _⟩ := traceZeroRatios hB hd (1 : Bˣ)
  have hcp := conjugate_eq_neg_of_traceZero hB s hs c hct
  have hword := (radicalWords s q).mul_mem (interchange_mem_words hB hd s hs q a b hab hb)
    (pureInterchange_mem_words hB hd s hs q (-(c : B))
      (neg_ne_zero.mpr (Units.ne_zero _)) (by simp [hcp]))
  let T := Units.mk0 b hb * c⁻¹
  have hT : (T : B) = b * (c : B)⁻¹ := by simp [T]
  rw [interchange_mul_pure _ _ _ _ _ hcp, hmiddle, ← hT] at hword
  let U := t * T⁻¹
  have hprod : (U : B) * (T : B) = t := by
    rw [← Units.val_mul]
    simp [U]
  have hbar : (conjugate s U)⁻¹ * (conjugate s T)⁻¹ = (conjugate s t)⁻¹ := by
    symm
    rw [← hprod, conjugate_mul]
    symm
    apply eq_inv_of_mul
    rw [mul_assoc, ← mul_assoc (conjugate s U),
      mul_inv_cancel₀ (conjugate_ne_zero s (Units.ne_zero U)), one_mul,
      mul_inv_cancel₀ (conjugate_ne_zero s (Units.ne_zero T))]
  have hm := (radicalWords s q).mul_mem (hscale U) hword
  have heq : Matrix.diagonal ![(U : B), 1, (conjugate s U)⁻¹] *
      Matrix.diagonal ![(T : B), r, (conjugate s T)⁻¹] =
      Matrix.diagonal ![(t : B), r, (conjugate s t)⁻¹] := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hprod, hbar]
  rwa [heq] at hm

section Hermitian

variable {s : AntiAutomorphism F B}
  {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)

private theorem pairing_symm (x y : V) :
    h.value y x = conjugate s (h.value x y) := h.hermitian x y

private theorem pairing_zero_right (x : V) : h.value x 0 = 0 := by
  simpa using h.smul_right x (0 : V) (0 : B)

private theorem pairing_zero_left (x : V) : h.value 0 x = 0 := by
  rw [pairing_symm h, pairing_zero_right, conjugate_zero]

private theorem pairing_add_left (x y z : V) :
    h.value (x + y) z = h.value x z + h.value y z := by
  calc
    h.value (x + y) z = conjugate s (h.value z (x + y)) := pairing_symm h _ _
    _ = conjugate s (h.value z x) + conjugate s (h.value z y) := by
      rw [h.add_right, conjugate_add]
    _ = h.value x z + h.value y z := by rw [← pairing_symm h z x, ← pairing_symm h z y]

private theorem pairing_sub_right (x y z : V) :
    h.value x (y - z) = h.value x y - h.value x z := by
  have := h.add_right x (y - z) z
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

private theorem pairing_sub_left (x y z : V) :
    h.value (x - y) z = h.value x z - h.value y z := by
  calc
    _ = conjugate s (h.value z (x - y)) := pairing_symm h _ _
    _ = _ := by rw [pairing_sub_right, conjugate_sub, ← pairing_symm h z x, ← pairing_symm h z y]

private theorem pairing_smul_left (x y : V) (a : B) :
    h.value (op a • x) y = conjugate s a * h.value x y := by
  calc
    _ = conjugate s (h.value y (op a • x)) := pairing_symm h _ _
    _ = _ := by rw [h.smul_right, conjugate_mul, ← pairing_symm h y x]

private theorem pairing_smul_both (x y : V) (a b : B) :
    h.value (op a • x) (op b • y) = conjugate s a * h.value x y * b := by
  rw [h.smul_right, pairing_smul_left]

private theorem pairing_norm_smul (x : V) (r : B) (hr : r * conjugate s r = 1) :
    h.value (op r • x) (op r • x) = h.value x x := by
  have hr' : conjugate s r * r = 1 := by
    have hr₀ : r ≠ 0 := fun he => by simp [he] at hr
    rw [eq_inv_of_mul _ _ hr, inv_mul_cancel₀ hr₀]
  obtain ⟨q, hq⟩ := h.central_norm x
  rw [pairing_smul_both, hq, ← Algebra.commutes, mul_assoc, hr', mul_one]

private theorem exists_nonisotropic (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x) [Nontrivial V] :
    ∃ x : V, h.value x x ≠ 0 := by
  by_contra! hz
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ := h.nondegenerate x hx
  obtain ⟨_, _, _, _, htr⟩ :=
    SymplecticInvolutionModels.quaternionConjugation.{u,v,u} hB hd
  obtain ⟨b, hb⟩ := htr 1
  let z := op ((h.value x y)⁻¹ * b) • y
  have hxz : h.value x z = b := by
    change h.value x (op ((h.value x y)⁻¹ * b) • y) = b
    rw [h.smul_right, ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
  have hsum := hz (x + z)
  rw [h.add_right, pairing_add_left, pairing_add_left, hz x, hz z, hxz, zero_add,
    add_zero, pairing_symm h x z, hxz, add_comm (conjugate s b) b,
    trace_eq hB s hs, hb, map_one] at hsum
  exact one_ne_zero hsum

private theorem difference_norm (u v : V) (huv : h.value u u = h.value v v)
    {r : B} (hr : r * conjugate s r = 1) :
    h.value (u - op r • v) (u - op r • v) =
      h.value u u + h.value u u - (h.value u v * r + conjugate s (h.value u v * r)) := by
  have hnorm : h.value (op r • v) (op r • v) = h.value u u :=
    (pairing_norm_smul h v r hr).trans huv.symm
  rw [pairing_sub_left, pairing_sub_right, pairing_sub_right, hnorm,
    pairing_symm h u (op r • v), h.smul_right]
  abel

private theorem nonisotropic_difference (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (u v : V) (huv : h.value u u = h.value v v) (hu : h.value u u ≠ 0)
    (hn : (2 : B) ≠ 0 ∨ h.value u v ≠ 0) :
    ∃ r : B, r * conjugate s r = 1 ∧ h.value (u - op r • v) (u - op r • v) ≠ 0 := by
  have h₁ : (1 : B) * conjugate s 1 = 1 := by simp
  by_cases hdif : h.value (u - op (1 : B) • v) (u - op (1 : B) • v) ≠ 0
  · exact ⟨1, h₁, hdif⟩
  have heq := difference_norm h u v huv h₁
  rw [not_not.mp hdif, mul_one] at heq
  by_cases htwo : (2 : B) ≠ 0
  · have hneg : (-1 : B) * conjugate s (-1) = 1 := by simp
    refine ⟨-1, hneg, fun hz => ?_⟩
    have hnegEq := difference_norm h u v huv hneg
    rw [hz, mul_neg_one, conjugate_neg, ← neg_add, sub_neg_eq_add] at hnegEq
    have hsum := (congrArg₂ (· + ·) heq hnegEq).symm
    rw [zero_add] at hsum
    have hfour : (2 : B) * ((2 : B) * h.value u u) = 0 := by
      calc
        _ = _ := by
          symm
          exact (show
            h.value u u + h.value u u - (h.value u v + conjugate s (h.value u v)) +
              (h.value u u + h.value u u + (h.value u v + conjugate s (h.value u v))) =
              2 * (2 * h.value u u) by noncomm_ring)
        _ = 0 := hsum
    exact mul_ne_zero htwo (mul_ne_zero htwo hu) hfour
  · have hc := hn.resolve_left htwo
    obtain ⟨r, hr, htr⟩ := traceOnNormOne hB hd s hs (h.value u v) hc
    refine ⟨r, hr, ?_⟩
    rw [difference_norm h u v huv hr, ← two_mul, not_not.mp htwo, zero_mul, zero_sub,
      trace_eq hB s hs, neg_ne_zero]
    exact (map_ne_zero (algebraMap F B)).mpr htr

private theorem orthogonal_equal_norm_bridge [Infinite F] (u v : V)
    (huv : h.value u u = h.value v v) (hu : h.value u u ≠ 0)
    (hc : h.value u v = 0) (htwo : (2 : B) = 0) :
    ∃ w : V, h.value w w = h.value u u ∧ h.value u w ≠ 0 ∧ h.value w v ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset F)
  have ha₀ : a ≠ 0 := fun he => ha (by simp [he])
  have ha₁ : a ≠ 1 := fun he => ha (by simp [he])
  let A := algebraMap F B a
  let C := 1 + A
  have hA : A ≠ 0 := (map_ne_zero (algebraMap F B)).mpr ha₀
  have hC : C ≠ 0 := by
    intro hz
    have ha' : 1 + A = 0 := hz
    have hm : (1 : B) + 1 = 0 := by simpa only [one_add_one_eq_two] using htwo
    have he : A = 1 := add_left_cancel (ha'.trans hm.symm)
    apply ha₁
    apply (algebraMap F B).injective
    rw [map_one]
    exact he
  have hbarA : conjugate s A = A := conjugate_scalar s a
  have hbarC : conjugate s C = C := by simp [C, hbarA]
  have hvc : h.value v u = 0 := by rw [pairing_symm h u v, hc, conjugate_zero]
  let w := op A • u + op C • v
  refine ⟨w, ?_, ?_, ?_⟩
  · change h.value (op A • u + op C • v) (op A • u + op C • v) = h.value u u
    rw [h.add_right, pairing_add_left, pairing_add_left]
    simp only [pairing_smul_both, hbarA, hbarC, hvc, hc, mul_zero, zero_mul, zero_add,
      add_zero, ← huv]
    have hcomm : h.value u u * A = A * h.value u u := (Algebra.commutes a _).symm
    have hcc : A * A + C * C = 1 := by
      change A * A + (1 + A) * (1 + A) = 1
      calc
        _ = 1 + (2 : B) * (A + A * A) := by noncomm_ring
        _ = 1 := by simp [htwo]
    calc
      _ = (A * A + C * C) * h.value u u := by
        have hcommC : h.value u u * C = C * h.value u u := by
          change _ * (1 + A) = (1 + A) * _
          rw [mul_add, add_mul, mul_one, one_mul, hcomm]
        simp only [mul_assoc, hcomm, hcommC, add_mul]
      _ = _ := by rw [hcc, one_mul]
  · change h.value u (op A • u + op C • v) ≠ 0
    simp [h.add_right, h.smul_right, hc, hu, hA]
  · change h.value (op A • u + op C • v) v ≠ 0
    simp [pairing_add_left, pairing_smul_left, hc, ← huv, hu, hC, hbarC]

private def lineCoefficient (z : V) : V →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun x := op ((h.value z z)⁻¹ * h.value z x)
  map_add' x y := by
    change op (_ * h.value z (x + y)) = op (_ * h.value z x) + op (_ * h.value z y)
    rw [h.add_right, mul_add, op_add]
  map_smul' a x := by
    change op (_ * h.value z (op (unop a) • x)) =
      op (_ * h.value z x * unop a)
    rw [h.smul_right, mul_assoc]

private theorem lineCoefficient_self (z : V) (hz : h.value z z ≠ 0) :
    lineCoefficient h z z = 1 := by
  change op ((h.value z z)⁻¹ * h.value z z) = 1
  rw [inv_mul_cancel₀ hz, op_one]

private def linePerp (z : V) : Submodule Bᵐᵒᵖ V := (lineCoefficient h z).ker

private theorem mem_linePerp_iff (z : V) (hz : h.value z z ≠ 0) (x : V) :
    x ∈ linePerp h z ↔ h.value z x = 0 := by
  change op ((h.value z z)⁻¹ * h.value z x) = 0 ↔ _
  rw [← op_zero, op_inj, mul_eq_zero, or_iff_right (inv_ne_zero hz)]

private def linePerpPairing (z : V) (hz : h.value z z ≠ 0) :
    HermitianPairing s (linePerp h z) where
  value x y := h.value x y
  add_right x y w := h.add_right x y w
  smul_right x y a := h.smul_right x y a
  hermitian x y := h.hermitian x y
  central_norm x := h.central_norm x
  nondegenerate := by
    intro x hx
    have hx₀ : (x : V) ≠ 0 := fun he => hx (Subtype.ext he)
    obtain ⟨y, hy⟩ := h.nondegenerate x hx₀
    let v := y - lineCoefficient h z y • z
    have hv : v ∈ linePerp h z := by
      change lineCoefficient h z (y - lineCoefficient h z y • z) = 0
      rw [map_sub, map_smul, lineCoefficient_self h z hz, smul_eq_mul, mul_one, sub_self]
    refine ⟨⟨v, hv⟩, ?_⟩
    have hzx := (mem_linePerp_iff h z hz x).mp x.property
    have hxz : h.value x z = 0 := by rw [pairing_symm h z x, hzx, conjugate_zero]
    change h.value x (y - op (unop (lineCoefficient h z y)) • z) ≠ 0
    rw [pairing_sub_right, h.smul_right, hxz, zero_mul, sub_zero]
    exact hy

private noncomputable def splitLine (z : V) (hz : h.value z z ≠ 0) :
    V ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ × linePerp h z where
  __ := (lineCoefficient h z).prod
    ((LinearMap.id - (lineCoefficient h z).smulRight z).codRestrict (linePerp h z) (fun x => by
      change lineCoefficient h z (x - lineCoefficient h z x • z) = 0
      rw [map_sub, map_smul, lineCoefficient_self h z hz, smul_eq_mul, mul_one, sub_self]))
  invFun p := p.1 • z + p.2
  left_inv x := by
    change lineCoefficient h z x • z + (x - lineCoefficient h z x • z) = x
    abel
  right_inv p := by
    have hperp : lineCoefficient h z p.2 = 0 := p.2.property
    have hc : lineCoefficient h z (p.1 • z + p.2) = p.1 := by
      rw [map_add, map_smul, lineCoefficient_self h z hz, smul_eq_mul, mul_one,
        hperp, add_zero]
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change p.1 • z + (p.2 : V) - lineCoefficient h z (p.1 • z + p.2) • z = p.2
      rw [hc]
      abel

private theorem splitLine_pairing (z : V) (hz : h.value z z ≠ 0)
    (x y : Bᵐᵒᵖ × linePerp h z) :
    h.value ((splitLine h z hz).symm x) ((splitLine h z hz).symm y) =
      conjugate s (unop x.1) * h.value z z * unop y.1 + h.value x.2 y.2 := by
  have hzx := (mem_linePerp_iff h z hz x.2).mp x.2.property
  have hzy := (mem_linePerp_iff h z hz y.2).mp y.2.property
  have hxz : h.value x.2 z = 0 := by rw [pairing_symm h z x.2, hzx, conjugate_zero]
  change h.value (op (unop x.1) • z + x.2) (op (unop y.1) • z + y.2) = _
  rw [h.add_right, pairing_add_left, pairing_add_left,
    pairing_smul_both, h.smul_right, pairing_smul_left, hxz, hzy]
  simp

private noncomputable def lineBlock (z : V) (hz : h.value z z ≠ 0)
    (r : B) (hr : r * conjugate s r = 1) (g : isometries (linePerpPairing h z hz)) :
    isometries h := by
  have hr₀ : r ≠ 0 := fun he => by simp [he] at hr
  let a : (Bᵐᵒᵖ)ˣ := Units.mk0 (op r) (by simpa using hr₀)
  let e := splitLine h z hz
  let d := (a.mulRightLinearEquiv Bᵐᵒᵖ).prodCongr g.val
  refine ⟨e.trans (d.trans e.symm), ?_⟩
  intro x y
  change h.value (e.symm (d (e x))) (e.symm (d (e y))) = h.value x y
  conv_rhs => rw [← e.symm_apply_apply x, ← e.symm_apply_apply y]
  simp only [e, splitLine_pairing]
  have hxy : h.value (g.val (e x).2) (g.val (e y).2) = h.value (e x).2 (e y).2 :=
    g.property _ _
  change conjugate s (r * unop (e x).1) * h.value z z * (r * unop (e y).1) +
    h.value (g.val (e x).2) (g.val (e y).2) =
    conjugate s (unop (e x).1) * h.value z z * unop (e y).1 + h.value (e x).2 (e y).2
  have hr' : conjugate s r * r = 1 := by
    rw [eq_inv_of_mul _ _ hr, inv_mul_cancel₀ hr₀]
  obtain ⟨q, hq⟩ := h.central_norm z
  have hcomm : conjugate s r * h.value z z = h.value z z * conjugate s r := by
    rw [hq, Algebra.commutes]
  rw [hxy, conjugate_mul, mul_assoc (conjugate s (unop (e x).1)), hcomm]
  simp only [mul_assoc, ← mul_assoc (conjugate s r) r, hr', one_mul]

private theorem lineBlock_apply (z : V) (hz : h.value z z ≠ 0)
    (r : B) (hr : r * conjugate s r = 1) (g : isometries (linePerpPairing h z hz))
    (x : V) :
    (lineBlock h z hz r hr g).val x =
      (lineCoefficient h z x * op r) • z + (g.val ((splitLine h z hz x).2) : V) := rfl

private noncomputable def lineReflection (z : V) (hz : h.value z z ≠ 0)
    (r : B) (hr : r * conjugate s r = 1) : isometries h :=
  lineBlock h z hz r hr 1

private theorem lineReflection_apply (z : V) (hz : h.value z z ≠ 0)
    (r : B) (hr : r * conjugate s r = 1) (x : V) :
    (lineReflection h z hz r hr).val x =
      x + op ((r - 1) * ((h.value z z)⁻¹ * h.value z x)) • z := by
  rw [lineReflection, lineBlock_apply]
  change ((lineCoefficient h z x) * op r) • z + (x - lineCoefficient h z x • z) = _
  change op (r * ((h.value z z)⁻¹ * h.value z x)) • z +
    (x - op ((h.value z z)⁻¹ * h.value z x) • z) = _
  rw [sub_mul, one_mul, op_sub, sub_smul]
  abel

private theorem lineReflection_isReflection (z : V) (hz : h.value z z ≠ 0)
    (r : B) (hr : r * conjugate s r = 1) :
    LineReflection h (lineReflection h z hz r hr) := by
  refine ⟨z, r, hz, hr, ?_, ?_⟩
  · rw [lineReflection_apply, inv_mul_cancel₀ hz, mul_one, op_sub, op_one, sub_smul, one_smul]
    abel
  · intro x hx
    rw [lineReflection_apply, hx, mul_zero, mul_zero, op_zero, zero_smul, add_zero]

private theorem align_difference (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (u v : V) (huv : h.value u u = h.value v v)
    (hz : h.value (u - v) (u - v) ≠ 0) :
    ∃ g : isometries h, LineReflection h g ∧ g.val u = v := by
  let z := u - v
  let a := h.value z u
  let q := h.value z z
  have hq : a + conjugate s a = q := by
    change h.value (u - v) u + conjugate s (h.value (u - v) u) = h.value (u - v) (u - v)
    rw [← pairing_symm h (u - v) u]
    simp only [pairing_sub_right, pairing_sub_left, ← huv]
    abel
  have ha : a ≠ 0 := by
    intro ha
    apply hz
    change q = 0
    rw [← hq, ha, conjugate_zero, zero_add]
  have hzq : q ≠ 0 := hz
  let r := -(conjugate s a * a⁻¹)
  have hr : r * conjugate s r = 1 := by
    change -(conjugate s a * a⁻¹) * conjugate s (-(conjugate s a * a⁻¹)) = 1
    rw [conjugate_neg, neg_mul_neg]
    have H := normOne_quotient_conjugate hB hd s hs (conjugate s a)
      (conjugate_ne_zero s ha)
    simpa only [conjugate_involutive hB s hs] using H
  have hr1 : r - 1 = -(q * a⁻¹) := by
    change -(conjugate s a * a⁻¹) - 1 = _
    rw [← hq, add_mul, mul_inv_cancel₀ ha]
    abel
  have hcoef : (r - 1) * (q⁻¹ * a) = -1 := by
    obtain ⟨Q, hQ⟩ := h.central_norm z
    have hcomm : Commute q a⁻¹ := by
      change h.value z z * a⁻¹ = a⁻¹ * h.value z z
      rw [hQ, Algebra.commutes]
    rw [hr1, neg_mul, hcomm.eq, mul_assoc a⁻¹, ← mul_assoc q q⁻¹, mul_inv_cancel₀ hzq,
      one_mul, inv_mul_cancel₀ ha]
  refine ⟨lineReflection h z hz r hr, lineReflection_isReflection h z hz r hr, ?_⟩
  rw [lineReflection_apply]
  change u + op ((r - 1) * (q⁻¹ * a)) • z = v
  rw [hcoef, op_neg, op_one, neg_smul, one_smul]
  change u + -(u - v) = v
  abel

private theorem align_nonorthogonal (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (u v : V) (huv : h.value u u = h.value v v) (hu : h.value u u ≠ 0)
    (hn : (2 : B) ≠ 0 ∨ h.value u v ≠ 0) :
    ∃ g ∈ Subgroup.closure {g : isometries h | LineReflection h g}, g.val u = v := by
  obtain ⟨r, hr, hz⟩ := nonisotropic_difference h hB hd hs u v huv hu hn
  have hvn := (pairing_norm_smul h v r hr).symm
  obtain ⟨g, hg, hgu⟩ := align_difference h hB hd hs u (op r • v) (huv.trans hvn) hz
  have hv : h.value v v ≠ 0 := huv ▸ hu
  have hr₀ : r ≠ 0 := fun he => by simp [he] at hr
  have hri : r⁻¹ * conjugate s r⁻¹ = 1 := by
    rw [conjugate_inv, eq_inv_of_mul _ _ hr, inv_inv, inv_mul_cancel₀ hr₀]
  let k := lineReflection h v hv r⁻¹ hri
  have hk := (lineReflection_isReflection h v hv r⁻¹ hri)
  refine ⟨k * g, (Subgroup.closure _).mul_mem (Subgroup.subset_closure hk)
    (Subgroup.subset_closure hg), ?_⟩
  change k.val (g.val u) = v
  rw [hgu, map_smul]
  have hkv : k.val v = op r⁻¹ • v := by
    change (lineReflection h v hv r⁻¹ hri).val v = _
    rw [lineReflection_apply, inv_mul_cancel₀ hv, mul_one, op_sub, op_one, sub_smul, one_smul]
    abel
  rw [hkv, smul_smul, ← op_mul, inv_mul_cancel₀ hr₀, op_one, one_smul]

private theorem align_equal_norm [Infinite F] (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (u v : V) (huv : h.value u u = h.value v v) (hu : h.value u u ≠ 0) :
    ∃ g ∈ Subgroup.closure {g : isometries h | LineReflection h g}, g.val u = v := by
  by_cases hn : (2 : B) ≠ 0 ∨ h.value u v ≠ 0
  · exact align_nonorthogonal h hB hd hs u v huv hu hn
  push Not at hn
  obtain ⟨w, hw, huw, hwv⟩ := orthogonal_equal_norm_bridge h u v huv hu hn.2 hn.1
  obtain ⟨g, hg, hgu⟩ := align_nonorthogonal h hB hd hs u w hw.symm hu (Or.inr huw)
  obtain ⟨k, hk, hkw⟩ := align_nonorthogonal h hB hd hs w v (hw.trans huv) (hw ▸ hu) (Or.inr hwv)
  refine ⟨k * g, (Subgroup.closure _).mul_mem hk hg, ?_⟩
  change k.val (g.val u) = v
  rw [hgu, hkw]

private theorem extendPerp_apply (z : V) (hz : h.value z z ≠ 0)
    (g : isometries (linePerpPairing h z hz)) (p : Bᵐᵒᵖ × linePerp h z) :
    (lineBlock h z hz 1 (by simp) g).val ((splitLine h z hz).symm p) =
      (splitLine h z hz).symm (p.1, g.val p.2) := by
  rw [lineBlock_apply]
  let e := splitLine h z hz
  change ((e (e.symm p)).1 * op (1 : B)) • z + (g.val (e (e.symm p)).2 : V) =
    p.1 • z + (g.val p.2 : V)
  rw [e.apply_symm_apply, op_one, mul_one]

private noncomputable def extendPerp (z : V) (hz : h.value z z ≠ 0) :
    isometries (linePerpPairing h z hz) →* isometries h where
  toFun g := lineBlock h z hz 1 (by simp) g
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨p, rfl⟩ := (splitLine h z hz).symm.surjective x
    change (lineBlock h z hz 1 (by simp) 1).val ((splitLine h z hz).symm p) =
      (splitLine h z hz).symm p
    rw [extendPerp_apply]
    rfl
  map_mul' g k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨p, rfl⟩ := (splitLine h z hz).symm.surjective x
    change (lineBlock h z hz 1 (by simp) (g * k)).val ((splitLine h z hz).symm p) =
      (lineBlock h z hz 1 (by simp) g).val
        ((lineBlock h z hz 1 (by simp) k).val ((splitLine h z hz).symm p))
    rw [extendPerp_apply, extendPerp_apply, extendPerp_apply]
    rfl

private theorem extendPerp_isReflection (z : V) (hz : h.value z z ≠ 0)
    (g : isometries (linePerpPairing h z hz))
    (hg : LineReflection (linePerpPairing h z hz) g) :
    LineReflection h (extendPerp h z hz g) := by
  obtain ⟨w, r, hw, hr, hwg, hfix⟩ := hg
  let e := splitLine h z hz
  have hwcoord : e.symm (0, w) = (w : V) := by
    change (0 : Bᵐᵒᵖ) • z + (w : V) = w
    simp
  refine ⟨w, r, hw, hr, ?_, ?_⟩
  · change (lineBlock h z hz 1 (by simp) g).val (w : V) = _
    rw [← hwcoord, extendPerp_apply, hwg]
    change (0 : Bᵐᵒᵖ) • z + (op r • (w : V)) = op r • e.symm (0, w)
    rw [hwcoord, zero_smul, zero_add]
  · intro x hx
    obtain ⟨p, rfl⟩ := e.symm.surjective x
    have hp := splitLine_pairing h z hz (0, w) p
    change h.value (e.symm (0, w)) (e.symm p) = _ at hp
    have hwp : (linePerpPairing h z hz).value w p.2 = 0 := by
      change h.value w p.2 = 0
      rw [hwcoord, hx] at hp
      simpa using hp.symm
    change (lineBlock h z hz 1 (by simp) g).val ((splitLine h z hz).symm p) = _
    rw [extendPerp_apply, hfix p.2 hwp]

private theorem exists_extendPerp_eq (z : V) (hz : h.value z z ≠ 0)
    (g : isometries h) (hg : g.val z = z) :
    ∃ k : isometries (linePerpPairing h z hz), extendPerp h z hz k = g := by
  let P := linePerp h z
  have hp (x : V) : g.val x ∈ P ↔ x ∈ P := by
    have heq : h.value z (g.val x) = h.value z x := by
      calc
        _ = h.value (g.val z) (g.val x) := by rw [hg]
        _ = _ := g.property _ _
    rw [mem_linePerp_iff h z hz, mem_linePerp_iff h z hz, heq]
  have hmap : P.map g.val.toLinearMap = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hp y).2 hy
    · intro hx
      refine ⟨g.val.symm x, ?_, g.val.apply_symm_apply x⟩
      exact (hp (g.val.symm x)).1 (by rwa [g.val.apply_symm_apply])
  let k : isometries (linePerpPairing h z hz) :=
    ⟨g.val.ofSubmodules P P hmap, fun x y => g.property x y⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := (splitLine h z hz).symm.surjective x
  change (lineBlock h z hz 1 (by simp) k).val ((splitLine h z hz).symm p) =
    g.val ((splitLine h z hz).symm p)
  rw [extendPerp_apply]
  change p.1 • z + g.val p.2 = g.val (p.1 • z + p.2)
  rw [map_add, map_smul, hg]

private theorem reflectionGeneration_of_finrank [Infinite F]
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x) (n : ℕ) :
    ∀ (V : Type w) [AddCommGroup V] [Module Bᵐᵒᵖ V] [Module.Finite Bᵐᵒᵖ V]
      (h : HermitianPairing s V), Module.finrank Bᵐᵒᵖ V = n →
        Subgroup.closure {g : isometries h | LineReflection h g} = ⊤ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ h hn
    let H := Subgroup.closure {g : isometries h | LineReflection h g}
    apply top_unique
    intro g _
    cases subsingleton_or_nontrivial V with
    | inl hsub =>
      have hg : g = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        exact hsub.elim _ _
      rw [hg]
      exact H.one_mem
    | inr hnon =>
      let : Nontrivial V := hnon
      obtain ⟨z, hz⟩ := exists_nonisotropic h hB hd hs
      have hdims := (splitLine h z hz).finrank_eq
      rw [hn, Module.finrank_prod, Module.finrank_self] at hdims
      have hlt : Module.finrank Bᵐᵒᵖ (linePerp h z) < n := by omega
      have hgen := ih _ hlt (linePerp h z) (linePerpPairing h z hz) rfl
      obtain ⟨a, ha, haz⟩ :=
        align_equal_norm h hB hd hs (g.val z) z (g.property z z)
          (by rw [g.property z z]; exact hz)
      have hg : (a * g).val z = z := haz
      obtain ⟨k, hk⟩ := exists_extendPerp_eq h z hz (a * g) hg
      have hle : Subgroup.closure {k : isometries (linePerpPairing h z hz) |
          LineReflection (linePerpPairing h z hz) k} ≤ H.comap (extendPerp h z hz) := by
        rw [Subgroup.closure_le]
        intro k hK
        exact Subgroup.subset_closure (extendPerp_isReflection h z hz k hK)
      have hkmem : extendPerp h z hz k ∈ H := hle (by rw [hgen]; trivial)
      have hm : a⁻¹ * (a * g) ∈ H := H.mul_mem (H.inv_mem ha) (hk ▸ hkmem)
      simpa using hm

theorem reflectionGeneration : ReflectionGeneration.{u,v,w} := by
  intro F B _ _ _ _ hB hd s hs V _ _ _ h
  exact reflectionGeneration_of_finrank hB hd hs _ V h rfl

end Hermitian

section Hyperbolic
open QuaternionHermitianCocharacters (pairing adjoint adjoint_mul adjoint_one mem_isometries_iff)

variable {s : AntiAutomorphism F B} {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V]

private structure HyperbolicPair (h : HermitianPairing s V) where
  e : V
  f : V
  ee : h.value e e = 0
  ff : h.value f f = 0
  ef : h.value e f = 1
  fe : h.value f e = 1

private def pairingLinear (h : HermitianPairing s V) (x : V) : V →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun y := op (h.value x y)
  map_add' y z := by rw [h.add_right, op_add]
  map_smul' a y := by
    apply unop_injective
    exact h.smul_right x y (unop a)

variable {h : HermitianPairing s V} (p : HyperbolicPair h)

private def hyperbolicPerp : Submodule Bᵐᵒᵖ V :=
  (pairingLinear h p.e).ker ⊓ (pairingLinear h p.f).ker

private theorem mem_hyperbolicPerp (x : V) :
    x ∈ hyperbolicPerp p ↔ h.value p.e x = 0 ∧ h.value p.f x = 0 := by
  simp [hyperbolicPerp, Submodule.mem_inf, LinearMap.mem_ker, pairingLinear]

private def hyperbolicProjection : V →ₗ[Bᵐᵒᵖ] V :=
  LinearMap.id - (LinearMap.toSpanSingleton _ _ p.e).comp (pairingLinear h p.f) -
    (LinearMap.toSpanSingleton _ _ p.f).comp (pairingLinear h p.e)

private theorem hyperbolicProjection_apply (x : V) :
    hyperbolicProjection p x = x - op (h.value p.f x) • p.e - op (h.value p.e x) • p.f := rfl

private theorem hyperbolicProjection_mem (x : V) :
    hyperbolicProjection p x ∈ hyperbolicPerp p := by
  simp [mem_hyperbolicPerp, hyperbolicProjection_apply, pairing_sub_right, h.smul_right,
    p.ee, p.ff, p.ef, p.fe]

private theorem hyperbolic_decompose (x : V) :
    op (h.value p.f x) • p.e + op (h.value p.e x) • p.f + hyperbolicProjection p x = x := by
  rw [hyperbolicProjection_apply]
  abel

private def hyperbolicPerpPairing : HermitianPairing s (hyperbolicPerp p) where
  value x y := h.value x y
  add_right x y z := h.add_right x y z
  smul_right x y a := h.smul_right x y a
  hermitian x y := h.hermitian x y
  central_norm x := h.central_norm x
  nondegenerate := by
    intro x hx
    have hx0 : (x : V) ≠ 0 := by
      intro e
      exact hx (Subtype.ext e)
    obtain ⟨y, hy⟩ := h.nondegenerate x hx0
    refine ⟨⟨hyperbolicProjection p y, hyperbolicProjection_mem p y⟩, ?_⟩
    obtain ⟨he, hf⟩ := (mem_hyperbolicPerp p x).mp x.property
    have he' : h.value x p.e = 0 := by rw [pairing_symm h p.e x, he, conjugate_zero]
    have hf' : h.value x p.f = 0 := by rw [pairing_symm h p.f x, hf, conjugate_zero]
    simpa [hyperbolicProjection_apply, pairing_sub_right, h.smul_right, he', hf'] using hy

private def hyperbolicCoordinates : V ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ × Bᵐᵒᵖ × hyperbolicPerp p :=
  LinearEquiv.ofLinearMap
    ((pairingLinear h p.f).prod ((pairingLinear h p.e).prod
      ((hyperbolicProjection p).codRestrict _ (hyperbolicProjection_mem p))))
    (((LinearMap.toSpanSingleton _ _ p.e).comp (LinearMap.fst _ _ _)) +
      ((LinearMap.toSpanSingleton _ _ p.f).comp ((LinearMap.fst _ _ _).comp
        (LinearMap.snd _ _ _))) + (hyperbolicPerp p).subtype.comp
        ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)))
    (by
      apply LinearMap.ext
      rintro ⟨a, b, w⟩
      obtain ⟨he, hf⟩ := (mem_hyperbolicPerp p w).mp w.property
      have hs (x y : V) (t : Bᵐᵒᵖ) : h.value x (t • y) = h.value x y * unop t :=
        h.smul_right x y (unop t)
      have ha : h.value p.f (a • p.e + b • p.f + w) = unop a := by
        simp [h.add_right, hs, p.fe, p.ff, hf]
      have hb : h.value p.e (a • p.e + b • p.f + w) = unop b := by
        simp [h.add_right, hs, p.ef, p.ee, he]
      let x : V := a • p.e + b • p.f + w
      change (op (h.value p.f x), op (h.value p.e x),
        (⟨hyperbolicProjection p x, hyperbolicProjection_mem p x⟩ : hyperbolicPerp p)) = (a, b, w)
      change h.value p.f x = unop a at ha
      change h.value p.e x = unop b at hb
      rw [ha, hb]
      simp only [op_unop, Prod.mk.injEq, true_and]
      apply Subtype.ext
      change hyperbolicProjection p x = (w : V)
      rw [hyperbolicProjection_apply, ha, hb, op_unop, op_unop]
      dsimp [x]
      abel)
    (by
      apply LinearMap.ext
      exact hyperbolic_decompose p)

private theorem hyperbolicCoordinates_symm_apply (a b : Bᵐᵒᵖ) (w : hyperbolicPerp p) :
    (hyperbolicCoordinates p).symm (a, b, w) = a • p.e + b • p.f + w := rfl

private theorem hyperbolicCoordinates_pairing (a b c d : B) (w z : hyperbolicPerp p) :
    h.value ((hyperbolicCoordinates p).symm (op a, op b, w))
      ((hyperbolicCoordinates p).symm (op c, op d, z)) =
        conjugate s a * d + conjugate s b * c + (hyperbolicPerpPairing p).value w z := by
  obtain ⟨he, hf⟩ := (mem_hyperbolicPerp p w).mp w.property
  obtain ⟨he', hf'⟩ := (mem_hyperbolicPerp p z).mp z.property
  have hwe : h.value w p.e = 0 := by rw [pairing_symm h p.e, he, conjugate_zero]
  have hwf : h.value w p.f = 0 := by rw [pairing_symm h p.f, hf, conjugate_zero]
  simp [hyperbolicCoordinates_symm_apply, pairing_add_left, h.add_right, h.smul_right,
    pairing_smul_left, p.ee, p.ff, p.ef, p.fe, he', hf', hwe, hwf, hyperbolicPerpPairing, add_comm]

set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I] [DecidableEq I]

private noncomputable def rightMatrix : Matrix I I B ≃ₐ[F] Module.End Bᵐᵒᵖ (I → B) :=
  (AlgEquiv.moduleEndSelfOp F (A := B)).mapMatrix.trans (endVecAlgEquivMatrixEnd I F Bᵐᵒᵖ B).symm

@[simp] private theorem rightMatrix_apply (M : Matrix I I B) (x : I → B) :
    rightMatrix (F := F) M x = M.mulVec x := rfl

private def oppositeCoordinates : B ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop
  map_add' := op_add
  map_smul' _ _ := rfl

private def twoCoefficients : (Fin 2 → B) ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ × Bᵐᵒᵖ :=
  (LinearEquiv.finTwoArrow Bᵐᵒᵖ B).trans (oppositeCoordinates.prodCongr oppositeCoordinates)

private def threeCoefficients : (Fin 3 → B) ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ × Bᵐᵒᵖ × Bᵐᵒᵖ where
  toFun x := (op (x 0), op (x 2), op (x 1))
  invFun x := ![unop x.1, unop x.2.2, unop x.2.1]
  left_inv := by intro x; funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨a, b, c⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def planeCoordinates : V ≃ₗ[Bᵐᵒᵖ] (Fin 2 → B) × hyperbolicPerp p :=
  (hyperbolicCoordinates p).trans ((LinearEquiv.prodAssoc Bᵐᵒᵖ _ _ _).symm.trans
    (twoCoefficients.symm.prodCongr (LinearEquiv.refl _ _)))

private def planeGram : Matrix (Fin 2) (Fin 2) B := !![0, 1; 1, 0]

private theorem planeCoordinates_pairing (x y : Fin 2 → B) (w z : hyperbolicPerp p) :
    h.value ((planeCoordinates p).symm (x, w)) ((planeCoordinates p).symm (y, z)) =
      pairing s.toAlgHom planeGram x y + (hyperbolicPerpPairing p).value w z := by
  change h.value ((hyperbolicCoordinates p).symm (op (x 0), op (x 1), w))
    ((hyperbolicCoordinates p).symm (op (y 0), op (y 1), z)) = _
  rw [hyperbolicCoordinates_pairing]
  simp [pairing, planeGram, Fin.sum_univ_two, conjugate, add_comm]

private noncomputable def threeCoordinates (z : hyperbolicPerp p)
    (hz : (hyperbolicPerpPairing p).value z z ≠ 0) :
    V ≃ₗ[Bᵐᵒᵖ] (Fin 3 → B) × linePerp (hyperbolicPerpPairing p) z :=
  (hyperbolicCoordinates p).trans
    ((LinearEquiv.refl _ _).prodCongr
      ((LinearEquiv.refl _ _).prodCongr (splitLine (hyperbolicPerpPairing p) z hz))) |>.trans
    (((LinearEquiv.refl _ _).prodCongr (LinearEquiv.prodAssoc Bᵐᵒᵖ _ _ _).symm).trans
      ((LinearEquiv.prodAssoc Bᵐᵒᵖ _ _ _).symm.trans
        (threeCoefficients.symm.prodCongr (LinearEquiv.refl _ _))))

private theorem threeCoordinates_pairing (z : hyperbolicPerp p)
    (hz : (hyperbolicPerpPairing p).value z z ≠ 0) (q : Fˣ)
    (hq : (hyperbolicPerpPairing p).value z z = algebraMap F B (q : F))
    (x y : Fin 3 → B) (w v : linePerp (hyperbolicPerpPairing p) z) :
    h.value ((threeCoordinates p z hz).symm (x, w)) ((threeCoordinates p z hz).symm (y, v)) =
      pairing s.toAlgHom (gram q) x y + (linePerpPairing (hyperbolicPerpPairing p) z hz).value w v := by
  change h.value ((hyperbolicCoordinates p).symm
    (op (x 0), op (x 2), (splitLine (hyperbolicPerpPairing p) z hz).symm (op (x 1), w)))
    ((hyperbolicCoordinates p).symm
    (op (y 0), op (y 2), (splitLine (hyperbolicPerpPairing p) z hz).symm (op (y 1), v))) = _
  rw [hyperbolicCoordinates_pairing, splitLine_pairing, hq]
  simp [pairing, gram, Fin.sum_univ_three, conjugate, add_comm, add_left_comm, add_assoc, mul_assoc]
  rfl

variable {Z : Type*} [AddCommGroup Z] [Module Bᵐᵒᵖ Z]

/-- Extend a pair of block endomorphisms in the chosen orthogonal coordinates. -/
private noncomputable def blockHom (d : V ≃ₗ[Bᵐᵒᵖ] (I → B) × Z) :
    Matrix I I B × Module.End Bᵐᵒᵖ Z →+* Module.End Bᵐᵒᵖ V :=
  d.conjRingEquiv.symm.toRingHom.comp
    ((LinearMap.prodMapRingHom Bᵐᵒᵖ (I → B) Z).comp
      ((rightMatrix (F := F)).toRingHom.prodMap (RingHom.id (Module.End Bᵐᵒᵖ Z))))

private theorem blockHom_apply (d : V ≃ₗ[Bᵐᵒᵖ] (I → B) × Z)
    (M : Matrix I I B) (N : Module.End Bᵐᵒᵖ Z) (x : V) :
    blockHom (F := F) d (M, N) x = d.symm (M.mulVec (d x).1, N (d x).2) := by
  change d.symm (rightMatrix (F := F) M (d x).1, N (d x).2) = _
  rw [rightMatrix_apply]

private noncomputable def extendBlock (d : V ≃ₗ[Bᵐᵒᵖ] (I → B) × Z) :
    Matrix I I B →* Module.End Bᵐᵒᵖ V where
  toFun M := blockHom (F := F) d (M, 1)
  map_one' := map_one (blockHom (F := F) d)
  map_mul' M N := by
    rw [← map_mul]
    simp only [Prod.mk_mul_mk, mul_one]

private theorem extendBlock_isometry (H : Matrix I I B) (hZ : HermitianPairing s Z)
    (d : V ≃ₗ[Bᵐᵒᵖ] (I → B) × Z)
    (hd : ∀ x y z w, h.value (d.symm (x, z)) (d.symm (y, w)) =
      pairing s.toAlgHom H x y + hZ.value z w)
    (M : (Matrix I I B)ˣ) (hM : adjoint s.toAlgHom M.val * H * M.val = H) :
    ∀ x y, h.value (extendBlock (F := F) d M.val x) (extendBlock (F := F) d M.val y) =
      h.value x y := by
  intro x y
  have h₀ := (mem_isometries_iff s.toAlgHom H M).mp hM
  change h.value (blockHom (F := F) d (M.val, 1) x) (blockHom (F := F) d (M.val, 1) y) = _
  rw [blockHom_apply, blockHom_apply, hd, h₀]
  simpa only [Module.End.one_apply, Prod.eta, LinearEquiv.symm_apply_apply] using
    (hd (d x).1 (d y).1 (d x).2 (d y).2).symm

private def firstProjector : Module.End Bᵐᵒᵖ V :=
  (LinearMap.toSpanSingleton _ _ p.e).comp (pairingLinear h p.f)

private def lastProjector : Module.End Bᵐᵒᵖ V :=
  (LinearMap.toSpanSingleton _ _ p.f).comp (pairingLinear h p.e)

@[simp] private theorem firstProjector_apply (x : V) :
    firstProjector p x = op (h.value p.f x) • p.e := rfl

@[simp] private theorem lastProjector_apply (x : V) :
    lastProjector p x = op (h.value p.e x) • p.f := rfl

private theorem firstProjector_squared : firstProjector p * firstProjector p = firstProjector p := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, p.fe]

private theorem lastProjector_squared : lastProjector p * lastProjector p = lastProjector p := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, p.ef]

private theorem firstProjector_mul_last : firstProjector p * lastProjector p = 0 := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, p.ff]

private theorem lastProjector_mul_first : lastProjector p * firstProjector p = 0 := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, p.ee]

private theorem pairing_firstProjector (x y : V) :
    h.value (firstProjector p x) y = h.value x (lastProjector p y) := by
  simp only [firstProjector_apply, lastProjector_apply, pairing_smul_left, h.smul_right,
    ← pairing_symm h]

private def IsUpperEnd (g : Module.End Bᵐᵒᵖ V) : Prop :=
  let e := firstProjector p
  let f := lastProjector p
  let m := hyperbolicProjection p
  g = 1 + (e * g * m + m * g * f) + e * g * f

private def HyperbolicPair.flip : HyperbolicPair h :=
  ⟨p.f, p.e, p.ff, p.ee, p.fe, p.ef⟩

private theorem hyperbolicProjection_def :
    hyperbolicProjection p = 1 - firstProjector p - lastProjector p := rfl

private theorem matrix_corner_upper (q : Fˣ) (a b : B) :
    let e := Matrix.single (0 : Fin 3) 0 (1 : B)
    let f := Matrix.single (2 : Fin 3) 2 (1 : B)
    let m := 1 - e - f
    let M := upper s q a b
    M = 1 + (e * M * m + m * M * f) + e * M * f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, upper, Matrix.single_apply, Matrix.one_apply]

private theorem matrix_corner_lower (q : Fˣ) (a b : B) :
    let e := Matrix.single (2 : Fin 3) 2 (1 : B)
    let f := Matrix.single (0 : Fin 3) 0 (1 : B)
    let m := 1 - e - f
    let M := lower s q a b
    M = 1 + (e * M * m + m * M * f) + e * M * f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, lower, Matrix.single_apply, Matrix.one_apply]

private theorem plane_corner_upper (b : B) :
    let e := Matrix.single (0 : Fin 2) 0 (1 : B)
    let f := Matrix.single (1 : Fin 2) 1 (1 : B)
    let m := 1 - e - f
    let M := planeUpper b
    M = 1 + (e * M * m + m * M * f) + e * M * f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, planeUpper, Matrix.single_apply, Matrix.one_apply]

private theorem plane_corner_lower (b : B) :
    let e := Matrix.single (1 : Fin 2) 1 (1 : B)
    let f := Matrix.single (0 : Fin 2) 0 (1 : B)
    let m := 1 - e - f
    let M := planeLower b
    M = 1 + (e * M * m + m * M * f) + e * M * f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, planeLower, Matrix.single_apply, Matrix.one_apply]

private theorem block_corner_upper (d : V ≃ₗ[Bᵐᵒᵖ] (I → B) × Z)
    {first last : I}
    (hd₁ : blockHom (F := F) d (Matrix.single first first 1, 0) = firstProjector p)
    (hd₂ : blockHom (F := F) d (Matrix.single last last 1, 0) = lastProjector p)
    (M : Matrix I I B)
    (hM :
      let e := Matrix.single first first (1 : B)
      let f := Matrix.single last last (1 : B)
      let m := 1 - e - f
      M = 1 + (e * M * m + m * M * f) + e * M * f) :
    IsUpperEnd p (extendBlock (F := F) d M) := by
  let e : Matrix I I B × Module.End Bᵐᵒᵖ Z := (Matrix.single first first 1, 0)
  let f : Matrix I I B × Module.End Bᵐᵒᵖ Z := (Matrix.single last last 1, 0)
  have h' : (M, (1 : Module.End Bᵐᵒᵖ Z)) =
      1 + (e * (M, 1) * (1 - e - f) + (1 - e - f) * (M, 1) * f) + e * (M, 1) * f := by
    apply Prod.ext
    · exact hM
    · simp [e, f]
  have he : blockHom (F := F) d e = firstProjector p := hd₁
  have hf : blockHom (F := F) d f = lastProjector p := hd₂
  have hmap := congrArg (blockHom (F := F) d) h'
  change blockHom (F := F) d (M, 1) = _ at hmap
  simpa only [map_one, map_add, map_mul, map_sub, he, hf, IsUpperEnd,
    hyperbolicProjection_def, extendBlock, MonoidHom.coe_mk, OneHom.coe_mk] using hmap

private theorem planeBlock_first :
    blockHom (F := F) (planeCoordinates p) (Matrix.single 0 0 1, 0) = firstProjector p := by
  apply LinearMap.ext
  intro x
  rw [blockHom_apply, firstProjector_apply]
  have hxy := (planeCoordinates p).symm_apply_apply x
  change (planeCoordinates p).symm
    (Matrix.single 0 0 1 *ᵥ (planeCoordinates p x).1, (0 : Module.End Bᵐᵒᵖ (hyperbolicPerp p)) _) = _
  simp only [Matrix.single_mulVec, one_mul, LinearMap.zero_apply]
  change (hyperbolicCoordinates p).symm (op (h.value p.f x), 0, 0) = _
  rw [hyperbolicCoordinates_symm_apply]
  simp

private theorem planeBlock_last :
    blockHom (F := F) (planeCoordinates p) (Matrix.single 1 1 1, 0) = lastProjector p := by
  apply LinearMap.ext
  intro x
  rw [blockHom_apply, lastProjector_apply]
  simp only [Matrix.single_mulVec, one_mul, LinearMap.zero_apply]
  change (hyperbolicCoordinates p).symm (0, op (h.value p.e x), 0) = _
  rw [hyperbolicCoordinates_symm_apply]
  simp

private theorem threeBlock_first (z : hyperbolicPerp p)
    (hz : (hyperbolicPerpPairing p).value z z ≠ 0) :
    blockHom (F := F) (Z := ↥(linePerp (hyperbolicPerpPairing p) z)) (threeCoordinates p z hz) (Matrix.single (0 : Fin 3) 0 1, 0) = firstProjector p := by
  apply LinearMap.ext
  intro x
  rw [blockHom_apply, firstProjector_apply]
  simp only [Matrix.single_mulVec, one_mul, LinearMap.zero_apply]
  change (hyperbolicCoordinates p).symm (op (h.value p.f x), 0,
    (splitLine (hyperbolicPerpPairing p) z hz).symm 0) = _
  rw [map_zero, hyperbolicCoordinates_symm_apply]
  simp

private theorem threeBlock_last (z : hyperbolicPerp p)
    (hz : (hyperbolicPerpPairing p).value z z ≠ 0) :
    blockHom (F := F) (Z := ↥(linePerp (hyperbolicPerpPairing p) z)) (threeCoordinates p z hz) (Matrix.single (2 : Fin 3) 2 1, 0) = lastProjector p := by
  apply LinearMap.ext
  intro x
  rw [blockHom_apply, lastProjector_apply]
  simp only [Matrix.single_mulVec, one_mul, LinearMap.zero_apply]
  change (hyperbolicCoordinates p).symm (0, op (h.value p.e x),
    (splitLine (hyperbolicPerpPairing p) z hz).symm 0) = _
  rw [map_zero, hyperbolicCoordinates_symm_apply]
  simp

private def endWords (J : Subgroup (isometries h)) : Submonoid (Module.End Bᵐᵒᵖ V) := by
  let f : isometries h →* Module.End Bᵐᵒᵖ V :=
    { toFun := fun g => g.val.toLinearMap
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact J.toSubmonoid.map f

private theorem endWords_mem_iff (J : Subgroup (isometries h)) (g : isometries h) :
    g.val.toLinearMap ∈ endWords J ↔ g ∈ J := by
  change (∃ q ∈ J, q.val.toLinearMap = g.val.toLinearMap) ↔ _
  constructor
  · rintro ⟨q, hq, h⟩
    have he : q = g := Subtype.ext (LinearEquiv.toLinearMap_injective h)
    exact he ▸ hq
  · intro hg
    exact ⟨g, hg, rfl⟩

private theorem block_mem_endWords (J : Subgroup (isometries h))
    (hshear : ∀ g : isometries h, IsUpperEnd p g.val.toLinearMap ∨
      IsUpperEnd p.flip g.val.toLinearMap → g ∈ J)
    (H : Matrix I I B) (hZ : HermitianPairing s Z)
    (d : V ≃ₗ[Bᵐᵒᵖ] (I → B) × Z)
    (hd : ∀ x y z w, h.value (d.symm (x, z)) (d.symm (y, w)) =
      pairing s.toAlgHom H x y + hZ.value z w)
    (M : Matrix I I B) (hu : IsUnit M) (hM : adjoint s.toAlgHom M * H * M = H)
    (hshape : IsUpperEnd p (extendBlock (F := F) d M) ∨ IsUpperEnd p.flip (extendBlock (F := F) d M)) :
    extendBlock (F := F) d M ∈ endWords J := by
  obtain ⟨U, rfl⟩ := hu
  let g := LinearMap.GeneralLinearGroup.toLinearEquiv (Units.map (extendBlock (F := F) d) U)
  let a : isometries h := ⟨g, extendBlock_isometry H hZ d hd U hM⟩
  change ∃ q ∈ J, q.val.toLinearMap = extendBlock (F := F) d U.val
  exact ⟨a, hshear a hshape, rfl⟩

private theorem plane_shears (b : B) (hb : conjugate s b = -b) :
    IsUnit (planeUpper b) ∧ adjoint s.toAlgHom (planeUpper b) * planeGram * planeUpper b = planeGram ∧
    IsUnit (planeLower b) ∧ adjoint s.toAlgHom (planeLower b) * planeGram * planeLower b = planeGram := by
  change unop (s b) = -b at hb
  have hu (b c : B) : planeUpper b * planeUpper c = planeUpper (b + c) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeUpper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hl (b c : B) : planeLower b * planeLower c = planeLower (b + c) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeLower, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hu₀ : planeUpper (0 : B) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hl₀ : planeLower (0 : B) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine ⟨⟨⟨planeUpper b, planeUpper (-b), by simp [hu, hu₀], by simp [hu, hu₀]⟩, rfl⟩,
    ?_, ⟨⟨planeLower b, planeLower (-b), by simp [hl, hl₀], by simp [hl, hl₀]⟩, rfl⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeUpper, planeGram, adjoint, Matrix.mul_apply, Fin.sum_univ_two, hb]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeLower, planeGram, adjoint, Matrix.mul_apply, Fin.sum_univ_two, hb]

variable (J : Subgroup (isometries h))
variable (hshear : ∀ g : isometries h, IsUpperEnd p g.val.toLinearMap ∨
    IsUpperEnd p.flip g.val.toLinearMap → g ∈ J)

include hshear in
private theorem planeShears_mem (b : B) (hb : conjugate s b = -b) :
    extendBlock (F := F) (planeCoordinates p) (planeUpper b) ∈ endWords J ∧
    extendBlock (F := F) (planeCoordinates p) (planeLower b) ∈ endWords J := by
  obtain ⟨hu, hU, hl, hL⟩ := plane_shears (s := s) b hb
  constructor
  · apply block_mem_endWords p J hshear planeGram (hyperbolicPerpPairing p)
      (planeCoordinates p) (planeCoordinates_pairing p) _ hu hU
    apply Or.inl
    exact block_corner_upper p _ (planeBlock_first p) (planeBlock_last p) _ (plane_corner_upper b)
  · apply block_mem_endWords p J hshear planeGram (hyperbolicPerpPairing p)
      (planeCoordinates p) (planeCoordinates_pairing p) _ hl hL
    apply Or.inr
    exact block_corner_upper p.flip _ (planeBlock_last p) (planeBlock_first p) _ (plane_corner_lower b)

include hshear in
private theorem pairScales_mem (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x) (t : Bˣ) :
    extendBlock (F := F) (planeCoordinates p)
      (Matrix.diagonal ![(t : B), (conjugate s t)⁻¹]) ∈ endWords J := by
  let i := extendBlock (F := F) (planeCoordinates p)
  have h₁ (b : Bˣ) (hb : reducedTrace hB b = 0) :
      i (planeInterchange (b : B)) ∈ endWords J := by
    have hb' := conjugate_eq_neg_of_traceZero hB s hs _ hb
    have hb'' := (purePlaneWords hB hd s hs).1 b hb |>.1
    rw [planeInterchange, map_mul, map_mul]
    exact (endWords J).mul_mem
      ((endWords J).mul_mem (planeShears_mem p J hshear _ hb').1
        (planeShears_mem p J hshear _ (conjugate_eq_neg_of_traceZero hB s hs _ hb'')).2)
      (planeShears_mem p J hshear _ hb').1
  obtain ⟨b, c, hb, hc, hbc⟩ := (purePlaneWords hB hd s hs).2 t
  let c' := Units.mk0 (-(c : B)) (neg_ne_zero.mpr c.ne_zero)
  have hc' : reducedTrace hB c' = 0 := by
    apply traceZero_of_conjugate_eq_neg hB s hs _
    change conjugate s (-(c : B)) = -(-(c : B))
    rw [conjugate_neg, conjugate_eq_neg_of_traceZero hB s hs _ hc]
  change i _ ∈ endWords J
  rw [← hbc, map_mul]
  exact (endWords J).mul_mem (h₁ b hb) (h₁ c' hc')

include hshear in
private theorem threeShears_mem
    (si : Function.Involutive (conjugate s)) (z : hyperbolicPerp p)
    (hz : (hyperbolicPerpPairing p).value z z ≠ 0) (q : Fˣ)
    (hq : (hyperbolicPerpPairing p).value z z = algebraMap F B (q : F))
    (a b : B) (hab : Admissible s q a b) :
    extendBlock (F := F) (Z := ↥(linePerp (hyperbolicPerpPairing p) z)) (threeCoordinates p z hz) (upper s q a b) ∈ endWords J ∧
    extendBlock (F := F) (Z := ↥(linePerp (hyperbolicPerpPairing p) z)) (threeCoordinates p z hz) (lower s q a b) ∈ endWords J := by
  obtain ⟨hu, hU, hl, hL⟩ := shearIsometries s si q a b hab
  constructor
  · apply block_mem_endWords p J hshear (gram q) (linePerpPairing (hyperbolicPerpPairing p) z hz)
      (threeCoordinates p z hz) (threeCoordinates_pairing p z hz q hq) _ hu hU
    exact Or.inl (block_corner_upper p _ (threeBlock_first p z hz) (threeBlock_last p z hz)
      _ (matrix_corner_upper (s := s) q a b))
  · apply block_mem_endWords p J hshear (gram q) (linePerpPairing (hyperbolicPerpPairing p) z hz)
      (threeCoordinates p z hz) (threeCoordinates_pairing p z hz q hq) _ hl hL
    exact Or.inr (block_corner_upper p.flip _ (threeBlock_last p z hz) (threeBlock_first p z hz)
      _ (matrix_corner_lower (s := s) q a b))

private noncomputable def middleIsometry (p : HyperbolicPair h) :
    isometries (hyperbolicPerpPairing p) →* isometries h where
  toFun g := by
    let d := hyperbolicCoordinates p
    let L : (Bᵐᵒᵖ × Bᵐᵒᵖ × hyperbolicPerp p) ≃ₗ[Bᵐᵒᵖ]
        (Bᵐᵒᵖ × Bᵐᵒᵖ × hyperbolicPerp p) :=
      (LinearEquiv.refl _ _).prodCongr ((LinearEquiv.refl _ _).prodCongr g.val)
    refine ⟨d.trans (L.trans d.symm), ?_⟩
    intro x y
    obtain ⟨⟨a, b, w⟩, rfl⟩ := d.symm.surjective x
    obtain ⟨⟨c, d', v⟩, rfl⟩ := d.symm.surjective y
    change h.value (d.symm (L (d (d.symm (a, b, w))))) (d.symm (L (d (d.symm (c, d', v))))) = _
    simp only [LinearEquiv.apply_symm_apply]
    change h.value (d.symm (a,b,g.val w)) (d.symm (c,d',g.val v)) = _
    obtain ⟨a,rfl⟩ := op_surjective a
    obtain ⟨b,rfl⟩ := op_surjective b
    obtain ⟨c,rfl⟩ := op_surjective c
    obtain ⟨d',rfl⟩ := op_surjective d'
    rw [hyperbolicCoordinates_pairing, hyperbolicCoordinates_pairing, g.property]
  map_one' := by
    apply Subtype.ext
    ext x
    exact (hyperbolicCoordinates p).symm_apply_apply x
  map_mul' g f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    let d := hyperbolicCoordinates p
    let z := d x
    let y := d.symm (z.1, z.2.1, f.val z.2.2)
    change d.symm (z.1, z.2.1, g.val (f.val z.2.2)) =
      d.symm ((d y).1, (d y).2.1, g.val (d y).2.2)
    simp only [y, LinearEquiv.apply_symm_apply]

private theorem middleIsometry_apply (g : isometries (hyperbolicPerpPairing p))
    (a b : Bᵐᵒᵖ) (w : hyperbolicPerp p) :
    (middleIsometry p g).val ((hyperbolicCoordinates p).symm (a, b, w)) =
      (hyperbolicCoordinates p).symm (a, b, g.val w) := by
  change (hyperbolicCoordinates p).symm
    (((LinearEquiv.refl _ _).prodCongr ((LinearEquiv.refl _ _).prodCongr g.val))
      ((hyperbolicCoordinates p) ((hyperbolicCoordinates p).symm (a, b, w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem reflection_action (z : hyperbolicPerp p)
    (hz : (hyperbolicPerpPairing p).value z z ≠ 0) (r : B)
    (g : isometries (hyperbolicPerpPairing p))
    (hg : g.val z = op r • z)
    (hw : ∀ x, (hyperbolicPerpPairing p).value z x = 0 → g.val x = x)
    (a : B) (x : linePerp (hyperbolicPerpPairing p) z) :
    g.val ((splitLine (hyperbolicPerpPairing p) z hz).symm (op a, x)) =
      (splitLine (hyperbolicPerpPairing p) z hz).symm (op (r * a), x) := by
  change g.val (op a • z + x) = op (r * a) • z + x
  have hx := (mem_linePerp_iff (hyperbolicPerpPairing p) z hz x).mp x.property
  rw [map_add, map_smul, hg, hw x hx, smul_smul, ← op_mul]

include hshear in
private theorem middleIsometries_mem [Infinite F] [Module.Finite Bᵐᵒᵖ V]
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (g : isometries (hyperbolicPerpPairing p)) : middleIsometry p g ∈ J := by
  let J' := J.comap (middleIsometry p)
  suffices hh : {g : isometries (hyperbolicPerpPairing p) | LineReflection (hyperbolicPerpPairing p) g} ⊆ J' by
    have hle := (Subgroup.closure_le J').mpr hh
    rw [reflectionGeneration hB hd s hs (hyperbolicPerpPairing p)] at hle
    exact hle (Subgroup.mem_top g)
  intro v hv
  obtain ⟨z, r, hz, hr, hzv, hvperp⟩ := hv
  obtain ⟨q₀, hq₀⟩ := (hyperbolicPerpPairing p).central_norm z
  have hq_ne : q₀ ≠ 0 := fun he => hz (by simpa [he] using hq₀)
  let q := Units.mk0 q₀ hq_ne
  let d := threeCoordinates p z hz
  let φ := extendBlock (F := F) (Z := ↥(linePerp (hyperbolicPerpPairing p) z)) d
  have hc : radicalWords s q ≤ (endWords J).comap φ := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨a, b, hab, rfl | rfl⟩
    · exact (threeShears_mem p J hshear (conjugate_involutive hB s hs) z hz q hq₀ a b hab).1
    · exact (threeShears_mem p J hshear (conjugate_involutive hB s hs) z hz q hq₀ a b hab).2
  have hh := hc (lineAndPairScaleWords hB hd s hs q 1 r hr)
  change φ (Matrix.diagonal ![((1 : Bˣ) : B), r, (conjugate s ↑(1 : Bˣ))⁻¹]) ∈ endWords J at hh
  simp only [Units.val_one, conjugate_one, inv_one] at hh
  apply (endWords_mem_iff J (middleIsometry p v)).mp
  convert hh using 1
  apply LinearMap.ext
  intro x
  obtain ⟨⟨y, w⟩, rfl⟩ := d.symm.surjective x
  change (middleIsometry p v).val (d.symm (y, w)) =
    blockHom (F := F) (Z := ↥(linePerp (hyperbolicPerpPairing p) z)) d
      (Matrix.diagonal ![1, r, 1], 1) (d.symm (y, w))
  rw [blockHom_apply, LinearEquiv.apply_symm_apply]
  change (middleIsometry p v).val ((hyperbolicCoordinates p).symm (op (y 0), op (y 2),
    (splitLine (hyperbolicPerpPairing p) z hz).symm (op (y 1), w))) = _
  rw [middleIsometry_apply, reflection_action p z hz r v hzv hvperp]
  have hdiag : Matrix.diagonal ![1, r, 1] *ᵥ y = ![y 0, r * y 1, y 2] := by
    funext j
    fin_cases j <;> simp [Matrix.mulVec_diagonal]
  rw [hdiag]
  rfl

include hshear in
private theorem hyperbolicLevi_mem [Infinite F] [Module.Finite Bᵐᵒᵖ V]
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ x, conjugate s x = quaternionConjugate hB x)
    (g : isometries h)
    (he : Commute g.val.toLinearMap (firstProjector p))
    (hf : Commute g.val.toLinearMap (lastProjector p)) : g ∈ J := by
  let a := h.value p.f (g.val p.e)
  let b := h.value p.e (g.val p.f)
  have hge : g.val p.e = op a • p.e := by
    have hh := congrArg (fun m : Module.End Bᵐᵒᵖ V => m p.e) he.eq
    simpa [a, Module.End.mul_apply, p.fe] using hh
  have hgf : g.val p.f = op b • p.f := by
    have hh := congrArg (fun m : Module.End Bᵐᵒᵖ V => m p.f) hf.eq
    simpa [b, Module.End.mul_apply, p.ef] using hh
  have hab : conjugate s a * b = 1 := by
    have hh := g.property p.e p.f
    rwa [hge, hgf, pairing_smul_both, p.ef, mul_one] at hh
  have ha : a ≠ 0 := by
    intro ha
    simp [ha] at hab
  have hb : b ≠ 0 := by
    intro hb
    simp [hb] at hab
  let t := Units.mk0 a ha
  have hbt : b = (conjugate s (t : B))⁻¹ := eq_inv_of_mul _ _ hab
  have hgo (w : hyperbolicPerp p) : g.val (w : V) ∈ hyperbolicPerp p := by
    obtain ⟨hew, hfw⟩ := (mem_hyperbolicPerp p w).mp w.property
    have e := g.property p.e w
    have f := g.property p.f w
    rw [hge, pairing_smul_left, hew] at e
    rw [hgf, pairing_smul_left, hfw] at f
    exact (mem_hyperbolicPerp p _).mpr
      ⟨(mul_eq_zero.mp e).resolve_left (conjugate_ne_zero s ha),
        (mul_eq_zero.mp f).resolve_left (conjugate_ne_zero s hb)⟩
  have hback (w : hyperbolicPerp p) : g.val.symm (w : V) ∈ hyperbolicPerp p := by
    obtain ⟨hew, hfw⟩ := (mem_hyperbolicPerp p w).mp w.property
    have e := g.property p.e (g.val.symm (w : V))
    have f := g.property p.f (g.val.symm (w : V))
    rw [LinearEquiv.apply_symm_apply, hge, pairing_smul_left, hew, mul_zero] at e
    rw [LinearEquiv.apply_symm_apply, hgf, pairing_smul_left, hfw, mul_zero] at f
    exact (mem_hyperbolicPerp p _).mpr ⟨e.symm, f.symm⟩
  let k : isometries (hyperbolicPerpPairing p) :=
    ⟨{ toFun := fun w => ⟨g.val w, hgo w⟩
       invFun := fun w => ⟨g.val.symm w, hback w⟩
       left_inv := fun w => Subtype.ext (g.val.symm_apply_apply (w : V))
       right_inv := fun w => Subtype.ext (g.val.apply_symm_apply (w : V))
       map_add' := fun x y => Subtype.ext (map_add g.val (x : V) (y : V))
       map_smul' := fun r x => Subtype.ext (map_smul g.val r (x : V)) },
      fun x y => g.property x y⟩
  obtain ⟨j, hj, hje⟩ := pairScales_mem p J hshear hB hd hs t
  have hmid := middleIsometries_mem p J hshear hB hd hs k
  have heq : g = j * middleIsometry p k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    let d := hyperbolicCoordinates p
    obtain ⟨⟨a', b', w⟩, rfl⟩ := d.symm.surjective x
    obtain ⟨c, rfl⟩ := op_surjective a'
    obtain ⟨d', rfl⟩ := op_surjective b'
    change g.val (d.symm (op c, op d', w)) =
      j.val ((middleIsometry p k).val (d.symm (op c, op d', w)))
    rw [middleIsometry_apply]
    have h := congrArg (fun m : Module.End Bᵐᵒᵖ V => m (d.symm (op c, op d', k.val w))) hje
    change j.val (d.symm (op c, op d', k.val w)) =
      blockHom (F := F) (planeCoordinates p)
        (Matrix.diagonal ![(t : B), (conjugate s t)⁻¹], 1) (d.symm (op c, op d', k.val w)) at h
    rw [h, blockHom_apply]
    have hd₂ : planeCoordinates p (d.symm (op c, op d', k.val w)) = (![c, d'], k.val w) := by
      change ((LinearEquiv.prodAssoc Bᵐᵒᵖ _ _ _).symm.trans
        (twoCoefficients.symm.prodCongr (LinearEquiv.refl _ _))) (d (d.symm (op c, op d', k.val w))) = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hd₂]
    change g.val (op c • p.e + op d' • p.f + w) =
      op ((Matrix.diagonal ![(t : B), (conjugate s t)⁻¹] *ᵥ ![c, d']) 0) • p.e +
      op ((Matrix.diagonal ![(t : B), (conjugate s t)⁻¹] *ᵥ ![c, d']) 1) • p.f + (k.val w : V)
    simp only [map_add, map_smul, hge, hgf, smul_smul, ← op_mul, Matrix.mulVec_diagonal]
    change op (a * c) • p.e + op (b * d') • p.f + g.val w =
      op (a * c) • p.e + op ((conjugate s (t : B))⁻¹ * d') • p.f + g.val w
    rw [hbt]
  rw [heq]
  exact J.mul_mem hj hmid

end Hyperbolic

section Approximation

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.GeometricRadicals (IsReductive)
open Specs.RootGroups (IsRootSubgroup rootPoint)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
open AdelicGroups

open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private rootPoint_hasLimit rootPoint_surjective from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private testPointSections contracting_le_unipotentGenerated from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

private theorem section_in_contracting {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k}
    {c : Specs.CharacterDescent.Cocharacter G.val} (D : LimitDecomposition c)
    {p : GroupPoints G.val (CommAlgCat.of k k)} (hp : HasLimit c p 1) :
    testPointSections G.val p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver k)) := by
  obtain ⟨q, rfl⟩ := (D.contracting_points _ p).mp hp
  refine ⟨testPointSections D.contracting.group q, ?_⟩
  change ((rationalSourceIso k).hom ≫ q) ≫ D.contracting.inclusion.hom.hom =
    (rationalSourceIso k).hom ≫ q ≫ D.contracting.inclusion.hom.hom
  exact Category.assoc ..

private theorem splitSymplecticDatum (k : Type u) [Field k] (n : ℕ)
    (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ Specs.SymplecticMatrixStructure.symplecticPoints k
      (Specs.SymplecticDatumTorusAndBorel.HyperbolicIndex.{u} (n + 1))) :
    ∃ P : Specs.Pinning.SplitBorelPair k, P.G = G ∧
      Specs.GeometricRadicals.IsSemisimple G ∧ Specs.SimplyConnectedLattice.GeometricallySimplyConnected G ∧
      Nonempty (Specs.Pinning.AttachedDatum P) := by
  obtain ⟨P, eG, _, D, _, _, _, _, _, _, _, _, _, _, _, _, _, H⟩ :=
    RootData.SymplecticDatum.basedComputation k n G c
  rcases H with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hG, hSC⟩
  exact ⟨P, eG, hG, hSC, ⟨D⟩⟩

private theorem split_root_point_mem {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (hR : IsReductive G) (T : ClosedSubgroup G.val)
    (hs : Specs.GeometricRadicals.IsSplitTorus T.group) (hm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    [IsCommMonObj T.group.X] (D : Specs.AbstractPairing.Datum T)
    {α : Specs.CharacterDescent.Character T.group} (hα : α ∈ absoluteRoots T)
    (U : ClosedSubgroup G.val) (hU : IsRootSubgroup T U α)
    (p : GroupPoints U.group (CommAlgCat.of k k)) :
    testPointSections G.val (p ≫ U.inclusion.hom.hom) ∈ unipotentGenerated G := by
  obtain ⟨V, _, _, _, ⟨A, x, hx⟩, hsame⟩ :=
    ((RootData.RootGroups.rootSubgroups G hR T hs hm).2 α hα).2.2
  obtain ⟨i, hi⟩ := (hsame U hU).2
  let a : Specs.AbstractPairing.Root T := ⟨α, hα⟩
  let y := Additive.toMul (D.rootDatum.coroot a)
  have hy : 0 < pairing T.group α y := by
    have h := D.rootDatum.root_coroot_two a
    rw [D.root_eq] at h
    change D.rootDatum.toLinearMap (Additive.ofMul α) (Additive.ofMul y) = 2 at h
    rw [D.pairing_eq] at h
    omega
  obtain ⟨L⟩ := existsLimitDecomposition G (y ≫ T.inclusion)
  let q : GroupPoints V.group (CommAlgCat.of k k) := p ≫ i.hom.hom
  obtain ⟨b, hb⟩ := rootPoint_surjective x _ q
  have hpoint : rootPoint (x.hom ≫ V.inclusion) (CommAlgCat.of k k) b =
      p ≫ U.inclusion.hom.hom := by
    change (rootPoint x.hom (CommAlgCat.of k k) b) ≫ V.inclusion.hom.hom = _
    rw [hb]
    calc
      _ = p ≫ (i ≫ V.inclusion).hom.hom := Category.assoc ..
      _ = p ≫ U.inclusion.hom.hom := congrArg (fun (f : U.group ⟶ G.val) => p ≫ f.hom.hom) hi
  rw [← hpoint]
  exact contracting_le_unipotentGenerated hR L
    (section_in_contracting L (rootPoint_hasLimit hx y hy _ b))

private theorem subgroup_eq_top_of_generators {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (J : Subgroup N) (roots : Set M)
    (hRoots : Subgroup.closure roots = ⊤)
    (hMem : ∀ q ∈ roots, e q ∈ J) : J = ⊤ := by
  have h := (Subgroup.closure_le (J.comap e.toMonoidHom)).mpr hMem
  rw [hRoots] at h
  apply top_unique
  intro g _
  have hg := h (Subgroup.mem_top (e.symm g))
  change e (e.symm g) ∈ J at hg
  rwa [e.apply_symm_apply] at hg

private theorem split_roots_generate {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (hG : Specs.GeometricRadicals.IsSemisimple G) (hR : IsReductive G)
    (hSC : Specs.SimplyConnectedLattice.GeometricallySimplyConnected G)
    (T : ClosedSubgroup G.val)
    (hs : Specs.GeometricRadicals.IsSplitTorus T.group) (hm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    [IsCommMonObj T.group.X] (D : Specs.AbstractPairing.Datum T) :
    unipotentGenerated G = ⊤ := by
  let R := CommAlgCat.of k k
  let roots : Set (GroupPoints G.val R) :=
    {g | ∃ α ∈ absoluteRoots T, ∃ U : ClosedSubgroup G.val, IsRootSubgroup T U α ∧
      ∃ p : GroupPoints U.group R, p ≫ U.inclusion.hom.hom = g}
  refine subgroup_eq_top_of_generators (testPointSections G.val) (unipotentGenerated G) roots
    (Arithmetic.SplitLocalGeneration.splitLocalGeneration G hG hSC T hs hm) ?_
  rintro _ ⟨α, hα, U, hU, p, rfl⟩
  exact split_root_point_mem hR T hs hm D hα U hU p

theorem splitLocalGeneration : IsotropicTypeC.SplitLocalGeneration.{u} := by
  intro k _ n G c
  obtain ⟨P, eG, hG, hSC, ⟨D⟩⟩ := splitSymplecticDatum k n G c
  let := D.comm
  clear c
  subst G
  exact split_roots_generate hG P.reductive hSC P.T P.split P.maximal D.datum

open private completionPointEquiv completionPointEquiv_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

theorem approximationFromLocalGeneration : ApproximationFromLocalGeneration.{u,v} := by
  intro K _ D G i hG c hc S hS hlocal
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  apply ((Arithmetic.OppositeRadicals.approximation D G i hG c hc P Q).2.2.2.2 S hS).2
  intro w
  have hfull : Arithmetic.OppositeRadicals.localPlus D i w.1 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨p, hp⟩ := (completionPointEquiv D i w.1).surjective g
    refine ⟨p, ?_, (completionPointEquiv_apply D i w.1 p).symm.trans hp⟩
    rw [hlocal w]
    exact Subgroup.mem_top p
  rw [hfull]
  exact dense_univ

end Approximation


open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj LaurentPolynomial

section Contraction

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (MultiplicativeGroup)
open LinearAlgebraicGroups.CocharacterDynamics
open SymplecticIsometryDescent (Involution isometryPoints tensorMap tensorMap_involution)

variable {F A : Type u} [Field F] [Ring A] [Algebra F A]

private structure HyperbolicIdempotents (σ : Involution F A) where
  first : A
  last : A
  first_sq : first * first = first
  last_sq : last * last = last
  first_last : first * last = 0
  last_first : last * first = 0
  adjoint_first : σ.toLinearMap first = last
  adjoint_last : σ.toLinearMap last = first

variable {σ : Involution F A} (P : HyperbolicIdempotents σ)

private def HyperbolicIdempotents.middle : A := 1 - P.first - P.last

private def HyperbolicIdempotents.flip : HyperbolicIdempotents σ where
  first := P.last
  last := P.first
  first_sq := P.last_sq
  last_sq := P.first_sq
  first_last := P.last_first
  last_first := P.first_last
  adjoint_first := P.adjoint_last
  adjoint_last := P.adjoint_first

@[simp] private theorem first_middle : P.first * P.middle = 0 := by
  simp [HyperbolicIdempotents.middle, mul_sub, P.first_sq, P.first_last]
@[simp] private theorem middle_first : P.middle * P.first = 0 := by
  simp [HyperbolicIdempotents.middle, sub_mul, P.first_sq, P.last_first]
@[simp] private theorem last_middle : P.last * P.middle = 0 := by
  simp [HyperbolicIdempotents.middle, mul_sub, P.last_sq, P.last_first]
@[simp] private theorem middle_last : P.middle * P.last = 0 := by
  simp [HyperbolicIdempotents.middle, sub_mul, P.last_sq, P.first_last]
@[simp] private theorem middle_sq : P.middle * P.middle = P.middle := by
  conv_lhs => enter [2]; rw [HyperbolicIdempotents.middle]
  simp [mul_sub]
private theorem first_middle_last : P.first + P.middle + P.last = 1 := by
  simp [HyperbolicIdempotents.middle]; abel
@[simp] private theorem adjoint_middle : σ.toLinearMap P.middle = P.middle := by
  simp only [HyperbolicIdempotents.middle, map_sub, σ.map_one, P.adjoint_first, P.adjoint_last]
  abel

private def hyperbolicScaleValue (R : TestAlgebra F) (t : Rˣ) : R ⊗[F] A :=
  (t : R) ⊗ₜ[F] P.first + (1 : R) ⊗ₜ[F] P.middle + (↑t⁻¹ : R) ⊗ₜ[F] P.last

private theorem hyperbolicScaleValue_one (R : TestAlgebra F) :
    hyperbolicScaleValue P R 1 = 1 := by
  unfold hyperbolicScaleValue
  simp only [Units.val_one, inv_one, ← TensorProduct.tmul_add, first_middle_last, Algebra.TensorProduct.one_def]

private theorem hyperbolicScaleValue_mul (R : TestAlgebra F) (s t : Rˣ) :
    hyperbolicScaleValue P R s * hyperbolicScaleValue P R t =
      hyperbolicScaleValue P R (s * t) := by
  simp only [hyperbolicScaleValue, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    P.first_sq, P.last_sq, P.first_last, P.last_first, first_middle, middle_first,
    last_middle, middle_last, middle_sq, TensorProduct.tmul_zero, zero_add, add_zero, one_mul,
    mul_one, Units.val_mul, mul_inv_rev]
  rw [mul_comm (↑s⁻¹ : R) (↑t⁻¹ : R)]

private theorem adjoint_hyperbolicScale (R : TestAlgebra F) (t : Rˣ) :
    (σ.baseChange R).toLinearMap (hyperbolicScaleValue P R t) =
      hyperbolicScaleValue P R t⁻¹ := by
  simp only [hyperbolicScaleValue, map_add, Involution.baseChange_tmul,
    P.adjoint_first, P.adjoint_last, adjoint_middle, inv_inv]
  abel

private def hyperbolicScale (R : TestAlgebra F) : Rˣ →* (isometryPoints σ).obj R where
  toFun t := ⟨{
    val := hyperbolicScaleValue P R t
    inv := hyperbolicScaleValue P R t⁻¹
    val_inv := by rw [hyperbolicScaleValue_mul, mul_inv_cancel, hyperbolicScaleValue_one]
    inv_val := by rw [hyperbolicScaleValue_mul, inv_mul_cancel, hyperbolicScaleValue_one]}, by
      change (σ.baseChange R).toLinearMap (hyperbolicScaleValue P R t) *
        hyperbolicScaleValue P R t = 1
      rw [adjoint_hyperbolicScale, hyperbolicScaleValue_mul, inv_mul_cancel, hyperbolicScaleValue_one]⟩
  map_one' := Subtype.ext (Units.ext (hyperbolicScaleValue_one P R))
  map_mul' s t := Subtype.ext (Units.ext (hyperbolicScaleValue_mul P R s t).symm)

private theorem hyperbolicScale_natural {R S : TestAlgebra F} (a : R ⟶ S) (t : Rˣ) :
    (isometryPoints σ).map a (hyperbolicScale P R t) =
      hyperbolicScale P S (Units.map a.hom.toMonoidHom t) := by
  apply Subtype.ext
  apply Units.ext
  change tensorMap a (hyperbolicScaleValue P R t) =
    hyperbolicScaleValue P S (Units.map a.hom.toMonoidHom t)
  simp [hyperbolicScaleValue, tensorMap, Algebra.TensorProduct.map_tmul]

private def constantIsometry (R : TestAlgebra F) : σ.isometries →* (isometryPoints σ).obj R :=
  σ.mapIsometries (σ.baseChange R) (Algebra.TensorProduct.includeRight.toRingHom) (fun _ => rfl)

private theorem constantIsometry_natural {R S : TestAlgebra F} (a : R ⟶ S) (g : σ.isometries) :
    (isometryPoints σ).map a (constantIsometry R g) = constantIsometry S g := by
  apply Subtype.ext
  apply Units.ext
  change tensorMap a (1 ⊗ₜ[F] (g.val : A)) = (1 : S) ⊗ₜ[F] (g.val : A)
  simp [Algebra.TensorProduct.map_tmul]

private theorem constantIsometry_bijective :
    Function.Bijective (constantIsometry (σ := σ) (CommAlgCat.of F F)) := by
  let e := Algebra.TensorProduct.lid F A
  have h₁ (x : A) : e.symm x = (1 : F) ⊗ₜ[F] x := by
    apply e.injective
    simp [e]
  have h₂ (x : A) : (σ.baseChange F).toLinearMap (e.symm x) = e.symm (σ.toLinearMap x) := by
    simp [h₁]
  constructor
  · intro x y h
    apply Subtype.ext
    apply Units.ext
    apply e.symm.injective
    rw [h₁, h₁]
    exact congrArg (fun z : (isometryPoints σ).obj (CommAlgCat.of F F) =>
      (z.val : F ⊗[F] A)) h
  · intro y
    let x := Units.map e.toMonoidHom y.val
    have hx : x ∈ σ.isometries := by
      apply (σ.mem_isometries x).mpr
      apply e.symm.injective
      rw [map_mul, map_one, ← h₂]
      change (σ.baseChange F).toLinearMap (e.symm (e y.val.val)) * e.symm (e y.val.val) = 1
      rw [e.symm_apply_apply]
      exact y.property
    refine ⟨⟨x, hx⟩, Subtype.ext (Units.ext ?_)⟩
    change (1 : F) ⊗ₜ[F] (e (y.val : F ⊗[F] A)) = y.val.val
    rw [← h₁, e.symm_apply_apply]

private theorem hyperbolicScaleValue_first_right (R : TestAlgebra F) (t : Rˣ) :
    hyperbolicScaleValue P R t * ((1 : R) ⊗ₜ[F] P.first) = (t : R) ⊗ₜ[F] P.first := by
  simp [hyperbolicScaleValue, add_mul, Algebra.TensorProduct.tmul_mul_tmul, P.first_sq, P.last_first]

private theorem hyperbolicScaleValue_middle_right (R : TestAlgebra F) (t : Rˣ) :
    hyperbolicScaleValue P R t * ((1 : R) ⊗ₜ[F] P.middle) = (1 : R) ⊗ₜ[F] P.middle := by
  simp [hyperbolicScaleValue, add_mul, Algebra.TensorProduct.tmul_mul_tmul]

private theorem hyperbolicScaleValue_middle_left (R : TestAlgebra F) (t : Rˣ) :
    ((1 : R) ⊗ₜ[F] P.middle) * hyperbolicScaleValue P R t = (1 : R) ⊗ₜ[F] P.middle := by
  simp [hyperbolicScaleValue, mul_add, Algebra.TensorProduct.tmul_mul_tmul]

private theorem hyperbolicScaleValue_last_left (R : TestAlgebra F) (t : Rˣ) :
    ((1 : R) ⊗ₜ[F] P.last) * hyperbolicScaleValue P R t⁻¹ = (t : R) ⊗ₜ[F] P.last := by
  simp [hyperbolicScaleValue, mul_add, Algebra.TensorProduct.tmul_mul_tmul, P.last_sq, P.last_first]

private def IsUpper (x : A) : Prop :=
  x = 1 + (P.first * x * P.middle + P.middle * x * P.last) + P.first * x * P.last

private theorem conjugate_upper_value (x : A) (hx : IsUpper P x) (R : TestAlgebra F) (t : Rˣ) :
    hyperbolicScaleValue P R t * ((1 : R) ⊗ₜ[F] x) * hyperbolicScaleValue P R t⁻¹ =
      1 + (t : R) ⊗ₜ[F] (P.first * x * P.middle + P.middle * x * P.last) +
        ((t : R) ^ 2) ⊗ₜ[F] (P.first * x * P.last) := by
  let l := hyperbolicScaleValue P R t
  let r := hyperbolicScaleValue P R t⁻¹
  have h (a b : A) :
      l * ((1 : R) ⊗ₜ[F] (a * x * b)) * r =
        (l * ((1 : R) ⊗ₜ[F] a)) * ((1 : R) ⊗ₜ[F] x) * (((1 : R) ⊗ₜ[F] b) * r) := by
    have h' : (1 : R) ⊗ₜ[F] (a * x * b) =
        ((1 : R) ⊗ₜ[F] a) * ((1 : R) ⊗ₜ[F] x) * ((1 : R) ⊗ₜ[F] b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h']
    noncomm_ring
  change l * ((1 : R) ⊗ₜ[F] x) * r = _
  nth_rw 1 [show x = _ from hx]
  simp only [TensorProduct.tmul_add, ← Algebra.TensorProduct.one_def, mul_add, add_mul, mul_one]
  rw [h, h, h, show l * r = 1 from by
    simp [l, r, hyperbolicScaleValue_mul, hyperbolicScaleValue_one]]
  simp only [l, r, hyperbolicScaleValue_first_right, hyperbolicScaleValue_middle_right,
    hyperbolicScaleValue_middle_left, hyperbolicScaleValue_last_left,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, pow_two, add_assoc]

open private unitEquiv unitEquiv_unitPoint unitPointHom_apply opposite_point from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {G : AffineAlgebraicGroup F}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scaleMorphism
    (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ) :
    (groupPointsFunctor F).obj (MultiplicativeGroup F) ⟶ (groupPointsFunctor F).obj G.val where
  app R := GrpCat.ofHom ((i.inv.app R).hom.comp ((hyperbolicScale P R).comp
    (unitEquiv R).toMonoidHom))
  naturality R S f := by
    apply GrpCat.ext
    intro x
    let t := unitEquiv R x
    have hx : unitPoint R t = x := (unitEquiv R).injective (unitEquiv_unitPoint R t)
    have hf := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (i.inv.naturality f))
      (hyperbolicScale P R t)
    change i.inv.app S (hyperbolicScale P S (unitEquiv S (mapPoints f x))) =
      ((groupPointsFunctor F).obj G.val).map f (i.inv.app R (hyperbolicScale P R t))
    rw [← hx, mapPoints_unitPoint, unitEquiv_unitPoint, ← hyperbolicScale_natural]
    exact hf

private noncomputable def scaleCocharacter
    (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ) : Cocharacter G.val :=
  (groupHomEquiv (MultiplicativeGroup F) G.val (by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance)).symm (scaleMorphism P i)

private theorem scaleCocharacter_apply
    (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ)
    (R : TestAlgebra F) (t : Rˣ) :
    i.hom.app R (cocharacterPoint (scaleCocharacter P i) R t) = hyperbolicScale P R t := by
  have h := (groupHomEquiv (MultiplicativeGroup F) G.val (by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance)).apply_symm_apply (scaleMorphism P i)
  change (groupPointsFunctor F).map (scaleCocharacter P i) = scaleMorphism P i at h
  unfold cocharacterPoint
  rw [h]
  change i.hom.app R (i.inv.app R (hyperbolicScale P R (unitEquiv R (unitPoint R t)))) = _
  rw [unitEquiv_unitPoint]
  exact (i.app R).groupIsoToMulEquiv.apply_symm_apply _

private theorem hyperbolicScaleValue_flip (R : TestAlgebra F) (t : Rˣ) :
    hyperbolicScaleValue P.flip R t = hyperbolicScaleValue P R t⁻¹ := by
  have hm : P.flip.middle = P.middle := by simp [HyperbolicIdempotents.middle, HyperbolicIdempotents.flip]; abel
  unfold hyperbolicScaleValue
  rw [hm]
  simp only [HyperbolicIdempotents.flip, inv_inv]
  abel

private theorem scaleCocharacter_opposite
    (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ) :
    scaleCocharacter P.flip i = oppositeCocharacter (scaleCocharacter P i) := by
  apply (groupHomEquiv (MultiplicativeGroup F) G.val (by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance)).injective
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  obtain ⟨t, rfl⟩ := (unitEquiv R).symm.surjective x
  change (((groupPointsFunctor F).map (scaleCocharacter P.flip i)).app R) ((unitEquiv R).symm t) =
    (((groupPointsFunctor F).map (oppositeCocharacter (scaleCocharacter P i))).app R)
      ((unitEquiv R).symm t)
  rw [show (unitEquiv R).symm t = unitPoint R t from unitPointHom_apply R t]
  change cocharacterPoint (scaleCocharacter P.flip i) R t =
    cocharacterPoint (oppositeCocharacter (scaleCocharacter P i)) R t
  rw [opposite_point]
  apply (i.app R).groupIsoToMulEquiv.injective
  change i.hom.app R (cocharacterPoint (scaleCocharacter P.flip i) R t) =
    i.hom.app R (cocharacterPoint (scaleCocharacter P i) R t⁻¹)
  rw [scaleCocharacter_apply, scaleCocharacter_apply]
  exact Subtype.ext (Units.ext (hyperbolicScaleValue_flip P R t))

private noncomputable def intoScheme (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ) :
    σ.isometries ≃* GroupPoints G.val (CommAlgCat.of F F) :=
  (MulEquiv.ofBijective _ constantIsometry_bijective).trans (i.app _).groupIsoToMulEquiv.symm

private theorem intoScheme_spec (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ)
    (x : σ.isometries) : i.hom.app _ (intoScheme i x) = constantIsometry _ x :=
  (i.app _).groupIsoToMulEquiv.apply_symm_apply _

/- The positive corners have weights one and two, so their orbit extends
over the affine line with value one at zero. -/
set_option backward.isDefEq.respectTransparency false in
private theorem scaleHasLimit
    (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ)
    (x : σ.isometries) (hx : IsUpper P (x.val : A)) :
    HasLimit (scaleCocharacter P i) (intoScheme i x) 1 := by
  let R := CommAlgCat.of F F
  let S := polynomialAlgebra R
  let T := laurentAlgebra R
  let j := tensorMap (A := A) (polynomialToLaurent R)
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat _ _ Polynomial.toLaurent_injective Function.injective_id
  let d := hyperbolicScale P T (laurentParameter R)
  let g := d * constantIsometry T x * d⁻¹
  let y : S ⊗[F] A :=
    1 + (Polynomial.X : S) ⊗ₜ[F] (P.first * x.val.val * P.middle + P.middle * x.val.val * P.last) +
      (Polynomial.X ^ 2 : S) ⊗ₜ[F] (P.first * x.val.val * P.last)
  have hy : j y = g.val.val := by
    change j y = hyperbolicScaleValue P T (laurentParameter R) *
      ((1 : T) ⊗ₜ[F] (x.val : A)) * hyperbolicScaleValue P T (laurentParameter R)⁻¹
    rw [conjugate_upper_value P _ hx]
    simp [j, y, tensorMap, Algebra.TensorProduct.map_tmul, polynomialToLaurent, laurentParameter,
      pow_two]
  have hy' : j ((σ.baseChange S).toLinearMap y) = (g.val⁻¹ : (T ⊗[F] A)ˣ).val := by
    change tensorMap (polynomialToLaurent R) ((σ.baseChange S).toLinearMap y) = _
    rw [tensorMap_involution]
    change (σ.baseChange T).toLinearMap (j y) = _
    rw [hy]
    exact (Units.mul_left_inj g.val).mp (g.property.trans g.val.inv_val.symm)
  have hl : (σ.baseChange S).toLinearMap y * y = 1 := by
    apply hj
    rw [map_mul, map_one, hy, hy']
    exact g.val.inv_val
  have hr : y * (σ.baseChange S).toLinearMap y = 1 := by
    apply hj
    rw [map_mul, map_one, hy, hy']
    exact g.val.val_inv
  let p : (isometryPoints σ).obj S := ⟨⟨y, (σ.baseChange S).toLinearMap y, hr, hl⟩, hl⟩
  refine ⟨i.inv.app S p, ?_, ?_⟩
  · apply (i.app T).groupIsoToMulEquiv.injective
    change i.hom.app T _ = i.hom.app T _
    have hnat := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (i.hom.naturality (polynomialToLaurent R)).symm) (i.inv.app S p)
    change (isometryPoints σ).map (polynomialToLaurent R) (i.hom.app S (i.inv.app S p)) =
      i.hom.app T (mapPoints (polynomialToLaurent R) (i.inv.app S p)) at hnat
    rw [← hnat]
    rw [show i.hom.app S (i.inv.app S p) = p from
      (i.app S).groupIsoToMulEquiv.apply_symm_apply p]
    have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (i.hom.naturality (laurentConstants R)).symm) (intoScheme i x)
    change (isometryPoints σ).map (laurentConstants R) (i.hom.app R (intoScheme i x)) =
      i.hom.app T (mapPoints (laurentConstants R) (intoScheme i x)) at h
    have h' : i.hom.app T (orbit (scaleCocharacter P i) (intoScheme i x)) = g := by
      unfold orbit
      change (i.hom.app T).hom (_ * _ * _) = _
      rw [map_mul, map_mul, map_inv, scaleCocharacter_apply, ← h, intoScheme_spec,
        constantIsometry_natural]
    rw [h']
    exact Subtype.ext (Units.ext hy)
  · apply (i.app R).groupIsoToMulEquiv.injective
    change i.hom.app R _ = i.hom.app R _
    have hnat := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (i.hom.naturality (polynomialEvaluate R 0)).symm) (i.inv.app S p)
    change (isometryPoints σ).map (polynomialEvaluate R 0) (i.hom.app S (i.inv.app S p)) =
      i.hom.app R (mapPoints (polynomialEvaluate R 0) (i.inv.app S p)) at hnat
    rw [← hnat]
    rw [show i.hom.app S (i.inv.app S p) = p from
      (i.app S).groupIsoToMulEquiv.apply_symm_apply p]
    rw [show i.hom.app R (1 : GroupPoints G.val R) = 1 from (i.hom.app R).hom.map_one]
    apply Subtype.ext
    apply Units.ext
    change tensorMap (polynomialEvaluate R 0) y = 1
    simp [y, tensorMap, Algebra.TensorProduct.map_tmul, polynomialEvaluate]


private noncomputable def laurentCoeffLinear (m : ℤ) : LaurentPolynomial F →ₗ[F] F where
  toFun a := a.coeff m
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private noncomputable def tensorCoefficient (m : ℤ) : LaurentPolynomial F ⊗[F] A →ₗ[F] A :=
  (Algebra.TensorProduct.lid F A).toLinearMap.comp
    (TensorProduct.map (laurentCoeffLinear m) (LinearMap.id : A →ₗ[F] A))

private theorem tensorCoefficient_T (m k : ℤ) (a : A) :
    tensorCoefficient m ((LaurentPolynomial.T k : LaurentPolynomial F) ⊗ₜ[F] a) =
      if k = m then a else 0 := by
  have h : laurentCoeffLinear (F := F) m (LaurentPolynomial.T k) =
      if k = m then 1 else 0 := by
    change (AddMonoidAlgebra.single k (1 : F)).coeff m = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  change (Algebra.TensorProduct.lid F A)
    (TensorProduct.map (laurentCoeffLinear m) (LinearMap.id : A →ₗ[F] A)
      (LaurentPolynomial.T k ⊗ₜ[F] a)) = _
  rw [TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, h]
  split <;> simp

open private centralizes_onAlgebras from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

/- The Laurent coefficients at one and minus one detect the two line projections. -/
set_option backward.isDefEq.respectTransparency false in
private theorem centralizer_commutes_projectors
    (i : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ)
    (x : σ.isometries) (hx : Centralizes (scaleCocharacter P i) (intoScheme i x)) :
    Commute (x.val : A) P.first ∧ Commute (x.val : A) P.last := by
  let R := CommAlgCat.of F F
  let S := laurentAlgebra R
  let t := laurentParameter R
  have h := (centralizes_onAlgebras (scaleCocharacter P i) (R := R) (intoScheme i x)).mp hx S
    (laurentConstants R) t
  have hcomm := h.map (i.hom.app S).hom
  have hnat := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (i.hom.naturality (laurentConstants R))) (intoScheme i x)
  change i.hom.app S (mapPoints (laurentConstants R) (intoScheme i x)) =
    (isometryPoints σ).map (laurentConstants R) (i.hom.app R (intoScheme i x)) at hnat
  change Commute (i.hom.app S (mapPoints (laurentConstants R) (intoScheme i x)))
    (i.hom.app S (cocharacterPoint (scaleCocharacter P i) S t)) at hcomm
  rw [hnat, intoScheme_spec, constantIsometry_natural, scaleCocharacter_apply] at hcomm
  have hval := congrArg (fun y : (isometryPoints σ).obj S => y.val.val) hcomm.eq
  change ((1 : S) ⊗ₜ[F] (x.val : A)) * hyperbolicScaleValue P S t =
    hyperbolicScaleValue P S t * ((1 : S) ⊗ₜ[F] (x.val : A)) at hval
  simp only [t, hyperbolicScaleValue, laurentParameter, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at hval
  rw [← LaurentPolynomial.T_zero] at hval
  change (LaurentPolynomial.T 1 : LaurentPolynomial F) ⊗ₜ[F] ((x.val : A) * P.first) +
      (LaurentPolynomial.T 0 : LaurentPolynomial F) ⊗ₜ[F] ((x.val : A) * P.middle) +
      (LaurentPolynomial.T (-1) : LaurentPolynomial F) ⊗ₜ[F] ((x.val : A) * P.last) =
    (LaurentPolynomial.T 1 : LaurentPolynomial F) ⊗ₜ[F] (P.first * (x.val : A)) +
      (LaurentPolynomial.T 0 : LaurentPolynomial F) ⊗ₜ[F] (P.middle * (x.val : A)) +
      (LaurentPolynomial.T (-1) : LaurentPolynomial F) ⊗ₜ[F] (P.last * (x.val : A)) at hval
  have h₁ := congrArg (tensorCoefficient (A := A) (F := F) 1) hval
  have h₂ := congrArg (tensorCoefficient (A := A) (F := F) (-1)) hval
  constructor
  · unfold Commute SemiconjBy
    simpa only [map_add, tensorCoefficient_T, ite_true, ite_false, add_zero, zero_add,
      show (0 : ℤ) ≠ 1 by decide, show (-1 : ℤ) ≠ 1 by decide] using h₁
  · unfold Commute SemiconjBy
    simpa only [map_add, tensorCoefficient_T, ite_true, ite_false, add_zero, zero_add,
      show (0 : ℤ) ≠ -1 by decide, show (1 : ℤ) ≠ -1 by decide] using h₂

end Contraction

section QuaternionMatrixModel

open LinearAlgebraicGroups.Specs
open Specs.SymplecticInvolutionModels (AntiAutomorphism HermitianPairing)
open SymplecticIsometryDescent (Involution isometryPoints)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open QuaternionHermitianCocharacters (adjoint adjoint_mul adjoint_one pairing mem_isometries_iff)
open Specs.SymplecticDivisionForms (dagger tensorMap intoTensor)
open private dagger_add dagger_smul extendEquiv matrixBaseChange matrixBaseChange_natural
  quaternion_point_compare hermitianValue_laws from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private hermitianValue_pairing quaternionIsometryComparison from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {n : ℕ}
variable (s : AntiAutomorphism F B) (H : (Matrix (Fin n) (Fin n) B)ˣ)
variable (hs : Function.Involutive (fun x : B => unop (s x))) (hH : dagger s H.val = H.val)

private def matrixHermitian
    (hne : ∀ x : Fin n → B, x ≠ 0 → ∃ y, pairing s.toAlgHom H.val x y ≠ 0)
    (hn : ∀ x, ∃ a : F, pairing s.toAlgHom H.val x x = algebraMap F B a) :
    HermitianPairing s (Fin n → B) := by
  have h := hermitianValue_laws s hs H.val hH
  rw [hermitianValue_pairing] at h
  exact
    { value := pairing s.toAlgHom H.val
      add_right := h.add_right
      smul_right := h.mul_right
      hermitian := h.symmetric
      nondegenerate := hne
      central_norm := hn }

include hs hH in
private def gramInvolution : Involution F (Matrix (Fin n) (Fin n) B) where
  toLinearMap :=
    { toFun := fun X => H.inv * adjoint s.toAlgHom X * H.val
      map_add' := fun X Y => by
        change H.inv * dagger s (X + Y) * H.val = _
        simp [dagger_add, mul_add, add_mul]; rfl
      map_smul' := fun a X => by
        change H.inv * dagger s (a • X) * H.val = a • (H.inv * dagger s X * H.val)
        rw [dagger_smul, mul_smul_comm, smul_mul_assoc] }
  map_one := by
    change H.inv * adjoint s.toAlgHom 1 * H.val = 1
    rw [adjoint_one, mul_one, H.inv_val]
  map_mul X Y := by
    change H.inv * adjoint s.toAlgHom (X * Y) * H.val =
      (H.inv * adjoint s.toAlgHom Y * H.val) * (H.inv * adjoint s.toAlgHom X * H.val)
    rw [adjoint_mul]
    simp only [mul_assoc, ← mul_assoc H.val H.inv, H.val_inv, one_mul]
  involutive X := by
    have hH₁ : adjoint s.toAlgHom H.val = H.val := hH
    have hH₂ : adjoint s.toAlgHom H.inv = H.inv := by
      apply (Units.mul_left_inj H).mp
      have h := congrArg (adjoint s.toAlgHom) H.val_inv
      rwa [adjoint_mul, adjoint_one, hH₁, ← H.inv_val] at h
    have hXX : adjoint s.toAlgHom (adjoint s.toAlgHom X) = X := by
      ext i j
      exact hs (X i j)
    change H.inv * adjoint s.toAlgHom (H.inv * adjoint s.toAlgHom X * H.val) * H.val = X
    rw [adjoint_mul, adjoint_mul, hH₁, hH₂, hXX]
    calc
      _ =
        (H.inv * H.val) * X * (H.inv * H.val) := by simp only [mul_assoc]
      _ = X := by rw [H.inv_val, one_mul, mul_one]

private noncomputable def gramInvolutionComparison :
    isometryPoints (gramInvolution s H (hs := hs) (hH := hH)) ≅
      QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H.val := by
  let σ := gramInvolution s H (hs := hs) (hH := hH)
  let e : Matrix (Fin n) (Fin n) B ≃ₐ[F] Matrix (Fin n) (Fin n) B := AlgEquiv.refl
  let E (R : Type u) [CommRing R] [Algebra F R] :=
    (extendEquiv (R := R) e).trans (matrixBaseChange (R := R) (Fin n))
  exact quaternionIsometryComparison σ s H.val E
    (fun R _ _ a => quaternion_point_compare (toDivisionInvolution σ).anti s H e (fun _ => rfl) a)
    (fun R T _ _ _ _ f x => matrixBaseChange_natural f e x)

set_option maxHeartbeats 30000 in
private theorem gramInvolution_isometry (g : (Matrix (Fin n) (Fin n) B)ˣ) :
    g ∈ (gramInvolution s H (hs := hs) (hH := hH)).isometries ↔
      ∀ x y, pairing s.toAlgHom H.val (g.val.mulVec x) (g.val.mulVec y) =
        pairing s.toAlgHom H.val x y := by
  rw [← mem_isometries_iff]
  change H.inv * adjoint s.toAlgHom g.val * H.val * g.val = 1 ↔
    adjoint s.toAlgHom g.val * H.val * g.val = H.val
  calc
    _ ↔ H.inv * (adjoint s.toAlgHom g.val * H.val * g.val) = H.inv * H.val := by
      rw [H.inv_val]
      simp only [mul_assoc]
    _ ↔ _ := Units.mul_right_inj H⁻¹

set_option maxHeartbeats 30000 in
private theorem gramInvolution_adjoint (X : Matrix (Fin n) (Fin n) B) (x y : Fin n → B) :
    pairing s.toAlgHom H.val (X.mulVec x) y =
      pairing s.toAlgHom H.val x (((gramInvolution s H (hs := hs) (hH := hH)).toLinearMap X).mulVec y) := by
  let col (v : Fin n → B) : Matrix (Fin n) Unit B := fun i _ => v i
  change ((adjoint s.toAlgHom (X * col x) * H.val) * col y) () () =
    ((adjoint s.toAlgHom (col x) * H.val) * ((H.inv * adjoint s.toAlgHom X * H.val) * col y)) () ()
  rw [adjoint_mul]
  have h : H.val * ((H.inv * adjoint s.toAlgHom X * H.val) * col y) =
      (adjoint s.toAlgHom X * H.val) * col y := by
    calc
      _ = ((H.val * H.inv) * adjoint s.toAlgHom X * H.val) * col y := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [H.val_inv, one_mul]
  rw [Matrix.mul_assoc (adjoint s.toAlgHom (col x)) H.val, h]
  simp only [Matrix.mul_assoc]

end QuaternionMatrixModel

section QuaternionGeneration

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.IsotropicTypeC
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open LinearAlgebraicGroups.CocharacterDynamics
open SymplecticIsometryDescent (Involution isometryPoints)
open QuaternionHermitianCocharacters (adjoint pairing)
open Specs.SymplecticDivisionForms (dagger)

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {n : ℕ}
variable (s : AntiAutomorphism F B) (H : (Matrix (Fin n) (Fin n) B)ˣ)
variable (hs : Function.Involutive (conjugate s)) (hH : dagger s H.val = H.val)
variable (hne : ∀ x : Fin n → B, x ≠ 0 → ∃ y, pairing s.toAlgHom H.val x y ≠ 0)
variable (hn : ∀ x, ∃ a : F, pairing s.toAlgHom H.val x x = algebraMap F B a)

private noncomputable def ambientIsometryEquiv :
    (gramInvolution s H (hs := hs) (hH := hH)).isometries ≃*
      isometries (matrixHermitian s H hs hH hne hn) := by
  let e := (Units.mapEquiv (rightMatrix (F := F) (B := B) (I := Fin n)).toMulEquiv).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Bᵐᵒᵖ (Fin n → B))
  have hact (g : (Matrix (Fin n) (Fin n) B)ˣ) (x : Fin n → B) : e g x = g.val.mulVec x :=
    rightMatrix_apply g.val x
  have hp (g : (Matrix (Fin n) (Fin n) B)ˣ) :
      g ∈ (gramInvolution s H (hs := hs) (hH := hH)).isometries ↔
        e g ∈ isometries (matrixHermitian s H hs hH hne hn) := by
    change g ∈ _ ↔ ∀ x y, pairing s.toAlgHom H.val (e g x) (e g y) =
      pairing s.toAlgHom H.val x y
    simpa only [hact] using gramInvolution_isometry s H (hs := hs) (hH := hH) g
  exact
    { toFun := fun a => ⟨e a.val, (hp a.val).mp a.property⟩
      invFun := fun a => ⟨e.symm a.val, (hp _).mpr (by
        rw [e.apply_symm_apply]
        exact a.property)⟩
      left_inv := fun _ => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun _ => Subtype.ext (e.apply_symm_apply _)
      map_mul' := fun x y => Subtype.ext (map_mul e x.val y.val) }

private theorem ambientIsometryEquiv_toLinearMap
    (g : (gramInvolution s H (hs := hs) (hH := hH)).isometries) :
    (ambientIsometryEquiv s H hs hH hne hn g).val.toLinearMap =
      rightMatrix (F := F) (g.val : Matrix (Fin n) (Fin n) B) := rfl

private theorem pairing_separates_right {h : HermitianPairing s (Fin n → B)} {x y : Fin n → B}
    (heq : ∀ z, h.value z x = h.value z y) : x = y := by
  apply sub_eq_zero.mp
  by_contra hn
  obtain ⟨z, hz⟩ := h.nondegenerate (x - y) hn
  apply hz
  rw [pairing_symm h z (x - y), pairing_sub_right, heq, sub_self, conjugate_zero]

private noncomputable def matrixHyperbolicIdempotents
    (p : HyperbolicPair (matrixHermitian s H hs hH hne hn)) :
    HyperbolicIdempotents (gramInvolution s H (hs := hs) (hH := hH)) := by
  let E := rightMatrix (F := F) (B := B) (I := Fin n)
  let a := E.symm (firstProjector p)
  let b := E.symm (lastProjector p)
  have ha : E a = firstProjector p := E.apply_symm_apply _
  have hb : E b = lastProjector p := E.apply_symm_apply _
  have haAdj : (gramInvolution s H (hs := hs) (hH := hH)).toLinearMap a = b := by
    apply E.injective
    apply LinearMap.ext
    intro y
    rw [hb]
    apply pairing_separates_right (F := F) (B := B) (n := n) s
      (h := matrixHermitian s H hs hH hne hn)
    intro x
    change pairing s.toAlgHom H.val x (E _ y) = _
    rw [show E ((gramInvolution s H (hs := hs) (hH := hH)).toLinearMap a) y =
      ((gramInvolution s H (hs := hs) (hH := hH)).toLinearMap a).mulVec y from rightMatrix_apply (F := F) _ _]
    rw [← gramInvolution_adjoint s H (hs := hs) (hH := hH)]
    have hf : a.mulVec x = firstProjector p x := (rightMatrix_apply (F := F) a x).symm.trans
      (congrArg (fun e : Module.End Bᵐᵒᵖ (Fin n → B) => e x) ha)
    rw [hf]
    exact pairing_firstProjector p x y
  refine ⟨a, b, ?_, ?_, ?_, ?_, haAdj, ?_⟩
  · apply E.injective
    rw [map_mul, ha]
    exact firstProjector_squared p
  · apply E.injective
    rw [map_mul, hb]
    exact lastProjector_squared p
  · apply E.injective
    rw [map_mul, map_zero, ha, hb]
    exact firstProjector_mul_last p
  · apply E.injective
    rw [map_mul, map_zero, ha, hb]
    exact lastProjector_mul_first p
  · rw [← haAdj]
    exact (gramInvolution s H (hs := hs) (hH := hH)).involutive a

open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 60000 in
theorem quaternionLocalGeneration : QuaternionLocalGeneration.{u} := by
  classical
  intro F _ _ G hR B _ _ hB hd s hs n H hH i h₀ hne hn e f hee hff hef hfe
  let si := conjugate_involutive hB s hs
  let h := matrixHermitian s H si hH hne hn
  let p : HyperbolicPair h := ⟨e, f, hee, hff, hef, hfe⟩
  let σ := gramInvolution s H (hs := si) (hH := hH)
  let i' : (groupPointsFunctor F).obj G.val ≅ isometryPoints σ :=
    i ≪≫ (gramInvolutionComparison s H si hH).symm
  let P := matrixHyperbolicIdempotents s H si hH hne hn p
  let c := scaleCocharacter P i'
  obtain ⟨D⟩ := existsLimitDecomposition G c
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  let X := SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections E.contracting (𝟙_ (SchemeOver F))
  let χ : σ.isometries ≃* isometries h := ambientIsometryEquiv s H si hH hne hn
  let ψ : isometries h ≃* (𝟙_ (SchemeOver F) ⟶ G.val.X) :=
    χ.symm.trans ((intoScheme i').trans (testPointSections G.val))
  let J := X.comap ψ.toMonoidHom
  let a := rightMatrix (F := F) (B := B) (I := Fin n)
  have hp : a P.first = firstProjector p := a.apply_symm_apply _
  have hq : a P.last = lastProjector p := a.apply_symm_apply _
  have hm : a P.middle = hyperbolicProjection p := by
    unfold HyperbolicIdempotents.middle
    rw [map_sub, map_sub, map_one, hp, hq, hyperbolicProjection_def]
  have hpoint (g : isometries h) :
      a ((χ.symm g).val : Matrix (Fin n) (Fin n) B) = g.val.toLinearMap := by
    rw [← ambientIsometryEquiv_toLinearMap s H si hH hne hn]
    change (χ (χ.symm g)).val.toLinearMap = _
    rw [χ.apply_symm_apply]
  have hshear (g : isometries h) (hg : IsUpperEnd p g.val.toLinearMap ∨
      IsUpperEnd p.flip g.val.toLinearMap) : g ∈ J := by
    rcases hg with hu | hl
    · have hu' : IsUpper P ((χ.symm g).val : Matrix (Fin n) (Fin n) B) := by
        unfold IsUpper
        apply a.injective
        simp only [map_one, map_add, map_mul, hp, hq, hm, hpoint]
        exact hu
      change ψ g ∈ X
      exact (le_sup_left : SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ≤ X)
        (section_in_contracting D (scaleHasLimit P i' (χ.symm g) hu'))
    · have hl' : IsUpper P.flip ((χ.symm g).val : Matrix (Fin n) (Fin n) B) := by
        have hm' : a P.flip.middle = hyperbolicProjection p.flip := by
          unfold HyperbolicIdempotents.middle
          change a (1 - P.last - P.first) = _
          rw [map_sub, map_sub, map_one, hp, hq, hyperbolicProjection_def]
          rfl
        unfold IsUpper
        apply a.injective
        simp only [map_one, map_add, map_mul, hm', hpoint]
        change g.val.toLinearMap = 1 +
          (a P.last * g.val.toLinearMap * hyperbolicProjection p.flip +
            hyperbolicProjection p.flip * g.val.toLinearMap * a P.first) +
          a P.last * g.val.toLinearMap * a P.first
        rw [hp, hq]
        exact hl
      have hl'' := scaleHasLimit P.flip i' (χ.symm g) hl'
      rw [scaleCocharacter_opposite] at hl''
      change ψ g ∈ X
      exact (le_sup_right : SubgroupSections E.contracting (𝟙_ (SchemeOver F)) ≤ X)
        (section_in_contracting E hl'')
  let coordinateEquiv : (Fin n → B) ≃ₗ[Bᵐᵒᵖ] (Fin n → Bᵐᵒᵖ) :=
    LinearEquiv.piCongrRight fun _ => oppositeCoordinates
  let : Module.Finite Bᵐᵒᵖ (Fin n → B) :=
    Module.Finite.of_surjective coordinateEquiv.symm.toLinearMap coordinateEquiv.symm.surjective
  have hC : SubgroupSections D.centralizer (𝟙_ (SchemeOver F)) ≤ X := by
    intro g hg
    obtain ⟨z, rfl⟩ := ψ.surjective g
    obtain ⟨q, hqSec⟩ := hg
    have hz : Centralizes c (intoScheme i' (χ.symm z)) := by
      apply (D.centralizer_points _ _).mpr
      refine ⟨(testPointSections D.centralizer.group).symm q, ?_⟩
      apply (testPointSections G.val).injective
      change (rationalSourceIso F).hom ≫
        ((testPointSections D.centralizer.group).symm q) ≫ D.centralizer.inclusion.hom.hom = ψ z
      rw [← Category.assoc]
      have hq' := (testPointSections D.centralizer.group).apply_symm_apply q
      exact (congrArg (· ≫ D.centralizer.inclusion.hom.hom) hq').trans hqSec
    have hCom := centralizer_commutes_projectors P i' (χ.symm z) hz
    have he := hCom.1.map a.toMonoidHom
    have hf := hCom.2.map a.toMonoidHom
    change Commute (a ((χ.symm z).val : Matrix (Fin n) (Fin n) B)) (a P.first) at he
    change Commute (a ((χ.symm z).val : Matrix (Fin n) (Fin n) B)) (a P.last) at hf
    rw [hpoint, hp] at he
    rw [hpoint, hq] at hf
    exact hyperbolicLevi_mem p J hshear hB hd hs z he hf
  have hX := Arithmetic.RelativeRayGeneration.twoRadicals_sup_centralizer hR D E
  change X ⊔ SubgroupSections D.centralizer (𝟙_ (SchemeOver F)) = ⊤ at hX
  rw [sup_eq_left.mpr hC] at hX
  apply top_unique
  rw [← hX]
  exact Arithmetic.RelativeRayGeneration.twoRadicals_le_unipotentGenerated hR D E

end QuaternionGeneration

section GlobalApproximation

open LinearAlgebraicGroups.Specs
open Specs.IsotropicTypeC
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral MultiplicativeGroup)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.SymplecticInvolutionModels
open Specs.SymplecticInvolutionModels.DivisionForms
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open LinearAlgebraicGroups.CocharacterDynamics
open AdelicGroups

open SymplecticIsometryDescent (Involution)
open LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
  (degreeOneDivision nonarchimedeanTypeC realDivision algebraicallyClosedDivision)
open private splitLocalModel_of_field quaternionLocalModel_of_degree_two from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

private theorem real_degree_alternative {k D : Type u} [Field k] [DivisionRing D] [Algebra k D]
    (e : k ≃+* ℝ) (hD : isCentralSimple k D) :
    Nonempty (D ≃ₐ[k] k) ∨ degree k D = 2 := by
  let ρ := (algebraMap k D).comp e.symm.toRingHom
  letI : Algebra ℝ D :=
    { smul := fun a b => ρ a * b
      algebraMap := ρ
      commutes' := fun a b => Algebra.commutes (R := k) (e.symm a) b
      smul_def' := fun _ _ => rfl }
  have he : (algebraMap ℝ D).comp e.toRingHom = (RingEquiv.refl D).toRingHom.comp (algebraMap k D) := by
    ext x
    change algebraMap k D (e.symm (e x)) = algebraMap k D x
    rw [e.symm_apply_apply]
  letI : Module.Finite k D := hD.2.2
  let j : D →ₛₗ[e.toRingHom] D :=
    { AddMonoidHom.id D with
      map_smul' := fun a b => by
        change a • b = ρ (e a) * b
        simpa [ρ, Algebra.smul_def] }
  have hF : Module.Finite ℝ D := Module.Finite.of_surjective j Function.surjective_id
  have hh : Algebra.IsCentral ℝ D := by
    letI := hD.2.1
    constructor
    intro x hx
    have hx' : x ∈ Subalgebra.center k D :=
      Subalgebra.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp hx)
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).mp hx'
    exact ⟨e a, Eq.trans (by
      change algebraMap k D (e.symm (e a)) = algebraMap k D a
      rw [e.symm_apply_apply]) ha.symm⟩
  have hdim := Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl D) he
  rcases realDivision (show isCentralSimple ℝ D from ⟨hD.1, hh, hF⟩) with ⟨d⟩ | ⟨d⟩
  · apply Or.inl (degreeOneDivision hD _)
    apply (RM03.CSA.degree_eq_iff hD).mpr
    exact ⟨by decide, by simpa using hdim.trans d.some.toLinearEquiv.finrank_eq⟩
  · apply Or.inr
    apply (RM03.CSA.degree_eq_iff hD).mpr
    exact ⟨by decide, hdim.trans (d.some.toLinearEquiv.finrank_eq.trans Quaternion.finrank_eq_four)⟩

private theorem complex_isAlgClosed {k : Type u} [Field k] (e : k ≃+* ℂ) : IsAlgClosed k := by
  apply IsAlgClosed.of_exists_root
  intro p hm hi
  have hp : p.degree ≠ 0 := fun h => hi.natDegree_pos.ne' (by simp [Polynomial.natDegree, h])
  have hc : (p.map e.toRingHom).degree ≠ 0 := by
    rwa [Polynomial.degree_map_eq_of_injective e.injective]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map e.toRingHom) hc
  refine ⟨e.symm z, e.injective ?_⟩
  change e.toRingHom (p.eval (e.symm z)) = e.toRingHom 0
  rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
  simpa [Polynomial.IsRoot] using hz

private theorem archimedeanTypeCOfRingEquiv {F A L : Type u} [Field F] [Ring A] [Algebra F A]
    [Field L] [Algebra F L] (hA : isCentralSimple F A) (s : Involution F A) {n : ℕ}
    (c : Specs.SymplecticDivisionForms.SplitComparison (toDivisionInvolution s) L n)
    (harch : Nonempty (F ≃+* ℝ) ∨ Nonempty (F ≃+* ℂ)) :
    NonarchimedeanLocalAlternatives s n := by
  obtain ⟨r, D, hDiv, hAlg, hc, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation F A hA
  letI := hDiv
  letI := hAlg
  have hD := RM03.CSA.isCentralSimple_of_isCentralDivision F D hc
  have hD' : Nonempty (D ≃ₐ[F] F) ∨ degree F D = 2 := by
    rcases harch with h | h
    · obtain ⟨e⟩ := h
      exact real_degree_alternative e hD
    · obtain ⟨e⟩ := h
      let := complex_isAlgClosed e
      exact Or.inl (algebraicallyClosedDivision hD)
  rcases hD' with h | hd
  · obtain ⟨d⟩ := h
    exact Or.inl (splitLocalModel_of_field hA s c hr (e.trans d.mapMatrix))
  · exact Or.inr ⟨D, hDiv, hAlg, hD, hd, quaternionLocalModel_of_degree_two hA s c hD hd hr e⟩

set_option backward.isDefEq.respectTransparency false in
private theorem typeCAtPlace {K A : Type u} [Field K] [Ring A]
    (D : GlobalFieldData.{u,v} K) (w : D.Place) [alg : Algebra (D.Completion w) A] {n : ℕ}
    (s : Involution (D.Completion w) A) (hA : isCentralSimple (D.Completion w) A)
    (c : Specs.SymplecticDivisionForms.SplitComparison (toDivisionInvolution s)
      (AlgebraicClosure (D.Completion w)) n) :
    NonarchimedeanLocalAlternatives s n := by
  cases w with
  | inl w =>
    letI : ValuativeRel (D.Completion (.inl w)) :=
      inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
    letI : IsNonarchimedeanLocalField (D.Completion (.inl w)) :=
      D.finiteCompletion_isLocalField w
    exact nonarchimedeanTypeC hA s n c
  | inr w =>
    cases D with
    | number hk =>
      letI := hk
      let F : Type u := w.Completion
      let fF : Field F := (NumberField.InfinitePlace.Completion.instNormedField w).toField
      letI := fF
      let algF : Algebra F A := alg
      letI := algF
      let s' : Involution F A := s
      have hA' : isCentralSimple F A := hA
      have c' : Specs.SymplecticDivisionForms.SplitComparison (toDivisionInvolution s')
          (AlgebraicClosure F) n := c
      refine @archimedeanTypeCOfRingEquiv F A (AlgebraicClosure F) fF ‹Ring A› algF
        (AlgebraicClosure.instField F) (AlgebraicClosure.instAlgebra F) hA' s' n c' ?_
      rcases w.isReal_or_isComplex with hr | hc
      · obtain ⟨e, _⟩ := numberRealCompletion w hr
        exact Or.inl ⟨e⟩
      · obtain ⟨e, _⟩ := numberComplexCompletion w hc
        exact Or.inr ⟨e⟩
    | function F t => exact w.elim

open private unitEquiv unitEquiv_unitPoint gm_baseChange from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private noncentral_extend globalField_infinite from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

set_option backward.isDefEq.respectTransparency false in
private noncomputable def quaternionCocharacter {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {G : GroupScheme F} (c : Cocharacter G) {r : ℕ}
    {s : AntiAutomorphism F B} {H : Matrix (Fin r) (Fin r) B}
    (i : (groupPointsFunctor F).obj G ≅
      QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H) :
    QuaternionHermitianCocharacters.multiplicativePoints.{u,u} F ⟶
      QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H where
  app R := GrpCat.ofHom
    ((i.hom.app R).hom.comp ((((groupPointsFunctor F).map c).app R).hom.comp
      ((unitEquiv R).symm.toMonoidHom.comp (MulEquiv.ulift.toMonoidHom))))
  naturality R S f := by
    apply GrpCat.ext
    rintro ⟨t⟩
    let a : Rˣ := t
    have hi := DFunLike.congr_fun
      (congrArg GrpCat.Hom.hom (i.hom.naturality f)) (cocharacterPoint c R a)
    change i.hom.app S (cocharacterPoint c S (Units.map f.hom.toMonoidHom a)) =
      (QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H).map f
        (i.hom.app R (cocharacterPoint c R a))
    rw [← mapPoints_cocharacterPoint f]
    exact hi

private theorem quaternionCocharacter_ne_one {F B : Type u} [Field F] [DivisionRing B]
    [Algebra F B] {G : GroupScheme F} (c : Cocharacter G) (hc : IsNoncentral c) {r : ℕ}
    {s : AntiAutomorphism F B} {H : Matrix (Fin r) (Fin r) B}
    (i : (groupPointsFunctor F).obj G ≅
      QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H) :
    ¬ ∀ (R : TestAlgebra F) (t : (QuaternionHermitianCocharacters.multiplicativePoints.{u,u} F).obj R),
        (quaternionCocharacter c i).app R t = 1 := by
  intro h
  have hpt (R : TestAlgebra F) (t : Rˣ) : cocharacterPoint c R t = 1 := by
    apply ((i.app R).groupIsoToMulEquiv).injective
    have he := h R ⟨t⟩
    change i.hom.app R (cocharacterPoint c R t) = 1 at he
    change i.hom.app R (cocharacterPoint c R t) = i.hom.app R (1 : GroupPoints G R)
    rw [show i.hom.app R (1 : GroupPoints G R) = 1 from (i.hom.app R).hom.map_one]
    exact he
  have hc1 : c.hom.hom = 1 := by
    apply hom_ext_of_points (X := (MultiplicativeGroup F).X) (by
      change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
      infer_instance)
    intro R p
    have hp : unitPoint R (unitEquiv R p) = p :=
      (unitEquiv R).injective (unitEquiv_unitPoint R (unitEquiv R p))
    calc
      p ≫ c.hom.hom = unitPoint R (unitEquiv R p) ≫ c.hom.hom :=
        congrArg (· ≫ c.hom.hom) hp.symm
      _ = 1 := hpt R _
      _ = p ≫ 1 := (MonObj.comp_one p).symm
  obtain ⟨X, g, hg⟩ := hc
  apply hg
  apply (centralizes_iff c g).mpr
  intro Y y t
  have ht : t ≫ c.hom.hom = 1 := by
    rw [hc1]
    exact MonObj.comp_one t
  rw [ht]
  exact Commute.one_right _

theorem typeCStrongApproximation : TypeCStrongApproximation.{u,v} := by
  intro K E _ _ _ _ D n G i hG hSC hC c hc S hS
  apply approximationFromLocalGeneration D G i hG c hc S hS
  obtain ⟨_, _, L, _, _, d, _⟩ :=
    LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels.globalTypeCModel
      (S := E) n G hG.1 hSC hC
  obtain ⟨P⟩ := existsLimitDecomposition G c
  let := globalField_infinite D
  intro w
  let F := D.Completion w.1
  let G' := baseChangedAlgebraicGroup F G
  letI : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  have hR := reductive_of_semisimple G'
    (Arithmetic.OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG).1
  obtain ⟨ee, _⟩ := gm_baseChange K F
  let c' : Cocharacter G'.val := ee.hom ≫ (groupBaseChange K F).map c
  have hc' : IsNoncentral c' := noncentral_extend hc P.centralizer_points ee
  obtain ⟨hA, ⟨spl⟩, ⟨iso⟩⟩ :=
    LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels.descendedTypeCBaseChange d F
  rcases typeCAtPlace D w.1 (d.model.fixed.involution.baseChange F) hA spl with h | h
  · obtain ⟨_, _, _, _, _, _, e, _⟩ := h
    exact splitLocalGeneration F n G' (iso ≪≫ e)
  · obtain ⟨B, hDiv, hAlg, hB, hd, h⟩ := h
    letI := hDiv
    letI := hAlg
    obtain ⟨_, s, H, hs, hH, _, _, _, hn, hcH, ⟨_, e, _, _⟩, hpair⟩ := h
    let j : (groupPointsFunctor F).obj G'.val ≅
        QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H.val := iso ≪≫ e
    obtain ⟨e₀, f₀, _, h₁, h₂, h₃, h₄⟩ :=
      (hpair (quaternionCocharacter c' j)).2 (quaternionCocharacter_ne_one c' hc' j)
    exact quaternionLocalGeneration F G' hR hB hd s hs H hH j hn hcH e₀ f₀ h₁ h₄ h₂ h₃

end GlobalApproximation

end LinearAlgebraicGroups.Arithmetic.IsotropicTypeC
