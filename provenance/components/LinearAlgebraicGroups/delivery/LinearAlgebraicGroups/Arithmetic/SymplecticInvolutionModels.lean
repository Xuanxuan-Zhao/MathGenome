import Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
import LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
import LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
import LinearAlgebraicGroups.Arithmetic.QuaternionHermitianCocharacters
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases
import MathGenome.Internal.D07.Ch23.Frobenius
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision

open scoped WithZero TensorProduct
open ValuativeRel MulOpposite
open RM03.CSA (degree_pos)
open _root_.Specs.RM03.CSA (degree)

namespace LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

open LocalDivisionAlgebras
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels

universe u v w

variable {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]

private def antiApply (s : AntiAutomorphism F B) (x : B) : B := unop (s x)

private theorem anti_mul (s : AntiAutomorphism F B) (x y : B) :
    antiApply s (x * y) = antiApply s y * antiApply s x := by
  simp [antiApply, map_mul]

private def antiOnSubfield {L : Type v} [Field L] [Algebra F L]
    (s : AntiAutomorphism F B) (i : L →ₐ[F] B) : L →ₐ[F] B where
  toFun x := antiApply s (i x)
  map_one' := by simp [antiApply]
  map_zero' := by simp [antiApply]
  map_add' x y := by simp [antiApply]
  map_mul' x y := by rw [mul_comm x y, map_mul, anti_mul]
  commutes' x := by simp [antiApply, i.commutes, s.commutes]

open private exists_subfield from LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras

private theorem anti_one (s : AntiAutomorphism F B) : antiApply s 1 = 1 := by
  simp [antiApply]

private def antiUnit (s : AntiAutomorphism F B) (a : Bˣ) : Bˣ where
  val := antiApply s (a : B)
  inv := antiApply s (↑a⁻¹ : B)
  val_inv := by rw [← anti_mul, Units.inv_mul, anti_one]
  inv_val := by rw [← anti_mul, Units.mul_inv, anti_one]

private def unitConj (a : Bˣ) : B →+* B where
  toFun x := (a : B) * x * (↑a⁻¹ : B)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by rw [mul_add, add_mul]
  map_mul' x y := by simp [mul_assoc]

private theorem unitConj_mul (a b : Bˣ) (x : B) :
    unitConj (a * b) x = unitConj a (unitConj b x) := by
  change ((a : B) * (b : B)) * x * ((↑b⁻¹ : B) * (↑a⁻¹ : B)) = _
  simp only [unitConj, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc]

private theorem unitConj_value (w : Valuation B ℤᵐ⁰) (a : Bˣ) (x : B) :
    w (unitConj a x) = w x := by
  change w ((a : B) * x * (↑a⁻¹ : B)) = _
  rw [map_mul, map_mul, mul_comm (w (a : B)) (w x), mul_assoc, ← map_mul,
    Units.mul_inv, map_one, mul_one]

section Local

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Two restrictions to the same element subfield are equivalent valuations.
Taking a power and comparing with a central scalar fixes their normalization. -/
private theorem anti_preserves_value
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (w : Valuation B ℤᵐ⁰) (hw : IsDivisionValuation hB w)
    (s : AntiAutomorphism F B) (x : B) : w (antiApply s x) = w x := by
  by_cases hx : x = 0
  · simp [hx, antiApply]
  obtain ⟨L, hL, hAlg, hFin, i, y, rfl⟩ := exists_subfield hB x
  let := hL
  let := hAlg
  let := hFin
  obtain ⟨rel, top, hExt, _, _⟩ := finiteExtension_localField (K := F) (L := L)
  let := rel
  let := top
  let := hExt
  let j := antiOnSubfield s i
  have hbase : (valuation F).IsEquiv ((valuation L).comap (algebraMap F L)) := by
    intro a b
    change valuation F a ≤ valuation F b ↔ valuation L (algebraMap F L a) ≤ valuation L (algebraMap F L b)
    rw [← (valuation F).vle_iff_le, ← (valuation L).vle_iff_le]
    exact (ValuativeExtension.vle_iff_vle (A := F) (B := L) a b).symm
  have heq := (restriction_to_subfields hB w hw j (valuation L) hbase).trans
    (restriction_to_subfields hB w hw i (valuation L) hbase).symm
  have hs : Function.Surjective (baseValue F) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
      (ValuativeRel.valuation_surjective (K := F))
  obtain ⟨a, ha⟩ := hs (w (i y))
  have hia : (w.comap i.toRingHom) (y ^ degree F B) =
      (w.comap i.toRingHom) (algebraMap F L a) := by
    change w (i (y ^ degree F B)) = w (i (algebraMap F L a))
    rw [map_pow, map_pow, i.commutes, hw.2, ha]
  have hja := heq.eq_iff.mpr hia
  change w (j (y ^ degree F B)) = w (j (algebraMap F L a)) at hja
  rw [map_pow, map_pow, j.commutes, hw.2, ha] at hja
  exact (pow_left_inj₀ zero_le zero_le (degree_pos hB).ne').mp hja

section Residue

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable (w : Valuation B ℤᵐ⁰)
variable (rF : IsField (ResidueRing w))

private def integerMap (f : B → B) (hf : ∀ x, w (f x) = w x) (x : w.integer) :
    w.integer :=
  ⟨f x, (hf x).trans_le x.property⟩

/-- An additive valuation-preserving map induces a ring map on the residue
field if it preserves the unit and residue products. This includes both
conjugation and anti-automorphisms. -/
private def reduceMap (f : B →+ B) (hf : ∀ x, w (f x) = w x) (h1 : f 1 = 1)
    (hm : ∀ x y, residue w (integerMap w f hf (x * y)) =
      residue w (integerMap w f hf x) * residue w (integerMap w f hf y)) :
    ResidueRing w →+* ResidueRing w := by
  let m : w.integer →+* ResidueRing w :=
    { toFun x := residue w (integerMap w f hf x)
      map_one' := by rw [show integerMap w f hf 1 = 1 from Subtype.ext h1, map_one]
      map_zero' := by rw [show integerMap w f hf 0 = 0 from Subtype.ext (map_zero f), map_zero]
      map_add' x y := by
        rw [← map_add]
        exact congrArg (residue w) (Subtype.ext (map_add f _ _))
      map_mul' := hm }
  refine RingCon.lift (maximalIdeal w).ringCon m ?_
  intro x y hxy
  apply (RingCon.ker_apply m).2
  change residue w (integerMap w f hf x) = residue w (integerMap w f hf y)
  have h := (maximalIdeal w).ringCon.eq.mpr hxy
  change residue w x = residue w y at h
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  change w (f (x : B) - f (y : B)) < 1
  rw [← map_sub, hf]
  exact h

private def residueConj (a : Bˣ) : ResidueRing w →+* ResidueRing w :=
  reduceMap w (unitConj a).toAddMonoidHom (unitConj_value w a) (map_one (unitConj a)) (by
    intro x y
    rw [← map_mul]
    exact congrArg (residue w) (Subtype.ext (map_mul (unitConj a) _ _)))

private theorem residueConj_apply (a : Bˣ) (x : w.integer) :
    residueConj w a (residue w x) = residue w (integerMap w (unitConj a) (unitConj_value w a) x) :=
  rfl

private theorem residueConj_mul (a b : Bˣ) (x : ResidueRing w) :
    residueConj w (a * b) x = residueConj w a (residueConj w b x) := by
  obtain ⟨y, rfl⟩ := residue_surjective w x
  rw [residueConj_apply, residueConj_apply, residueConj_apply]
  exact congrArg (residue w) (Subtype.ext (unitConj_mul a b (y : B)))

private theorem residueConj_of_value_one (rF : IsField (ResidueRing w)) (a : Bˣ) (ha : w (a : B) = 1)
    (x : ResidueRing w) : residueConj w a x = x := by
  obtain ⟨y, rfl⟩ := residue_surjective w x
  let A : w.integer := ⟨(a : B), ha.le⟩
  let Ai : w.integer := ⟨(↑a⁻¹ : B), by
    change w (↑a⁻¹ : B) ≤ 1
    rw [Units.val_inv_eq_inv_val, w.map_inv, ha, inv_one]⟩
  rw [residueConj_apply]
  change residue w (A * y * Ai) = residue w y
  have h : A * Ai = 1 := Subtype.ext (Units.mul_inv a)
  calc
    residue w (A * y * Ai) = residue w y * (residue w A * residue w Ai) := by
      rw [map_mul, map_mul, rF.mul_comm (residue w A) (residue w y), mul_assoc]
    _ = residue w y := by rw [← map_mul, h, map_one, mul_one]

private abbrev antiIntegerMap (s : AntiAutomorphism F B) :
    B →+ B where
  toFun := antiApply s
  map_zero' := by simp [antiApply]
  map_add' x y := by simp [antiApply]

private def antiResidue (s : AntiAutomorphism F B) (hs : ∀ x, w (antiApply s x) = w x) :
    ResidueRing w →+* ResidueRing w :=
  reduceMap w (antiIntegerMap s) hs (anti_one s) (by
    intro x y
    rw [rF.mul_comm, ← map_mul]
    exact congrArg (residue w) (Subtype.ext (anti_mul s _ _)))

private theorem antiResidue_apply (s : AntiAutomorphism F B)
    (hs : ∀ x, w (antiApply s x) = w x) (x : w.integer) :
    antiResidue w rF s hs (residue w x) = residue w (integerMap w (antiApply s) hs x) :=
  rfl

private theorem residue_conjugation_reversal (s : AntiAutomorphism F B)
    (hs : ∀ x, w (antiApply s x) = w x) (a : Bˣ) (x : ResidueRing w) :
    residueConj w (antiUnit s a) (antiResidue w rF s hs (residueConj w a x)) =
      antiResidue w rF s hs x := by
  obtain ⟨y, rfl⟩ := residue_surjective w x
  rw [residueConj_apply, antiResidue_apply, residueConj_apply, antiResidue_apply]
  apply congrArg (residue w)
  apply Subtype.ext
  change antiApply s (a : B) * antiApply s ((a : B) * (y : B) * (↑a⁻¹ : B)) *
    antiApply s (↑a⁻¹ : B) = antiApply s (y : B)
  rw [anti_mul, anti_mul, ← mul_assoc, ← anti_mul, Units.inv_mul, anti_one, one_mul,
    mul_assoc, ← anti_mul, Units.inv_mul, anti_one, mul_one]

end Residue

theorem localDivisionDegreeBound : LocalDivisionDegreeBound.{u,v} := by
  intro F _ _ _ _ B _ _ hB s
  obtain ⟨w, hw, _⟩ := valuation_exists hB
  obtain ⟨r⟩ := residue_field hB w hw
  obtain ⟨_, _, ⟨p⟩⟩ := cyclic_structure hB w hw r
  let := r.isField.toField
  let := r.algebra
  let := p.fieldL
  let := p.algebraL
  let := p.galois
  let : FiniteDimensional F B := hB.2.2
  let : FiniteDimensional F p.L := Module.Finite.of_injective p.embed.toLinearMap p.embed.injective
  let τ := p.residueAutEquiv p.τ
  let C := residueConj w p.uniformizer
  let st := antiResidue w r.isField s (anti_preserves_value hB w hw s)
  have hC : ∀ z : ResidueRing w, C z = τ z := by
    intro z
    obtain ⟨a, ha⟩ := (p.residueEquiv.surjective.comp
      (IsLocalRing.residue_surjective (R := p.vL.valuationSubring))) z
    change p.residueEquiv (IsLocalRing.residue _ a) = z at ha
    let b : p.vL.valuationSubring := ⟨p.τ (a : p.L), by
      change p.vL (p.τ (a : p.L)) ≤ 1
      rw [p.τ_preserves_value]
      exact a.property⟩
    let emb (x : p.vL.valuationSubring) : w.integer := ⟨p.embed (x : p.L), by
      change w (p.embed (x : p.L)) ≤ 1
      rw [p.restrict_val]
      exact pow_le_one₀ zero_le x.property⟩
    rw [← ha, p.residue_eq a (emb a) rfl, show C = residueConj w p.uniformizer from rfl,
      residueConj_apply]
    have hb : integerMap w (unitConj p.uniformizer) (unitConj_value w p.uniformizer) (emb a) =
        emb b := by
      apply Subtype.ext
      change (p.uniformizer : B) * p.embed (a : p.L) * (↑p.uniformizer⁻¹ : B) =
        p.embed (p.τ (a : p.L))
      rw [p.conjugation, mul_assoc, Units.mul_inv, mul_one]
    rw [hb, ← p.residue_eq b (emb b) rfl, p.residue_aut p.τ a b rfl,
      p.residue_eq a (emb a) rfl]
  obtain ⟨m, _, hm⟩ := p.frobenius
  have hFrob (z : ResidueRing w) : τ z = z ^ (Nat.card (BaseResidue F) ^ m) := by
    obtain ⟨a, rfl⟩ := (p.residueEquiv.surjective.comp
      (IsLocalRing.residue_surjective (R := p.vL.valuationSubring))) z
    let b : p.vL.valuationSubring := ⟨p.τ (a : p.L), by
      change p.vL (p.τ (a : p.L)) ≤ 1
      rw [p.τ_preserves_value]
      exact a.property⟩
    exact (p.residue_aut p.τ a b rfl).symm.trans (hm a b rfl)
  have hcomm (z : ResidueRing w) : st (C z) = C (st z) := by
    rw [hC, hC, hFrob, hFrob, map_pow]
  have heq (z : ResidueRing w) : residueConj w (antiUnit s p.uniformizer) z = C z := by
    let a := antiUnit s p.uniformizer * p.uniformizer⁻¹
    have ha : w (a : B) = 1 := by
      change w (antiApply s (p.uniformizer : B) * (↑p.uniformizer⁻¹ : B)) = 1
      rw [map_mul, anti_preserves_value hB w hw s, ← map_mul, Units.mul_inv, map_one]
    rw [show antiUnit s p.uniformizer = a * p.uniformizer by simp [a, mul_assoc],
      residueConj_mul, residueConj_of_value_one w r.isField a ha]
  have ht : τ ^ 2 = 1 := by
    ext z
    change τ (τ z) = z
    apply st.injective
    have h := residue_conjugation_reversal w r.isField s (anti_preserves_value hB w hw s) p.uniformizer z
    change residueConj w (antiUnit s p.uniformizer) (st (C z)) = st z at h
    rw [heq, ← hcomm] at h
    simpa only [hC] using h
  have hτ : p.τ ^ 2 = 1 := p.residueAutEquiv.injective (by simpa [τ, map_pow] using ht)
  have hd : orderOf p.τ = degree F B := by
    rw [orderOf_eq_card_of_zpowers_eq_top p.gen, IsGalois.card_aut_eq_finrank]
    exact p.degree
  apply Nat.le_of_dvd (by decide : 0 < 2)
  rw [← hd]
  exact orderOf_dvd_of_pow_eq_one hτ

end Local

theorem degreeOneDivision : DegreeOneDivision.{u,v} := by
  intro F _ B _ _ hB hd
  let : FiniteDimensional F B := hB.2.2
  have hr : Module.finrank F B = 1 := by
    rw [RM03.CSA.finrank_eq_degree_sq hB]
    change degree F B ^ 2 = 1
    simp [hd]
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId F B)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hr)).symm⟩

section MatrixOpposite

variable {F : Type u} [Field F] {D : Type*} [Ring D] [Algebra F D]

/-- Transposition with entrywise passage to the opposite is multiplicative
even over a noncommutative coefficient algebra. -/
private def matrixOpposite (r : ℕ) :
    (Matrix (Fin r) (Fin r) D)ᵐᵒᵖ ≃ₐ[F] Matrix (Fin r) (Fin r) Dᵐᵒᵖ where
  toFun x i j := op (unop x j i)
  invFun x := op (fun i j => unop (x j i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    ext i j
    change op ((unop y * unop x) j i) =
      ∑ k : Fin r, op (unop x k i) * op (unop y j k)
    rw [Matrix.mul_apply, Finset.op_sum]
    rfl
  commutes' a := by
    ext i j
    change op (algebraMap F (Matrix (Fin r) (Fin r) D) a j i) =
      algebraMap F (Matrix (Fin r) (Fin r) Dᵐᵒᵖ) a i j
    rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j <;> simp [h, eq_comm]

end MatrixOpposite

theorem divisionFactorAntiAutomorphism : DivisionFactorAntiAutomorphism.{u,v,w} := by
  intro F _ A _ _ B _ _ r hr hA e s
  let eop := s.trans ((AlgEquiv.op e).trans (matrixOpposite r))
  exact (RM03.CSA.MatrixDivision.presentation_unique F A hA B Bᵐᵒᵖ r r hr hr e eop).2

theorem nonarchimedeanDivisionFactor : NonarchimedeanDivisionFactor.{u,v,w} := by
  intro F _ _ _ _ A _ _ B _ _ r hr hA hB e s
  obtain ⟨t⟩ := divisionFactorAntiAutomorphism hr hA e s
  have h := localDivisionDegreeBound hB t
  have hpos : 0 < degree F B := degree_pos hB
  by_cases h₂ : degree F B = 2
  · exact Or.inr h₂
  · exact Or.inl (degreeOneDivision hB (by omega))

theorem algebraicallyClosedDivision : AlgebraicallyClosedDivision.{u,v} := by
  intro F _ _ B _ _ hB
  let : FiniteDimensional F B := hB.2.2
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId F B)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩


theorem realDivision : RealDivision.{v} := by
  intro B _ _ hB
  let : FiniteDimensional ℝ B := hB.2.2
  let : Algebra.IsCentral ℝ B := hB.2.1
  obtain ⟨_, hm, _⟩ := D07.Ch23.Frobenius.finiteDimensionalClassification B
  rcases hm with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · exact Or.inl ⟨e.symm⟩
  · have hc : e Complex.I ∈ Subalgebra.center ℝ B := by
      apply Subalgebra.mem_center_iff.mpr
      intro b
      obtain ⟨z, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, mul_comm]
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hc
    have he : Complex.I = algebraMap ℝ ℂ a := e.injective (ha.trans (e.commutes a).symm)
    have hi := congrArg Complex.im he
    simp at hi
  · exact Or.inr ⟨e.symm⟩

theorem nonarchimedeanPresentations : NonarchimedeanPresentations.{u,v} := by
  intro F _ _ _ _ A _ _ hA s
  obtain ⟨r, B, hDiv, hAlg, hB, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation F A hA
  let := hDiv
  let := hAlg
  have hB' := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  exact ⟨B, hDiv, hAlg, r, hB', hr, ⟨e⟩, nonarchimedeanDivisionFactor hr hA hB' e s⟩

theorem archimedeanPresentations : ArchimedeanPresentations.{v} := by
  constructor
  · intro A _ _ hA
    obtain ⟨r, B, hDiv, hAlg, hB, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation ℝ A hA
    let := hDiv
    let := hAlg
    have hB' := RM03.CSA.isCentralSimple_of_isCentralDivision ℝ B hB
    refine ⟨r, hr, ?_⟩
    rcases realDivision hB' with hreal | hquat
    · obtain ⟨eB⟩ := hreal
      exact Or.inl ⟨e.trans eB.mapMatrix⟩
    · obtain ⟨eB⟩ := hquat
      exact Or.inr ⟨e.trans eB.mapMatrix⟩
  · intro A _ _ hA
    obtain ⟨r, B, hDiv, hAlg, hB, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation ℂ A hA
    let := hDiv
    let := hAlg
    obtain ⟨eB⟩ := algebraicallyClosedDivision (RM03.CSA.isCentralSimple_of_isCentralDivision ℂ B hB)
    exact ⟨r, hr, ⟨e.trans (eB.mapMatrix)⟩⟩

universe z

theorem hyperbolicPartner : HyperbolicPartner.{u,v,z} := by
  intro F _ B _ _ s hs V _ _ h e he hee
  obtain ⟨y, hy⟩ := h.nondegenerate e he
  let v₀ := op (h.value e y)⁻¹ • y
  have hev : h.value e v₀ = 1 := by
    rw [h.smul_right, mul_inv_cancel₀ hy]
  have hve : h.value v₀ e = 1 := by
    rw [h.hermitian e v₀, hev, map_one, unop_one]
  obtain ⟨q, hq⟩ := h.central_norm v₀
  obtain ⟨a, ha⟩ := hs (-q)
  let f := v₀ + op a • e
  have hef : h.value e f = 1 := by
    change h.value e (v₀ + op a • e) = 1
    rw [h.add_right, h.smul_right _ e a, hev, hee, zero_mul, add_zero]
  have hfe : h.value f e = 1 := by
    rw [h.hermitian e f, hef, map_one, unop_one]
  have hvf : h.value v₀ f = algebraMap F B q + a := by
    change h.value v₀ (v₀ + op a • e) = _
    rw [h.add_right, h.smul_right _ e a, hve, hq, one_mul]
  refine ⟨f, hef, hfe, ?_⟩
  have hfv : h.value f v₀ = algebraMap F B q + antiApply s a := by
    rw [h.hermitian v₀ f, hvf, map_add, unop_add, s.commutes]
    rfl
  change h.value f (v₀ + op a • e) = 0
  rw [h.add_right, h.smul_right _ e a, hfv, hfe, one_mul,
    add_assoc, add_comm (antiApply s a) a]
  change algebraMap F B q + (a + unop (s a)) = 0
  rw [ha, map_neg, add_neg_cancel]

section Quaternion

local notation "qTrace" => LocalDivisionNormTraceReduction.reducedTrace

private theorem adjugate_eq_trace_sub {L : Type*} [Field L]
    (M : Matrix (Fin 2) (Fin 2) L) :
    M.adjugate = Matrix.scalar (Fin 2) M.trace - M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.scalar_apply, add_sub_cancel_left]

private theorem adjugate_add_quaternion {L : Type*} [Field L]
    (M N : Matrix (Fin 2) (Fin 2) L) :
    (M + N).adjugate = M.adjugate + N.adjugate := by
  simp only [adjugate_eq_trace_sub, Matrix.trace_add, map_add, add_sub_add_comm]

private theorem adjugate_scalar_quaternion {L : Type*} [Field L] (a : L) :
    (algebraMap L (Matrix (Fin 2) (Fin 2) L) a).adjugate = algebraMap L _ a := by
  rw [adjugate_eq_trace_sub, Matrix.algebraMap_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, two_mul]

private theorem split_reducedTrace
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (hd : degree F B = 2)
    {L : Type*} [Field L] [Algebra F L] (e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
    (x : B) : algebraMap F L (qTrace hB x) = (e (1 ⊗ₜ[F] x)).trace := by
  have hd' : RM03.CSA.degree F B = 2 := hd
  revert e
  rw [← hd']
  exact fun e => LocalDivisionAlgebras.reducedTrace_map hB e x

private theorem split_quaternion_conjugate
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (hd : degree F B = 2)
    {L : Type*} [Field L] [Algebra F L] (e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
    (x : B) : e (1 ⊗ₜ[F] quaternionConjugate hB x) = (e (1 ⊗ₜ[F] x)).adjugate := by
  have ht := split_reducedTrace hB hd e x
  let T : B →ₐ[F] Matrix (Fin 2) (Fin 2) L :=
    (e.restrictScalars F).toAlgHom.comp Algebra.TensorProduct.includeRight
  change T (algebraMap F B (qTrace hB x) - x) = (T x).adjugate
  rw [map_sub, T.commutes, IsScalarTower.algebraMap_apply F L (Matrix (Fin 2) (Fin 2) L),
    adjugate_eq_trace_sub]
  exact congrArg (fun z : L => Matrix.scalar (Fin 2) z - T x) ht


theorem quaternionConjugation : QuaternionConjugation.{u,v,w} := by
  intro F _ B _ _ hB hd
  have hd' : RM03.CSA.degree F B = 2 := hd
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hB
  let L := AlgebraicClosure F
  let e₂ : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L := hd' ▸ e
  let T : B →ₐ[F] Matrix (Fin 2) (Fin 2) L :=
    (e₂.restrictScalars F).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hT : Function.Injective T :=
    e₂.injective.comp (Algebra.TensorProduct.includeRight_injective
      (B := B) (algebraMap F L).injective)
  let bar := quaternionConjugate hB
  have hb (x : B) : T (bar x) = (T x).adjugate := split_quaternion_conjugate hB hd e₂ x
  have hb2 (x : B) : bar (bar x) = x := hT (by
    rw [hb, hb, Matrix.adjugate_adjugate']
    simp)
  let s : AntiAutomorphism F B :=
    { toFun x := op (bar x)
      invFun x := bar (unop x)
      left_inv := hb2
      right_inv x := congrArg op (hb2 (unop x))
      map_mul' x y := by
        change op (bar (x * y)) = op (bar y * bar x)
        apply congrArg op
        apply hT
        rw [hb, map_mul, Matrix.adjugate_mul_distrib, map_mul, hb, hb]
      map_add' x y := by
        change op (bar (x + y)) = op (bar x + bar y)
        apply congrArg op
        apply hT
        rw [hb, map_add, map_add, hb, hb]
        exact adjugate_add_quaternion (T x) (T y)
      commutes' a := by
        apply congrArg op
        apply hT
        rw [hb, T.commutes, IsScalarTower.algebraMap_apply F L (Matrix (Fin 2) (Fin 2) L)]
        exact adjugate_scalar_quaternion (algebraMap F L a) }
  refine ⟨s, fun _ => rfl, hb2, fun _ _ _ es x => split_quaternion_conjugate hB hd es x, ?_⟩
  have ht (x : B) : algebraMap F L (qTrace hB x) = (T x).trace :=
    split_reducedTrace hB hd e₂ x
  obtain ⟨y, hy⟩ : ∃ y, qTrace hB y ≠ 0 := by
    by_contra! h
    have hz (t : L ⊗[F] B) : (e₂ t).trace = 0 := by
      induction t using TensorProduct.inductionOn with
      | tmul a x =>
        rw [show a ⊗ₜ[F] x = a • ((1 : L) ⊗ₜ[F] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          map_smul, Matrix.trace_smul]
        change a • (T x).trace = 0
        rw [← ht, h, map_zero, smul_zero]
      | add a b ha hb => simp [map_add, Matrix.trace_add, ha, hb]
    obtain ⟨M, hM⟩ := Matrix.trace_surjective (n := Fin 2) (R := L) 1
    obtain ⟨z, rfl⟩ := e₂.surjective M
    exact one_ne_zero (hM.symm.trans (hz z))
  intro a
  refine ⟨(a / qTrace hB y) • y, ?_⟩
  apply (algebraMap F L).injective
  rw [ht, map_smul, Matrix.trace_smul, ← ht, Algebra.smul_def, ← map_mul,
    div_mul_cancel₀ _ hy]

theorem quaternionAlternatingPlane : QuaternionAlternatingPlane.{u} := by
  intro F _
  dsimp only
  constructor
  · intro X
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alternatingPlane, Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · intro X ht hdiag
    have h₀ : X 1 0 = 0 := by
      simpa [alternatingPlane, Matrix.mul_apply, Fin.sum_univ_two] using hdiag 0
    have h₁ : X 0 1 = 0 := by
      simpa [alternatingPlane, Matrix.mul_apply, Fin.sum_univ_two] using hdiag 1
    have hd : X 0 0 = X 1 1 := by
      have hh := congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => Y 0 1) ht
      simpa [alternatingPlane, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hh
    refine ⟨X 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h₀, h₁, hd]

theorem quaternionHyperbolicPartner : QuaternionHyperbolicPartner.{u,v,z} := by
  intro F _ B _ _ hB hd s hbar V _ _ h e he hee
  have htrace := (quaternionConjugation.{u,v,u} hB hd).elim (fun _ hs => hs.2.2.2)
  apply hyperbolicPartner s _ h e he hee
  intro a
  obtain ⟨b, hb⟩ := htrace a
  refine ⟨b, ?_⟩
  rw [hbar, quaternionConjugate, hb, add_comm, sub_add_cancel]

end Quaternion

section TypeC

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open Specs.TypeCSplitRecognition (MatrixTwisting sliceTest)
open Specs.SymplecticMatrixStructure (PointGroup symplecticPoints)
open Specs.SymplecticDatumAdjointDescent (adjoint)
open Specs.SymplecticDatumTorusAndBorel (HyperbolicIndex)
open Specs.RelativeFormComparison (fieldMap fieldTest transportedAut)
open Specs.AutomorphismSequence (relativePoints)
open SymplecticIsometryDescent (PointsOf overBase coefficientHom SplitComparison)
open private liftOverTestAlgebra restrictIsometry
  from LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {n : ℕ} {G H : AffineAlgebraicGroup k}
variable {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
variable {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}

private def twistingActions (t : MatrixTwisting n G H c f) : TwistingActions t where
  lifts := by
    obtain ⟨_, hflat, hsurj, hfp, _⟩ :=
      Classification.CentralIsogenies.representsQuotient_isFppfGroupQuotient t.represents
    let := hflat
    let := hsurj
    let := hfp
    let : IsAffine H.val.X.left := H.property.1
    let : IsAffine t.quotient.val.X.left := t.quotient.property.1
    let : IsAffineHom t.projection.hom.hom.left := isAffineHom_of_isAffine _
    exact liftOverTestAlgebra t.projection
  groupAction R :=
    { toFun := fun a => restrictIsometry (t.action R a) (t.preservesAdjoint R a)
      map_one' := by
        ext g : 1
        apply Subtype.ext
        change t.action R 1 g.val = g.val
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        ext g : 1
        apply Subtype.ext
        change t.action R (a * b) g.val = t.action R a (t.action R b g.val)
        rw [map_mul]
        rfl }
  onMatrix _ _ _ := rfl

private theorem coefficient_comp {S T : TestAlgebra K}
    (d : overBase k K S ⟶ overBase k K T) (σ : Gal(K/k))
    (h : ∀ b : K, d.hom (algebraMap K S b) = algebraMap K T (σ b)) :
    coefficientHom (k := k) S ≫ d =
      CommAlgCat.ofHom σ.toAlgHom ≫ coefficientHom (k := k) T := by
  ext b
  exact h b

private def toAffineSlice : TestAlgebra K ⥤ (Over (fieldTest k K))ᵒᵖ where
  obj R := op (sliceTest (k := k) R)
  map {S T} d := (Over.homMk ((testSpec k).map ((restrictTestAlgebra k K).map d).op) (by
    change _ ≫ (testSpec k).map (coefficientHom (k := k) S).op =
      (testSpec k).map (coefficientHom (k := k) T).op
    rw [← Functor.map_comp, ← op_comp]
    congr 2
    ext b
    exact d.hom.commutes b)).op
  map_id R := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change (testSpec k).map ((restrictTestAlgebra k K).map (𝟙 R)).op = 𝟙 _
    rw [(restrictTestAlgebra k K).map_id, op_id, (testSpec k).map_id]
  map_comp a b := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change (testSpec k).map ((restrictTestAlgebra k K).map (a ≫ b)).op =
      (testSpec k).map ((restrictTestAlgebra k K).map b).op ≫
        (testSpec k).map ((restrictTestAlgebra k K).map a).op
    rw [Functor.map_comp, op_comp, Functor.map_comp]

private def relativeComparison (t : MatrixTwisting n G H c f) :
    restrictTestAlgebra k K ⋙ PointsOf G.val ≅
      restrictTestAlgebra k K ⋙ symplecticPoints k (HyperbolicIndex.{u} (n + 1)) :=
  (show restrictTestAlgebra k K ⋙ PointsOf G.val ≅
      restrictTestAlgebra k K ⋙ PointsOf H.val from
    Functor.isoWhiskerLeft (toAffineSlice (k := k) (K := K)) t.comparison.symm) ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra k K) c

private theorem relativeComparison_inner (t : MatrixTwisting n G H c f)
    (σ : Gal(K/k)) (S T : TestAlgebra K) (d : overBase k K S ⟶ overBase k K T)
    (hd : ∀ b : K, d.hom (algebraMap K S b) = algebraMap K T (σ b))
    (x : (PointsOf G.val).obj (overBase k K S)) :
    (relativeComparison t).hom.app T ((PointsOf G.val).map d x) =
      (twistingActions t).groupAction (overBase k K T)
        ((PointsOf t.quotient.val).map (coefficientHom T) (t.cocycle σ))
        (Specs.SymplecticMatrixStructure.mapSymplecticPoint d.hom.toRingHom
          ((relativeComparison t).hom.app S x)) := by
  let U := sliceTest (k := k) S
  let V := sliceTest (k := k) T
  let V' := (Over.map (fieldMap k K σ)).obj V
  let β : V' ⟶ U := Over.homMk ((testSpec k).map d.op) (by
    change (testSpec k).map d.op ≫ (testSpec k).map (coefficientHom S).op =
      (testSpec k).map (coefficientHom T).op ≫ (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      coefficient_comp d σ hd])
  let y : (PointsOf H.val).obj (overBase k K S) := t.comparison.inv.app (op U) x
  let z := (PointsOf H.val).map d y
  have hy : t.comparison.hom.app (op U) y = x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app t.comparison.inv_hom_id (op U)) x
  have he : t.comparison.hom.app (op V') z = (PointsOf G.val).map d x := by
    have h := ConcreteCategory.congr_hom (t.comparison.hom.naturality β.op) y
    change t.comparison.hom.app (op V') z =
      (PointsOf G.val).map d (t.comparison.hom.app (op U) y) at h
    exact h.trans (congrArg ((PointsOf G.val).map d) hy)
  have hz := t.onTestAlgebra σ T z
  change (show PointGroup _ _ from
      c.hom.app _ (t.comparison.inv.app (op V) (t.comparison.hom.app (op V') z))).val =
    t.action (overBase k K T) ((coefficientHom (k := k) T |> fun b =>
      (testSpec k).map b.op) ≫ t.cocycle σ)
      (show PointGroup _ _ from c.hom.app _ z).val at hz
  have hn := ConcreteCategory.congr_hom (c.hom.naturality d) y
  change c.hom.app (overBase k K T) z =
    Specs.SymplecticMatrixStructure.mapSymplecticPoint d.hom.toRingHom
      (c.hom.app (overBase k K S) y) at hn
  apply Subtype.ext
  change (show PointGroup _ _ from
      c.hom.app _ (t.comparison.inv.app (op V) ((PointsOf G.val).map d x))).val =
    t.action (overBase k K T) ((PointsOf t.quotient.val).map (coefficientHom T) (t.cocycle σ))
      (Specs.SymplecticMatrixStructure.mapSymplecticPoint d.hom.toRingHom (c.hom.app _ y)).val
  rw [← hn, ← he]
  exact hz

private theorem descendTwisting [FiniteDimensional k K] [IsGalois k K]
    (t : MatrixTwisting n G H c f) : Nonempty (DescendedTypeC t) := by
  let a := twistingActions t
  let i : SplitComparison a.presentation G t.cocycle :=
    ⟨relativeComparison t, relativeComparison_inner t⟩
  obtain ⟨m⟩ := SymplecticIsometryDescent.descent k K (HyperbolicIndex.{u} (n + 1))
    a.presentation G t.cocycle i
  exact ⟨⟨a, i, fun _ _ => rfl, m⟩⟩

theorem globalTypeCModel : GlobalTypeCModel.{u} := by
  intro k S _ _ _ _ n G hss hsc htype
  obtain ⟨H, c, L, f, ⟨t⟩⟩ :=
    LinearAlgebraicGroups.TypeCSplitRecognition.typeCSplitRecognitionFromCartan
      (S := S) n G hss hsc htype
  obtain ⟨d⟩ := descendTwisting t
  refine ⟨H, c, L, f, t, d, ?_⟩
  exact d.model.fixed.degree.trans (by simp [HyperbolicIndex])

end

end TypeC

section LocalModels

open CategoryTheory
open scoped Matrix
open LinearAlgebraicGroups.Specs
open Specs.SymplecticInvolutionModels.DivisionForms
open Specs.SymplecticDivisionForms (AntiEquiv SplitComparison antiValue dagger extendAnti
  hermitianValue intoTensor tensorMap)
open SymplecticIsometryDescent (Involution isometryPoints)
open private extendAnti_tmul from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {F A B L : Type u} [Field F] [Ring A] [Algebra F A]
  [DivisionRing B] [Algebra F B] [Field L] [Algebra F L]

private theorem extendAnti_involution (s : Involution F A) (R : Type u)
    [CommRing R] [Algebra F R] (x : R ⊗[F] A) :
    antiValue (extendAnti (toDivisionInvolution s).anti R) x =
      (s.baseChange R).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rw [extendAnti_tmul, Involution.baseChange_tmul]; rfl
  | add a b ha hb =>
    simp only [antiValue, map_add]
    exact congrArg₂ (· + ·) ha hb

private theorem extendAnti_conjugation {D R : Type u} [Ring D] [Algebra F D]
    [CommRing R] [Algebra F R] (b : AntiEquiv F D) (x : R ⊗[F] D) :
    antiValue (extendAnti b R) x = unop (QuaternionHermitianCocharacters.extendConjugation b.toAlgHom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rw [extendAnti_tmul, QuaternionHermitianCocharacters.extendConjugation_tmul]; rfl
  | add a b ha hb =>
    simp only [antiValue, map_add]
    exact congrArg₂ (· + ·) ha hb

private theorem hermitianValue_pairing {D : Type u} {I : Type*} [Ring D] [Algebra F D] [Fintype I]
    (b : AntiEquiv F D) (H : Matrix I I D) :
    hermitianValue b H = QuaternionHermitianCocharacters.pairing b.toAlgHom H := by
  funext x y
  change (∑ i, unop (b (x i)) * ∑ j, H i j * y j) =
    ∑ j, (∑ i, unop (b (x i)) * H i j) * y j
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

private theorem extendedPairing_eq {I : Type*} {R : Type u} [Fintype I] [CommRing R] [Algebra F R]
    (b : AntiEquiv F B) (H : Matrix I I (R ⊗[F] B)) :
    hermitianValue (extendAnti b R) H = QuaternionHermitianCocharacters.pairing (QuaternionHermitianCocharacters.extendConjugation b.toAlgHom) H := by
  funext x y
  change (∑ i, antiValue (extendAnti b R) (x i) * ∑ j, H i j * y j) =
    ∑ j, (∑ i, unop (QuaternionHermitianCocharacters.extendConjugation b.toAlgHom (x i)) * H i j) * y j
  simp only [extendAnti_conjugation, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

private def quaternionIsometryComparison {n : ℕ} (s : Involution F A)
    (b : AntiEquiv F B) (H : Matrix (Fin n) (Fin n) B)
    (E : ∀ (R : Type u) [CommRing R] [Algebra F R],
      (R ⊗[F] A) ≃ₐ[R] Matrix (Fin n) (Fin n) (R ⊗[F] B))
    (hE : ∀ (R : Type u) [CommRing R] [Algebra F R] (g : (R ⊗[F] A)ˣ),
      antiValue (extendAnti (toDivisionInvolution s).anti R) g.val * g.val = 1 ↔
        let h := hermitianValue (extendAnti b R) (H.map (intoTensor R B))
        ∀ x y, h (E R g.val *ᵥ x) (E R g.val *ᵥ y) = h x y)
    (hNat : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (f : R →ₐ[F] S) (x : R ⊗[F] A),
      E S (tensorMap A f x) = (E R x).map (tensorMap B f)) :
    isometryPoints s ≅ QuaternionHermitianCocharacters.isometryPoints b.toAlgHom H := by
  let η (R : TestAlgebra F) := Units.mapEquiv (E R).toMulEquiv
  have hη (R : TestAlgebra F) (g : (R ⊗[F] A)ˣ) :
      g ∈ (s.baseChange R).isometries ↔
        η R g ∈ QuaternionHermitianCocharacters.isometries (QuaternionHermitianCocharacters.extendConjugation b.toAlgHom)
          (H.map (intoTensor R B)) := by
    rw [Involution.mem_isometries, QuaternionHermitianCocharacters.mem_isometries_iff]
    have h := hE R g
    dsimp only at h
    rw [extendAnti_involution, extendedPairing_eq] at h
    exact h
  let eR (R : TestAlgebra F) :
      (isometryPoints s).obj R ≃* (QuaternionHermitianCocharacters.isometryPoints b.toAlgHom H).obj R :=
    { toFun := fun g => ⟨η R g.val, (hη R g.val).mp g.property⟩
      invFun := fun g => ⟨(η R).symm g.val, (hη R _).mpr (by
        rw [MulEquiv.apply_symm_apply]
        exact g.property)⟩
      left_inv := fun g => Subtype.ext ((η R).symm_apply_apply g.val)
      right_inv := fun g => Subtype.ext ((η R).apply_symm_apply g.val)
      map_mul' := fun g h => Subtype.ext (map_mul (η R) g.val h.val) }
  refine NatIso.ofComponents (fun R => (eR R).toGrpIso) ?_
  intro R S f
  apply GrpCat.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  exact hNat R S f.hom (g.val : R ⊗[F] A)

private theorem unliftHyperbolicMatrix_J (n : ℕ) (R : Type u) [CommRing R] :
    unliftHyperbolicMatrix n R (Matrix.J (Specs.SymplecticDatumTorusAndBorel.HyperbolicIndex n) R) =
      Matrix.J (Fin n) R := by
  ext i j
  cases i <;> cases j <;>
    simp [unliftHyperbolicMatrix, Matrix.coe_reindexAlgEquiv, Matrix.J, Matrix.one_apply]

private theorem unliftHyperbolicMatrix_transpose (n : ℕ) (R : Type u) [CommRing R]
    (X : Specs.SymplecticDatumAdjointDescent.MatrixAlgebra
      (Specs.SymplecticDatumTorusAndBorel.HyperbolicIndex n) R) :
    unliftHyperbolicMatrix n R X.transpose = (unliftHyperbolicMatrix n R X).transpose := rfl

private theorem unliftHyperbolicMatrix_mem (n : ℕ) (R : Type u) [CommRing R]
    (X : Specs.SymplecticDatumAdjointDescent.MatrixAlgebra
      (Specs.SymplecticDatumTorusAndBorel.HyperbolicIndex n) R) :
    unliftHyperbolicMatrix n R X ∈ Matrix.symplecticGroup (Fin n) R ↔
      X ∈ Matrix.symplecticGroup (Specs.SymplecticDatumTorusAndBorel.HyperbolicIndex n) R := by
  simp only [SymplecticGroup.mem_iff', ← unliftHyperbolicMatrix_J,
    ← unliftHyperbolicMatrix_transpose, ← map_mul]
  exact (unliftHyperbolicMatrix n R).injective.eq_iff

private noncomputable def splitIsometryComparison {I : Type u} [Fintype I] [DecidableEq I] (s : Involution F A)
    (E : ∀ (R : Type u) [CommRing R] [Algebra F R],
      (R ⊗[F] A) ≃ₐ[R] Matrix (I ⊕ I) (I ⊕ I) R)
    (hE : ∀ (R : Type u) [CommRing R] [Algebra F R] (x : R ⊗[F] A),
      E R x ∈ Matrix.symplecticGroup I R ↔ (s.baseChange R).toLinearMap x * x = 1)
    (hNat : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (f : R →ₐ[F] S) (x : R ⊗[F] A), E S (tensorMap A f x) = (E R x).map f) :
    isometryPoints s ≅ Specs.SymplecticMatrixStructure.symplecticPoints F I := by
  let eR (R : TestAlgebra F) :
      (isometryPoints s).obj R ≃* Matrix.symplecticGroup I R := by
    let toMatrix : (isometryPoints s).obj R →* Matrix.symplecticGroup I R :=
      { toFun := fun g => ⟨E R (g.val : R ⊗[F] A), (hE R _).mpr g.property⟩
        map_one' := Subtype.ext ((E R).map_one)
        map_mul' := fun g h => Subtype.ext ((E R).map_mul _ _) }
    apply MulEquiv.ofBijective toMatrix
    constructor
    · intro g h heq
      exact Subtype.ext (Units.ext ((E R).injective (congrArg Subtype.val heq)))
    · intro g
      let gunit := (Submonoid.subtype (Matrix.symplecticGroup I R)).toHomUnits g
      obtain ⟨x, hx⟩ := (Units.mapEquiv (E R).toMulEquiv).surjective gunit
      have he : E R (x : R ⊗[F] A) = g.val := congrArg Units.val hx
      exact ⟨⟨x, (hE R _).mp (he.symm ▸ g.property)⟩, Subtype.ext he⟩
  refine NatIso.ofComponents (fun R => (eR R).toGrpIso) ?_
  intro R S f
  apply GrpCat.ext
  intro g
  apply Subtype.ext
  exact hNat R S f.hom (g.val : R ⊗[F] A)

private theorem splitLocalModel_of_field {n r : ℕ}
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F A) (s : Involution F A)
    (c : SplitComparison (toDivisionInvolution s) L n)
    (hr : 0 < r) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F) : SplitLocalModel s n := by
  obtain ⟨_, _, _, _, _, _, _, _, E, _, hE, hNat⟩ :=
    SymplecticDivisionForms.fieldModel.{u,u,u,u} hA (toDivisionInvolution s) c e
  have hEq (R : Type u) [CommRing R] [Algebra F R] (x : R ⊗[F] A) :
      E R x ∈ Matrix.symplecticGroup (Fin n) R ↔ (s.baseChange R).toLinearMap x * x = 1 := by
    rw [← extendAnti_involution s]
    exact hE R x
  let E' (R : Type u) [CommRing R] [Algebra F R] :=
    (E R).trans (unliftHyperbolicMatrix n R).symm
  have hEq' (R : Type u) [CommRing R] [Algebra F R] (x : R ⊗[F] A) :
      E' R x ∈ Matrix.symplecticGroup (Specs.SymplecticDatumTorusAndBorel.HyperbolicIndex n) R ↔
        (s.baseChange R).toLinearMap x * x = 1 := by
    rw [← unliftHyperbolicMatrix_mem]
    exact ((unliftHyperbolicMatrix n R).apply_symm_apply (E R x)) ▸ hEq R x
  have hNat' (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (f : R →ₐ[F] S) (x : R ⊗[F] A) :
      E' S (tensorMap A f x) = (E' R x).map f := by
    change (unliftHyperbolicMatrix n S).symm (E S (tensorMap A f x)) = _
    rw [hNat]
    rfl
  refine ⟨r, hr, e, E, hEq, hNat, splitIsometryComparison s E' hEq' hNat', ?_⟩
  intro R g
  exact (unliftHyperbolicMatrix n R).apply_symm_apply (E R (g.val : R ⊗[F] A))

private theorem quaternionLocalModel_of_degree_two {n r : ℕ}
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F A) (s : Involution F A)
    (c : SplitComparison (toDivisionInvolution s) L n)
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (hd : degree F B = 2)
    (hr : 0 < r) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B) : QuaternionLocalModel s n hB := by
  have hs : degree F A = n + n :=
    RM03.CSA.degree_eq_matrix_size hA
      (c.equiv.trans (Matrix.reindexAlgEquiv L L finSumFinEquiv))
  have hm : degree F A = r * degree F B :=
    RM03.CSA.degree_matrix_division hA hB.2 hr e
  rw [hs, hd] at hm
  have hrn : r = n := by omega
  subst r
  obtain ⟨b, hbar, hsq, hadj, _⟩ := quaternionConjugation.{u,u,u} hB hd
  let b' : Specs.SymplecticDivisionForms.Involution F B := ⟨b, hsq⟩
  have hcan : Specs.SymplecticDivisionForms.CanonicalConjugation.{u,u,u} hB b' :=
    ⟨hbar, hadj⟩
  obtain ⟨H, hsym, hAdj, hdiag, hLaws, hnondeg, hnorm, E, hPure, _, hE, hNat⟩ :=
    SymplecticDivisionForms.quaternionModel.{u,u,u,u,u}
      hA (toDivisionInvolution s) c hB hd b' hcan e
  have hpair : hermitianValue b'.anti H.val = QuaternionHermitianCocharacters.pairing b.toAlgHom H.val :=
    hermitianValue_pairing b H.val
  rw [hpair] at hLaws hnondeg hnorm
  let h : HermitianPairing b (Fin n → B) :=
    { value := QuaternionHermitianCocharacters.pairing b.toAlgHom H.val
      add_right := hLaws.add_right
      smul_right := hLaws.mul_right
      hermitian := hLaws.symmetric
      nondegenerate := hnondeg
      central_norm := hnorm }
  refine ⟨e, b, H, hbar, hsym, hAdj, hdiag, hLaws, hnondeg, hnorm,
    ⟨E, quaternionIsometryComparison s b H.val E hE hNat, hPure, fun _ _ => rfl⟩, ?_⟩
  let hasHyperbolicPair : Prop := ∃ x y : Fin n → B,
    x ≠ 0 ∧ h.value x x = 0 ∧ h.value x y = 1 ∧ h.value y x = 1 ∧ h.value y y = 0
  have hyperbolicOfNontrivial
      (cochar : QuaternionHermitianCocharacters.multiplicativePoints.{u,u} F ⟶
        QuaternionHermitianCocharacters.isometryPoints b.toAlgHom H.val)
      (hnontrivial : ¬ ∀ R t, cochar.app R t = 1) : hasHyperbolicPair := by
    classical
    by_contra hNoPair
    have anisotropic (x : Fin n → B) (hxx : h.value x x = 0) : x = 0 := by
      by_contra hx
      obtain ⟨y, hxy, hyx, hyy⟩ := quaternionHyperbolicPartner hB hd b hbar h x hx hxx
      exact hNoPair ⟨x, y, hx, hxx, hxy, hyx, hyy⟩
    exact hnontrivial (QuaternionHermitianCocharacters.cocharacter_eq_one_of_anisotropic
      b.toAlgHom H.val anisotropic cochar)
  dsimp only
  intro cochar
  refine ⟨?_, hyperbolicOfNontrivial cochar⟩
  intro hnoncentral
  apply hyperbolicOfNontrivial cochar
  intro htrivial
  apply hnoncentral
  intro R t g
  rw [htrivial]
  exact Commute.one_left g

theorem nonarchimedeanTypeC : NonarchimedeanTypeC.{u} := by
  intro F A L _ _ _ _ _ _ _ _ hA s n c
  obtain ⟨B, hDiv, hAlg, r, hB, hr, ⟨e⟩, h⟩ :=
    nonarchimedeanPresentations hA (toDivisionInvolution s).anti
  let := hDiv
  let := hAlg
  rcases h with hfield | hd
  · obtain ⟨eB⟩ := hfield
    exact Or.inl (splitLocalModel_of_field hA s c hr (e.trans eB.mapMatrix))
  · exact Or.inr ⟨B, hDiv, hAlg, hB, hd, quaternionLocalModel_of_degree_two hA s c hB hd hr e⟩

theorem realTypeC : RealTypeC := by
  intro A L _ _ _ _ hA s n c
  obtain ⟨r, B, hDiv, hAlg, hB, hr, ⟨e⟩⟩ :=
    RM03.CSA.MatrixDivision.exists_presentation ℝ A hA
  let := hDiv
  let := hAlg
  have hB' := RM03.CSA.isCentralSimple_of_isCentralDivision ℝ B hB
  rcases realDivision hB' with hfield | hquaternion
  · obtain ⟨eB⟩ := hfield
    exact Or.inl (splitLocalModel_of_field hA s c hr (e.trans eB.mapMatrix))
  · obtain ⟨eB⟩ := hquaternion
    have hd : degree ℝ B = 2 := by
      apply (RM03.CSA.degree_eq_iff hB').mpr
      exact ⟨by decide, eB.toLinearEquiv.finrank_eq.trans Quaternion.finrank_eq_four⟩
    exact Or.inr ⟨B, hDiv, hAlg, hB', ⟨eB⟩, quaternionLocalModel_of_degree_two hA s c hB' hd hr e⟩

theorem complexTypeC : ComplexTypeC := by
  intro A L _ _ _ _ hA s n c
  obtain ⟨r, hr, ⟨e⟩⟩ := archimedeanPresentations.2 hA
  exact splitLocalModel_of_field hA s c hr e

end LocalModels

section BaseChange

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix
open LinearAlgebraicGroups.Specs
open Specs.SymplecticInvolutionModels.DivisionForms
open Specs.SymplecticDivisionForms (SplitComparison antiValue standardAdjoint)
open Specs.SymplecticDatumAdjointDescent (adjoint)
open Specs.SymplecticDatumTorusAndBorel (HyperbolicIndex)
open Specs.SymplecticMatrixStructure (symplecticPoints)
open Specs.TypeCSplitRecognition (MatrixTwisting)
open SymplecticIsometryDescent (Involution PointsOf isometryPoints overBase)
open private extendSplit split_comparison_all
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations

noncomputable section

variable {k F A : Type u} [Field k] [Field F] [Algebra k F] [Ring A] [Algebra k A]

private def cancelTensorBaseChange (R : Type u)
    [CommRing R] [Algebra k R] [Algebra F R] [IsScalarTower k F R] :
    (R ⊗[F] (F ⊗[k] A)) ≃ₐ[R] R ⊗[k] A :=
  (Algebra.TensorProduct.assoc k F R R F A).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid F R R) (.refl : A ≃ₐ[k] A))

private theorem cancelTensorBaseChange_tmul (R : Type u)
    [CommRing R] [Algebra k R] [Algebra F R] [IsScalarTower k F R]
    (r : R) (f : F) (a : A) :
    cancelTensorBaseChange R (r ⊗ₜ[F] (f ⊗ₜ[k] a)) = (f • r) ⊗ₜ[k] a := by
  simp [cancelTensorBaseChange]

private theorem cancelBaseChange_involution (s : Involution k A) (R : Type u)
    [CommRing R] [Algebra k R] [Algebra F R] [IsScalarTower k F R]
    (x : R ⊗[F] (F ⊗[k] A)) :
    cancelTensorBaseChange (k := k) (F := F) (A := A) R
      (((s.baseChange F).baseChange R).toLinearMap x) =
    (s.baseChange R).toLinearMap (cancelTensorBaseChange (k := k) (F := F) (A := A) R x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r y =>
    rw [Involution.baseChange_tmul]
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      rw [Involution.baseChange_tmul, cancelTensorBaseChange_tmul,
        cancelTensorBaseChange_tmul, Involution.baseChange_tmul]
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

private def cancelTestAlgebra (R : TestAlgebra F) :
    (R ⊗[F] (F ⊗[k] A)) ≃ₐ[R] (overBase k F R ⊗[k] A) :=
  letI : Algebra k R := ((algebraMap F R).comp (algebraMap k F)).toAlgebra
  letI : IsScalarTower k F R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  cancelTensorBaseChange (k := k) (F := F) (A := A) R

private theorem cancelTestAlgebra_involution (s : Involution k A) (R : TestAlgebra F)
    (x : R ⊗[F] (F ⊗[k] A)) :
    cancelTestAlgebra R (((s.baseChange F).baseChange R).toLinearMap x) =
      (s.baseChange (overBase k F R)).toLinearMap (cancelTestAlgebra R x) := by
  let : Algebra k R := ((algebraMap F R).comp (algebraMap k F)).toAlgebra
  let : IsScalarTower k F R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact cancelBaseChange_involution s R x

private theorem cancelTestAlgebra_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (x : R ⊗[F] (F ⊗[k] A)) :
    cancelTestAlgebra S (SymplecticIsometryDescent.tensorMap f x) =
      SymplecticIsometryDescent.tensorMap ((restrictTestAlgebra k F).map f)
        (cancelTestAlgebra R x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r y =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul a x =>
      let : Algebra k R := ((algebraMap F R).comp (algebraMap k F)).toAlgebra
      let : Algebra k S := ((algebraMap F S).comp (algebraMap k F)).toAlgebra
      let : IsScalarTower k F R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let : IsScalarTower k F S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      simp only [cancelTestAlgebra, cancelTensorBaseChange_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change (a • f.hom r) ⊗ₜ[k] x = f.hom (a • r) ⊗ₜ[k] x
      rw [map_smul]

private def isometryPointsBaseChange (s : Involution k A) :
    isometryPoints (s.baseChange F) ≅ restrictTestAlgebra k F ⋙ isometryPoints s := by
  let unitsEquiv : ∀ R : TestAlgebra F, (R ⊗[F] (F ⊗[k] A))ˣ ≃* (overBase k F R ⊗[k] A)ˣ :=
    fun R => Units.mapEquiv (cancelTestAlgebra (k := k) (A := A) R).toMulEquiv
  have hUnits (R : TestAlgebra F) (g : (R ⊗[F] (F ⊗[k] A))ˣ) :
      g ∈ ((s.baseChange F).baseChange R).isometries ↔
        unitsEquiv R g ∈ (s.baseChange (overBase k F R)).isometries := by
    rw [Involution.mem_isometries, Involution.mem_isometries]
    let e := cancelTestAlgebra (k := k) (A := A) R
    change ((s.baseChange F).baseChange R).toLinearMap g.val * g.val = 1 ↔
      (s.baseChange (overBase k F R)).toLinearMap (e g.val) * e g.val = 1
    rw [← cancelTestAlgebra_involution, ← map_mul]
    exact ⟨fun h => by rw [h, map_one], fun h => e.injective (h.trans (e.map_one).symm)⟩
  let eR (R : TestAlgebra F) :
      (isometryPoints (s.baseChange F)).obj R ≃*
        (restrictTestAlgebra k F ⋙ isometryPoints s).obj R :=
    { toFun := fun g => ⟨unitsEquiv R g.val, (hUnits R g.val).mp g.property⟩
      invFun := fun g => ⟨(unitsEquiv R).symm g.val, (hUnits R _).mpr (by
        rw [MulEquiv.apply_symm_apply]
        exact g.property)⟩
      left_inv := fun g => Subtype.ext ((unitsEquiv R).symm_apply_apply g.val)
      right_inv := fun g => Subtype.ext ((unitsEquiv R).apply_symm_apply g.val)
      map_mul' := fun g h => Subtype.ext (map_mul (unitsEquiv R) g.val h.val) }
  refine NatIso.ofComponents (fun R => (eR R).toGrpIso) ?_
  intro R S f
  apply GrpCat.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  exact cancelTestAlgebra_natural f (g.val : R ⊗[F] (F ⊗[k] A))

variable {K : Type u} [Field K] [Algebra k K]

private def splitComparisonBaseChange [Algebra.IsAlgebraic k K]
    (s : Involution k A) {n : ℕ} (c : SplitComparison (toDivisionInvolution s) K n) :
    SplitComparison (toDivisionInvolution (s.baseChange F)) (AlgebraicClosure F) n := by
  let M := AlgebraicClosure F
  let j : K →ₐ[k] M := IsAlgClosed.lift
  letI : Algebra K M := j.toRingHom.toAlgebra
  letI : IsScalarTower k K M := IsScalarTower.of_algHom j
  let e := cancelTensorBaseChange (k := k) (F := F) (A := A) M
  let cM : SplitComparison (toDivisionInvolution s) M n := extendSplit c
  refine ⟨e.trans cM.equiv, ?_⟩
  intro a
  change cM.equiv (e (1 ⊗ₜ[F] (s.baseChange F).toLinearMap a)) =
    standardAdjoint n (cM.equiv (e (1 ⊗ₜ[F] a)))
  have he := cancelBaseChange_involution s M ((1 : M) ⊗ₜ[F] a)
  rw [Involution.baseChange_tmul] at he
  change e (1 ⊗ₜ[F] (s.baseChange F).toLinearMap a) =
    (s.baseChange M).toLinearMap (e (1 ⊗ₜ[F] a)) at he
  rw [he]
  have hc := split_comparison_all cM (e (1 ⊗ₜ[F] a))
  rwa [extendAnti_involution] at hc

variable {n : ℕ} {G H : AffineAlgebraicGroup k}
variable {c : PointsOf H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))}
variable {f : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val}
variable {t : MatrixTwisting n G H c f}

private def descendedInvolutionSplit (d : DescendedTypeC t) :
    SplitComparison (toDivisionInvolution d.model.fixed.involution) K (n + 1) := by
  let q := unliftHyperbolicMatrix (n + 1) K
  refine ⟨d.model.fixed.split.trans q, ?_⟩
  intro a
  change q (d.model.fixed.split (1 ⊗ₜ[k] d.model.fixed.involution.toLinearMap a)) =
    standardAdjoint (n + 1) (q (d.model.fixed.split (1 ⊗ₜ[k] a)))
  rw [← Involution.baseChange_tmul, d.model.fixed.splitInvolution, adjoint,
    standardAdjoint, map_mul, map_mul, map_neg, unliftHyperbolicMatrix_J,
    unliftHyperbolicMatrix_transpose]

private theorem involutionTraceOne (s : Involution k A) {n : ℕ}
    (c : SplitComparison (toDivisionInvolution s) K n) :
    ∃ z : A, z + s.toLinearMap z = 1 := by
  let P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    Matrix.fromBlocks 1 0 0 0
  have hP : P + standardAdjoint n P = 1 := by
    simp [P, standardAdjoint, Matrix.J, Matrix.fromBlocks_neg, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  let traceMap : A →ₗ[k] A := LinearMap.id + s.toLinearMap
  obtain ⟨y, hy⟩ := c.equiv.surjective P
  have hSplit := split_comparison_all c y
  rw [extendAnti_involution] at hSplit
  have hY : traceMap.baseChange K y = 1 := by
    apply c.equiv.injective
    simp only [traceMap, LinearMap.baseChange_add, LinearMap.baseChange_id,
      LinearMap.add_apply, LinearMap.id_apply, map_add, map_one]
    change c.equiv y + c.equiv ((s.baseChange K).toLinearMap y) = 1
    rw [hSplit, hy]
    exact hP
  let Q := A ⧸ LinearMap.range traceMap
  let q : A →ₗ[k] Q := (LinearMap.range traceMap).mkQ
  have hzero (x : K ⊗[k] A) : q.baseChange K (traceMap.baseChange K x) = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      have hz : q (traceMap a) = 0 := by
        apply LinearMap.mem_ker.mp
        change traceMap a ∈ LinearMap.ker (LinearMap.range traceMap).mkQ
        rw [Submodule.ker_mkQ]
        exact LinearMap.mem_range_self traceMap a
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hz, TensorProduct.tmul_zero]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  have hq : q 1 = 0 := by
    apply Module.Flat.tensorProduct_mk_injective (R := k) (S := K) (M := Q)
    change (1 : K) ⊗ₜ[k] q 1 = (1 : K) ⊗ₜ[k] (0 : Q)
    rw [TensorProduct.tmul_zero, ← LinearMap.baseChange_tmul, ← Algebra.TensorProduct.one_def, ← hY]
    exact hzero y
  have hm : (1 : A) ∈ LinearMap.range traceMap := by
    rw [← Submodule.ker_mkQ (LinearMap.range traceMap)]
    exact LinearMap.mem_ker.mpr hq
  exact hm

theorem descendedTypeCTraceOne : DescendedTypeCTraceOne.{u} := by
  intro k K _ _ _ n G H c f t d
  exact involutionTraceOne d.model.fixed.involution (descendedInvolutionSplit d)

theorem descendedTypeCBaseChange : DescendedTypeCBaseChange.{u} := by
  intro k K _ _ _ _ n G H c f t d F _ _
  refine ⟨RM03.CSA.isCentralSimple_baseChange d.model.fixed.centralSimple,
    ⟨splitComparisonBaseChange d.model.fixed.involution (descendedInvolutionSplit d)⟩, ?_⟩
  exact ⟨groupBaseChangePointIso F G.val ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra k F) d.model.comparison ≪≫
      (isometryPointsBaseChange d.model.fixed.involution).symm⟩

theorem nonarchimedeanTypeCAtExtension : NonarchimedeanTypeCAtExtension.{u} := by
  intro k K _ _ _ _ n G H c f t d F _ _ _ _ _
  obtain ⟨hA, ⟨cF⟩, hG⟩ := descendedTypeCBaseChange d F
  exact ⟨hG, nonarchimedeanTypeC hA _ (n + 1) cF⟩

theorem realTypeCAtExtension : RealTypeCAtExtension := by
  intro k K _ _ _ _ _ n G H c f t d
  obtain ⟨hA, ⟨cF⟩, hG⟩ := descendedTypeCBaseChange d ℝ
  exact ⟨hG, realTypeC hA _ (n + 1) cF⟩

theorem complexTypeCAtExtension : ComplexTypeCAtExtension := by
  intro k K _ _ _ _ _ n G H c f t d
  obtain ⟨hA, ⟨cF⟩, hG⟩ := descendedTypeCBaseChange d ℂ
  exact ⟨hG, complexTypeC hA _ (n + 1) cF⟩


end
end BaseChange

end LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
