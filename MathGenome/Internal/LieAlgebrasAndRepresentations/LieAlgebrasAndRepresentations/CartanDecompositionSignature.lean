import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CharacteristicRadical
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Cartan decomposition, reductivity and the Killing signature for a compact-form involution. -/

noncomputable section

open scoped TensorProduct
open Complex Module LieAlgebra
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact involutionConjugation)
open Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition (IsReductive_value)

universe u

namespace LieAlgebrasAndRepresentations.CartanDecompositionSignature

abbrev complexFixed := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.complexFixed
abbrev fixedConjugation := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.fixedConjugation
abbrev compactEigenspace := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.compactEigenspace
abbrev mulI := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.mulI
abbrev compactPart := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.compactPart
abbrev noncompactPart := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.noncompactPart
abbrev killingQuadratic := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.killingQuadratic
abbrev killingSignature := @Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.killingSignature

open private killing_fixed from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

section Decomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
variable (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a)

local notation "E₊" => compactEigenspace ω a 1
local notation "E₋" => compactEigenspace ω a (-1)
local notation "σ" => involutionConjugation ω a hcomm hinv
local notation "P" => compactPart ω a hcomm hinv
local notation "N" => noncompactPart ω a hcomm hinv

private theorem eq_zero_of_eq_neg {V : Type*} [AddCommGroup V] [Module ℂ V]
    {x : V} (h : x = -x) : x = 0 := by
  have hx : (2 : ℂ) • x = 0 := by
    rw [two_smul, add_eq_zero_iff_eq_neg]
    exact h
  exact (smul_eq_zero.mp hx).resolve_left (by norm_num)

private theorem mulI_apply (x : L) : mulI x = I • x := rfl

private theorem compact_mem_realForm {x : L} (hx : x ∈ E₊) : x ∈ (σ).fixed := by
  obtain ⟨hω, ha⟩ : ω.map x = x ∧ a x = (1 : ℂ) • x := hx
  change a (ω.map x) = x
  rw [hω, ha, one_smul]

private theorem imaginary_mem_realForm {x : L} (hx : x ∈ E₋) : I • x ∈ (σ).fixed := by
  obtain ⟨hω, ha⟩ : ω.map x = x ∧ a x = (-1 : ℂ) • x := hx
  change a (ω.map (I • x)) = I • x
  rw [ω.antilinear, star_def, conj_I, hω, map_smul, ha]
  simp

include hcomm hinv in
theorem compact_eigenspace_decomposition :
    Disjoint E₊ E₋ ∧ E₊ ⊔ E₋ = ω.fixed.toSubmodule := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hp : a x = (1 : ℂ) • x := hx.2
    have hn : a x = (-1 : ℂ) • x := hy.2
    exact eq_zero_of_eq_neg (by simpa using hp.symm.trans hn)
  · apply le_antisymm
    · exact sup_le (fun {_} h => h.1) (fun {_} h => h.1)
    · intro x hx
      change ω.map x = x at hx
      let p := (2 : ℂ)⁻¹ • (x + a x)
      let n := (2 : ℂ)⁻¹ • (x - a x)
      have hax : ω.map (a x) = a x := by rw [hcomm, hx]
      have hreal : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
        simp
      have hp : p ∈ E₊ := by
        refine ⟨?_, ?_⟩
        · simp only [p, ω.antilinear, hreal, map_add, hx, hax]
        · simp only [p, map_smul, map_add, hinv x, one_smul, add_comm (a x) x]
      have hn : n ∈ E₋ := by
        refine ⟨?_, ?_⟩
        · simp only [n, ω.antilinear, hreal, map_sub, hx, hax]
        · simp only [n, map_smul, map_sub, hinv x, neg_one_smul]
          rw [← smul_neg, neg_sub]
      exact Submodule.mem_sup.mpr ⟨p, hp, n, hn, by dsimp [p, n]; module⟩

private theorem compact_imaginary_disjoint :
    Disjoint E₊ (E₋.map mulI) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨hω, _⟩ : ω.map y = y ∧ a y = (-1 : ℂ) • y := ‹y ∈ E₋›
  have he : ω.map (mulI y) = mulI y := hx.1
  rw [mulI_apply, ω.antilinear, star_def, conj_I, neg_smul, hω] at he
  exact eq_zero_of_eq_neg he.symm

private theorem real_form_parts {x : L} (hx : x ∈ (σ).fixed) :
    ∃ p ∈ E₊, ∃ n ∈ E₋, p + I • n = x := by
  change a (ω.map x) = x at hx
  have hax : a x = ω.map x := (congrArg a hx.symm).trans (hinv _)
  obtain ⟨p, n, hp, hn, he⟩ := fixed_parts_formula ω x
  refine ⟨(p : L), ⟨p.property, ?_⟩, (n : L), ⟨n.property, ?_⟩, he⟩
  · rw [one_smul, hp, map_smul, map_add, hax, hx, add_comm]
  · rw [neg_one_smul, hn, map_smul, map_sub, hax, hx, ← neg_sub, smul_neg]

theorem real_form_decomposition :
    IsRealForm (σ).fixed ∧ Disjoint E₊ (E₋.map mulI) ∧
      E₊ ⊔ E₋.map mulI = (σ).fixed.toSubmodule := by
  refine ⟨fixed_isRealForm σ, compact_imaginary_disjoint ω a, le_antisymm ?_ ?_⟩
  · refine sup_le (fun {_} hx => compact_mem_realForm ω a hcomm hinv hx) ?_
    rintro x ⟨n, hn, rfl⟩
    exact imaginary_mem_realForm ω a hcomm hinv hn
  · intro x hx
    obtain ⟨p, hp, n, hn, he⟩ := real_form_parts ω a hcomm hinv hx
    exact Submodule.mem_sup.mpr ⟨p, hp, mulI n, Submodule.mem_map_of_mem hn, he⟩

private theorem cartan_parts_complementary : IsCompl P N := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have he := (Submodule.disjoint_def.mp (compact_imaginary_disjoint ω a)) (x : L) hx hy
    exact Subtype.ext he
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨p, hp, n, hn, he⟩ := real_form_parts ω a hcomm hinv x.property
    refine Submodule.mem_sup.mpr ⟨⟨p, compact_mem_realForm ω a hcomm hinv hp⟩, hp,
      ⟨I • n, imaginary_mem_realForm ω a hcomm hinv hn⟩, ⟨n, hn, rfl⟩, Subtype.ext he⟩

end Decomposition

section Reductive

theorem reductive_of_positive_invariant (A : Type u) [LieRing A] [LieAlgebra ℝ A]
    [FiniteDimensional ℝ A] (B : LinearMap.BilinForm ℝ A) (hB : B.lieInvariant A)
    (hpos : ∀ x : A, x ≠ 0 → 0 < B x x) : IsReductive_value ℝ A := by
  have zero_of_self {x : A} (hx : B x x = 0) : x = 0 := by
    by_contra h
    exact (hpos x h).ne' hx
  have central_of_abelian (J : LieIdeal ℝ A) (hJ : ⁅J, J⁆ = ⊥) :
      J ≤ center ℝ A := by
    intro y hy x
    have hz : ⁅x, y⁆ ∈ J := J.lie_mem hy
    have hc : ⁅y, ⁅x, y⁆⁆ = 0 :=
      by
        have h : ⁅y, ⁅x, y⁆⁆ ∈ ⁅J, J⁆ := LieSubmodule.lie_mem_lie hy hz
        simpa [hJ] using h
    apply zero_of_self
    have he := hB y x ⁅x, y⁆
    rw [hc, LinearMap.map_zero, neg_zero, ← lie_skew y x] at he
    exact neg_eq_zero.mp (by simpa only [map_neg, LinearMap.neg_apply] using he)
  -- A central derived term forces the preceding term to be abelian.
  let R := LieAlgebra.radical ℝ A
  let D := fun n => derivedSeriesOfIdeal ℝ A n R
  have descend (n : ℕ) (hn : D n ≤ center ℝ A) : R ≤ center ℝ A := by
    induction n with
    | zero => exact hn
    | succ n ih =>
      apply ih
      apply central_of_abelian
      apply le_antisymm _ bot_le
      rw [LieSubmodule.lie_le_iff]
      intro x hx y hy
      have hxy : ⁅x, y⁆ ∈ D (n + 1) := by
        rw [show D (n + 1) = ⁅D n, D n⁆ from derivedSeriesOfIdeal_succ ℝ A R n]
        exact LieSubmodule.lie_mem_lie hx hy
      have hc : ⁅x, ⁅x, y⁆⁆ = 0 := hn hxy x
      change ⁅x, y⁆ = 0
      apply zero_of_self
      rw [hB x y ⁅x, y⁆, hc, LinearMap.map_zero, neg_zero]
  obtain ⟨n, hn⟩ := IsSolvable.solvable ℝ R
  have hz : D n = ⊥ := (R.derivedSeries_eq_bot_iff n).mp hn
  exact le_antisymm (descend n (hz.symm ▸ bot_le)) (center_le_radical ℝ A)

end Reductive


section FixedReductivity

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a)

local notation "K" => complexFixed a
local notation "κ" => fixedConjugation ω a hcomm

private def compactFixedInclusion : (κ).fixed →ₗ⁅ℝ⁆ ω.fixed where
  toFun x := ⟨((x : K) : L), congrArg Subtype.val x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

omit [FiniteDimensional ℂ L] in
private theorem compactFixedInclusion_injective :
    Function.Injective (compactFixedInclusion ω a hcomm) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : ω.fixed => (z : L)) h))

theorem compact_fixed_reductive (hc : IsCompact ω) : IsReductive_value ℝ (κ).fixed := by
  let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let : FiniteDimensional ℝ ω.fixed :=
    FiniteDimensional.of_injective ω.fixed.toSubmodule.subtype Subtype.val_injective
  let f := compactFixedInclusion ω a hcomm
  let : FiniteDimensional ℝ (κ).fixed :=
    FiniteDimensional.of_injective f.toLinearMap (compactFixedInclusion_injective ω a hcomm)
  let B := (-killingForm ℝ ω.fixed).compl₁₂ f.toLinearMap f.toLinearMap
  apply reductive_of_positive_invariant _ B
  · intro x y z
    change -(killingForm ℝ ω.fixed (f ⁅x, y⁆) (f z)) =
      -(-(killingForm ℝ ω.fixed (f y) (f ⁅x, z⁆)))
    rw [f.map_lie, f.map_lie, killingForm, LieModule.traceForm_apply_lie_apply']
  · intro x hx
    change 0 < -(killingForm ℝ ω.fixed (f x) (f x))
    exact neg_pos.mpr (hc (f x) (fun h =>
      hx (compactFixedInclusion_injective ω a hcomm (h.trans (map_zero f).symm))))

private theorem complexification_reductive
    (A : Type u) [LieRing A] [LieAlgebra ℝ A] [FiniteDimensional ℝ A]
    (hA : IsReductive_value ℝ A) :
    IsReductive_value ℂ (ℂ ⊗[ℝ] A) := by
  change LieAlgebra.radical ℝ A = center ℝ A at hA
  change LieAlgebra.radical ℂ (ℂ ⊗[ℝ] A) = center ℂ (ℂ ⊗[ℝ] A)
  have hrad : LieAlgebra.radical ℂ (ℂ ⊗[ℝ] A) =
      (LieAlgebra.radical ℝ A).baseChange ℂ := radical_baseChange ℝ A ℂ
  have hc : ⁅(⊤ : LieIdeal ℝ A), center ℝ A⁆ = ⊥ := by
    rw [eq_bot_iff, LieSubmodule.lie_le_iff]
    intro x _ y hy
    exact (LieSubmodule.mem_bot _).mpr (hy x)
  have hc' := congrArg (fun J : LieIdeal ℝ A => J.baseChange ℂ) hc
  rw [LieSubmodule.lie_baseChange, LieSubmodule.baseChange_top, LieSubmodule.baseChange_bot] at hc'
  refine le_antisymm ?_ (center_le_radical _ _)
  rw [hrad, hA]
  intro y hy x
  exact (LieSubmodule.mem_bot _).mp
    (hc' ▸ LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy)

private theorem reductive_of_equiv {A B : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
    (e : A ≃ₗ⁅ℂ⁆ B) (hA : IsReductive_value ℂ A) : IsReductive_value ℂ B := by
  change LieAlgebra.radical ℂ A = center ℂ A at hA
  change LieAlgebra.radical ℂ B = center ℂ B
  let R := LieAlgebra.radical ℂ B
  let J := R.comap e.toLieHom
  let f : J →ₗ⁅ℂ⁆ R :=
    { toFun x := ⟨e x, x.property⟩
      map_add' x y := Subtype.ext (map_add e (x : A) (y : A))
      map_smul' r x := Subtype.ext (map_smul e r (x : A))
      map_lie' {x y} := Subtype.ext (e.map_lie (x : A) (y : A)) }
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (e.injective (congrArg Subtype.val h))
  have hJ : IsSolvable J := hf.lieAlgebra_isSolvable
  have hJc : J ≤ center ℂ A := hA ▸ (LieAlgebra.LieIdeal.solvable_iff_le_radical ℂ A J).mp hJ
  refine le_antisymm ?_ (center_le_radical _ _)
  intro y hy x
  obtain ⟨y, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := e.surjective x
  have hz : ⁅x, y⁆ = 0 := hJc hy x
  change ⁅e x, e y⁆ = 0
  rw [← e.map_lie, hz, map_zero]

include hcomm in
theorem complex_fixed_reductive (hc : IsCompact ω) : IsReductive_value ℂ K := by
  let : FiniteDimensional ℂ K :=
    FiniteDimensional.of_injective (complexFixed a).toSubmodule.subtype Subtype.val_injective
  let : FiniteDimensional ℝ K := FiniteDimensional.trans ℝ ℂ K
  let : FiniteDimensional ℝ (κ).fixed := FiniteDimensional.of_injective
    (κ).fixed.toSubmodule.subtype Subtype.val_injective
  obtain ⟨e, _⟩ := fixed_complexification κ
  exact reductive_of_equiv e (complexification_reductive _
    (compact_fixed_reductive ω a hcomm hc))

end FixedReductivity

section Signature

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
variable (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a)

local notation "E₊" => compactEigenspace ω a 1
local notation "E₋" => compactEigenspace ω a (-1)
local notation "σ" => involutionConjugation ω a hcomm hinv
local notation "P" => compactPart ω a hcomm hinv
local notation "N" => noncompactPart ω a hcomm hinv
local notation "K" => complexFixed a
local notation "κ" => fixedConjugation ω a hcomm
local notation "S" => Conjugation.fixed σ

private def compactPartEquiv : P ≃ₗ[ℝ] (κ).fixed where
  toFun x :=
    ⟨⟨((x : S) : L), (x.property.2.trans (one_smul ℂ _))⟩, Subtype.ext x.property.1⟩
  invFun x := by
    have hx : ((x : K) : L) ∈ E₊ :=
      ⟨congrArg (fun z : K => (z : L)) x.property, (x : K).property.trans (one_smul ℂ _).symm⟩
    exact ⟨⟨((x : K) : L), compact_mem_realForm ω a hcomm hinv hx⟩, hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℂ L] in
private theorem fixed_finrank (τ : Conjugation L) :
    finrank ℝ τ.fixed = finrank ℂ L := by
  obtain ⟨e, _⟩ := fixed_complexification τ
  exact Module.finrank_baseChange.symm.trans e.toLinearEquiv.finrank_eq


theorem cartan_killing (hc : IsCompact ω) :
    (∀ x : P, (x : S) ≠ 0 → killingForm ℝ S x x < 0) ∧
    (∀ y : N, (y : S) ≠ 0 → 0 < killingForm ℝ S y y) ∧
    (∀ (x : P) (y : N), killingForm ℝ S x y = 0) := by
  let B := killingForm ℂ L
  have horth {p n : L} (hp : p ∈ E₊) (hn : n ∈ E₋) : B p n = 0 := by
    have h := LieAlgebra.killingForm_of_equiv_apply a p n
    have hp' : a p = p := hp.2.trans (one_smul ℂ p)
    have hn' : a n = -n := hn.2.trans (neg_one_smul ℂ n)
    rw [hp', hn', map_neg] at h
    exact eq_zero_of_eq_neg h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    let p : ω.fixed := ⟨((x : S) : L), x.property.1⟩
    have hp : p ≠ 0 := fun h => hx (Subtype.ext (congrArg (fun z : ω.fixed => (z : L)) h))
    have h := (killing_fixed σ (x : S) (x : S)).symm.trans (killing_fixed ω p p)
    exact (Complex.ofReal_inj.mp h).trans_lt (hc p hp)
  · intro x hx
    obtain ⟨n, hn, he⟩ : ((x : S) : L) ∈ E₋.map mulI := x.property
    rw [mulI_apply] at he
    let q : ω.fixed := ⟨n, hn.1⟩
    have hq : q ≠ 0 := by
      intro hz
      apply hx
      apply Subtype.ext
      rw [← he, show n = 0 from congrArg (fun z : ω.fixed => (z : L)) hz, smul_zero]
      rfl
    have hm : B (I • n) (I • n) = -B n n := by
      simp [B, map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, I_mul_I]
    have h : ((killingForm ℝ S x x : ℝ) : ℂ) = -(killingForm ℝ ω.fixed q q : ℂ) := calc
      _ = B ((x : S) : L) ((x : S) : L) := (killing_fixed σ (x : S) (x : S)).symm
      _ = -B n n := by rw [← he, hm]
      _ = _ := congrArg Neg.neg (killing_fixed ω q q)
    rw [← ofReal_neg] at h
    exact (Complex.ofReal_inj.mp h).symm ▸ neg_pos.mpr (hc q hq)
  · intro x y
    obtain ⟨n, hn, he⟩ : ((y : S) : L) ∈ E₋.map mulI := y.property
    rw [mulI_apply] at he
    have hz : B ((x : S) : L) ((y : S) : L) = 0 := by
      rw [← he, map_smul, horth (p := ((x : S) : L)) x.property hn, smul_zero]
    exact Complex.ofReal_eq_zero.mp ((killing_fixed σ (x : S) (y : S)).symm.trans hz)

theorem killing_indices (hc : IsCompact ω) :
    sigNeg (killingQuadratic S) = finrank ℂ K ∧
    sigPos (killingQuadratic S) + finrank ℂ K = finrank ℂ L := by
  let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let : FiniteDimensional ℝ S :=
    FiniteDimensional.of_injective (σ).fixed.toSubmodule.subtype Subtype.val_injective
  let Q := killingQuadratic S
  obtain ⟨hp, hn, _⟩ := cartan_killing ω a hcomm hinv hc
  have hp' : ((-Q).restrict P).PosDef := by
    intro x hx
    exact neg_pos.mpr (hp x (fun h => hx (Subtype.ext h)))
  have hn' : (Q.restrict N).PosDef := by
    intro y hy
    exact hn y (fun h => hy (Subtype.ext h))
  have hp₁ := le_sigNeg_of_negDef Q hp'
  have hn₁ := le_sigPos_of_posDef Q hn'
  have hp₂ : sigPos Q + finrank ℝ P ≤ finrank ℝ S :=
    QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q) (V := P) fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · exact (hp ⟨x, hx⟩ h).le
  have hn₂ : sigNeg Q + finrank ℝ N ≤ finrank ℝ S :=
    QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := N) fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · exact neg_nonpos.mpr (hn ⟨x, hx⟩ h).le
  have hdim := Submodule.finrank_add_eq_of_isCompl (cartan_parts_complementary ω a hcomm hinv)
  have hK : finrank ℝ P = finrank ℂ K :=
    (compactPartEquiv ω a hcomm hinv).finrank_eq.trans (fixed_finrank κ)
  rw [hK, fixed_finrank σ] at hdim hp₂
  rw [hK] at hp₁
  rw [fixed_finrank σ] at hn₂
  change sigNeg Q = finrank ℂ K ∧ sigPos Q + finrank ℂ K = finrank ℂ L
  omega

theorem killing_signature (hc : IsCompact ω) :
    killingSignature S = (finrank ℂ L : ℤ) - 2 * (finrank ℂ K : ℤ) := by
  obtain ⟨hn, hp⟩ := killing_indices ω a hcomm hinv hc
  change (sigPos (killingQuadratic S) : ℤ) - (sigNeg (killingQuadratic S) : ℤ) = _
  omega

end Signature

/-- Apply the decomposition and signature to the complex extension of a given
real involution of the compact form. -/
theorem compact_involution_geometry :
    Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature.compact_involution_geometry_type.{u} := by
  intro L _ _ _ ω hc θ hθ
  obtain ⟨a, ⟨he, hcomm, hinv⟩, _⟩ :=
    PolarRealStructures.compact_involution_extension ω θ hθ
  obtain ⟨hform, hd, hs⟩ := real_form_decomposition ω a hcomm hinv
  exact ⟨a, hcomm, hinv, he, hform, hd, hs, complex_fixed_reductive ω a hcomm hc,
    killing_signature ω a hcomm hinv hc⟩

end LieAlgebrasAndRepresentations.CartanDecompositionSignature
