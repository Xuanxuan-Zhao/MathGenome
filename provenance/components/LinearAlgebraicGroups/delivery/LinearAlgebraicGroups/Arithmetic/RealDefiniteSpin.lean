import Specs.LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin
import LinearAlgebraicGroups.Albert.SpinFunctor
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Module

namespace LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin

open CliffordAlgebra Module
open RealDefiniteSpinSpec
open LinearAlgebraicGroups.Albert
open scoped TensorProduct Pointwise

set_option linter.unusedSectionVars false

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (q : QuadraticForm ℝ V)

private abbrev lid := Algebra.TensorProduct.lid ℝ (CliffordAlgebra q)
private abbrev lidV := TensorProduct.lid ℝ V

private theorem lid_baseChange {M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (f : M →ₗ[ℝ] N) (x : ℝ ⊗[ℝ] M) :
    TensorProduct.lid ℝ N (f.baseChange ℝ x) = f (TensorProduct.lid ℝ M x) := by
  induction x with
  | tmul s m => simp
  | add x y hx hy => simp [hx, hy]

private theorem lid_mem_baseChange {M : Type*} [AddCommGroup M] [Module ℝ M]
    (P : Submodule ℝ M) (x : ℝ ⊗[ℝ] M) :
    TensorProduct.lid ℝ M x ∈ P ↔ x ∈ P.baseChange ℝ := by
  constructor
  · intro h
    have h' := (TensorProduct.lid ℝ M).symm_apply_apply x
    rw [TensorProduct.lid_symm_apply] at h'
    exact h' ▸ Submodule.tmul_mem_baseChange_of_mem 1 h
  · intro h
    rw [Submodule.baseChange_eq_span] at h
    induction h using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add a b _ _ ha hb => exact map_add (TensorProduct.lid ℝ M) a b ▸ P.add_mem ha hb
    | smul r a _ ha => exact map_smul (TensorProduct.lid ℝ M) r a ▸ P.smul_mem r ha

private theorem lid_vec (x : ℝ ⊗[ℝ] V) :
    lid q (SpinSpecification.vectors q ℝ x) = ι q (lidV x) :=
  lid_baseChange (ι q) x

private theorem lid_range (x : SpinSpecification.ScalarClifford q ℝ) :
    lid q x ∈ LinearMap.range (ι q) ↔
      x ∈ LinearMap.range (SpinSpecification.vectors q ℝ) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨lidV.symm v, (lid q).injective (by simpa only [lid_vec, lidV.apply_symm_apply] using hv)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨lidV v, (lid_vec q v).symm⟩

theorem pointComparison : PointComparison := by
  intro V _ _ q a
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  have he : lid q a ∈ evenOdd q 0 ↔
      (a : SpinSpecification.ScalarClifford q ℝ) ∈ SpinSpecification.evenPart q ℝ :=
    lid_mem_baseChange (evenOdd q 0) a
  have hr : reverse (lid q a) * lid q a = 1 ↔ SpinSpecification.reversion q ℝ a * a = 1 := by
    have hrev : lid q (SpinSpecification.reversion q ℝ a) = reverse (lid q a) :=
      lid_baseChange (reverse (Q := q)) a
    rw [← hrev]
    rw [← map_mul, ← map_one (lid q), (lid q).injective.eq_iff]
  have hm (a : (SpinSpecification.ScalarClifford q ℝ)ˣ) :
      Set.MapsTo (SpinSpecification.conjugate q ℝ a) (LinearMap.range (SpinSpecification.vectors q ℝ))
        (LinearMap.range (SpinSpecification.vectors q ℝ)) ↔
      Set.MapsTo (fun x => lid q a * x * lid q ↑a⁻¹) (LinearMap.range (ι q))
        (LinearMap.range (ι q)) := by
    have h (x : SpinSpecification.ScalarClifford q ℝ) :
        lid q (SpinSpecification.conjugate q ℝ a x) = lid q a * lid q x * lid q ↑a⁻¹ := by
      simp only [SpinSpecification.conjugate, map_mul]
    refine ⟨fun H y hy => ?_, fun H x hx => ?_⟩
    · have h' := (lid_range q _).mpr (H ((lid_range q _).mp
        (show lid q ((lid q).symm y) ∈ LinearMap.range (ι q) by simpa using hy)))
      rw [h, AlgEquiv.apply_symm_apply] at h'
      exact h'
    · exact (lid_range q _).mp (h x ▸ H ((lid_range q x).mpr hx))
  exact and_congr he.symm (and_congr hr.symm (and_congr (hm a) (hm a⁻¹)))

variable [Module.Finite ℝ V]

private abbrev basis := Module.finBasis ℝ V

private abbrev spinSubgroup : Subgroup (CliffordAlgebra q)ˣ :=
  (SpinFunctor.spinSubgroup q ℝ (basis (V := V))).map (Units.map (lid q).toMonoidHom)

private theorem mem_spinSubgroup (a : (CliffordAlgebra q)ˣ) :
    a ∈ spinSubgroup q ↔ a ∈ spinPoints q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (pointComparison q x).mp hx
  · intro ha
    let x := Units.map (lid q).symm.toMonoidHom a
    have hx : Units.map (lid q).toMonoidHom x = a := Units.ext (by simp [x])
    exact ⟨x, (pointComparison q x).mpr (hx.symm ▸ ha), hx⟩

private theorem vector_injective : Function.Injective (ι q) := by
  obtain ⟨p, hp⟩ := CliffordModel.vector_summand q (basis (V := V))
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun hp x)

private theorem exists_action (a : (CliffordAlgebra q)ˣ) (ha : a ∈ spinPoints q) :
    ∃! g, Acts q a g := by
  obtain ⟨x, hx, rfl⟩ := (mem_spinSubgroup q a).mpr ha
  let s : SpinFunctor.Spin q ℝ (basis (V := V)) := ⟨x, hx⟩
  let g := lidV.symm.trans ((SpinFunctor.vectorAction q ℝ (basis (V := V)) s).trans lidV)
  have hg : Acts q (Units.map (lid q).toMonoidHom x) g := by
    intro v
    rw [← map_inv]
    change ι q (lidV ((SpinFunctor.vectorAction q ℝ (basis (V := V)) s) (lidV.symm v))) =
      lid q x * ι q v * lid q ↑x⁻¹
    have hv := congrArg (lid q) (SpinFunctor.vectorAction_characterization q ℝ
      (basis (V := V)) s (lidV.symm v))
    simpa only [lid_vec, SpinSpecification.conjugate, map_mul, lidV.apply_symm_apply] using hv
  refine ⟨g, hg, fun h hh => ?_⟩
  ext v
  exact vector_injective q ((hh v).trans (hg v).symm)

open private scalar_injective contract_coord contract_polar orderedBasis orderedBasis_empty polar_range
  from LinearAlgebraicGroups.Albert.SpinFunctor

private theorem action_preserves (a : (CliffordAlgebra q)ˣ) {g : V ≃ₗ[ℝ] V}
    (hg : Acts q a g) (x : V) : q (g x) = q x := by
  apply scalar_injective q (basis (V := V))
  rw [← ι_sq_scalar, ← ι_sq_scalar, hg]
  calc
    _ = (a : CliffordAlgebra q) * (ι q x * ι q x) * ↑a⁻¹ := by
      simp only [mul_assoc, ← mul_assoc (↑a⁻¹ : CliffordAlgebra q), Units.inv_mul, one_mul]
    _ = _ := by
      rw [ι_sq_scalar, ← Algebra.commutes (q x) (a : CliffordAlgebra q),
        mul_assoc, Units.mul_inv, mul_one]

private theorem polar_ker (hq : IsDefinite q) : LinearMap.ker q.polarBilin = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  by_contra h
  have hxx := LinearMap.congr_fun hx x
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul] at hxx
  change q x + q x = 0 at hxx
  rcases hq with hp | hn
  · linarith [hp x h]
  · linarith [hn x h]

/-- The elements acting trivially by twisted conjugation are exactly the scalars. -/
private theorem twisted_centralizer (hq : IsDefinite q) (c : CliffordAlgebra q)
    (hc : ∀ x, ι q x * c = involute c * ι q x) :
    ∃ t : ℝ, c = algebraMap ℝ _ t := by
  classical
  let b := basis (V := V)
  let B := orderedBasis q b
  have hp : Function.Surjective q.polarBilin := by
    rw [← LinearMap.range_eq_top, polar_range q b, polar_ker q hq, Submodule.dualAnnihilator_bot]
  have hz (s : Finset (Fin (finrank ℝ V))) (hs : s ≠ ∅) : B.coord s c = 0 := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨x, hx⟩ := hp (b.coord i)
    apply contract_coord q b c i _ s hi
    rw [← hx, contract_polar, hc, sub_self]
  refine ⟨B.coord ∅ c, ?_⟩
  conv_lhs => rw [← B.sum_repr c]
  rw [Finset.sum_eq_single ∅]
  · rw [← Basis.coord_apply]
    change (B.coord ∅ c) • orderedBasis q b ∅ = _
    rw [orderedBasis_empty, Algebra.smul_def, mul_one]
  · intro s _ hs
    rw [← Basis.coord_apply, hz s hs, zero_smul]
  · simp

private def Twists (a : (CliffordAlgebra q)ˣ) (g : V ≃ₗ[ℝ] V) : Prop :=
  ∀ x, ι q (g x) = involute (a : CliffordAlgebra q) * ι q x * ↑a⁻¹

private theorem twists_one : Twists q 1 1 := fun x => by simp

private theorem twists_mul {a b : (CliffordAlgebra q)ˣ} {g h : V ≃ₗ[ℝ] V}
    (ha : Twists q a g) (hb : Twists q b h) : Twists q (a * b) (g * h) := by
  intro x
  change ι q (g (h x)) = _
  rw [ha, hb, Units.val_mul, map_mul, mul_inv_rev, Units.val_mul]
  simp only [mul_assoc]

private theorem twists_inv {a : (CliffordAlgebra q)ˣ} {g : V ≃ₗ[ℝ] V}
    (ha : Twists q a g) : Twists q a⁻¹ g⁻¹ := by
  intro x
  have h := ha (g⁻¹ x)
  rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h
  have k := congrArg (fun z : CliffordAlgebra q => involute (↑a⁻¹ : CliffordAlgebra q) * z * a) h
  have hinv : involute (↑a⁻¹ : CliffordAlgebra q) * involute (a : CliffordAlgebra q) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  simp only [mul_assoc, Units.inv_mul, mul_one] at k
  rw [← mul_assoc (involute (↑a⁻¹ : CliffordAlgebra q)) (involute (a : CliffordAlgebra q)),
    hinv, one_mul] at k
  rw [inv_inv]
  simpa only [mul_assoc] using k.symm

private theorem twists_scalar {a : (CliffordAlgebra q)ˣ} (hq : IsDefinite q)
    (ha : Twists q a 1) : ∃ t : ℝ, (a : CliffordAlgebra q) = algebraMap ℝ _ t := by
  apply twisted_centralizer q hq
  intro x
  have h := congrArg (· * (a : CliffordAlgebra q)) (ha x)
  change ι q x * a = _ at h
  simpa only [mul_assoc, Units.inv_mul, mul_one] using h

private theorem same_twist {a b : (CliffordAlgebra q)ˣ} {g : V ≃ₗ[ℝ] V} (hq : IsDefinite q)
    (ha : Twists q a g) (hb : Twists q b g) :
    ∃ t : ℝ, (a : CliffordAlgebra q) = t • (b : CliffordAlgebra q) := by
  have h := twists_mul q ha (twists_inv q hb)
  rw [mul_inv_cancel] at h
  obtain ⟨t, ht⟩ := twists_scalar q hq h
  refine ⟨t, ?_⟩
  have hh := congrArg (· * (b : CliffordAlgebra q)) ht
  simpa only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one, ← Algebra.smul_def] using hh

private theorem action_kernel {a : (CliffordAlgebra q)ˣ} (ha : a ∈ spinPoints q)
    {g : V ≃ₗ[ℝ] V} (hg : Acts q a g) (hq : IsDefinite q) :
    g = 1 ↔ (a : CliffordAlgebra q) = 1 ∨ (a : CliffordAlgebra q) = -1 := by
  constructor
  · rintro rfl
    have h : Twists q a 1 := by
      intro x
      simpa only [involute_eq_of_mem_even ha.1] using hg x
    obtain ⟨t, ht⟩ := twists_scalar q hq h
    have ht₂ := ha.2.1
    change reverse (a : CliffordAlgebra q) * (a : CliffordAlgebra q) = 1 at ht₂
    rw [ht, reverse.commutes, ← map_mul, ← map_one (algebraMap ℝ (CliffordAlgebra q))] at ht₂
    have hh := scalar_injective q (basis (V := V)) ht₂
    have : t = 1 ∨ t = -1 := by
      have hh' : (t - 1) * (t + 1) = 0 := by nlinarith
      simpa [sub_eq_zero, add_eq_zero_iff_eq_neg] using mul_eq_zero.mp hh'
    rcases this with rfl | rfl
    · left; simpa using ht
    · right; simpa using ht
  · intro h
    ext x
    apply vector_injective q
    change ι q (g x) = ι q x
    have H := congrArg (· * (a : CliffordAlgebra q)) (hg x)
    have H' : ι q (g x) * (a : CliffordAlgebra q) = (a : CliffordAlgebra q) * ι q x := by
      simpa only [mul_assoc, Units.inv_mul, mul_one] using H
    rcases h with h | h <;> simpa [h] using H'

private theorem exists_sign (hq : IsDefinite q) :
    ∃ s : ℝ, s * s = 1 ∧ ∀ x ≠ 0, 0 < s * q x := by
  rcases hq with hn | hn
  · exact ⟨1, by norm_num, by simpa using hn⟩
  · exact ⟨-1, by norm_num, by simpa using hn⟩

@[instance_reducible] private def innerCore (s : ℝ) (hs : ∀ x ≠ 0, 0 < s * q x) : InnerProductSpace.Core ℝ V where
  inner x y := (s / 2) * q.polarBilin x y
  conj_inner_symm x y := by
    simp only [RCLike.conj_to_real, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  re_inner_nonneg x := by
    change 0 ≤ (s / 2) * q.polarBilin x x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
    by_cases hx : x = 0
    · simp [hx]
    · nlinarith [hs x hx]
  definite x hx := by
    by_contra hn
    change (s / 2) * q.polarBilin x x = 0 at hx
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul] at hx
    nlinarith [hs x hn]
  add_left x y z := by rw [map_add, LinearMap.add_apply, mul_add]
  smul_left x y r := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]
    ring

private def vectorUnit (s : ℝ) (hs : s * s = 1) (u : V) (hu : q u = s) :
    (CliffordAlgebra q)ˣ where
  val := ι q u
  inv := s • ι q u
  val_inv := by
    rw [mul_smul_comm, ι_sq_scalar, hu, Algebra.smul_def, ← map_mul, hs, map_one]
  inv_val := by
    rw [smul_mul_assoc, ι_sq_scalar, hu, Algebra.smul_def, ← map_mul, hs, map_one]

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module.Finite ℝ E]
variable (q : QuadraticForm ℝ E)
variable (s : ℝ) (hs : s * s = 1)
variable (hinner : ∀ x y : E, inner ℝ x y = (s / 2) * q.polarBilin x y)

include hinner in
private theorem norm_sq (x : E) : ‖x‖ ^ 2 = s * q x := by
  rw [← real_inner_self_eq_norm_sq, hinner, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, two_nsmul]
  ring

include hs hinner in
private theorem norm_eq_one_iff (x : E) : ‖x‖ = 1 ↔ q x = s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  constructor
  · intro h
    have k := norm_sq q s hinner x
    rw [h, one_pow, ← hs] at k
    exact (mul_left_cancel₀ hs0 k).symm
  · intro h
    have k := norm_sq q s hinner x
    rw [h, hs] at k
    nlinarith [norm_nonneg x]

private abbrev reflection (u : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ u)ᗮ.reflection

private theorem det_reflection (u : E) (hu : u ≠ 0) :
    LinearMap.det (reflection u).toLinearEquiv.toLinearMap = -1 := by
  change LinearMap.det ((ℝ ∙ u)ᗮ.reflection.toLinearMap) = -1
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hu, pow_one]

include hs hinner in
private theorem reflection_formula (u : E) (hu : q u = s) (x : E) :
    reflection u x = x - (s * q.polarBilin u x) • u := by
  have hn := (norm_eq_one_iff q s hs hinner u).mpr hu
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hn, hinner]
  simp only [RCLike.ofReal_one, one_pow, div_one, neg_sub, two_smul ℕ, ← add_smul]
  congr 2
  ring

include hinner in
private theorem twists_reflection (u : E) (hu : q u = s) :
    Twists q (vectorUnit q s hs u hu) (reflection u).toLinearEquiv := by
  intro x
  change ι q (reflection u x) = involute (ι q u) * ι q x * (s • ι q u)
  rw [involute_ι, mul_smul_comm, neg_mul, neg_mul, ι_mul_ι_mul_ι, ← map_neg, ← map_smul,
    reflection_formula q s hs hinner u hu, QuadraticMap.polarBilin_apply_apply]
  simp only [neg_sub, smul_sub, smul_smul, hu, hs, one_smul]

include hs hinner in
private theorem reflection_word (g : E ≃ₗ[ℝ] E) (hg : ∀ x, q (g x) = q x) :
    ∃ l : List E, (∀ u ∈ l, q u = s) ∧
      g = ((l.map reflection).prod : E ≃ₗᵢ[ℝ] E).toLinearEquiv := by
  let G : E ≃ₗᵢ[ℝ] E :=
    { g with
      norm_map' := fun x => by
        have h := norm_sq q s hinner (g x)
        rw [hg, ← norm_sq q s hinner x] at h
        nlinarith [norm_nonneg (g x), norm_nonneg x] }
  obtain ⟨l, _, hl⟩ := G.reflections_generate_dim
  have normalize (l : List E) :
      ∃ L : List E, (∀ u ∈ L, q u = s) ∧ (L.map reflection).prod = (l.map reflection).prod := by
    induction l with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons u l ih =>
      obtain ⟨L, hL, hprod⟩ := ih
      by_cases hu : u = 0
      · refine ⟨L, hL, ?_⟩
        have hz : reflection (0 : E) = 1 := by
          ext x
          change reflection (0 : E) x = x
          rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
          simp
        simpa [hu, hz] using hprod
      · let v := ‖u‖⁻¹ • u
        have hn : ‖v‖ = 1 := by
          simp [v, norm_smul, norm_ne_zero_iff.mpr hu]
        have hspan : ℝ ∙ v = ℝ ∙ u :=
          Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (norm_ne_zero_iff.mpr hu))) u
        refine ⟨v :: L, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact (norm_eq_one_iff q s hs hinner v).mp hn
          · exact hL w hw
        · simp only [List.map_cons, List.prod_cons, hprod]
          have H : reflection v = reflection u :=
            congrArg (fun K : Submodule ℝ E => Kᗮ.reflection) hspan
          rw [H]
  obtain ⟨L, hL, hprod⟩ := normalize l
  exact ⟨L, hL, congrArg LinearIsometryEquiv.toLinearEquiv (hl.trans hprod.symm)⟩

private def wordUnits (l : List E) (hl : ∀ u ∈ l, q u = s) : (CliffordAlgebra q)ˣ :=
  (l.attach.map fun u => vectorUnit q s hs u.val (hl u.val u.property)).prod

private theorem wordUnits_cons (u : E) (l : List E) (hl : ∀ v ∈ u :: l, q v = s) :
    wordUnits q s hs (u :: l) hl =
      vectorUnit q s hs u (hl _ (by simp)) *
        wordUnits q s hs l (fun v hv => hl v (List.mem_cons_of_mem _ hv)) := by
  simp [wordUnits, List.attach_cons, List.map_map, Function.comp_def]

include hinner in
private theorem word_twists (l : List E) (hl : ∀ u ∈ l, q u = s) :
    Twists q (wordUnits q s hs l hl) ((l.map reflection).prod : E ≃ₗᵢ[ℝ] E).toLinearEquiv := by
  induction l with
  | nil => exact twists_one q
  | cons u l ih =>
    rw [wordUnits_cons]
    exact twists_mul q (twists_reflection q s hs hinner u (hl _ (by simp))) (ih _)

include hs in
private theorem word_det (l : List E) (hl : ∀ u ∈ l, q u = s) :
    LinearMap.det ((l.map reflection).prod : E ≃ₗᵢ[ℝ] E).toLinearEquiv.toLinearMap =
      (-1) ^ l.length := by
  induction l with
  | nil =>
    change LinearMap.det (1 : Module.End ℝ E) = (-1) ^ (0 : ℕ)
    rw [map_one, pow_zero]
  | cons u l ih =>
    have hu : u ≠ 0 := by
      rintro rfl
      have h := hl 0 (by simp)
      simp at h
      simp [← h] at hs
    change LinearMap.det ((reflection u).toLinearEquiv.toLinearMap *
      ((l.map reflection).prod : E ≃ₗᵢ[ℝ] E).toLinearEquiv.toLinearMap) = _
    rw [map_mul, det_reflection u hu, ih (fun v hv => hl v (List.mem_cons_of_mem _ hv)),
      List.length_cons, pow_succ']
    
private theorem word_involute (l : List E) (hl : ∀ u ∈ l, q u = s) :
    involute (wordUnits q s hs l hl : CliffordAlgebra q) =
      ((-1 : ℝ) ^ l.length) • (wordUnits q s hs l hl : CliffordAlgebra q) := by
  induction l with
  | nil => simp [wordUnits]
  | cons u l ih =>
    rw [wordUnits_cons, Units.val_mul, map_mul]
    change involute (ι q u) * _ = _
    rw [involute_ι, ih, mul_smul_comm, neg_mul, smul_neg, ← neg_smul,
      List.length_cons, pow_succ', neg_one_mul]
    rfl

private theorem spin_of_twist {a : (CliffordAlgebra q)ˣ} {g : E ≃ₗ[ℝ] E}
    (he : (a : CliffordAlgebra q) ∈ evenOdd q 0)
    (hn : reverse (a : CliffordAlgebra q) * a = 1) (hg : Twists q a g) :
    a ∈ spinPoints q := by
  refine ⟨he, hn, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, by simpa only [involute_eq_of_mem_even he] using hg x⟩
  · rintro _ ⟨x, rfl⟩
    have hh := twists_inv q hg (x := x)
    have hei : (↑a⁻¹ : CliffordAlgebra q) ∈ evenOdd q 0 := by
      have h := congrArg (· * (↑a⁻¹ : CliffordAlgebra q)) hn
      have h' : reverse (a : CliffordAlgebra q) = ↑a⁻¹ := by
        simpa only [mul_assoc, Units.mul_inv, mul_one, one_mul] using h
      rw [← h', reverse_mem_evenOdd_iff]
      exact he
    exact ⟨g⁻¹ x, by simpa only [involute_eq_of_mem_even hei, inv_inv] using hh⟩

include hinner in
private theorem pair_mem (u v : E) (hu : q u = s) (hv : q v = s) :
    vectorUnit q s hs u hu * vectorUnit q s hs v hv ∈ spinPoints q := by
  apply spin_of_twist q (ι_mul_ι_mem_evenOdd_zero q u v)
  · change reverse (ι q u * ι q v) * (ι q u * ι q v) = 1
    rw [reverse.map_mul, reverse_ι, reverse_ι, mul_assoc, ← mul_assoc (ι q u),
      ι_sq_scalar, hu, ← Algebra.smul_def, mul_smul_comm, ι_sq_scalar, hv,
      Algebra.smul_def, ← map_mul, hs, map_one]
  · exact twists_mul q (twists_reflection q s hs hinner u hu)
      (twists_reflection q s hs hinner v hv)

include hinner in
private theorem even_word_mem (l : List E) (hl : ∀ u ∈ l, q u = s) (he : Even l.length) :
    wordUnits q s hs l hl ∈ spinPoints q := by
  induction l using List.twoStepInduction with
  | nil => exact (mem_spinSubgroup q _).mp (one_mem _)
  | singleton u => simp at he
  | cons_cons u v l ih _ =>
    have he' : Even l.length := by
      rw [List.length_cons, List.length_cons] at he
      simpa [Nat.even_add, Nat.add_assoc] using he
    rw [wordUnits_cons, wordUnits_cons, ← mul_assoc]
    apply (mem_spinSubgroup q _).mp
    exact mul_mem ((mem_spinSubgroup q _).mpr (pair_mem q s hs hinner u v
      (hl _ (by simp)) (hl _ (by simp)))) ((mem_spinSubgroup q _).mpr (ih _ he'))

include hs hinner in
private theorem det_of_spin {a : (CliffordAlgebra q)ˣ} (ha : a ∈ spinPoints q)
    {g : E ≃ₗ[ℝ] E} (hg : Acts q a g) (hq : IsDefinite q) :
    LinearMap.det g.toLinearMap = 1 := by
  obtain ⟨l, hl, hg'⟩ := reflection_word q s hs hinner g (action_preserves q a hg)
  let b := wordUnits q s hs l hl
  have hb : Twists q b g := hg'.symm ▸ word_twists q s hs hinner l hl
  have hat : Twists q a g := by
    intro x
    simpa only [involute_eq_of_mem_even ha.1] using hg x
  obtain ⟨t, ht⟩ := same_twist q hq hat hb
  have h := involute_eq_of_mem_even ha.1
  rw [ht, map_smul, show involute (b : CliffordAlgebra q) = ((-1 : ℝ) ^ l.length) •
    (b : CliffordAlgebra q) from word_involute q s hs l hl, smul_smul] at h
  have h' : t * (-1 : ℝ) ^ l.length = t := by
    apply scalar_injective q (basis (V := E))
    have h'' := congrArg (· * (↑b⁻¹ : CliffordAlgebra q)) h
    simpa only [smul_mul_assoc, mul_assoc, Units.mul_inv, Algebra.smul_def, mul_one] using h''
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  rw [hg', word_det q s hs l hl]
  exact mul_left_cancel₀ ht0 (h'.trans (mul_one t).symm)

include hs hinner in
private theorem lift_special (g : E ≃ₗ[ℝ] E) (hg : ∀ x, q (g x) = q x)
    (hd : LinearMap.det g.toLinearMap = 1) :
    ∃ a ∈ spinPoints q, Acts q a g := by
  obtain ⟨l, hl, rfl⟩ := reflection_word q s hs hinner g hg
  rw [word_det q s hs l hl] at hd
  have he := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hd
  let b := wordUnits q s hs l hl
  have hb : b ∈ spinPoints q := even_word_mem q s hs hinner l hl he
  refine ⟨b, hb, fun x => ?_⟩
  have h : Twists q b _ := word_twists q s hs hinner l hl
  simpa only [involute_eq_of_mem_even hb.1] using h x

section Topology

local instance : TopologicalSpace (CliffordAlgebra q) := moduleTopology ℝ (CliffordAlgebra q)

local instance : Module.Finite ℝ (CliffordAlgebra q) :=
  Module.Finite.of_basis (orderedBasis q (basis (V := E)))

local instance : IsTopologicalRing (CliffordAlgebra q) :=
  IsModuleTopology.isTopologicalRing ℝ (CliffordAlgebra q)

private theorem one_mem_cliffordPoints : (1 : CliffordAlgebra q) ∈ cliffordPoints q :=
  ⟨1, (mem_spinSubgroup q 1).mp (one_mem _), rfl⟩

private theorem cliffordPoints_mul : cliffordPoints q * cliffordPoints q ⊆ cliffordPoints q := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  exact ⟨a * b, (mem_spinSubgroup q _).mp
    (mul_mem ((mem_spinSubgroup q _).mpr ha) ((mem_spinSubgroup q _).mpr hb)), rfl⟩

include hs hinner in
private theorem pair_joined (hd : 2 ≤ finrank ℝ E) (u v : E) (hu : q u = s) (hv : q v = s) :
    JoinedIn (cliffordPoints q) 1 (ι q u * ι q v) := by
  have hr : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < finrank ℝ E by omega)
  let F := Metric.sphere (0 : E) 1
  have hF : IsPathConnected F := isPathConnected_sphere hr 0 zero_le_one
  have hn : ‖s • u‖ = 1 := (norm_eq_one_iff q s hs hinner _).mpr (by
    rw [q.map_smul, hs, one_smul, hu])
  have hv' : v ∈ F := by
    change v ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right]
    exact (norm_eq_one_iff q s hs hinner v).mpr hv
  have hu' : s • u ∈ F := by
    change s • u ∈ Metric.sphere 0 1
    rwa [Metric.mem_sphere, dist_zero_right]
  let f (x : E) := ι q u * ι q x
  have hc : Continuous f := continuous_const.mul (ι q).continuous_of_finiteDimensional
  have hstart : f (s • u) = 1 := by
    change ι q u * ι q (s • u) = 1
    rw [map_smul]
    exact (vectorUnit q s hs u hu).val_inv
  have h := (hF.joinedIn _ hu' _ hv').map hc.continuousOn
  rw [hstart] at h
  apply h.mono
  rintro _ ⟨x, hx, rfl⟩
  have hnx : ‖x‖ = 1 := by simpa [F, Metric.mem_sphere, dist_zero_right] using hx
  have hqx := (norm_eq_one_iff q s hs hinner x).mp hnx
  exact ⟨vectorUnit q s hs u hu * vectorUnit q s hs x hqx,
    pair_mem q s hs hinner u x hu hqx, rfl⟩

include hs hinner in
private theorem neg_one_joined (hd : 2 ≤ finrank ℝ E) :
    JoinedIn (cliffordPoints q) 1 (-1 : CliffordAlgebra q) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  let u := ‖x‖⁻¹ • x
  have hn : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hx]
  have hu := (norm_eq_one_iff q s hs hinner u).mp hn
  have hv : q (-(s • u)) = s := by rw [q.map_neg, q.map_smul, hs, one_smul, hu]
  have h := pair_joined q s hs hinner hd u (-(s • u)) hu hv
  have h' : ι q u * ι q (-(s • u)) = -1 := by
    rw [map_neg, mul_neg, map_smul (ι q) s u]
    exact congrArg Neg.neg (vectorUnit q s hs u hu).val_inv
  rwa [h'] at h

include hinner in
private theorem even_word_joined (hd : 2 ≤ finrank ℝ E)
    (l : List E) (hl : ∀ u ∈ l, q u = s) (he : Even l.length) :
    JoinedIn (cliffordPoints q) 1 (wordUnits q s hs l hl : CliffordAlgebra q) := by
  induction l using List.twoStepInduction with
  | nil => exact JoinedIn.refl (one_mem_cliffordPoints q)
  | singleton u => simp at he
  | cons_cons u v l ih _ =>
    have he' : Even l.length := by
      rw [List.length_cons, List.length_cons] at he
      simpa [Nat.even_add, Nat.add_assoc] using he
    have H := (pair_joined q s hs hinner hd u v (hl _ (by simp)) (hl _ (by simp))).mul
      (ih (fun w hw => hl w (by simp [hw])) he')
    rw [one_mul] at H
    rw [wordUnits_cons, wordUnits_cons, ← mul_assoc]
    exact H.mono (cliffordPoints_mul q)

include hs hinner in
private theorem spin_joined (hd : 2 ≤ finrank ℝ E) (hq : IsDefinite q)
    (a : (CliffordAlgebra q)ˣ) (ha : a ∈ spinPoints q) :
    JoinedIn (cliffordPoints q) 1 (a : CliffordAlgebra q) := by
  obtain ⟨g, hg, _⟩ := exists_action q a ha
  obtain ⟨l, hl, hg'⟩ := reflection_word q s hs hinner g (action_preserves q a hg)
  have hdet := det_of_spin q s hs hinner ha hg hq
  rw [hg', word_det q s hs l hl] at hdet
  have he := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hdet
  let b := wordUnits q s hs l hl
  have hb : b ∈ spinPoints q := even_word_mem q s hs hinner l hl he
  have hat : Twists q a g := fun x => by simpa only [involute_eq_of_mem_even ha.1] using hg x
  have hbt : Twists q b g := hg'.symm ▸ word_twists q s hs hinner l hl
  have hc : a * b⁻¹ ∈ spinPoints q := (mem_spinSubgroup q _).mp
    (mul_mem ((mem_spinSubgroup q _).mpr ha) (inv_mem ((mem_spinSubgroup q _).mpr hb)))
  have hct := twists_mul q hat (twists_inv q hbt)
  rw [mul_inv_cancel] at hct
  have hca : Acts q (a * b⁻¹) 1 := fun v => by
    simpa only [involute_eq_of_mem_even hc.1] using hct v
  have hval := (action_kernel q hc hca hq).mp rfl
  have hjoin : JoinedIn (cliffordPoints q) 1 ((a * b⁻¹ : (CliffordAlgebra q)ˣ) : CliffordAlgebra q) := by
    rcases hval with h | h
    · rw [h]
      exact JoinedIn.refl (one_mem_cliffordPoints q)
    · rw [h]
      exact neg_one_joined q s hs hinner hd
  have H := (hjoin.mul (even_word_joined q s hs hinner hd l hl he)).mono (cliffordPoints_mul q)
  simpa only [one_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one, b] using H

include hs hinner in
private theorem plane_lift (e f : E) (he : q e = s) (hf : q f = s)
    (hef : q.polarBilin e f = 0) :
    let B := ι q e * ι q f
    B * B = -1 ∧
    ∃ p : ℝ → (CliffordAlgebra q)ˣ,
      Continuous (fun θ => (p θ : CliffordAlgebra q)) ∧
      (p 0 : CliffordAlgebra q) = 1 ∧ (p (2 * Real.pi) : CliffordAlgebra q) = -1 ∧
      ∀ θ,
        p θ ∈ spinPoints q ∧
        (p θ : CliffordAlgebra q) = Real.cos (θ / 2) • (1 : CliffordAlgebra q) +
          Real.sin (θ / 2) • B ∧
        ∃ g : E ≃ₗ[ℝ] E, Acts q (p θ) g ∧
          g e = Real.cos θ • e - (s * Real.sin θ) • f ∧
          g f = (s * Real.sin θ) • e + Real.cos θ • f ∧
          ∀ x, q.polarBilin e x = 0 → q.polarBilin f x = 0 → g x = x := by
  dsimp only
  have hfe : q.polarBilin f e = 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm q f e] using hef
  have hanti : ι q f * ι q e = -(ι q e * ι q f) := by
    rw [ι_mul_ι_comm, ← QuadraticMap.polarBilin_apply_apply, hfe, map_zero, zero_sub]
  constructor
  · rw [← mul_assoc, mul_assoc (ι q e), hanti, mul_neg, neg_mul, ← mul_assoc (ι q e),
      ι_sq_scalar, mul_assoc, ι_sq_scalar, he, hf, ← map_mul, hs, map_one]
  let v (θ : ℝ) : E := (s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f
  have hv (θ : ℝ) : q (v θ) = s := by
    let c := Real.cos (θ / 2)
    let d := Real.sin (θ / 2)
    change q ((s * c) • e + d • f) = s
    have h : q.polarBilin ((s * c) • e) (d • f) = 0 := by
      simp [map_smul, LinearMap.smul_apply, hef]
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, sub_sub] at h
    rw [sub_eq_zero] at h
    rw [h, q.map_smul, q.map_smul, he, hf]
    change (s * c * (s * c)) * s + (d * d) * s = s
    rw [show s * c * (s * c) = c ^ 2 by linear_combination c ^ 2 * hs]
    calc
      c ^ 2 * s + d * d * s = (c ^ 2 + d ^ 2) * s := by ring
      _ = s := by rw [Real.cos_sq_add_sin_sq, one_mul]
  let p (θ : ℝ) := vectorUnit q s hs e he * vectorUnit q s hs (v θ) (hv θ)
  have hformula (θ : ℝ) : (p θ : CliffordAlgebra q) =
      Real.cos (θ / 2) • (1 : CliffordAlgebra q) + Real.sin (θ / 2) • (ι q e * ι q f) := by
    change ι q e * ι q (v θ) = _
    rw [show v θ = (s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f from rfl,
      map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm, ι_sq_scalar, he,
      Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 2
    linear_combination Real.cos (θ / 2) * hs
  refine ⟨p, ?_, ?_, ?_, fun θ => ?_⟩
  · simp only [hformula]
    fun_prop
  · simp [hformula]
  · rw [hformula, show 2 * Real.pi / 2 = Real.pi by ring, Real.cos_pi, Real.sin_pi]
    simp
  · have hmem : p θ ∈ spinPoints q := pair_mem q s hs hinner e (v θ) he (hv θ)
    let g := (reflection e).toLinearEquiv * (reflection (v θ)).toLinearEquiv
    have htw : Twists q (p θ) g :=
      twists_mul q (twists_reflection q s hs hinner e he)
        (twists_reflection q s hs hinner (v θ) (hv θ))
    have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul, show 2 * (θ / 2) = θ by ring]
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      rw [← Real.sin_two_mul, show 2 * (θ / 2) = θ by ring]
    have hre : reflection e e = -e := Submodule.reflection_orthogonalComplement_singleton_eq_neg e
    have hrf : reflection e f = f := by
      rw [reflection_formula q s hs hinner e he, hef, mul_zero, zero_smul, sub_zero]
    refine ⟨hmem, hformula θ, g, fun x => ?_, ?_, ?_, ?_⟩
    · simpa only [involute_eq_of_mem_even hmem.1] using htw x
    · have hee : q.polarBilin e e = 2 * s := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, he, two_nsmul, two_mul]
      have hve : q.polarBilin (v θ) e = 2 * Real.cos (θ / 2) := by
        change q.polarBilin ((s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f) e = _
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hee, hfe, smul_eq_mul]
        linear_combination (2 * Real.cos (θ / 2)) * hs
      change reflection e (reflection (v θ) e) = _
      rw [reflection_formula q s hs hinner (v θ) (hv θ), hve, map_sub, map_smul, hre,
        show v θ = (s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f from rfl,
        map_add, map_smul, map_smul, hre, hrf, hcos, hsin]
      match_scalars <;> first | ring1 | linear_combination (2 * Real.cos (θ / 2) ^ 2) * hs
    · have hff : q.polarBilin f f = 2 * s := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hf, two_nsmul, two_mul]
      have hvf : q.polarBilin (v θ) f = 2 * s * Real.sin (θ / 2) := by
        change q.polarBilin ((s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f) f = _
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hff, hef, smul_eq_mul]
        ring
      change reflection e (reflection (v θ) f) = _
      rw [reflection_formula q s hs hinner (v θ) (hv θ), hvf, map_sub, map_smul, hrf,
        show v θ = (s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f from rfl,
        map_add, map_smul, map_smul, hre, hrf, hcos, hsin,
        show s * (2 * s * Real.sin (θ / 2)) = 2 * Real.sin (θ / 2) by
          linear_combination (2 * Real.sin (θ / 2)) * hs]
      match_scalars <;> first | ring1 | linear_combination -2 * Real.cos_sq_add_sin_sq (θ / 2)
    · intro x hex hfx
      have hvx : q.polarBilin (v θ) x = 0 := by
        change q.polarBilin ((s * Real.cos (θ / 2)) • e + Real.sin (θ / 2) • f) x = _
        simp [map_smul, LinearMap.smul_apply, hex, hfx]
      change reflection e (reflection (v θ) x) = x
      rw [reflection_formula q s hs hinner (v θ) (hv θ), hvx, mul_zero, zero_smul, sub_zero,
        reflection_formula q s hs hinner e he, hex, mul_zero, zero_smul, sub_zero]

end Topology

end InnerProduct

theorem vectorAction : VectorAction := by
  intro V _ _ _ q hq
  obtain ⟨s, hs, hp⟩ := exists_sign q hq
  let c := innerCore q s hp
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  have hinner (x y : V) : inner ℝ x y = (s / 2) * q.polarBilin x y := rfl
  exact ⟨fun a ha => ⟨exists_action q a ha, fun g hg =>
    ⟨action_preserves q a hg, det_of_spin q s hs hinner ha hg hq, action_kernel q ha hg hq⟩⟩,
    lift_special q s hs hinner⟩

theorem pathConnected : PathConnected := by
  intro V _ _ _ q hq hd
  obtain ⟨s, hs, hp⟩ := exists_sign q hq
  let c := innerCore q s hp
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  have hinner (x y : V) : inner ℝ x y = (s / 2) * q.polarBilin x y := rfl
  refine ⟨1, one_mem_cliffordPoints q, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact spin_joined q s hs hinner hd hq a ha

theorem planeLift : PlaneLift := by
  intro V _ _ _ q hq s e f hs he hf hef
  obtain ⟨t, ht, hp⟩ := exists_sign q hq
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have he0 : e ≠ 0 := by rintro rfl; exact hs0 (by simpa using he.symm)
  have hpos := hp e he0
  rw [he] at hpos
  have hts : t * s = 1 := by
    have h : (t * s - 1) * (t * s + 1) = 0 := by linear_combination s ^ 2 * ht + hs
    rcases mul_eq_zero.mp h with h | h <;> linarith
  have h : t = s := mul_right_cancel₀ hs0 (hts.trans hs.symm)
  subst t
  let c := innerCore q s hp
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  have hinner (x y : V) : inner ℝ x y = (s / 2) * q.polarBilin x y := rfl
  exact plane_lift q s hs hinner e f he hf hef

end
end LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin
