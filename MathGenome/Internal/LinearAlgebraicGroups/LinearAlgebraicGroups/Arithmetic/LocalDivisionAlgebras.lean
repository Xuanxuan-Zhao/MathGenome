import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionCyclicPresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Module.Lattice
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.SimpleRing.Congr
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.CentralizerDimension

noncomputable section

open scoped WithZero TensorProduct
open ValuativeRel
open RM03.CSA

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]

private abbrev valueIso (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :=
  IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K

private theorem baseValue_le_one (a : F) : baseValue F a ≤ 1 ↔ valuation F a ≤ 1 := by
  change valueIso F (valuation F a) ≤ 1 ↔ _
  rw [← map_one (valueIso F)]
  exact (valueIso F).toOrderIso.le_iff_le

private theorem baseValue_lt_one (a : F) : baseValue F a < 1 ↔ valuation F a < 1 := by
  change valueIso F (valuation F a) < 1 ↔ _
  rw [← map_one (valueIso F)]
  exact (valueIso F).toOrderIso.lt_iff_lt

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem reducedNorm_scalar (hB : IsCentralSimple F B) (a : F) :
    reducedNorm hB (algebraMap F B a) = a ^ degree F B := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [reducedNorm_map hB _ e, map_pow]
  let f : B →ₐ[F] Matrix (Fin (degree F B)) (Fin (degree F B)) (AlgebraicClosure F) :=
    (e.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  change Matrix.det (f (algebraMap F B a)) = _
  rw [f.commutes, IsScalarTower.algebraMap_apply F (AlgebraicClosure F),
    Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

private def scaledValueHom (hB : IsCentralSimple F B) : B →*₀ ℤᵐ⁰ where
  toFun := scaledValue hB
  map_zero' := by
    change baseValue F (reducedNorm hB 0) = 0
    simpa [baseValue, (degree_pos hB).ne'] using congrArg (baseValue F) (reducedNorm_scalar hB 0)
  map_one' := by
    change baseValue F (reducedNorm hB 1) = 1
    rw [reducedNorm_one]
    simp [baseValue]
  map_mul' x y := by
    change baseValue F (reducedNorm hB (x * y)) =
      baseValue F (reducedNorm hB x) * baseValue F (reducedNorm hB y)
    rw [reducedNorm_mul]
    simp [baseValue]

private theorem scaledValueHom_scalar (hB : IsCentralSimple F B) (a : F) :
    scaledValueHom hB (algebraMap F B a) = (baseValue F a) ^ degree F B := by
  change baseValue F (reducedNorm hB (algebraMap F B a)) = _
  rw [reducedNorm_scalar]
  simp [baseValue]

/-- Polynomiality of the reduced norm gives continuity in the coordinates of
any finite-dimensional commutative subfield, including inseparable ones. -/
private theorem continuous_reducedNorm_on_subfield (hB : IsCentralSimple F B)
    {L : Type v} [Field L] [Algebra F L] [TopologicalSpace L] (i : L →ₐ[F] B)
    (b : Module.Basis (Fin (Module.finrank F L)) F L) (hb : Continuous b.equivFun) :
    Continuous fun x : L => reducedNorm hB (i x) := by
  have : IsTopologicalRing F := inferInstance
  let p := genericReducedNorm hB fun j => i (b j)
  have he (x : L) : reducedNorm hB (i x) = MvPolynomial.eval (b.equivFun x) p := by
    rw [genericReducedNorm_eval]
    congr 1
    calc
      i x = i (∑ j, b.equivFun x j • b j) := congrArg i (b.sum_repr x).symm
      _ = ∑ j, b.equivFun x j • i (b j) := by
        rw [map_sum i]
        exact Finset.sum_congr rfl fun j _ => map_smul i (b.equivFun x j) (b j)
  simp_rw [he]
  exact (MvPolynomial.continuous_eval (p := p)).comp hb

private abbrev rankOne (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
    [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] :
    (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
  let h := (inferInstance : IsRankLeOne K).nonempty.some
  { hom' := h.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := h.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }

/-- The norm character detects the unit ball of every subfield. Compactness
bounds its values on the powers of an integral element. A central scalar
then distinguishes the elements with value strictly outside the unit ball. -/
private theorem norm_character_le_one (hB : IsCentralSimple F B)
    {L : Type v} [Field L] [Algebra F L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (i : L →ₐ[F] B) (b : Module.Basis (Fin (Module.finrank F L)) F L)
    (hb : Continuous b.equivFun) (x : L) :
    scaledValueHom hB (i x) ≤ 1 ↔ valuation L x ≤ 1 := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup (G := L)
  let : (Valued.v (R := F)).RankOne := rankOne F
  let : (Valued.v (R := L)).RankOne := rankOne L
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  let : NontriviallyNormedField L := Valued.toNontriviallyNormedField L (ValueGroupWithZero L)
  let N : B →* F :=
    { toFun := reducedNorm hB
      map_one' := reducedNorm_one hB
      map_mul' := reducedNorm_mul hB }
  let g := scaledValueHom hB
  change g (i x) ≤ 1 ↔ _
  have hle (y : L) : valuation L y ≤ 1 → g (i y) ≤ 1 := by
    intro hy
    have hcont : Continuous (fun y : L => ‖reducedNorm hB (i y)‖) :=
      (continuous_reducedNorm_on_subfield hB i b hb).norm
    obtain ⟨M, hM⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall L 1).bddAbove_image
      hcont.continuousOn
    apply (baseValue_le_one _).2
    apply Valued.toNormedField.norm_le_one_iff.mp
    by_contra! hh
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hh
    have hyk : valuation L (y ^ k) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one₀ zero_le hy
    have hbound := hM (Set.mem_image_of_mem (fun z : L => ‖reducedNorm hB (i z)‖) hyk)
    change ‖N (i (y ^ k))‖ ≤ M at hbound
    rw [map_pow, map_pow, norm_pow] at hbound
    exact hk.not_ge hbound
  refine ⟨fun hx => ?_, hle x⟩
  by_contra! hval
  obtain ⟨a, ha₀, ha⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have haL : algebraMap F L a ≠ 0 := (map_ne_zero (algebraMap F L)).mpr ha₀
  have hxn : 1 < ‖x‖ := Valued.toNormedField.one_lt_norm_iff.mpr hval
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖algebraMap F L a‖)⁻¹ hxn
  have hz : valuation L ((algebraMap F L a * x ^ k)⁻¹) ≤ 1 := by
    apply Valued.toNormedField.norm_le_one_iff.mp
    rw [norm_inv, norm_mul, norm_pow]
    rw [mul_comm]
    exact inv_le_one_of_one_le₀ ((inv_lt_iff_one_lt_mul₀ (norm_pos_iff.mpr haL)).mp hk).le
  have hsmall : g (algebraMap F B a) < 1 := by
    rw [scaledValueHom_scalar]
    exact pow_lt_one₀ zero_le ((baseValue_lt_one _).2 ha) (degree_pos hB).ne'
  have hh := hle _ hz
  rw [map_inv₀, map_mul, i.commutes, map_pow, map_inv₀, map_mul, map_pow] at hh
  have hprod : g (algebraMap F B a) * g (i x) ^ k < 1 :=
    (mul_le_of_le_one_right' (pow_le_one₀ zero_le hx)).trans_lt hsmall
  have hprod₀ : g (algebraMap F B a) * g (i x) ^ k ≠ 0 := by
    have hx₀ : x ≠ 0 := by
      intro h
      simp [h] at hval
    exact mul_ne_zero
      ((map_ne_zero g).mpr ((map_ne_zero (algebraMap F B)).mpr ha₀))
      (pow_ne_zero _ ((map_ne_zero g).mpr ((map_ne_zero i).mpr hx₀)))
  exact (one_lt_inv₀ (zero_lt_iff.mpr hprod₀) |>.2 hprod).not_ge hh

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_subfield (hB : IsCentralSimple F B) (x : B) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra F L), FiniteDimensional F L ∧
      ∃ (i : L →ₐ[F] B) (y : L), i y = x := by
  let : FiniteDimensional F B := hB.2.2
  let L := Algebra.adjoin F ({x} : Set B)
  let : CommRing L :=
    { (inferInstance : Ring L) with
      mul_comm := fun a b => Subtype.ext <| (Algebra.commute_of_mem_adjoin_singleton_of_commute
        b.2 (Algebra.commute_of_mem_adjoin_self a.2).symm).eq }
  let : Field L := fieldOfFiniteDimensional F L
  exact ⟨L, inferInstance, inferInstance, inferInstance, L.val,
    ⟨x, Algebra.self_mem_adjoin_singleton F x⟩, rfl⟩

private theorem scaledValue_one_add (hB : IsCentralSimple F B) (x : B)
    (hx : scaledValueHom hB x ≤ 1) : scaledValueHom hB (1 + x) ≤ 1 := by
  obtain ⟨L, hf, ha, hfin, i, y, rfl⟩ := exists_subfield hB x
  let := hf
  let := ha
  let := hfin
  obtain ⟨r, T, _, hlocal, _, hb, _⟩ := finiteExtension_localField (K := F) (L := L)
  let := r
  let := T
  let := hlocal
  let b := Module.finBasis F L
  have h := norm_character_le_one hB i b (hb b).1
  simpa only [map_add, map_one] using
    (h (1 + y)).2 ((valuation L).map_add_le (by simp) ((h y).1 hx))

theorem valuation_exists : ValuationExists.{u,v} := by
  intro F _ _ _ _ B _ _ hB
  let g := scaledValueHom hB
  have hadd (a b : B) (h : g b ≤ g a) : g (a + b) ≤ g a := by
    by_cases ha : a = 0
    · simpa [ha] using h
    have hh : g (a⁻¹ * b) ≤ 1 := by
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr ((map_ne_zero g).mpr ha)), mul_one]
      exact h
    have he : a * (1 + a⁻¹ * b) = a + b := by
      rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [← he, map_mul]
    exact mul_le_of_le_one_right' (scaledValue_one_add hB _ hh)
  let w : Valuation B ℤᵐ⁰ :=
    { toMonoidWithZeroHom := g
      map_add_le_max' a b := by
        change g (a + b) ≤ max (g a) (g b)
        rcases le_total (g a) (g b) with h | h
        · rw [max_eq_right h, add_comm]
          exact hadd b a h
        · rw [max_eq_left h]
          exact hadd a b h }
  refine ⟨w, ⟨fun _ => rfl, scaledValueHom_scalar hB⟩, ?_⟩
  exact fun w' hw' => Valuation.ext hw'.1

theorem restriction_to_subfields : RestrictionToSubfields.{u,v} := by
  intro F _ _ _ _ B _ _ hB w hw L _ _ i Γ _ s hs
  let : FiniteDimensional F B := hB.2.2
  let : FiniteDimensional F L := Module.Finite.of_injective i.toLinearMap i.injective
  obtain ⟨r, T, hex, hlocal, _, hb, huniq⟩ := finiteExtension_localField (K := F) (L := L)
  let := r
  let := T
  let := hlocal
  let b := Module.finBasis F L
  have hcomp : (w.comap i.toRingHom).IsEquiv (valuation L) := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    change w (i x) ≤ 1 ↔ _
    rw [hw.1]
    exact norm_character_le_one hB i b (hb b).1 x
  have hsEq : ValuativeRel.ofValuation s = r := by
    let rs := ValuativeRel.ofValuation s
    have hsext : @ValuativeExtension F L _ _ _ rs _ := by
      constructor
      intro x y
      change s (algebraMap F L x) ≤ s (algebraMap F L y) ↔ _
      exact (hs x y).symm.trans ((valuation F).vle_iff_le (x := x) (y := y)).symm
    exact huniq rs hsext
  refine hcomp.trans (fun x y => ?_)
  refine ((valuation L).vle_iff_le (x := x) (y := y)).symm.trans ?_
  change @ValuativeRel.vle L _ r x y ↔ s x ≤ s y
  rw [← hsEq]
  rfl

/-- The reduced norm is continuous in the coordinates of a given basis. -/
private theorem continuous_coordinate_norm (hB : IsCentralSimple F B)
    (b : Module.Basis (Fin (Module.finrank F B)) F B) :
    Continuous fun c : Fin (Module.finrank F B) → F => reducedNorm hB (b.equivFun.symm c) := by
  have : IsTopologicalRing F := inferInstance
  rw [show (fun c => reducedNorm hB (b.equivFun.symm c)) =
      fun c => MvPolynomial.eval c (genericReducedNorm hB b) from ?_]
  · exact MvPolynomial.continuous_eval _
  · funext c
    rw [← reducedNorm_basis_eval hB b (b.equivFun.symm c)]
    exact congrArg (fun x => MvPolynomial.eval x (genericReducedNorm hB b))
      (b.equivFun.apply_symm_apply c)

private theorem coordinate_integers_compact_open (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰)
    (hw : IsDivisionValuation hB w) (b : Module.Basis (Fin (Module.finrank F B)) F B) :
    letI : TopologicalSpace B := TopologicalSpace.induced b.equivFun inferInstance
    IsCompact (w.integer : Set B) ∧ IsOpen (w.integer : Set B) := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne := rankOne F
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  let : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let d := Module.finrank F B
  let V := Fin d → F
  let P : V → F := fun c => reducedNorm hB (b.equivFun.symm c)
  have hP : Continuous P := continuous_coordinate_norm hB b
  let : TopologicalSpace B := TopologicalSpace.induced b.equivFun inferInstance
  let e : B ≃ₜ V := b.equivFun.toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩
  have hmem : (w.integer : Set B) = e ⁻¹' {c | P c ∈ Integers F} := by
    ext x
    change w x ≤ 1 ↔ valuation F (reducedNorm hB (b.equivFun.symm (b.equivFun x))) ≤ 1
    rw [b.equivFun.symm_apply_apply, hw.1]
    exact baseValue_le_one _
  rw [hmem, e.isCompact_preimage, e.isOpen_preimage]
  have hopen : IsOpen {c : V | P c ∈ Integers F} :=
    (localField_properties F).2.2.2.preimage hP
  refine ⟨?_, hopen⟩
  have hclosed : IsClosed {c : V | P c ∈ Integers F} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall F 1).isClosed.preimage hP
  have hd : 0 < d := by
    change 0 < Module.finrank F B
    rw [finrank_eq_degree_sq hB]
    exact Nat.pow_pos (degree_pos hB)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let S : Set V := {c | ‖c‖ = 1}
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : V) 1).of_isClosed_subset
      (isClosed_eq continuous_norm continuous_const) (by
        intro c hc
        simpa [Metric.mem_closedBall, dist_zero_right] using (le_of_eq hc : ‖c‖ ≤ 1))
  have hSne : S.Nonempty := ⟨fun _ => 1, by
    change ‖(fun _ : Fin d => (1 : F))‖ = 1
    rw [Pi.norm_def]
    simp [Finset.sup_const Finset.univ_nonempty]⟩
  obtain ⟨c₀, hc₀, hmin⟩ := hS.exists_isMinOn hSne hP.norm.continuousOn
  have hp_ne (c : V) (hc : c ≠ 0) : P c ≠ 0 :=
    (reducedNorm_ne_zero_iff_isUnit hB _).mpr
      (isUnit_iff_ne_zero.mpr fun h => hc (b.equivFun.symm.injective (h.trans (map_zero _).symm)))
  have hpos : 0 < ‖P c₀‖ := norm_pos_iff.mpr (hp_ne c₀ (by
    intro hc
    change ‖c₀‖ = 1 at hc₀
    simp [hc] at hc₀))
  refine (isCompact_closedBall (0 : V) (max 1 ‖P c₀‖⁻¹)).of_isClosed_subset hclosed ?_
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hsize : ‖c‖ ≤ 1
  · exact hsize.trans (le_max_left _ _)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun j => ‖c j‖₊)
  have hjnorm : ‖c‖ = ‖c j‖ := by rw [Pi.norm_def, hj]; rfl
  have hj₀ : c j ≠ 0 := by
    intro hh
    exact hsize (by simp [hjnorm, hh])
  let y := (c j)⁻¹ • c
  have hy : y ∈ S := by
    change ‖(c j)⁻¹ • c‖ = 1
    rw [norm_smul, norm_inv, hjnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj₀)]
  have hyc : (c j) • y = c := by simp [y, smul_smul, hj₀]
  have hPc : P c = (c j) ^ degree F B * P y := by
    calc
      P c = reducedNorm hB (b.equivFun.symm ((c j) • y)) := by rw [hyc]
      _ = (c j) ^ degree F B * P y := by
        rw [map_smul, Algebra.smul_def, reducedNorm_mul, reducedNorm_scalar]
  have hbound : ‖c j‖ ^ degree F B * ‖P c₀‖ ≤ 1 := by
    calc
      _ ≤ ‖c j‖ ^ degree F B * ‖P y‖ := mul_le_mul_of_nonneg_left (hmin hy) (by positivity)
      _ = ‖P c‖ := by rw [hPc, norm_mul, norm_pow]
      _ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hc
  have hpow : ‖c j‖ ≤ ‖c j‖ ^ degree F B := by
    calc
      ‖c j‖ = ‖c j‖ ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ‖c j‖ ^ degree F B :=
        pow_le_pow_right₀ (hjnorm ▸ (lt_of_not_ge hsize).le) (degree_pos hB)
  have hinv : ‖c j‖ ^ degree F B ≤ ‖P c₀‖⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hpos).mpr hbound
  exact (hjnorm.trans_le <| hpow.trans hinv).trans (le_max_right _ _)

theorem residue_eq_zero_iff (w : Valuation B ℤᵐ⁰) (x : w.integer) :
    residue w x = 0 ↔ w (x : B) < 1 := by
  change (maximalIdeal w).ringCon.mk' x = 0 ↔ _
  rw [← map_zero (maximalIdeal w).ringCon.mk']
  change ((x : ResidueRing w) = ((0 : w.integer) : ResidueRing w)) ↔ _
  rw [(maximalIdeal w).ringCon.eq, TwoSidedIdeal.rel_iff, sub_zero]
  simp [maximalIdeal]

theorem residue_surjective (w : Valuation B ℤᵐ⁰) : Function.Surjective (residue w) :=
  (maximalIdeal w).ringCon.mk'_surjective

set_option maxHeartbeats 1000000 in
private theorem finite_residue (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰)
    (hw : IsDivisionValuation hB w) : Finite (ResidueRing w) := by
  let : FiniteDimensional F B := hB.2.2
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne := rankOne F
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  let b := Module.finBasis F B
  let : TopologicalSpace B := TopologicalSpace.induced b.equivFun inferInstance
  let : CompactSpace w.integer :=
    isCompact_iff_compactSpace.mp (coordinate_integers_compact_open hB w hw b).1
  let : TopologicalSpace (ResidueRing w) := ⊥
  let : DiscreteTopology (ResidueRing w) := ⟨rfl⟩
  have hcoord : Continuous b.equivFun := continuous_induced_dom
  have hP : Continuous fun x : B => reducedNorm hB x := by
    rw [show (fun x : B => reducedNorm hB x) =
        (fun c => reducedNorm hB (b.equivFun.symm c)) ∘ b.equivFun from by
      funext x
      rw [Function.comp_apply, b.equivFun.symm_apply_apply]]
    exact (continuous_coordinate_norm hB b).comp hcoord
  have hpre (z : ResidueRing w) : IsOpen (residue w ⁻¹' {z}) := by
    obtain ⟨y, rfl⟩ := residue_surjective w z
    have htranslate : Continuous (fun x : w.integer => ((x : B) - (y : B))) := by
      apply continuous_induced_rng.mpr
      change Continuous (fun x : w.integer => b.equivFun ((x : B) - (y : B)))
      simp only [map_sub]
      exact (hcoord.comp continuous_subtype_val).sub continuous_const
    have he : residue w ⁻¹' {residue w y} =
        {x : w.integer | ‖reducedNorm hB ((x : B) - (y : B))‖ < 1} := by
      ext x
      change residue w x = residue w y ↔ _
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hw.1]
      rw [show ((↑(x - y) : B)) = (x : B) - (y : B) from rfl]
      exact (baseValue_lt_one _).trans Valued.toNormedField.norm_lt_one_iff.symm
    rw [he]
    exact isOpen_lt ((hP.comp htranslate).norm) continuous_const
  have hcont : Continuous (residue w) := by
    rw [continuous_def]
    intro s _
    rw [show residue w ⁻¹' s = ⋃ (z ∈ s), residue w ⁻¹' {z} from by
      ext x; simp]
    exact isOpen_iUnion fun z => isOpen_iUnion fun _ => hpre z
  have hcompact : IsCompact (Set.univ : Set (ResidueRing w)) := by
    simpa only [Set.image_univ, (residue_surjective w).range_eq] using isCompact_univ.image hcont
  let : CompactSpace (ResidueRing w) := isCompact_univ_iff.mp hcompact
  exact finite_of_compact_of_discrete

private theorem residue_isField (w : Valuation B ℤᵐ⁰) [Finite (ResidueRing w)] :
    IsField (ResidueRing w) := by
  have hone : residue w 1 ≠ 0 := by
    rw [ne_eq, residue_eq_zero_iff]
    change ¬ w 1 < 1
    simp
  let : Nontrivial (ResidueRing w) := ⟨⟨1, 0, by simpa only [map_one] using hone⟩⟩
  let : NoZeroDivisors (ResidueRing w) := ⟨by
    intro a b hab
    obtain ⟨x, rfl⟩ := residue_surjective w a
    obtain ⟨y, rfl⟩ := residue_surjective w b
    rw [← map_mul, residue_eq_zero_iff] at hab
    by_contra! h
    have hx : w (x : B) = 1 := le_antisymm x.2 (le_of_not_gt (mt (residue_eq_zero_iff w x).2 h.1))
    have hy : w (y : B) = 1 := le_antisymm y.2 (le_of_not_gt (mt (residue_eq_zero_iff w y).2 h.2))
    change w ((x : B) * (y : B)) < 1 at hab
    simp [hx, hy] at hab⟩
  let : IsDomain (ResidueRing w) := NoZeroDivisors.to_isDomain _
  exact Finite.isDomain_to_isField _

private def scalar_in_integers (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰)
    (hw : IsDivisionValuation hB w) : Integers F →+* w.integer :=
  ((algebraMap F B).comp (valuation F).valuationSubring.subtype).codRestrict w.integer (by
    intro a
    change w (algebraMap F B (a : F)) ≤ 1
    rw [hw.2]
    exact pow_le_one₀ zero_le ((baseValue_le_one _).2 a.2))

theorem residue_field : ResidueField.{u,v} := by
  intro F _ _ _ _ B _ _ hB w hw
  let : Finite (ResidueRing w) := finite_residue hB w hw
  let hfield := residue_isField w
  let : Field (ResidueRing w) := hfield.toField
  let f := (residue w).comp (scalar_in_integers hB w hw)
  let j : BaseResidue F →+* ResidueRing w :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Integers F)) f (by
      intro a ha
      have ha' := (Valuation.mem_maximalIdeal_iff F (valuation F)).1 ha
      apply (residue_eq_zero_iff w _).2
      change w (algebraMap F B (a : F)) < 1
      rw [hw.2]
      exact pow_lt_one₀ zero_le ((baseValue_lt_one _).2 ha') (degree_pos hB).ne')
  refine ⟨{
    isField := hfield
    finite := inferInstance
    algebra := j.toAlgebra
    map_scalar := ?_ }⟩
  intro a x hx
  change residue w x = f a
  have he : x = scalar_in_integers hB w hw a := Subtype.ext hx
  rw [he]
  rfl

/-- An `Integers F`-submodule structure on the valuation ring. -/
private def integerSubmodule (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰)
    (hw : IsDivisionValuation hB w) :
    letI := Algebra.compHom B (valuation F).valuationSubring.subtype
    Submodule (Integers F) B :=
  letI := Algebra.compHom B (valuation F).valuationSubring.subtype
  { w.integer.toAddSubgroup with
    smul_mem' := fun a x hx => by
      change a • x ∈ w.integer
      rw [w.mem_integer_iff, Algebra.smul_def]
      change w (algebraMap F B (a : F) * x) ≤ 1
      rw [map_mul, hw.2]
      exact mul_le_one' (pow_le_one₀ zero_le ((baseValue_le_one _).2 a.2)) hx }

set_option maxHeartbeats 1000000 in
theorem integer_lattice : IntegerLattice.{u,v} := by
  intro F _ _ _ _ B _ _ hB w hw
  change IsCentralSimple F B at hB
  refine ⟨coordinate_integers_compact_open hB w hw, ?_⟩
  let : FiniteDimensional F B := hB.2.2
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne := rankOne F
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  let : Algebra (Integers F) B := Algebra.compHom B (valuation F).valuationSubring.subtype
  have : IsScalarTower (Integers F) F B := IsScalarTower.of_algebraMap_eq' rfl
  let M := integerSubmodule hB w hw
  let b := Module.finBasis F B
  let : TopologicalSpace B := TopologicalSpace.induced b.equivFun inferInstance
  have hcoord : Continuous b.equivFun := continuous_induced_dom
  obtain ⟨C, hC⟩ := (coordinate_integers_compact_open hB w hw b).1.bddAbove_image
    hcoord.norm.continuousOn
  obtain ⟨t, ht⟩ := NormedField.exists_one_lt_norm F
  have large (C : ℝ) : ∃ a : F, max 1 C < ‖a‖ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max 1 C) ht
    exact ⟨t ^ k, by simpa only [norm_pow] using hk⟩
  obtain ⟨a, ha₁⟩ := large C
  have ha : 0 < ‖a‖ := zero_lt_one.trans ((le_max_left _ _).trans_lt ha₁)
  have ha₀ : a ≠ 0 := norm_pos_iff.mp ha
  have hint (x : M) (j : Fin (Module.finrank F B)) :
      b.equivFun (a⁻¹ • (x : B)) j ∈ Integers F := by
    change valuation F (b.equivFun (a⁻¹ • (x : B)) j) ≤ 1
    apply Valued.toNormedField.norm_le_one_iff.mp
    rw [map_smul]
    change ‖a⁻¹ * b.equivFun (x : B) j‖ ≤ 1
    rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_le_iff₀ ha, one_mul]
    have hcx : ‖b.equivFun (x : B)‖ ≤ C :=
      hC (Set.mem_image_of_mem _ (show (x : B) ∈ w.integer from x.2))
    exact (norm_le_pi_norm (b.equivFun (x : B)) j).trans
      (hcx.trans ((le_max_right _ _).trans ha₁.le))
  let f : M →ₗ[Integers F] (Fin (Module.finrank F B) → Integers F) :=
    { toFun := fun x j => ⟨_, hint x j⟩
      map_add' := by
        intro x y
        funext j
        apply Subtype.ext
        change b.equivFun (a⁻¹ • ((x : B) + (y : B))) j =
          b.equivFun (a⁻¹ • (x : B)) j + b.equivFun (a⁻¹ • (y : B)) j
        simp [smul_add]
      map_smul' := by
        intro c x
        funext j
        apply Subtype.ext
        change b.equivFun (a⁻¹ • ((c : F) • (x : B))) j =
          (c : F) * b.equivFun (a⁻¹ • (x : B)) j
        rw [smul_comm, map_smul]
        rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hxy : b.equivFun (a⁻¹ • (x : B)) = b.equivFun (a⁻¹ • (y : B)) := by
      funext j
      exact congrArg (fun z => (z j : F)) h
    have hxy' := congrArg (a • ·) (b.equivFun.injective hxy)
    simpa [smul_smul, ha₀] using hxy'
  let : Module.Finite (Integers F) M := Module.Finite.of_injective f hf
  let : Submodule.IsLattice F M :=
    { fg := (Module.Finite.iff_fg (N := M)).mp inferInstance
      span_eq_top := by
        apply eq_top_iff.mpr
        intro x _
        obtain ⟨c, hc⟩ := large ‖reducedNorm hB x‖
        have hc₁ : 1 < ‖c‖ := (le_max_left _ _).trans_lt hc
        have hcpos : 0 < ‖c‖ := zero_lt_one.trans hc₁
        have hc₀ : c ≠ 0 := norm_pos_iff.mp hcpos
        have hx : (c⁻¹ • x) ∈ M := by
          change w (c⁻¹ • x) ≤ 1
          rw [hw.1]
          change baseValue F (reducedNorm hB (c⁻¹ • x)) ≤ 1
          rw [baseValue_le_one]
          apply Valued.toNormedField.norm_le_one_iff.mp
          change ‖reducedNorm hB (c⁻¹ • x)‖ ≤ 1
          rw [Algebra.smul_def, reducedNorm_mul, reducedNorm_scalar, norm_mul, norm_pow,
            norm_inv, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (pow_pos hcpos _), one_mul]
          calc
            _ ≤ ‖c‖ := (le_max_right _ _).trans hc.le
            _ = ‖c‖ ^ (1 : ℕ) := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ hc₁.le (degree_pos hB)
        simpa [smul_smul, hc₀] using
          (Submodule.span F (M : Set B)).smul_mem c (Submodule.subset_span hx) }
  let : Module.IsTorsionFree (Integers F) F := Module.isTorsionFree_iff_algebraMap_injective.mpr
    Subtype.val_injective
  let : Module.Free (Integers F) M := Submodule.IsLattice.free F M
  let b₀ := Module.finBasis (Integers F) M
  have hn : Module.finrank (Integers F) M = Module.finrank F B := by
    simpa using (Module.finrank_eq_card_basis (b₀.extendOfIsLattice F)).symm
  let bO := b₀.reindex (finCongr hn)
  let bF := bO.extendOfIsLattice F
  refine ⟨bF, fun x => ⟨?_, ?_⟩⟩
  · intro hx j
    let y : M := ⟨x, hx⟩
    have hsmul (k : Fin (Module.finrank F B)) :
        ((bO.equivFun y k : Integers F) : F) • bF k =
          ((bO.equivFun y k • bO k : M) : B) := by
      change _ • bO.extendOfIsLattice F k = _
      rw [Module.Basis.extendOfIsLattice_apply]
      rfl
    have hsum : bF.equivFun.symm (fun k => ((bO.equivFun y k : Integers F) : F)) = x := by
      rw [Module.Basis.equivFun_symm_apply]
      simp_rw [hsmul, ← Submodule.coe_sum]
      exact congrArg Subtype.val (bO.sum_repr y)
    have hcoords := congrArg bF.equivFun hsum
    rw [bF.equivFun.apply_symm_apply] at hcoords
    have he : bF.equivFun x j = ((bO.equivFun y j : Integers F) : F) := congrFun hcoords.symm j
    rw [he]
    exact (bO.equivFun y j).2
  · intro hx
    let c : Fin (Module.finrank F B) → Integers F := fun j => ⟨_, hx j⟩
    let y : M := ∑ j, c j • bO j
    have he : (y : B) = x := by
      rw [show (y : B) = ∑ j, bF.equivFun x j • bF j from by
        simp only [y, Submodule.coe_sum]
        apply Finset.sum_congr rfl
        intro j _
        change bF.equivFun x j • (bO j : B) = bF.equivFun x j • bO.extendOfIsLattice F j
        rw [Module.Basis.extendOfIsLattice_apply]]
      exact bF.sum_repr x
    rw [← he]
    exact y.2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The dimension bound from the centralizer formula applies even to
inseparable commutative subfields of a central division algebra. -/
theorem subfield_degree_le (hB : IsCentralSimple F B) {L : Type*}
    [Field L] [Algebra F L] (i : L →ₐ[F] B) : Module.finrank F L ≤ degree F B := by
  let : FiniteDimensional F B := hB.2.2
  let e : L ≃ₐ[F] i.range := AlgEquiv.ofInjective i i.injective
  have hsimple : IsSimpleRing i.range := IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  let C := Subalgebra.centralizer F (i.range : Set B)
  have hle : i.range ≤ C := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hx
    exact (Commute.all b a).map i
  have hdim : Module.finrank F i.range ≤ Module.finrank F C := by
    have hsub : i.range.toSubmodule ≤ C.toSubmodule := hle
    exact Submodule.finrank_mono hsub
  have hmul := (centralizer_simple_and_finrank hB i.range hsimple).2
  change Module.finrank F i.range * Module.finrank F C = Module.finrank F B at hmul
  rw [finrank_eq_degree_sq hB] at hmul
  have hsq : Module.finrank F i.range ^ 2 ≤ degree F B ^ 2 := by
    rw [pow_two, ← hmul]
    exact Nat.mul_le_mul_left _ hdim
  rw [e.toLinearEquiv.finrank_eq]
  exact (Nat.pow_le_pow_iff_left (by decide)).1 hsq

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A lift of a generator of the multiplicative group of the residue field
gives a commutative subfield whose integral elements map onto the residue field. -/
theorem exists_subfield_surjecting_onto_residue
    (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰) (r : ResidueData (F := F) w) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra F L), FiniteDimensional F L ∧
      ∃ i : L →ₐ[F] B, ∀ z : ResidueRing w, ∃ (a : L) (x : w.integer),
        i a = (x : B) ∧ residue w x = z := by
  let : Field (ResidueRing w) := r.isField.toField
  let : Finite (ResidueRing w) := r.finite
  obtain ⟨α, hα⟩ := @IsCyclic.exists_generator (ResidueRing w)ˣ _ _
  obtain ⟨x, hx⟩ := residue_surjective w (α : ResidueRing w)
  have hval : w (x : B) = 1 := by
    refine le_antisymm x.2 (le_of_not_gt fun hlt => ?_)
    exact α.ne_zero (hx.symm.trans ((residue_eq_zero_iff w x).2 hlt))
  have hx₀ : (x : B) ≠ 0 := by
    intro he
    simp [he] at hval
  let u : w.integerˣ :=
    { val := x
      inv := ⟨(x : B)⁻¹, by
        change w (x : B)⁻¹ ≤ 1
        rw [w.map_inv, hval, inv_one]⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hx₀)
      inv_val := Subtype.ext (inv_mul_cancel₀ hx₀) }
  obtain ⟨L, hL, hAlg, hd, i, y, hy⟩ := exists_subfield hB (x : B)
  let := hL
  let := hAlg
  let := hd
  have hy₀ : y ≠ 0 := fun he => hx₀ (hy.symm.trans (by simp [he]))
  let v := Units.mk0 y hy₀
  let j := w.integer.subtype
  have he : Units.map i.toMonoidHom v = Units.map j.toMonoidHom u := Units.ext hy
  have hρ : Units.map (residue w).toMonoidHom u = α := Units.ext hx
  refine ⟨L, hL, hAlg, hd, i, fun z => ?_⟩
  by_cases hz : z = 0
  · exact ⟨0, 0, map_zero _, by simp [hz]⟩
  obtain ⟨m, hm⟩ := hα (Units.mk0 z hz)
  have h1 : i (↑(v ^ m) : L) = (↑(↑(u ^ m) : w.integer) : B) := by
    have H := congrArg (fun b : Bˣ => (b : B)) (congrArg (fun b : Bˣ => b ^ m) he)
    rw [← map_zpow, ← map_zpow] at H
    exact H
  have h2 : residue w (↑(u ^ m) : w.integer) = z := by
    have H := congrArg (fun b : (ResidueRing w)ˣ => (b : ResidueRing w))
      ((map_zpow (Units.map (residue w).toMonoidHom) u m).trans
        ((congrArg (fun b : (ResidueRing w)ˣ => b ^ m) hρ).trans hm))
    exact H
  exact ⟨(v ^ m : Lˣ), (u ^ m : w.integerˣ), h1, h2⟩

/-- Lifts of linearly independent residue classes are linearly independent
over the base field. To reduce a hypothetical relation, divide all coefficients
by one having largest multiplicative valuation. -/
theorem linearIndependent_of_independent_residues
    (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰) (hw : IsDivisionValuation hB w)
    (r : ResidueData (F := F) w) {ι : Type*} [Fintype ι] (x : ι → w.integer) :
    letI := r.isField.toField
    letI := r.algebra
    LinearIndependent (BaseResidue F) (fun j => residue w (x j)) →
      LinearIndependent F (fun j => (x j : B)) := by
  classical
  let := r.isField.toField
  let := r.algebra
  intro hind
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  by_contra hj
  have : Nonempty ι := ⟨j⟩
  let vf := valuation F
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup (α := ValueGroupWithZero F) (Finset.univ : Finset ι)
    Finset.univ_nonempty (fun i => vf (g i))
  have hmax (i : ι) : vf (g i) ≤ vf (g k) := by
    rw [← hk]
    exact Finset.le_sup (s := Finset.univ) (f := fun i : ι => vf (g i)) (Finset.mem_univ i)
  have hk₀ : g k ≠ 0 := by
    intro he
    have H := hmax j
    rw [he, map_zero] at H
    exact (not_le_of_gt (zero_lt_iff.mpr ((map_ne_zero vf).2 hj))) H
  let c : ι → Integers F := fun i =>
    ⟨(g k)⁻¹ * g i, by
      change vf ((g k)⁻¹ * g i) ≤ 1
      rw [map_mul, vf.map_inv, inv_mul_le_iff₀ (zero_lt_iff.mpr ((map_ne_zero vf).2 hk₀)), mul_one]
      exact hmax i⟩
  have hc : c k = 1 := Subtype.ext (inv_mul_cancel₀ hk₀)
  let f := scalar_in_integers hB w hw
  have hsum : ∑ i, f (c i) * x i = 0 := by
    apply Subtype.ext
    change w.integer.subtype _ = w.integer.subtype 0
    rw [map_sum, map_zero]
    change ∑ i, (algebraMap F B ((g k)⁻¹ * g i)) * (x i : B) = 0
    simp_rw [← Algebra.smul_def, mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have hred := congrArg (residue w) hsum
  rw [map_sum, map_zero] at hred
  simp_rw [map_mul, r.map_scalar (c _) (f (c _)) rfl, ← Algebra.smul_def] at hred
  have hkzero := (Fintype.linearIndependent_iff.mp hind _ hred) k
  rw [hc, map_one] at hkzero
  exact one_ne_zero hkzero

/-- The degree of the residue field is at most the degree of the division algebra. -/
theorem residue_degree_le (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰)
    (hw : IsDivisionValuation hB w) (r : ResidueData (F := F) w) :
    letI := r.isField.toField
    letI := r.algebra
    Module.finrank (BaseResidue F) (ResidueRing w) ≤ degree F B := by
  classical
  let := r.isField.toField
  let := r.algebra
  let : Finite (ResidueRing w) := r.finite
  let : FiniteDimensional (BaseResidue F) (ResidueRing w) := Module.Finite.of_finite
  let b := Module.finBasis (BaseResidue F) (ResidueRing w)
  obtain ⟨L, hL, hAlg, hd, i, hsurj⟩ := exists_subfield_surjecting_onto_residue hB w r
  let := hL
  let := hAlg
  let := hd
  choose a x hx hres using fun j => hsurj (b j)
  have hlin : LinearIndependent F (fun j => (x j : B)) := by
    apply linearIndependent_of_independent_residues hB w hw r
    simp_rw [hres]
    exact b.linearIndependent
  have hlina : LinearIndependent F a := by
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    apply Fintype.linearIndependent_iff.mp hlin g
    have H := congrArg i.toLinearMap hg
    rw [map_sum, map_zero] at H
    simp_rw [map_smul, AlgHom.toLinearMap_apply, hx] at H
    exact H
  simpa using hlina.fintype_card_le_finrank.trans (subfield_degree_le hB i)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The coefficient definition of reduced trace equals matrix trace in
any splitting of the central simple algebra. -/
theorem reducedTrace_map (hB : IsCentralSimple F B) {L : Type*} [Field L] [Algebra F L]
    (e : BaseChange F L B ≃ₐ[L] Matrix (Fin (degree F B)) (Fin (degree F B)) L) (x : B) :
    algebraMap F L (reducedTrace hB x) = (e (1 ⊗ₜ[F] x)).trace := by
  have : Nonempty (Fin (degree F B)) := ⟨⟨0, degree_pos hB⟩⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← reducedCharpoly_map hB x e]
  unfold reducedTrace LocalDivisionNormTraceReduction.reducedTrace
  rw [map_neg, Polynomial.coeff_map]
  rfl

/-- The reduced norm of an integral element is integral in the base field. -/
theorem norm_integral (hB : IsCentralSimple F B) (w : Valuation B ℤᵐ⁰)
    (hw : IsDivisionValuation hB w) (x : w.integer) :
    reducedNorm hB (x : B) ∈ Integers F := by
  apply (baseValue_le_one _).1
  change scaledValue hB (x : B) ≤ 1
  rw [← hw.1]
  exact x.2

/-- The division value group and residue field have degree `n`, and the
unramified maximal subfield gives an integral cyclic presentation. -/
theorem cyclic_structure : CyclicStructure.{u,v} := by
  intro F _ _ _ _ B _ _ hB w hw r
  let := r.isField.toField
  let := r.algebra
  let : Finite (ResidueRing w) := r.finite
  let reduction : LocalDivisionRamification.IntegralReduction
      (F := F) (degree F B) w (ResidueRing w) :=
    { scalar_value := hw.2
      lattice := (integer_lattice hB w hw).2
      reduction := residue w
      onto := residue_surjective w
      ker := residue_eq_zero_iff w
      scalar_reduction := r.map_scalar }
  obtain ⟨hsurj, hdegree, ⟨s⟩⟩ := LocalDivisionRamification.ramification hB reduction
  let := s.fieldL
  let := s.algebraL
  let := s.galois
  have haction (σ : s.L ≃ₐ[F] s.L) (a b : s.vL.valuationSubring)
      (h : (b : s.L) = σ (a : s.L)) :
      s.residueEquiv (IsLocalRing.residue _ b) =
        s.autEquiv σ (s.residueEquiv (IsLocalRing.residue _ a)) :=
    (s.residue_aut σ a b h).symm
  obtain ⟨hcentralizer, π, τ, t, b, hπ, hconj, hval, hgen, ⟨m, hm, hfrob⟩, ht, hpow, hb, hint⟩ :=
    LocalDivisionCyclicPresentation.cyclicPresentation hB w hw.2 hsurj s.embed s.degree
      s.vL s.onto_vL s.restrict_value (residue w) (residue_surjective w)
      (residue_eq_zero_iff w) r.map_scalar s.residueEquiv s.residue_eq s.autEquiv haction
  exact ⟨hsurj, hdegree, ⟨{
    L := s.L
    fieldL := s.fieldL
    algebraL := s.algebraL
    embed := s.embed
    degree := s.degree
    centralizer_eq := hcentralizer
    galois := s.galois
    vL := s.vL
    surj_vL := s.onto_vL
    base_value := s.base_value
    restrict_val := s.restrict_value
    residueEquiv := s.residueEquiv
    residue_separable := s.residue_separable
    residue_eq := s.residue_eq
    residue_scalar := s.residue_scalar
    residueAutEquiv := s.autEquiv
    residue_aut := haction
    τ := τ
    τ_preserves_value := hval
    gen := hgen
    frobenius := ⟨m, hm, fun a b h => (haction τ a b h).trans (hfrob _)⟩
    uniformizer := π
    value_uniformizer := hπ
    conjugation := hconj
    parameter := t
    value_parameter := ht
    power_uniformizer := hpow
    basis := b
    basis_eq := hb
    integral_coordinates := hint }⟩⟩

/-- In the integral cyclic presentation, reduction of the reduced norm and
trace is the norm and trace of the residue field extension. -/
theorem reduction_of_norm_trace : ReductionOfNormTrace.{u,v} := by
  intro F _ _ _ _ B _ _ hB w hw r
  let := r.isField.toField
  let := r.algebra
  let : Finite (ResidueRing w) := r.finite
  obtain ⟨_, _, ⟨s⟩⟩ := cyclic_structure hB w hw r
  let := s.fieldL
  let := s.algebraL
  let := s.galois
  exact LocalDivisionNormTraceReduction.reductionOfNormTrace hB w hw.2 s.embed s.vL
    s.degree s.surj_vL s.restrict_val s.τ s.gen s.uniformizer s.parameter s.value_uniformizer
    s.value_parameter s.conjugation s.power_uniformizer s.basis s.basis_eq s.integral_coordinates
    (residue w) (residue_eq_zero_iff w) r.map_scalar s.residueEquiv
    (fun a x h => (s.residue_eq a x h).symm) s.residueAutEquiv s.residue_aut

end LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
