import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.LinearAlgebra.Quotient.Bilinear

open scoped TensorProduct
open CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
open IsLocalRing

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit

noncomputable section

open scoped ExteriorTensorInverseLimit

set_option maxHeartbeats 1000000

variable {k : Type*} [Field k] {a b : ℕ}

private theorem map_variableIdeal (σ τ : Type*) [Finite σ] (f : σ → τ) :
    (variableIdeal k σ).map (MvPowerSeries.rename (R := k) f).toRingHom =
      Ideal.span (Set.range (fun i => MvPowerSeries.X (R := k) (f i))) := by
  rw [variableIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  simp [Function.comp_def, MvPowerSeries.rename_X]

private theorem rectangle_eq (i j : ℕ) :
    rectangle k a b i j =
      ((variableIdeal k (Fin a)).map (includeX k a b).toRingHom) ^ i ⊔
      ((variableIdeal k (YIndex b)).map (includeY k a b).toRingHom) ^ j := by
  simp only [rectangle, xIdeal, yIdeal, Ideal.map_pow]

private theorem jointIdeal_eq :
    jointIdeal k a b =
      (variableIdeal k (Fin a)).map (includeX k a b).toRingHom ⊔
      (variableIdeal k (YIndex b)).map (includeY k a b).toRingHom := by
  rw [map_variableIdeal, map_variableIdeal, ← Ideal.span_union]
  change Ideal.span _ = Ideal.span _
  congr 1
  ext f
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩

private theorem sup_pow_le {R : Type*} [CommRing R] (I J : Ideal R)
    (i j : ℕ) : (I ⊔ J) ^ (i + j - 1) ≤ I ^ i ⊔ J ^ j := by
  rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro m _
  by_cases h : i ≤ m
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right h).trans le_sup_left))
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right (show j ≤ i + j - 1 - m by omega)).trans le_sup_right))

theorem cofinalPowers : CofinalPowers := by
  intro k _ a b n _
  rw [rectangle_eq, jointIdeal_eq]
  exact ⟨by simpa only [two_mul] using sup_pow_le _ _ n n,
    sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)⟩

private theorem series_mem_pow {σ : Type*} [Finite σ] (n : ℕ) (p : MvPowerSeries σ k) :
    p ∈ variableIdeal k σ ^ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → MvPowerSeries.coeff d p = 0 := by
  classical
  let := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  let E := MvPowerSeries.renameEquiv k e
  have hmap : (variableIdeal k σ ^ n).map E.toRingEquiv = variableIdeal k (Fin (Fintype.card σ)) ^ n := by
    rw [Ideal.map_pow]
    congr 1
    change (variableIdeal k σ).map (MvPowerSeries.rename (R := k) e).toRingHom = _
    rw [map_variableIdeal]
    change Ideal.span _ = Ideal.span _
    congr 1
    exact e.surjective.range_comp (MvPowerSeries.X (R := k))
  rw [← Ideal.apply_mem_of_equiv_iff (f := E.toRingEquiv), hmap]
  have hm := (CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k (Fintype.card σ)).2.2.2.1
  rw [show variableIdeal k (Fin (Fintype.card σ)) = maximalIdeal _ from hm.symm]
  rw [CommutativeAlgebraNotes.CompleteRegularPowerSeries.maximalIdealPower k]
  have hdeg (d : σ →₀ ℕ) : (d.embDomain e.toEmbedding).degree = d.degree := by
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
  simp only [IsLocalRing.maximalIdeal_eq_bot]
  constructor
  · intro h d hd
    specialize h (d.embDomain e.toEmbedding)
    rw [hdeg, Ideal.bot_pow (show n - d.degree ≠ 0 by omega), Submodule.mem_bot] at h
    exact (MvPowerSeries.coeff_embDomain_rename e.toEmbedding p d).symm.trans h
  · intro h d
    let t := Finsupp.comapDomain e d e.injective.injOn
    have ht : t.embDomain e.toEmbedding = d :=
      Finsupp.embDomain_comapDomain (by simp [e.surjective.range_eq])
    rw [← ht, hdeg]
    by_cases hd : t.degree < n
    · rw [Ideal.bot_pow (show n - t.degree ≠ 0 by omega), Submodule.mem_bot]
      change MvPowerSeries.coeff (t.embDomain e.toEmbedding)
        (MvPowerSeries.rename e p) = 0
      exact (MvPowerSeries.coeff_embDomain_rename e.toEmbedding p t).trans (h t hd)
    · rw [show n - t.degree = 0 by omega, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top

private theorem truncTotal_sub_mem {σ : Type*} [Finite σ] (n : ℕ) (p : MvPowerSeries σ k) :
    p - (p.truncTotal n : MvPowerSeries σ k) ∈ variableIdeal k σ ^ n := by
  rw [series_mem_pow]
  intro d hd
  simp [MvPowerSeries.coeff_truncTotal _ hd]

private theorem truncated_ext {σ C : Type*} [Finite σ] [CommRing C] [Algebra k C]
    {f g : MvPowerSeries σ k →ₐ[k] C} (n : ℕ)
    (hf : variableIdeal k σ ^ n ≤ RingHom.ker f.toRingHom)
    (hg : variableIdeal k σ ^ n ≤ RingHom.ker g.toRingHom)
    (h : ∀ s, f (MvPowerSeries.X s) = g (MvPowerSeries.X s)) : f = g := by
  have hp : f.comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      g.comp (MvPolynomial.coeToMvPowerSeries.algHom k) := by
    apply MvPolynomial.algHom_ext
    intro s
    simpa using h s
  ext p
  have h₁ := RingHom.mem_ker.mp (hf (truncTotal_sub_mem n p))
  have h₂ := RingHom.mem_ker.mp (hg (truncTotal_sub_mem n p))
  simp only [map_sub, sub_eq_zero] at h₁ h₂
  exact h₁.trans ((DFunLike.congr_fun hp (p.truncTotal n)).trans h₂.symm)

/-- Polynomial evaluation extends to series when sufficiently high monomials vanish. -/
private def evalTruncated {σ C : Type*} [Finite σ] [CommRing C] [Algebra k C]
    (v : σ → C) (n : ℕ)
    (h : MvPolynomial.idealOfVars σ k ^ n ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
    MvPowerSeries σ k →ₐ[k] C :=
  let J := MvPolynomial.idealOfVars σ k ^ n
  let g : (MvPolynomial σ k ⧸ J) →ₐ[k] C :=
    Ideal.Quotient.liftₐ J (MvPolynomial.aeval v)
      (fun _p hp => (RingHom.mem_ker (f := (MvPolynomial.aeval v).toRingHom)).mp (h hp))
  let f : MvPowerSeries σ k →ₐ[k] (MvPolynomial σ k ⧸ J) :=
    (MvPowerSeries.truncTotalAlgHom σ k n).restrictScalars k
  g.comp f

private theorem evalTruncated_apply {σ C : Type*} [Finite σ] [CommRing C] [Algebra k C]
    (v : σ → C) (n : ℕ) (h) (p : MvPowerSeries σ k) :
    evalTruncated v n h p =
      (Ideal.Quotient.liftₐ (MvPolynomial.idealOfVars σ k ^ n) (MvPolynomial.aeval v)
        (fun _ hp => RingHom.mem_ker.mp (h hp)))
      (MvPowerSeries.truncTotalAlgHom σ k n p) := rfl

private theorem evalTruncated_coe {σ C : Type*} [Finite σ] [CommRing C] [Algebra k C]
    (v : σ → C) (n : ℕ) (h) (p : MvPolynomial σ k) :
    evalTruncated v n h (p : MvPowerSeries σ k) = MvPolynomial.aeval v p := by
  rw [evalTruncated_apply]
  have hp : MvPowerSeries.truncTotalAlgHom σ k n (p : MvPowerSeries σ k) =
      Ideal.Quotient.mk (MvPolynomial.idealOfVars σ k ^ n) p :=
    (MvPowerSeries.truncTotalAlgHom σ k n).commutes p
  rw [hp]
  rfl

private theorem evalTruncated_ker {σ C : Type*} [Finite σ] [CommRing C] [Algebra k C]
    (v : σ → C) (n : ℕ) (h) :
    variableIdeal k σ ^ n ≤ RingHom.ker (evalTruncated v n h).toRingHom := by
  intro p hp
  have hz : p.truncTotal n = 0 := by
    apply MvPolynomial.ext
    intro d
    by_cases hd : d.degree < n
    · simp [MvPowerSeries.coeff_truncTotal _ hd, (series_mem_pow n p).mp hp d hd]
    · simp [MvPowerSeries.coeff_truncTotal_eq_zero _ (Nat.le_of_not_lt hd)]
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, evalTruncated_apply]
  rw [MvPowerSeries.truncTotalAlgHom_apply, hz, map_zero, map_zero]

private def leftIn (i j : ℕ) : X k a →ₐ[k] TensorRing k a b i j :=
  (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := XRing k a i)
    (B := YRing k b j)).comp (Ideal.Quotient.mkₐ k (xIdeal k a i))

private def rightIn (i j : ℕ) : Y k b →ₐ[k] TensorRing k a b i j :=
  (Algebra.TensorProduct.includeRight (R := k) (A := XRing k a i)
    (B := YRing k b j)).comp (Ideal.Quotient.mkₐ k (yIdeal k b j))

private theorem leftIn_ker (i j : ℕ) :
    xIdeal k a i ≤ RingHom.ker (leftIn (k := k) (a := a) (b := b) i j).toRingHom := by
  intro r hr
  rw [RingHom.mem_ker]
  change Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := YRing k b j)
    (Ideal.Quotient.mk (xIdeal k a i) r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

private theorem rightIn_ker (i j : ℕ) :
    yIdeal k b j ≤ RingHom.ker (rightIn (k := k) (a := a) (b := b) i j).toRingHom := by
  intro r hr
  rw [RingHom.mem_ker]
  change Algebra.TensorProduct.includeRight (R := k) (A := XRing k a i)
    (Ideal.Quotient.mk (yIdeal k b j) r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

private def tensorVariables (i j : ℕ) : Fin a ⊕ YIndex b → TensorRing k a b i j :=
  Sum.elim (leftIn (k := k) (a := a) (b := b) i j ∘ MvPowerSeries.X) (rightIn (k := k) (a := a) (b := b) i j ∘ MvPowerSeries.X)

private theorem tensorVariables_map (i j : ℕ) :
    (MvPolynomial.idealOfVars (Fin a ⊕ YIndex b) k).map
        (MvPolynomial.aeval (tensorVariables (k := k) (a := a) (b := b) i j)).toRingHom =
      (variableIdeal k (Fin a)).map (leftIn (k := k) (a := a) (b := b) i j).toRingHom ⊔
      (variableIdeal k (YIndex b)).map (rightIn (k := k) (a := a) (b := b) i j).toRingHom := by
  have hv (s : Fin a ⊕ YIndex b) :
      (MvPolynomial.aeval (tensorVariables (k := k) (a := a) (b := b) i j)).toRingHom
        (MvPolynomial.X s : MvPolynomial (Fin a ⊕ YIndex b) k) = tensorVariables (k := k) (a := a) (b := b) i j s :=
    MvPolynomial.aeval_X (tensorVariables (k := k) (a := a) (b := b) i j) s
  unfold variableIdeal
  simp only [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp,
    ← Ideal.span_union, Function.comp_def, hv]
  congr 1
  ext z
  constructor
  · rintro ⟨s | t, rfl⟩
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr ⟨t, rfl⟩
  · rintro (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨Sum.inl s, rfl⟩
    · exact ⟨Sum.inr t, rfl⟩

private theorem tensorVariables_nilpotent (i j : ℕ) :
    MvPolynomial.idealOfVars (Fin a ⊕ YIndex b) k ^ (i + j - 1) ≤
      RingHom.ker (MvPolynomial.aeval (tensorVariables (k := k) (a := a) (b := b) i j)).toRingHom := by
  let L := (leftIn (k := k) (a := a) (b := b) i j).toRingHom
  let R := (rightIn (k := k) (a := a) (b := b) i j).toRingHom
  have hx : (variableIdeal k (Fin a) ^ i).map L = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker L).mpr (leftIn_ker (k := k) (a := a) (b := b) i j)
  have hy : (variableIdeal k (YIndex b) ^ j).map R = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker R).mpr (rightIn_ker (k := k) (a := a) (b := b) i j)
  erw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, tensorVariables_map]
  have hh := sup_pow_le ((variableIdeal k (Fin a)).map L) ((variableIdeal k (YIndex b)).map R) i j
  rw [← Ideal.map_pow, ← Ideal.map_pow, hx, hy, sup_idem] at hh
  exact eq_bot_iff.mpr hh

private def jointToTensor (i j : ℕ) : S k a b →ₐ[k] TensorRing k a b i j :=
  evalTruncated (tensorVariables (k := k) (a := a) (b := b) i j) (i + j - 1) (tensorVariables_nilpotent i j)

private theorem jointToTensor_X (i j : ℕ) (s : Fin a ⊕ YIndex b) :
    jointToTensor (k := k) (a := a) (b := b) i j (MvPowerSeries.X s) = tensorVariables (k := k) (a := a) (b := b) i j s := by
  unfold jointToTensor
  rw [← MvPolynomial.coe_X, evalTruncated_coe, MvPolynomial.aeval_X]

private theorem jointToTensor_ker (i j : ℕ) :
    jointIdeal k a b ^ (i + j - 1) ≤
      RingHom.ker (jointToTensor (k := k) (a := a) (b := b) i j).toRingHom :=
  evalTruncated_ker _ _ _

private theorem jointToTensor_left (i j : ℕ) :
    (jointToTensor (k := k) (a := a) (b := b) i j).comp (includeX k a b) = leftIn (k := k) (a := a) (b := b) i j := by
  refine truncated_ext (k := k) (σ := Fin a) (C := TensorRing k a b i j)
    (f := (jointToTensor (k := k) (a := a) (b := b) i j).comp (includeX k a b))
    (g := leftIn (k := k) (a := a) (b := b) i j) (max (i + j - 1) i) ?_ ?_ ?_
  · change _ ≤ RingHom.ker ((jointToTensor (k := k) (a := a) (b := b) i j).toRingHom.comp _)
    rw [← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine (Ideal.pow_right_mono (I := (variableIdeal k (Fin a)).map _) ?_ _).trans
      ((Ideal.pow_le_pow_right (le_max_left _ _)).trans (jointToTensor_ker i j))
    rw [jointIdeal_eq]
    exact le_sup_left
  · exact (Ideal.pow_le_pow_right (le_max_right _ _)).trans (leftIn_ker i j)
  · intro s
    change jointToTensor (k := k) (a := a) (b := b) i j (includeX k a b (MvPowerSeries.X s)) = _
    rw [show includeX k a b (MvPowerSeries.X s) = MvPowerSeries.X (Sum.inl s)
      from MvPowerSeries.rename_X _ _, jointToTensor_X]
    rfl

private theorem jointToTensor_right (i j : ℕ) :
    (jointToTensor (k := k) (a := a) (b := b) i j).comp (includeY k a b) = rightIn (k := k) (a := a) (b := b) i j := by
  refine truncated_ext (k := k) (σ := YIndex b) (C := TensorRing k a b i j)
    (f := (jointToTensor (k := k) (a := a) (b := b) i j).comp (includeY k a b))
    (g := rightIn (k := k) (a := a) (b := b) i j) (max (i + j - 1) j) ?_ ?_ ?_
  · change _ ≤ RingHom.ker ((jointToTensor (k := k) (a := a) (b := b) i j).toRingHom.comp _)
    rw [← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine (Ideal.pow_right_mono (I := (variableIdeal k (YIndex b)).map _) ?_ _).trans
      ((Ideal.pow_le_pow_right (le_max_left _ _)).trans (jointToTensor_ker i j))
    rw [jointIdeal_eq]
    exact le_sup_right
  · exact (Ideal.pow_le_pow_right (le_max_right _ _)).trans (rightIn_ker i j)
  · intro s
    change jointToTensor (k := k) (a := a) (b := b) i j (includeY k a b (MvPowerSeries.X s)) = _
    rw [show includeY k a b (MvPowerSeries.X s) = MvPowerSeries.X (Sum.inr s)
      from MvPowerSeries.rename_X _ _, jointToTensor_X]
    rfl

private def ringLevelToTensor (i j : ℕ) : RingLevel k a b i j →ₐ[k] TensorRing k a b i j :=
  Ideal.Quotient.liftₐ _ (jointToTensor (k := k) (a := a) (b := b) i j) (by
    have h : rectangle k a b i j ≤ RingHom.ker (jointToTensor (k := k) (a := a) (b := b) i j).toRingHom := by
      apply sup_le
      · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
        change xIdeal k a i ≤ RingHom.ker
          (((jointToTensor (k := k) (a := a) (b := b) i j).comp (includeX k a b)).toRingHom)
        rw [jointToTensor_left]
        exact leftIn_ker (k := k) (a := a) (b := b) i j
      · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
        change yIdeal k b j ≤ RingHom.ker
          (((jointToTensor (k := k) (a := a) (b := b) i j).comp (includeY k a b)).toRingHom)
        rw [jointToTensor_right]
        exact rightIn_ker (k := k) (a := a) (b := b) i j
    exact fun _ hs => RingHom.mem_ker.mp (h hs))

theorem tensorRingToLevel_tmul (i j : ℕ) (x : X k a) (y : Y k b) :
    tensorRingToLevel k a b i j
      (Ideal.Quotient.mk _ x ⊗ₜ[k] Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (includeX k a b x * includeY k a b y) := by
  rw [tensorRingToLevel, Algebra.TensorProduct.lift_tmul, map_mul]
  rfl

private theorem ringLevelToTensor_mk (i j : ℕ) (s : S k a b) :
    ringLevelToTensor (k := k) (a := a) (b := b) i j (Ideal.Quotient.mk _ s) = jointToTensor (k := k) (a := a) (b := b) i j s := rfl

theorem ringComparison : RingComparison := by
  intro k _ a b i j
  let F := tensorRingToLevel k a b i j
  let G := ringLevelToTensor (k := k) (a := a) (b := b) i j
  have hfg : G.comp F = AlgHom.id k _ := by
    apply Algebra.TensorProduct.ext'
    intro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    dsimp only [F, G]
    rw [tensorRingToLevel_tmul, ringLevelToTensor_mk, map_mul]
    rw [show jointToTensor (k := k) (a := a) (b := b) i j (includeX k a b x) = leftIn (k := k) (a := a) (b := b) i j x
        from DFunLike.congr_fun (jointToTensor_left i j) x,
      show jointToTensor (k := k) (a := a) (b := b) i j (includeY k a b y) = rightIn (k := k) (a := a) (b := b) i j y
        from DFunLike.congr_fun (jointToTensor_right i j) y]
    change (_ ⊗ₜ[k] (1 : YRing k b j)) * ((1 : XRing k a i) ⊗ₜ[k] _) = _
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hgf : F.comp (jointToTensor (k := k) (a := a) (b := b) i j) = Ideal.Quotient.mkₐ k (rectangle k a b i j) := by
    apply truncated_ext (i + j - 1)
    · intro x hx
      rw [RingHom.mem_ker]
      change F (jointToTensor (k := k) (a := a) (b := b) i j x) = 0
      have hh : jointToTensor (k := k) i j x = 0 := RingHom.mem_ker.mp (jointToTensor_ker i j hx)
      rw [hh, map_zero]
    · intro x hx
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((by rw [jointIdeal_eq, rectangle_eq]; exact sup_pow_le _ _ i j :
          jointIdeal k a b ^ (i + j - 1) ≤ rectangle k a b i j) hx)
    · intro s
      change F (jointToTensor (k := k) (a := a) (b := b) i j (MvPowerSeries.X s)) = _
      rw [jointToTensor_X]
      cases s with
      | inl s =>
        change F (Ideal.Quotient.mk _ (MvPowerSeries.X s) ⊗ₜ[k] Ideal.Quotient.mk _ 1) = _
        rw [tensorRingToLevel_tmul, map_one, mul_one, MvPowerSeries.rename_X]
        rfl
      | inr s =>
        change F (Ideal.Quotient.mk _ 1 ⊗ₜ[k] Ideal.Quotient.mk _ (MvPowerSeries.X s)) = _
        rw [tensorRingToLevel_tmul, map_one, one_mul, MvPowerSeries.rename_X]
        rfl
  have hleft : Function.LeftInverse G F := fun z => DFunLike.congr_fun hfg z
  refine ⟨hleft.injective, fun z => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨G (Ideal.Quotient.mk _ s), DFunLike.congr_fun hgf s⟩

private theorem finiteModuleComplete {R E : Type*} [CommRing R] [AddCommGroup E]
    [Module R E] [IsNoetherianRing R] [Module.Finite R E] (I : Ideal R)
    [IsAdicComplete I R] : IsAdicComplete I E := by
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  refine { toIsHausdorff := IsHausdorff.of_le_jacobson I E hI
           toIsPrecomplete := AdicCompletion.of_surjective_iff.mp ?_ }
  let e := (TensorProduct.lid R E).symm.trans <|
    TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R E)
  have he : (AdicCompletion.of I E : E → AdicCompletion I E) =
      fun x => AdicCompletion.ofTensorProduct I E (e x) := by
    funext x
    change AdicCompletion.of I E x =
      AdicCompletion.ofTensorProduct I E (AdicCompletion.of I R 1 ⊗ₜ[R] x)
    rw [AdicCompletion.ofTensorProduct_tmul]
    change AdicCompletion.of I E x = (algebraMap R (AdicCompletion I R) 1) • _
    rw [map_one, one_smul]
  rw [he]
  exact (AdicCompletion.ofTensorProduct_surjective_of_finite I E).comp e.surjective

theorem quotientLimitComparison : QuotientLimitComparison := by
  intro k _ a b E _ _ _
  let I := jointIdeal k a b
  let : IsAdicComplete I (S k a b) := by
    change IsAdicComplete (Ideal.span (Set.range MvPowerSeries.X)) (S k a b)
    infer_instance
  let : IsAdicComplete I E := finiteModuleComplete I
  have hsmall (n : ℕ) : levelSubmodule k a b E (n + 1) (n + 1) ≤
      (I ^ n • ⊤ : Submodule (S k a b) E) :=
    Submodule.smul_mono_left <| (cofinalPowers k a b (n + 1) (by omega)).2.trans
      (Ideal.pow_le_pow_right (Nat.le_succ n))
  constructor
  · intro x y hxy
    apply (IsHausdorff.eq_iff_smodEq (I := I)).2
    intro n
    apply SModEq.mono (hsmall n)
    exact congrArg (fun f : LevelLimit k a b E => f.val (n + 1) (n + 1)) hxy
  · intro f
    choose g hg using fun n : ℕ =>
      (levelSubmodule k a b E (n + 1) (n + 1)).mkQ_surjective (f.val (n + 1) (n + 1))
    have compat (n m : ℕ) (hnm : n ≤ m) :
        g m ≡ g n [SMOD levelSubmodule k a b E (n + 1) (n + 1)] := by
      have h := f.property (n + 1) (m + 1) (n + 1) (m + 1)
        (Nat.succ_le_succ hnm) (Nat.succ_le_succ hnm)
      rw [← hg m, ← hg n] at h
      exact h
    obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := I) g
      (fun {n m} hnm => SModEq.mono (hsmall n) (compat n m hnm).symm)
    refine ⟨x, Subtype.ext (funext fun i => funext fun j => ?_)⟩
    let p := max i j + 1
    let n := 2 * p
    have hi : i ≤ p := by dsimp [p]; omega
    have hj : j ≤ p := by dsimp [p]; omega
    have hin : i ≤ n + 1 := by dsimp [n]; omega
    have hjn : j ≤ n + 1 := by dsimp [n]; omega
    have hn : I ^ n ≤ rectangle k a b i j :=
      (Ideal.pow_le_pow_right (show 2 * p - 1 ≤ n by dsimp [n]; omega)).trans
        ((cofinalPowers k a b p (by simp [p])).1.trans (rectangle_antitone k a b hi hj))
    have hx' := SModEq.mono (Submodule.smul_mono_left hn) (hx n)
    have hf := f.property i (n + 1) j (n + 1) hin hjn
    rw [← hg n] at hf
    exact Eq.trans (show (Submodule.Quotient.mk x : ModuleLevel k a b E i j) =
      Submodule.Quotient.mk (g n) from hx'.symm) hf

section PositiveIndices

variable {R : Type*} [CommRing R] (F : ℕ → ℕ → Type*)
  [∀ i j, AddCommGroup (F i j)] [∀ i j, Module R (F i j)]
  (tr : ∀ {i i' j j' : ℕ}, i ≤ i' → j ≤ j' → F i' j' →ₗ[R] F i j)

private def restrictPositive : compatibleLimit F (@tr) →ₗ[R] compatibleLimitSucc F (@tr) where
  toFun z := ⟨fun i j => z.val (i + 1) (j + 1),
    fun _ _ _ _ hi hj => z.property _ _ _ _ (Nat.succ_le_succ hi) (Nat.succ_le_succ hj)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictPositive_bijective
    (hleft : ∀ j, Subsingleton (F 0 j)) (hright : ∀ i, Subsingleton (F i 0)) :
    Function.Bijective (restrictPositive F (@tr)) := by
  constructor
  · intro z z' heq
    apply Subtype.ext
    funext i j
    cases i with
    | zero => exact (hleft j).elim _ _
    | succ i =>
      cases j with
      | zero => exact (hright (i + 1)).elim _ _
      | succ j => exact congrArg (fun z : compatibleLimitSucc F (@tr) => z.val i j) heq
  · intro z
    let f : ∀ i j, F i j
      | 0, _ => 0
      | _ + 1, 0 => 0
      | i + 1, j + 1 => z.val i j
    refine ⟨⟨f, ?_⟩, rfl⟩
    intro i i' j j' hi hj
    cases i with
    | zero => exact (hleft j).elim _ _
    | succ i =>
      cases j with
      | zero => exact (hright (i + 1)).elim _ _
      | succ j =>
        cases i' with
        | zero => omega
        | succ i' =>
          cases j' with
          | zero => omega
          | succ j' => exact z.property i i' j j' (Nat.le_of_succ_le_succ hi) (Nat.le_of_succ_le_succ hj)

end PositiveIndices

section ModuleComparison

open TensorProduct

variable (k : Type*) [Field k] (a b : ℕ)
  (M N : Type*) [AddCommGroup M] [Module (X k a) M] [AddCommGroup N] [Module (Y k b) N]

local notation "A" => X k a
local notation "B" => Y k b
local notation "R" => S k a b
local notation "T" => Product k a b M N
local notation "U" => ModuleTensor k a b M N
local notation "Q" => ModuleLevel k a b T
local notation "x₀" => xSubmodule k a M
local notation "y₀" => ySubmodule k b N

scoped instance tensorModuleInstance (i j : ℕ) : Module R (U i j) := tensorModule k a b M N ringComparison i j

private theorem quotientScalar (i j : ℕ) (x : A) (y : B) (m : XM k a M i) (n : YN k b N j) :
    (includeX k a b x * includeY k a b y) • (m ⊗ₜ[k] n : U i j) =
      (x • m) ⊗ₜ[k] (y • n) := by
  let e : TensorRing k a b i j ≃ₐ[k] RingLevel k a b i j :=
    AlgEquiv.ofBijective (tensorRingToLevel k a b i j) (ringComparison k a b i j)
  have he : e.symm (Ideal.Quotient.mk (rectangle k a b i j) (includeX k a b x * includeY k a b y)) =
      (Ideal.Quotient.mk (xIdeal k a i) x) ⊗ₜ[k] (Ideal.Quotient.mk (yIdeal k b j) y) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (tensorRingToLevel_tmul i j x y).symm
  change tensorAction k a b M N i j (e.symm (Ideal.Quotient.mk _
    (includeX k a b x * includeY k a b y))) (m ⊗ₜ[k] n) = _
  rw [he]
  rfl

private theorem quotientScalar_zero (i j : ℕ) (r : R) (hr : r ∈ rectangle k a b i j)
    (w : U i j) : r • w = 0 := by
  let e : TensorRing k a b i j ≃ₐ[k] RingLevel k a b i j :=
    AlgEquiv.ofBijective (tensorRingToLevel k a b i j) (ringComparison k a b i j)
  change tensorAction k a b M N i j (e.symm (Ideal.Quotient.mk _ r)) w = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero, LinearMap.zero_apply]

private theorem quotientScalar_left (i j : ℕ) (x : A) (m : XM k a M i) (n : YN k b N j) :
    includeX k a b x • (m ⊗ₜ[k] n : U i j) = (x • m) ⊗ₜ[k] n := by
  simpa only [map_one, mul_one, one_smul] using quotientScalar k a b M N i j x 1 m n

private theorem quotientScalar_right (i j : ℕ) (y : B) (m : XM k a M i) (n : YN k b N j) :
    includeY k a b y • (m ⊗ₜ[k] n : U i j) = m ⊗ₜ[k] (y • n) := by
  simpa only [map_one, one_mul, one_smul] using quotientScalar k a b M N i j 1 y m n

private def pair (m : M) (n : N) : T := ((1 : R) ⊗ₜ[A] m) ⊗ₜ[B] n

private theorem pair_left (x : A) (m : M) (n : N) :
    pair k a b M N (x • m) n = includeX k a b x • pair k a b M N m n := by
  unfold pair
  rw [TensorProduct.tmul_smul, ExteriorTensorProduct.smul_tmul]
  change (((includeX k a b x * 1) ⊗ₜ[A] m) ⊗ₜ[B] n) =
    (((includeX k a b x * 1) ⊗ₜ[A] m) ⊗ₜ[B] n)
  rfl

private theorem pair_right (y : B) (m : M) (n : N) :
    pair k a b M N m (y • n) = includeY k a b y • pair k a b M N m n := by
  unfold pair
  rw [TensorProduct.tmul_smul]
  rfl

private theorem level_smul_zero (i j : ℕ) (r : R) (hr : r ∈ rectangle k a b i j)
    (w : Q i j) : r • w = 0 := by
  induction w using Submodule.Quotient.induction_on with
  | _ t =>
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hr Submodule.mem_top)

private def fromProduct (i j : ℕ) : T →ₗ[R] U i j := by
  letI : Module B (U i j) := Module.compHom _ (algebraMap B R)
  letI : IsScalarTower B R (U i j) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module A (N →ₗ[B] U i j) := Module.compHom _ (algebraMap A R)
  letI : IsScalarTower A R (N →ₗ[B] U i j) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] N →ₗ[B] U i j :=
    { toFun := fun m =>
        { toFun := fun n => (x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n
          map_add' := fun n n' => by rw [map_add, tmul_add]
          map_smul' := fun y n => by
            change (x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ (y • n) =
              (includeY k a b y) • ((x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n : U i j)
            rw [map_smul, quotientScalar_right] }
      map_add' := fun m m' => LinearMap.ext fun n => by
        change (x₀ i).mkQ (m + m') ⊗ₜ[k] (y₀ j).mkQ n =
          (x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n + (x₀ i).mkQ m' ⊗ₜ[k] (y₀ j).mkQ n
        rw [map_add, add_tmul]
      map_smul' := fun x m => LinearMap.ext fun n => by
        change (x₀ i).mkQ (x • m) ⊗ₜ[k] (y₀ j).mkQ n =
          (includeX k a b x) • ((x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n : U i j)
        rw [map_smul, quotientScalar_left] }
  exact AlgebraTensorModule.lift (f.liftBaseChange R)

private theorem fromProduct_tmul (i j : ℕ) (r : R) (m : M) (n : N) :
    fromProduct k a b M N i j ((r ⊗ₜ[A] m) ⊗ₜ[B] n) =
      r • ((x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n : U i j) := rfl

private theorem fromProduct_ker (i j : ℕ) :
    levelSubmodule k a b T i j ≤ LinearMap.ker (fromProduct k a b M N i j) := by
  change rectangle k a b i j • (⊤ : Submodule R T) ≤ _
  refine Submodule.smul_le.mpr ?_
  intro r hr t _
  rw [LinearMap.mem_ker, map_smul]
  exact quotientScalar_zero k a b M N i j r hr _

set_option maxSynthPendingDepth 3 in
private def fromLevel (i j : ℕ) : Q i j →ₗ[R] U i j := by
  let P : Submodule R T := levelSubmodule k a b T i j
  letI : HasQuotient T (Submodule R T) := Submodule.hasQuotient
  let f : T →ₗ[R] U i j := fromProduct k a b M N i j
  have hf : P ≤ f.ker := fromProduct_ker k a b M N i j
  have h : Q i j →ₗ[R] U i j := Submodule.liftQ P f hf
  exact h

private theorem fromLevel_pair (i j : ℕ) (m : M) (n : N) :
    fromLevel k a b M N i j (Submodule.Quotient.mk (pair k a b M N m n)) =
      (x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n := by
  rw [fromLevel, Submodule.liftQ_apply, pair, fromProduct_tmul, one_smul]

private def pairBilinear (i j : ℕ) :
    M →ₛₗ[(includeX k a b).toRingHom] N →ₛₗ[(includeY k a b).toRingHom] Q i j :=
  { toFun := fun m =>
      { toFun := fun n => Submodule.Quotient.mk (pair k a b M N m n)
        map_add' := fun n n' => by simp only [pair, tmul_add, Submodule.Quotient.mk_add]
        map_smul' := fun y n => by
          change (Submodule.Quotient.mk (pair k a b M N m (y • n)) : Q i j) =
            includeY k a b y • Submodule.Quotient.mk (pair k a b M N m n)
          rw [pair_right, Submodule.Quotient.mk_smul] }
    map_add' := fun m m' => LinearMap.ext fun n => by
      simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, pair, tmul_add, add_tmul,
        Submodule.Quotient.mk_add]
    map_smul' := fun x m => LinearMap.ext fun n => by
      change (Submodule.Quotient.mk (pair k a b M N (x • m) n) : Q i j) =
        includeX k a b x • Submodule.Quotient.mk (pair k a b M N m n)
      rw [pair_left, Submodule.Quotient.mk_smul] }

private def levelBilinear (i j : ℕ) :
    XM k a M i →ₛₗ[(includeX k a b).toRingHom]
      YN k b N j →ₛₗ[(includeY k a b).toRingHom] Q i j :=
  (pairBilinear k a b M N i j).liftQ₂ (x₀ i) (y₀ j)
    (Submodule.smul_le.mpr fun x hx m _ => by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro n
      change (Submodule.Quotient.mk (pair k a b M N (x • m) n) : Q i j) = 0
      rw [pair_left, Submodule.Quotient.mk_smul]
      exact level_smul_zero k a b M N i j _ (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hx)) _)
    (Submodule.smul_le.mpr fun y hy n _ => by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro m
      change (Submodule.Quotient.mk (pair k a b M N m (y • n)) : Q i j) = 0
      rw [pair_right, Submodule.Quotient.mk_smul]
      exact level_smul_zero k a b M N i j _ (Submodule.mem_sup_right (Ideal.mem_map_of_mem _ hy)) _)

private def toLevelOverField (i j : ℕ) : U i j →ₛₗ[algebraMap k R] Q i j := by
  let f := levelBilinear k a b M N i j
  let g := LinearMap.mk₂'ₛₗ (algebraMap k R) (algebraMap k R)
    (fun (m : XM k a M i) (n : YN k b N j) => f m n)
    (fun m m' n => LinearMap.congr_fun (f.map_add m m') n)
    (fun c m n => by
      change f ((algebraMap k A c) • m) n = (algebraMap k R c) • f m n
      rw [f.map_smulₛₗ]
      change includeX k a b (algebraMap k A c) • f m n = _
      rw [AlgHom.commutes])
    (fun m n n' => (f m).map_add n n')
    (fun c m n => by
      change f m ((algebraMap k B c) • n) = (algebraMap k R c) • f m n
      rw [(f m).map_smulₛₗ]
      change includeY k a b (algebraMap k B c) • f m n = _
      rw [AlgHom.commutes])
  exact TensorProduct.lift g

private theorem toLevelOverField_tmul (i j : ℕ) (m : XM k a M i) (n : YN k b N j) :
    toLevelOverField k a b M N i j (m ⊗ₜ[k] n) = levelBilinear k a b M N i j m n := rfl

private theorem toLevelOverField_pair (i j : ℕ) (m : M) (n : N) :
    toLevelOverField k a b M N i j ((x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n) =
      Submodule.Quotient.mk (pair k a b M N m n) := rfl

private theorem toLevelOverField_smul_split (i j : ℕ) (x : A) (y : B) (w : U i j) :
    toLevelOverField k a b M N i j ((includeX k a b x * includeY k a b y) • w) =
      (includeX k a b x * includeY k a b y) • toLevelOverField k a b M N i j w := by
  induction w using TensorProduct.inductionOn with
  | tmul m n =>
    rw [quotientScalar, toLevelOverField_tmul, toLevelOverField_tmul]
    let f := levelBilinear k a b M N i j
    change f (x • m) (y • n) = _
    rw [f.map_smulₛₗ]
    change includeX k a b x • f m (y • n) = _
    rw [(f m).map_smulₛₗ, ← mul_smul]
    rfl
  | add w w' hw hw' => simp only [smul_add, map_add, hw, hw']

private theorem toLevelOverField_smul (i j : ℕ) (s : R) (w : U i j) :
    toLevelOverField k a b M N i j (s • w) =
      s • toLevelOverField k a b M N i j w := by
  let F := tensorRingToLevel k a b i j
  let G := toLevelOverField k a b M N i j
  obtain ⟨z, hz⟩ := (ringComparison k a b i j).2 (Ideal.Quotient.mk (rectangle k a b i j) s)
  have hrep (z : TensorRing k a b i j) :
      ∃ r : R, F z = Ideal.Quotient.mk (rectangle k a b i j) r ∧
        G (r • w) = r • G w := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨_, tensorRingToLevel_tmul i j x y, toLevelOverField_smul_split k a b M N i j x y w⟩
    | add z z' hz hz' =>
      obtain ⟨r, hr, hG⟩ := hz
      obtain ⟨r', hr', hG'⟩ := hz'
      exact ⟨r + r', by rw [map_add, hr, hr', map_add],
        by rw [add_smul, map_add, hG, hG', add_smul]⟩
  obtain ⟨r, hr, hG⟩ := hrep z
  have hsr := Ideal.Quotient.eq.mp (hz.symm.trans hr)
  have h₁ : s • w = r • w := sub_eq_zero.mp <| by
    rw [← sub_smul]
    exact quotientScalar_zero k a b M N i j _ hsr _
  have h₂ : s • G w = r • G w := sub_eq_zero.mp <| by
    rw [← sub_smul]
    exact level_smul_zero k a b M N i j _ hsr _
  rw [h₁, h₂]
  exact hG

private def toLevel (i j : ℕ) : U i j →ₗ[R] Q i j where
  toFun := toLevelOverField k a b M N i j
  map_add' := (toLevelOverField k a b M N i j).map_add
  map_smul' := toLevelOverField_smul k a b M N i j

private theorem toLevel_pair (i j : ℕ) (m : M) (n : N) :
    toLevel k a b M N i j ((x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n) =
      Submodule.Quotient.mk (pair k a b M N m n) :=
  toLevelOverField_pair k a b M N i j m n

/-- The canonical finite-level comparison. -/
def moduleComparison (i j : ℕ) : Q i j ≃ₗ[R] U i j :=
  @LinearEquiv.ofLinearMap R R (Q i j) (U i j) _ _ _ _ _ _
    (RingHom.id R) (RingHom.id R) _ _ (fromLevel k a b M N i j) (toLevel k a b M N i j)
    (by
      apply LinearMap.ext
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul m n =>
        obtain ⟨m, rfl⟩ := (x₀ i).mkQ_surjective m
        obtain ⟨n, rfl⟩ := (y₀ j).mkQ_surjective n
        simp only [LinearMap.comp_apply, LinearMap.id_apply, toLevel_pair, fromLevel_pair]
      | add t t' ht ht' => simp only [map_add, ht, ht'])
    (by
      refine @Submodule.linearMap_qext R T _ _ _ (levelSubmodule k a b T i j)
        R (Q i j) _ _ _ (RingHom.id R) _ _ ?_
      apply AlgebraTensorModule.ext
      intro t n
      induction t using TensorProduct.inductionOn with
      | tmul r m =>
        have h : ((r ⊗ₜ[A] m) ⊗ₜ[B] n : T) = r • pair k a b M N m n := by
          rw [pair, ExteriorTensorProduct.smul_tmul, mul_one]
        rw [h]
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_smul, Submodule.mkQ_apply,
          fromLevel_pair]
        exact congrArg (r • ·) (toLevel_pair k a b M N i j m n)
      | add t t' ht ht' => simp only [add_tmul, map_add, ht, ht'])

@[simp] theorem moduleComparison_pair (i j : ℕ) (m : M) (n : N) :
    moduleComparison k a b M N i j
        (Submodule.Quotient.mk (((1 : R) ⊗ₜ[A] m) ⊗ₜ[B] n)) =
      (x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n :=
  fromLevel_pair k a b M N i j m n

private theorem toLevel_transition {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') (z : U i' j') :
    toLevel k a b M N i j (tensorTransition k a b M N hi hj z) =
      levelTransition k a b T hi hj (toLevel k a b M N i' j' z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    obtain ⟨m, rfl⟩ := (x₀ i').mkQ_surjective m
    obtain ⟨n, rfl⟩ := (y₀ j').mkQ_surjective n
    change toLevel k a b M N i j ((x₀ i).mkQ m ⊗ₜ[k] (y₀ j).mkQ n) =
      levelTransition k a b T hi hj (toLevel k a b M N i' j' ((x₀ i').mkQ m ⊗ₜ[k] (y₀ j').mkQ n))
    rw [toLevel_pair, toLevel_pair]
    rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The usual transition on the tensor of the two quotients, bundled as a joint-ring
linear map. Each index may decrease independently. -/
def tensorTransitionLinear {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    U i' j' →ₗ[R] U i j :=
  (moduleComparison k a b M N i j).toLinearMap.comp
    ((levelTransition k a b T hi hj).comp (toLevel k a b M N i' j'))

@[simp] theorem tensorTransitionLinear_apply {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j')
    (z : U i' j') :
    tensorTransitionLinear k a b M N hi hj z = tensorTransition k a b M N hi hj z := by
  change moduleComparison k a b M N i j (levelTransition k a b T hi hj (toLevel k a b M N i' j' z)) = _
  rw [← toLevel_transition k a b M N hi hj]
  exact (moduleComparison k a b M N i j).apply_symm_apply _

theorem moduleComparison_transition {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') (t : Q i' j') :
    tensorTransitionLinear k a b M N hi hj (moduleComparison k a b M N i' j' t) =
      moduleComparison k a b M N i j (levelTransition k a b T hi hj t) := by
  change moduleComparison k a b M N i j (levelTransition k a b T hi hj
    ((moduleComparison k a b M N i' j').symm (moduleComparison k a b M N i' j' t))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The inverse limit of the tensors of the two module truncations. -/
abbrev TensorLimit :=
  compatibleLimit U (@tensorTransitionLinear k _ a b M N _ _ _ _)

private def levelFamilyComparison :
    LevelLimit k a b T ≃ₗ[R] TensorLimit k a b M N where
  toFun t := ⟨fun i j => moduleComparison k a b M N i j (t.val i j),
    fun i i' j j' hi hj => by
      rw [moduleComparison_transition, t.property i i' j j' hi hj]⟩
  invFun z := ⟨fun i j => (moduleComparison k a b M N i j).symm (z.val i j),
    fun i i' j j' hi hj => by
      apply (moduleComparison k a b M N i j).injective
      rw [← moduleComparison_transition, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact z.property i i' j j' hi hj⟩
  left_inv t := Subtype.ext (funext fun i => funext fun j => LinearEquiv.symm_apply_apply _ _)
  right_inv z := Subtype.ext (funext fun i => funext fun j => LinearEquiv.apply_symm_apply _ _)
  map_add' f g := Subtype.ext (funext fun i => funext fun j =>
    map_add (moduleComparison k a b M N i j) (f.val i j) (g.val i j))
  map_smul' r f := Subtype.ext (funext fun i => funext fun j =>
    map_smul (moduleComparison k a b M N i j) r (f.val i j))

/-- The exterior tensor product is isomorphic to the inverse limit via its
canonical reductions at every pair of indices. -/
def limitComparison [Module.Finite A M] [Module.Finite B N] :
    T ≃ₗ[R] TensorLimit k a b M N :=
  (LinearEquiv.ofBijective (toLevelLimit k a b T) (quotientLimitComparison k a b T)).trans
    (levelFamilyComparison k a b M N)

@[simp] theorem limitComparison_apply [Module.Finite A M] [Module.Finite B N] (t : T) (i j : ℕ) :
    (limitComparison k a b M N t).val i j =
      moduleComparison k a b M N i j (Submodule.Quotient.mk t) := rfl

private theorem tensorLevel_zero (i j : ℕ) (h : i = 0 ∨ j = 0) : Subsingleton (U i j) := by
  have hp : rectangle k a b i j = ⊤ := by
    obtain rfl | rfl := h <;> simp [rectangle, Ideal.one_eq_top, Ideal.map_top]
  have hone : (1 : R) ∈ rectangle k a b i j := by
    rw [hp]
    exact Submodule.mem_top
  have hz (z : U i j) : z = 0 := by
    simpa only [one_smul] using quotientScalar_zero k a b M N i j 1 hone z
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

abbrev PositiveTensorLimit :=
  compatibleLimitSucc U (@tensorTransitionLinear k _ a b M N _ _ _ _)

/-- The canonical inverse-limit isomorphism over positive truncation indices. -/
def positiveLimitComparison [Module.Finite A M] [Module.Finite B N] :
    T ≃ₗ[R] PositiveTensorLimit k a b M N :=
  (limitComparison k a b M N).trans
    (LinearEquiv.ofBijective (restrictPositive U (@tensorTransitionLinear k _ a b M N _ _ _ _))
      (restrictPositive_bijective U _ (fun j => tensorLevel_zero k a b M N 0 j (Or.inl rfl))
        (fun i => tensorLevel_zero k a b M N i 0 (Or.inr rfl))))

@[simp] theorem positiveLimitComparison_apply [Module.Finite A M] [Module.Finite B N]
    (t : T) (i j : ℕ) :
    (positiveLimitComparison k a b M N t).val i j =
      moduleComparison k a b M N (i + 1) (j + 1) (Submodule.Quotient.mk t) := rfl

/-- The map of quotients by the product of an ideal and a module. -/
def quotientLinearMap {C L L' : Type*} [CommRing C] [AddCommGroup L] [Module C L]
    [AddCommGroup L'] [Module C L'] (I : Ideal C) (f : L →ₗ[C] L') :
    (L ⧸ (I • ⊤ : Submodule C L)) →ₗ[C] (L' ⧸ (I • ⊤ : Submodule C L')) :=
  Submodule.mapQ _ _ f <| Submodule.smul_le.mpr fun r hr m _ => by
    change f (r • m) ∈ (I • ⊤ : Submodule C L')
    rw [map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

section Naturality

variable {M' N' : Type*} [AddCommGroup M'] [Module (X k a) M']
    [AddCommGroup N'] [Module (Y k b) N']

/-- The tensor product of the induced maps on the two truncated modules. -/
def moduleTensorMap (f : M →ₗ[A] M') (g : N →ₗ[B] N') (i j : ℕ) :
    U i j →ₗ[k] ModuleTensor k a b M' N' i j :=
  TensorProduct.map ((quotientLinearMap (xIdeal k a i) f).restrictScalars k)
    ((quotientLinearMap (yIdeal k b j) g).restrictScalars k)

private theorem toLevel_natural (f : M →ₗ[A] M') (g : N →ₗ[B] N') (i j : ℕ) (z : U i j) :
    toLevel k a b M' N' i j (moduleTensorMap k a b M N f g i j z) =
      quotientLinearMap (rectangle k a b i j) (ExteriorTensorProduct.map f g)
        (toLevel k a b M N i j z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    obtain ⟨m, rfl⟩ := (x₀ i).mkQ_surjective m
    obtain ⟨n, rfl⟩ := (y₀ j).mkQ_surjective n
    change toLevel k a b M' N' i j
        ((xSubmodule k a M' i).mkQ (f m) ⊗ₜ[k] (ySubmodule k b N' j).mkQ (g n)) = _
    rw [toLevel_pair, toLevel_pair]
    rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem moduleComparison_natural (f : M →ₗ[A] M') (g : N →ₗ[B] N') (i j : ℕ) (t : Q i j) :
    moduleTensorMap k a b M N f g i j (moduleComparison k a b M N i j t) =
      moduleComparison k a b M' N' i j
        (quotientLinearMap (rectangle k a b i j) (ExteriorTensorProduct.map f g) t) := by
  apply (moduleComparison k a b M' N' i j).symm.injective
  change toLevel k a b M' N' i j (moduleTensorMap k a b M N f g i j (moduleComparison k a b M N i j t)) =
    (moduleComparison k a b M' N' i j).symm (moduleComparison k a b M' N' i j
        (quotientLinearMap (rectangle k a b i j) (ExteriorTensorProduct.map f g) t))
  rw [toLevel_natural, LinearEquiv.symm_apply_apply]
  have ht : toLevel k a b M N i j (moduleComparison k a b M N i j t) = t :=
    (moduleComparison k a b M N i j).symm_apply_apply t
  rw [ht]

theorem limitComparison_natural [Module.Finite A M] [Module.Finite B N]
    [Module.Finite A M'] [Module.Finite B N']
    (f : M →ₗ[A] M') (g : N →ₗ[B] N') (t : T) (i j : ℕ) :
    moduleTensorMap k a b M N f g i j ((limitComparison k a b M N t).val i j) =
      (limitComparison k a b M' N' (ExteriorTensorProduct.map f g t)).val i j := by
  rw [limitComparison_apply, limitComparison_apply]
  exact moduleComparison_natural k a b M N f g i j (Submodule.Quotient.mk t)

theorem positiveLimitComparison_natural [Module.Finite A M] [Module.Finite B N]
    [Module.Finite A M'] [Module.Finite B N']
    (f : M →ₗ[A] M') (g : N →ₗ[B] N') (t : T) (i j : ℕ) :
    moduleTensorMap k a b M N f g (i + 1) (j + 1)
      ((positiveLimitComparison k a b M N t).val i j) =
      (positiveLimitComparison k a b M' N' (ExteriorTensorProduct.map f g t)).val i j := by
  rw [positiveLimitComparison_apply, positiveLimitComparison_apply]
  exact moduleComparison_natural k a b M N f g (i + 1) (j + 1) (Submodule.Quotient.mk t)

end Naturality

end ModuleComparison

theorem exteriorComparison : ExteriorComparison := by
  intro k _ a b M N _ _ _ _ h
  dsimp only
  refine ⟨moduleComparison k a b M N, moduleComparison_pair k a b M N,
    @tensorTransitionLinear k _ a b M N _ _ _ _, ?_, ?_, ?_⟩
  · intro i i' j j' hi hj z
    exact tensorTransitionLinear_apply k a b M N hi hj z
  · intro i i' j j' hi hj t
    exact moduleComparison_transition k a b M N hi hj t
  · intro _ _
    exact ⟨positiveLimitComparison k a b M N, positiveLimitComparison_apply k a b M N⟩

end

end CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
