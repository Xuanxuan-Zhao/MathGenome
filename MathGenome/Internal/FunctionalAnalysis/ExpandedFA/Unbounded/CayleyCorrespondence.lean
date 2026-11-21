import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.CayleyCorrespondence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.Tactic.Module

/-! Cayley isometries and the self-adjoint/unitary correspondence. The forward
map is constructed on the two signed ranges. The reverse map is extracted from
the graph equation U(y+ix)=y−ix; surjectivity of its signed shifts then gives
self-adjointness by the accepted exact-domain range criterion. -/

noncomputable section
universe u
namespace ExpandedFA.Unbounded
open CayleyCorrespondenceSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The source's kernel condition and the fixed-vector formulation agree. -/
theorem cayley_noFixedVectors_iff_kernel : NoFixedVectorsKernelExpected := by
  intro H _ _ _ U
  constructor
  · intro hf
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    change x - U x = 0 at hx
    exact hf x (sub_eq_zero.mp hx).symm
  · intro hk x hx
    have hm : x ∈ (LinearMap.id - U.toLinearMap).ker := by
      change x - U x = 0
      rw [hx, sub_self]
    rwa [hk, Submodule.mem_bot] at hm

private theorem plus_range (S : Operator ℂ H H) :
    (plus S).range = range (shift (-Complex.I) S) := by
  rw [range_shift_eq_range_sub]
  congr 1
  ext x
  simp [plus, sub_eq_add_neg]

private theorem minus_range (S : Operator ℂ H H) :
    (minus S).range = range (shift Complex.I S) :=
  (range_shift_eq_range_sub S Complex.I).symm

private theorem signed_injective (S : Operator ℂ H H) (hs : IsSymmetric S)
    (z : ℂ) (hz : z.im ≠ 0) : Function.Injective (S.toFun - z • S.domain.subtype) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have h := hs.nonreal_lower_bound z x
  change S x - z • (x : H) = 0 at hx
  rw [hx, norm_zero] at h
  apply Subtype.ext
  have hp := abs_pos.mpr hz
  have : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
  exact norm_eq_zero.mp this

private theorem plus_injective (S : Operator ℂ H H) (hs : IsSymmetric S) :
    Function.Injective (plus S) := by
  have he : plus S = S.toFun - (-Complex.I) • S.domain.subtype := by
    ext x; simp [plus, sub_eq_add_neg]
  rw [he]
  exact signed_injective S hs _ (by simp)

private theorem signed_norm (S : Operator ℂ H H) (hs : IsSymmetric S) (x : S.domain) :
    ‖minus S x‖ = ‖plus S x‖ := by
  have hp := hs.norm_sub_sq (-Complex.I) x
  have hm := hs.norm_sub_sq Complex.I x
  simp only [Complex.neg_im, Complex.I_im, Complex.neg_re, Complex.I_re, neg_zero,
    Complex.ofReal_zero, zero_smul, sub_zero, abs_neg, abs_one, one_pow, one_mul] at hp hm
  have he : S x - (-Complex.I) • (x : H) = plus S x := by simp [plus, sub_eq_add_neg]
  rw [he] at hp
  change ‖S x - Complex.I • (x : H)‖ ^ 2 = _ at hm
  have : ‖minus S x‖ ^ 2 = ‖plus S x‖ ^ 2 := hm.trans hp.symm
  nlinarith [norm_nonneg (minus S x), norm_nonneg (plus S x)]

private def partialCayley (S : Operator ℂ H H) (hs : IsSymmetric S) :
    (plus S).range ≃ₗᵢ[ℂ] (minus S).range :=
  { toLinearEquiv := (LinearEquiv.ofInjective (plus S) (plus_injective S hs)).symm.trans
      (LinearEquiv.ofInjective (minus S) (signed_injective S hs _ (by simp)))
    norm_map' := by
      intro y
      obtain ⟨x, hx⟩ := y.prop
      have he : y = (LinearEquiv.ofInjective (plus S) (plus_injective S hs)) x :=
        Subtype.ext hx.symm
      subst y
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      change ‖(minus S) x‖ = ‖(plus S) x‖
      exact signed_norm S hs x }

private theorem partialCayley_apply (S : Operator ℂ H H) (hs : IsSymmetric S)
    (x : S.domain) :
    partialCayley S hs ⟨plus S x, ⟨x, rfl⟩⟩ = ⟨minus S x, ⟨x, rfl⟩⟩ := by
  change (LinearEquiv.ofInjective (minus S) (signed_injective S hs _ (by simp)))
    ((LinearEquiv.ofInjective (plus S) (plus_injective S hs)).symm
    ((LinearEquiv.ofInjective (plus S) (plus_injective S hs)) x)) = _
  apply Subtype.ext
  simp
  rfl

theorem cayley_partial_isometry : PartialExpected := by
  intro H _ _ _ S hc hs
  have hp := plus_range S
  have hm := minus_range S
  obtain ⟨hrp, hrm⟩ := closed_symmetric_signed_ranges S hc hs
  refine ⟨?_, ?_, hp.trans hrp, hm.trans hrm, partialCayley S hs, partialCayley_apply S hs⟩
  · rw [hp]; exact closed_symmetric_shift_range_isClosed S hc hs _ (by simp)
  · rw [hm]; exact closed_symmetric_shift_range_isClosed S hc hs _ (by simp)

private theorem selfAdjoint_closed {S : Operator ℂ H H} (hs : IsSelfAdjoint S) :
    IsClosed S := by
  have he : S = hilbertAdjoint S := hs.2
  rw [he]
  exact hilbertAdjoint_isClosed S hs.1

private theorem selfAdjoint_symmetric {S : Operator ℂ H H} (hs : IsSelfAdjoint S) :
    IsSymmetric S := ⟨hs.1, hs.2.le⟩

private theorem plus_surjective {S : Operator ℂ H H} (hs : IsSelfAdjoint S) :
    Function.Surjective (plus S) := by
  apply LinearMap.range_eq_top.mp
  rw [plus_range]
  exact ((closed_symmetric_selfAdjoint_iff_ranges S (selfAdjoint_closed hs)
    (selfAdjoint_symmetric hs)).mp hs).1

private theorem forward_exists (S : Operator ℂ H H) (hs : IsSelfAdjoint S) :
    ∃ U : H ≃ₗᵢ[ℂ] H, NoFixedVectors U ∧ Pair S U := by
  have hsym := selfAdjoint_symmetric hs
  have hp : (plus S).range = ⊤ := LinearMap.range_eq_top.mpr (plus_surjective hs)
  have hm : (minus S).range = ⊤ := by
    rw [minus_range]
    exact ((closed_symmetric_selfAdjoint_iff_ranges S (selfAdjoint_closed hs) hsym).mp hs).2
  let U := (LinearIsometryEquiv.ofTop H (plus S).range hp).symm |>.trans
    (partialCayley S hsym) |>.trans (LinearIsometryEquiv.ofTop H (minus S).range hm)
  have hpair : Pair S U := by
    intro x
    have he : (LinearIsometryEquiv.ofTop H (plus S).range hp).symm (plus S x) =
        (⟨plus S x, ⟨x, rfl⟩⟩ : (plus S).range) := by
      apply (LinearIsometryEquiv.ofTop H (plus S).range hp).injective
      simp
    change ((partialCayley S hsym) ((LinearIsometryEquiv.ofTop H (plus S).range hp).symm
      (plus S x)) : H) = _
    rw [he, partialCayley_apply]
  refine ⟨U, ?_, hpair⟩
  intro y hy
  obtain ⟨x, rfl⟩ := plus_surjective hs y
  have hh : minus S x = plus S x := (hpair x).symm.trans hy
  have hx : (x : H) = 0 := by
    have hh' : (2 : ℂ) • (Complex.I • (x : H)) = 0 := by
      change S x - Complex.I • (x : H) = S x + Complex.I • (x : H) at hh
      calc
        _ = -((S x - Complex.I • (x : H)) - (S x + Complex.I • (x : H))) := by module
        _ = 0 := by rw [hh, sub_self, neg_zero]
    simpa using hh'
  have xx : x = 0 := Subtype.ext hx
  simp [xx, plus]

private def inverseGraphMap (U : H ≃ₗᵢ[ℂ] H) : (H × H) →L[ℂ] H :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.snd ℂ H H + Complex.I • ContinuousLinearMap.fst ℂ H H) -
    (ContinuousLinearMap.snd ℂ H H - Complex.I • ContinuousLinearMap.fst ℂ H H)

private theorem inverseGraphMap_apply (U : H ≃ₗᵢ[ℂ] H) (p : H × H) :
    inverseGraphMap U p = U (p.2 + Complex.I • p.1) - (p.2 - Complex.I • p.1) := rfl

private def inverseCayley (U : H ≃ₗᵢ[ℂ] H) : Operator ℂ H H :=
  (inverseGraphMap U).ker.toLinearPMap

private theorem inverseCayley_graph (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U) :
    (inverseCayley U).graph = (inverseGraphMap U).ker := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hx
  change inverseGraphMap U p = 0 at hp
  rw [inverseGraphMap_apply, hx, smul_zero, add_zero, sub_zero, sub_eq_zero] at hp
  exact hf _ hp

private theorem inverseCayley_mem_graph (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U)
    (x : H) : (x - U x, Complex.I • (x + U x)) ∈ (inverseCayley U).graph := by
  rw [inverseCayley_graph U hf]
  change inverseGraphMap U _ = 0
  rw [inverseGraphMap_apply]
  have hp : Complex.I • (x + U x) + Complex.I • (x - U x) = (2 * Complex.I) • x := by module
  have hm : Complex.I • (x + U x) - Complex.I • (x - U x) = (2 * Complex.I) • U x := by module
  rw [hp, hm, U.map_smul, sub_self]

private theorem inverseCayley_pair (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U) :
    Pair (inverseCayley U) U := by
  intro x
  have hx := (inverseCayley U).mem_graph x
  rw [inverseCayley_graph U hf] at hx
  exact sub_eq_zero.mp hx

private theorem pair_coordinates {S : Operator ℂ H H} {U : H ≃ₗᵢ[ℂ] H}
    (hp : Pair S U) (x : S.domain) :
    let t := (-Complex.I / 2) • plus S x
    t - U t = (x : H) ∧ Complex.I • (t + U t) = S x := by
  dsimp only
  rw [U.map_smul, hp x]
  dsimp [plus, minus]
  constructor <;> match_scalars <;> ring_nf <;> simp [Complex.I_sq]

private theorem difference_dense (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U) :
    Dense (((LinearMap.id - U.toLinearMap).range : Submodule ℂ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  have hh (x : H) : inner ℂ x y = inner ℂ (U x) y := by
    have h := hy (x - U x) ⟨x, rfl⟩
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have he : U y = y := by
    apply ext_inner_left ℂ
    intro x
    obtain ⟨w, rfl⟩ := U.surjective x
    rw [U.inner_map_map]
    exact hh w
  exact hf y he

private theorem inverseCayley_dense (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U) :
    DenselyDefined (inverseCayley U) := by
  apply (difference_dense U hf).mono
  rintro y ⟨x, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (inverseCayley_mem_graph U hf x)

private theorem inverseCayley_symmetric (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U) :
    IsSymmetric (inverseCayley U) := by
  let S := inverseCayley U
  have hd := inverseCayley_dense U hf
  have hp := inverseCayley_pair U hf
  have hi (x y : S.domain) : inner ℂ (S x) (y : H) = inner ℂ (x : H) (S y) := by
    obtain ⟨hx, hSx⟩ := pair_coordinates hp x
    obtain ⟨hy, hSy⟩ := pair_coordinates hp y
    rw [← hx, ← hSx, ← hy, ← hSy]
    simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, Complex.conj_I, U.inner_map_map]
    ring
  change DenselyDefined S ∧ S ≤ hilbertAdjoint S
  refine ⟨hd, ?_, ?_⟩
  · intro x hx
    exact (mem_hilbertAdjoint_domain_iff S hd x).mpr ⟨S ⟨x, hx⟩, fun y => hi y ⟨x, hx⟩⟩
  · intro x y hxy
    exact (hilbertAdjoint_apply_eq S hd y (S x) (fun z => by
      rw [← hxy]
      exact hi z x)).symm

private theorem inverseCayley_ranges (U : H ≃ₗᵢ[ℂ] H) (hf : NoFixedVectors U) :
    (plus (inverseCayley U)).range = ⊤ ∧ (minus (inverseCayley U)).range = ⊤ := by
  have hparam (x : H) := inverseCayley_mem_graph U hf x
  have hplus (x : H) : (2 * Complex.I) • x ∈ (plus (inverseCayley U)).range := by
    obtain ⟨w, hw, hSw⟩ := (inverseCayley U).mem_graph_iff.mp (hparam x)
    refine ⟨w, ?_⟩
    change inverseCayley U w + Complex.I • (w : H) = _
    rw [hw, hSw]
    module
  have hminus (x : H) : (2 * Complex.I) • U x ∈ (minus (inverseCayley U)).range := by
    obtain ⟨w, hw, hSw⟩ := (inverseCayley U).mem_graph_iff.mp (hparam x)
    refine ⟨w, ?_⟩
    change inverseCayley U w - Complex.I • (w : H) = _
    rw [hw, hSw]
    module
  constructor
  · apply top_unique; intro y _
    have h := hplus ((-Complex.I / 2) • y)
    have he : (2 * Complex.I) • ((-Complex.I / 2) • y) = y := by
      match_scalars
      ring_nf
      simp [Complex.I_sq]
    rwa [he] at h
  · apply top_unique; intro y _
    obtain ⟨x, hx⟩ := U.surjective ((-Complex.I / 2) • y)
    have h := hminus x
    rw [hx] at h
    have he : (2 * Complex.I) • ((-Complex.I / 2) • y) = y := by
      match_scalars
      ring_nf
      simp [Complex.I_sq]
    rwa [he] at h

theorem cayley_inverse_exists : InverseExpected := by
  intro H _ _ _ U hf
  refine ⟨inverseCayley U, ?_, inverseCayley_pair U hf⟩
  obtain ⟨hp, hm⟩ := inverseCayley_ranges U hf
  rw [plus_range] at hp
  rw [minus_range] at hm
  apply isSelfAdjoint_of_conjugate_shift_ranges _ (inverseCayley_symmetric U hf) (-Complex.I) hp
  simpa only [map_neg, Complex.conj_I, neg_neg] using hm

theorem cayley_inverse_formula : InverseFormulaExpected := by
  intro H _ _ _ S U hs hp
  have hg (x : H) : (x - U x, Complex.I • (x + U x)) ∈ S.graph := by
    obtain ⟨w, hw⟩ := plus_surjective hs ((2 * Complex.I) • x)
    have ht : (-Complex.I / 2) • plus S w = x := by
      rw [hw]
      match_scalars
      ring_nf
      simp [Complex.I_sq]
    have hc := pair_coordinates hp w
    dsimp only at hc
    rw [ht] at hc
    exact S.mem_graph_iff.mpr ⟨w, hc.1.symm, hc.2.symm⟩
  refine ⟨?_, hg⟩
  apply le_antisymm
  · intro x hx
    have hc := (pair_coordinates hp ⟨x, hx⟩).1
    exact ⟨(-Complex.I / 2) • plus S ⟨x, hx⟩, hc⟩
  · rintro y ⟨x, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (hg x)

private theorem pair_operator_unique {S T : Operator ℂ H H} {U : H ≃ₗᵢ[ℂ] H}
    (hs : IsSelfAdjoint S) (ht : IsSelfAdjoint T) (hp : Pair S U) (hq : Pair T U) :
    S = T := by
  have hle {A B : Operator ℂ H H} (hA : Pair A U) (hB : IsSelfAdjoint B)
      (hpB : Pair B U) : A.graph ≤ B.graph := by
    intro p hmem
    obtain ⟨w, hw, hAw⟩ := A.mem_graph_iff.mp hmem
    have hc := pair_coordinates hA w
    dsimp only at hc
    have hh := (cayley_inverse_formula B U hB hpB).2 ((-Complex.I / 2) • plus A w)
    rw [hc.1, hc.2] at hh
    simpa only [hw, hAw, Prod.mk.eta] using hh
  exact LinearPMap.eq_of_eq_graph (le_antisymm (hle hp ht hq) (hle hq hs hp))

private theorem pair_unitary_unique {S : Operator ℂ H H} {U V : H ≃ₗᵢ[ℂ] H}
    (hs : IsSelfAdjoint S) (hp : Pair S U) (hq : Pair S V) : U = V := by
  ext y
  obtain ⟨x, rfl⟩ := plus_surjective hs y
  exact (hp x).trans (hq x).symm

theorem cayley_correspondence : CorrespondenceExpected := by
  intro H _ _ _
  let f : SelfAdjointOperators H → UnitariesWithoutFixedVectors H := fun S =>
    ⟨(forward_exists S.val S.property).choose, (forward_exists S.val S.property).choose_spec.1⟩
  have hf (S : SelfAdjointOperators H) : Pair S.val (f S).val :=
    (forward_exists S.val S.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply pair_operator_unique S.property T.property (hf S)
    rw [h]
    exact hf T
  have hsurj : Function.Surjective f := by
    intro U
    obtain ⟨S, hs, hp⟩ := cayley_inverse_exists U.val U.property
    refine ⟨⟨S, hs⟩, ?_⟩
    apply Subtype.ext
    exact pair_unitary_unique hs (hf ⟨S, hs⟩) hp
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, hf, ?_⟩
  intro U
  apply cayley_inverse_formula (e.symm U).val U.val (e.symm U).property
  have h := hf (e.symm U)
  have he : f (e.symm U) = U := e.apply_symm_apply U
  rwa [he] at h

end ExpandedFA.Unbounded
