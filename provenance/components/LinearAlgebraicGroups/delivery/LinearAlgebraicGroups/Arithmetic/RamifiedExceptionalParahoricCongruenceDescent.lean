import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricCongruenceDescent
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceCongruence
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalUnramifiedCocycle
import Batteries.Tactic.OpenPrivate

/-! Higher congruence descent for the marked ramified parahoric. -/

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricCongruenceDescent

open CategoryTheory IsLocalRing ValuativeRel WithZero
open scoped CategoryTheory.MonObj TensorProduct ValuativeRel WithZero
open Specs.ExceptionalAffineBruhat (coefficientPoints)
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalIwahoriCongruence
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open Specs.IntegralSemisimpleModel
open Specs.RamifiedExceptionalAuxiliaryTower (UniformizerRootExtension)
open Specs.RamifiedExceptionalFaceCongruence
open Specs.RamifiedExceptionalParahoricCongruenceDescent

open RamifiedExceptionalAuxiliaryTower
  (normalizedValuation_surjective normalizedValuation_le_one normalizedValuation_of_uniformizerRoot)
open private normalizedUniformizer_generates uniformizerRoot_valuation_lt_one
  equal_indices_of_weighted_values from LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower
open private residueGaloisComparisonProof
  from LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalUnramifiedCocycle

universe u

noncomputable section

private theorem transportSimplexPoint {V : Type u} {I : Type*} [Finite I]
    [AddCommGroup V] [Module ℚ V] (r r' : RealCoordinates V) (vertex : I → V)
    (t : Weights I) (x : V)
    (hx : rationalPoint r x = simplexPoint r vertex t) :
    rationalPoint r' x = simplexPoint r' vertex t := by
  let e := r.symm.trans r'
  have hpt (z : V) : e (rationalPoint r z) = rationalPoint r' z := by
    simp [e, Specs.ExceptionalRealAlcove.rationalPoint]
  classical
  let _ := Fintype.ofFinite I
  unfold simplexPoint Specs.ExceptionalRealAlcove.simplexPoint at hx ⊢
  simp only [finsum_eq_sum_of_fintype] at hx ⊢
  simpa only [map_sum, LinearEquiv.map_smul, hpt] using congrArg e hx

/-- The distinguished root of a uniformizer is itself a uniformizer in the
degree-matched extension, including when the root is inseparable. -/
private theorem uniformizerRoot_isUniformizer {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {d : ℕ} {π : K} (U : UniformizerRootExtension K d π)
    (hπ : normalizedValuation K π = exp (-1 : ℤ)) :
    (valuation U.field).IsUniformizer (U.root : U.field) := by
  classical
  let ξ : U.field := U.root
  let v := normalizedValuation U.field
  let B := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite (R := K) ξ) U.generated
  have hgen : B.gen = ξ := PowerBasis.ofAdjoinEqTop_gen _ _
  have hdim : B.dim = d := B.finrank.symm.trans U.degree
  have hpow : ξ ^ B.dim = algebraMap K U.field π := hdim.symm ▸ U.power
  let c := log (v ξ)
  have hξnz : v ξ ≠ 0 := (map_ne_zero v).2 U.root.ne_zero
  have hc : c < 0 := by
    rw [← exp_lt_one_iff, exp_log hξnz]
    exact uniformizerRoot_valuation_lt_one π hπ ξ B.dim hpow
  obtain ⟨τ, hτ⟩ := normalizedValuation_surjective U.field (exp (-1 : ℤ))
  let a := B.basis.repr τ
  let z (i : Fin B.dim) := algebraMap K U.field (a i) * ξ ^ (i : ℕ)
  let m (i : Fin B.dim) : ℤ := (B.dim : ℤ) * (-log (normalizedValuation K (a i))) + i.val
  have hval (i : Fin B.dim) (hi : a i ≠ 0) : v (z i) = exp (c * m i) := by
    dsimp only [z]
    rw [map_mul, map_pow, normalizedValuation_of_uniformizerRoot π hπ ξ B.dim hpow _ hi]
    change v ξ ^ _ * v ξ ^ _ = _
    rw [← zpow_natCast, ← zpow_add₀ hξnz, ← exp_log hξnz, ← exp_zsmul]
    simp [m, c, mul_comm]
  have hsum : ∑ i, z i = τ := by
    simpa only [z, a, ← Algebra.smul_def, ← hgen, ← B.basis_eq_pow] using B.basis.sum_repr τ
  have hτ₀ : τ ≠ 0 := (map_ne_zero v).1 (hτ.trans_ne exp_ne_zero)
  have hnonempty : (Finset.univ : Finset (Fin B.dim)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero B.dim_ne_zero⟩, Finset.mem_univ _⟩
  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image Finset.univ (fun j => v (z j)) hnonempty
  have hj : a j ≠ 0 := by
    intro h
    have hzero (i : Fin B.dim) : z i = 0 :=
      by
        by_contra hne
        exact ((map_ne_zero v).2 hne)
          (le_antisymm ((hjmax i (Finset.mem_univ i)).trans (by simp [z, h])) zero_le)
    apply hτ₀
    rw [← hsum]
    simp [hzero]
  have hτval : v τ = v (z j) := by
    rw [← hsum]
    apply v.map_sum_eq_of_lt hjmem
    intro i hi
    have hij : i ≠ j := by simpa using hi
    by_cases ha : a i = 0
    · rw [show z i = 0 by simp [z, ha], map_zero, hval j hj]
      exact exp_pos
    · refine lt_of_le_of_ne (hjmax i (Finset.mem_univ i)) ?_
      intro he
      rw [hval i ha, hval j hj, exp_inj] at he
      exact hij (equal_indices_of_weighted_values i j _ _ (mul_left_cancel₀ hc.ne he))
  rw [hval j hj] at hτval
  have hlog : c = -1 := by
    rw [show v τ = exp (-1 : ℤ) from hτ, exp_inj] at hτval
    have hdiv : -c ∣ (1 : ℤ) := ⟨m j, by linarith only [hτval]⟩
    have := Int.le_of_dvd (by decide : (0 : ℤ) < 1) hdiv
    omega
  have hnorm : v ξ = exp (-1 : ℤ) := by rw [← exp_log hξnz]; exact congrArg exp hlog
  let ξ₀ : 𝒪[U.field] := ⟨ξ, (normalizedValuation_le_one ξ).mp (by
    change v ξ ≤ 1
    rw [hnorm]
    simp)⟩
  exact (valuation U.field).isUniformizer_of_maximalIdeal_eq_span
    (normalizedUniformizer_generates ξ₀ hnorm)

private def integralAction {Γ E : Type u} [Group Γ] [Field E] [ValuativeRel E]
    (ρ : Γ →* (E ≃+* E))
    (f : ∀ g, Specs.RamifiedExceptionalAuxiliaryTower.ValuedFieldMap (ρ g).toRingHom) :
    Γ →* (𝒪[E] ≃+* 𝒪[E]) where
  toFun g := RingEquiv.ofRingHom (f g).integers (f g⁻¹).integers
    (by
      apply RingHom.ext
      intro z
      apply Subtype.ext
      change ((f g).integers ((f g⁻¹).integers z) : E) = (z : E)
      rw [(f g).field_eq, (f g⁻¹).field_eq]
      change (ρ g * ρ g⁻¹) (z : E) = (z : E)
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl)
    (by
      apply RingHom.ext
      intro z
      apply Subtype.ext
      change ((f g⁻¹).integers ((f g).integers z) : E) = (z : E)
      rw [(f g⁻¹).field_eq, (f g).field_eq]
      change (ρ g⁻¹ * ρ g) (z : E) = (z : E)
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl)
  map_one' := by
    apply RingEquiv.ext
    intro z
    apply Subtype.ext
    change ((f 1).integers z : E) = (z : E)
    rw [(f 1).field_eq]
    change ρ 1 (z : E) = (z : E)
    rw [map_one]
    rfl
  map_mul' g h := by
    apply RingEquiv.ext
    intro z
    apply Subtype.ext
    change ((f (g * h)).integers z : E) = ((f g).integers ((f h).integers z) : E)
    rw [(f (g * h)).field_eq, (f g).field_eq, (f h).field_eq]
    change ρ (g * h) (z : E) = ρ g (ρ h (z : E))
    rw [map_mul, RingAut.mul_apply]

private def restrictFaceAction {Γ G : Type u} [Group Γ] [Group G]
    (ρ : Γ →* MulAut G) (H : Subgroup G) (stable : ∀ g (z : H), ρ g z.val ∈ H) :
    Γ →* MulAut H where
  toFun g :=
    { toFun := fun z => ⟨ρ g z.val, stable g z⟩
      invFun := fun z => ⟨ρ g⁻¹ z.val, stable g⁻¹ z⟩
      left_inv := fun z => Subtype.ext (by
        change (ρ g⁻¹ * ρ g) z.val = z.val
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun z => Subtype.ext (by
        change (ρ g * ρ g⁻¹) z.val = z.val
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl)
      map_mul' := fun z w => Subtype.ext ((ρ g).map_mul z.val w.val) }
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change ρ 1 z.val = z.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change ρ (g * h) z.val = ρ g (ρ h z.val)
    rw [map_mul, MulAut.mul_apply]

private theorem depthOne_iff_residue {K : Type u} [Field K] [ValuativeRel K]
    (G : IntegralGroup.{u}) (z : IntegralPoints G (localIntegers K)) :
    changeRingHom G (congruenceHom (localIntegers K) 1) z = 1 ↔
      changeRingHom G (Specs.ExceptionalIwahoriImageComparison.residueReduction K) z = 1 := by
  let R := localIntegers K
  let e : congruenceRing R 1 ≅ residueRing R :=
    CommAlgCat.isoMk (Ideal.quotientEquivAlgOfEq Integers.{u} (pow_one (maximalIdeal R)))
  have he : congruenceHom R 1 ≫ e.hom = residueHom R := rfl
  have hred : residueHom R = Specs.ExceptionalIwahoriImageComparison.residueReduction K := by
    ext z
    rfl
  have hinj : Function.Injective (changeRingHom G e.hom) :=
    ((integralPointFunctor G).mapIso e).groupIsoToMulEquiv.injective
  rw [← hred, ← he]
  change _ ↔ ((integralPointFunctor G).map (congruenceHom R 1 ≫ e.hom)).hom z = 1
  rw [Functor.map_comp]
  change _ ↔ changeRingHom G e.hom (changeRingHom G (congruenceHom R 1) z) = 1
  rw [← (changeRingHom G e.hom).map_one, hinj.eq_iff]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Correct a cocycle already trivial in the actual scaled residue group,
over the given finite unramified stage. -/
theorem parahoricCongruenceDescent : ParahoricCongruenceDescent.{u} := by
  classical
  intro F L S fF fL fS aFL aFS vF tF lfF vL tL lfL vFL fdL galL sepS sepFS
    σ hdegree hσ hram D M R numbering hnumbering hspan hdiagram A X J hJ
    k₀ t x ht hct hx π hπ d hd y hy P k scale act a ha hred
  let T := (X k).compositum
  let U := P.auxiliary.extension k
  have hx' : rationalPoint (X k).building.realization.coordinates x =
      simplexPoint (X k).building.realization.coordinates (X k).building.realization.vertex t := by
    have hver : (X k₀).building.realization.vertex = (X k).building.realization.vertex := by
      funext i
      exact (X k).building.realization.vertex_unique i _ ((X k₀).building.realization.vertex_marked i)
    rw [hver] at hx
    let _ := (X k).building.realization.finite_types
    exact transportSimplexPoint _ _ _ _ _ hx
  have hξ := uniformizerRoot_isUniformizer U ((T.unramified (π : L)).trans hπ)
  let ξ : 𝒪[U.field] := ⟨U.root, hξ.val_lt_one.le⟩
  let I := integralAction (P.auxiliary.action k) (P.auxiliary.actionValued k)
  obtain ⟨ρ, hρ, _, _⟩ := (X k).coefficients
  let ρ₀ := restrictFaceAction ρ ((X k).parahoric J)
    (fun g z => hρ g z.val ▸ scale.coefficient_mem g z)
  have hact (g) (z : (X k).parahoric J) : ρ₀ g z = act g z :=
    Subtype.ext (hρ g z.val)
  let V : ScaledFace T (X k).folded J x :=
    { E := U.field
      d := d
      d_pos := hd
      uniformizer := π
      uniformizer_value := hπ
      xi := ξ
      xi_uniformizer := hξ
      xi_power := U.power
      unchanged_residue := (Nat.card_congr (Equiv.ofBijective _ U.residue_bijective)).symm
      cocharacter := y
      cocharacter_eq := hy
      coefficient := P.auxiliary.action k
      coefficient_extends := P.auxiliary.action_extends k
      coefficient_fixes_xi := P.auxiliary.action_fixes_root k
      integralCoefficient := I
      integralCoefficient_eq := fun g z => (P.auxiliary.actionValued k g).field_eq z
      action := ρ₀
      action_eq := fun g z => hρ g z.val
      point := scale.integral
      point_eq := fun z => by
        have heq : Units.mk0 (ξ : U.field) hξ.ne_zero = U.root := Units.ext rfl
        rw [heq]
        exact DFunLike.congr_fun scale.conjugation z
      point_equivariant := fun g z => by
        change scale.integral (ρ₀ g z) =
          changeRingHom M.group (integralRingMap (I g).toRingHom) (scale.integral z)
        rw [hact g z]
        let b := P.auxiliary.action k g
        let b₀ : Specs.RamifiedExceptionalLocalFaceCoordinates.ValuedFieldMap b.toRingHom :=
          { integers := (P.auxiliary.actionValued k g).integers
            isLocal := (P.auxiliary.actionValued k g).isLocal
            field_eq := (P.auxiliary.actionValued k g).field_eq }
        exact (scale.equivariant g b b₀
          (P.auxiliary.action_extends k g) (P.auxiliary.action_fixes_root k g) z).1 }
  have hker (z : (X k).parahoric J) : z ∈ congruenceSubgroup V 1 ↔ scale.reduction z = 1 :=
    depthOne_iff_residue M.group (scale.integral z)
  obtain ⟨e, he⟩ := residueGaloisComparisonProof F k.field k.unramified
  have hgal (g : Gal(k.field/F)) (z w : 𝒪[k.field]) (hw : (w : k.field) = g (z : k.field)) :
      e g (residue _ z) = residue _ w := by
    obtain ⟨w', hw', h⟩ := he g z
    exact h.trans (congrArg (residue _) (Subtype.ext (hw'.trans hw.symm)))
  obtain ⟨layers, _⟩ := RamifiedExceptionalFaceCongruence.ramifiedFaceCongruenceLayers
    F L k.field k.unramified σ hdegree hσ hram R numbering hnumbering hspan hdiagram
    T A (X k).folded (X k).coefficients (X k).building J hJ x t ht hct hx' V e hgal
  obtain ⟨_, _, _, _, _, _, correct⟩ := layers
  obtain ⟨b, hb⟩ := correct a (fun g h => (ha g h).trans (congrArg (a g * ·) (hact g (a h)).symm))
    (fun g => (hker (a g)).mpr (hred g))
  refine ⟨⟨b.val, (hker b.val).mp b.property⟩, fun g => ?_⟩
  exact (hb g).trans (congrArg (fun q => b.val * q⁻¹) (hact g b.val))

end

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricCongruenceDescent
