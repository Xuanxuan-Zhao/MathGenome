import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.BorelSubalgebras
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactFlagOrbit
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SolvableProjectiveFixed
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section

/-! LA-F06: the algebraic assertions follow from the trace criterion and
the opposite-root orthogonality of the Killing form. For conjugacy, the
Plücker map takes the compact flag orbit into the projectivized exterior
power, where the solvable fixed-point lemma applies. -/

set_option backward.isDefEq.respectTransparency false

universe u

namespace LieAlgebrasAndRepresentations.BorelSubalgebras

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit
open Specs.LieAlgebrasAndRepresentations.CompactConjugation (PositiveRoot)
open Specs.LieAlgebrasAndRepresentations.BorelSubalgebras
open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Borel subalgebra is a maximal solvable Lie subalgebra. -/
abbrev IsBorel := @Specs.LieAlgebrasAndRepresentations.BorelSubalgebras.IsBorel

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private abbrev positives (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :
    Submodule ℂ L :=
  ⨆ α : PositiveRoot H φ, rootSpace H α.val

private abbrev negatives (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :
    Submodule ℂ L :=
  ⨆ α : {a : Module.Dual ℂ H // a ∈ rootSet H ∧ φ a < 0}, rootSpace H α.val

private theorem bracket_mem_positives (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) {x y : L}
    (hx : x ∈ borel H φ) (hy : y ∈ borel H φ) :
    ⁅x, y⁆ ∈ positives H φ := by
  let bracket : L →ₗ[ℂ] L →ₗ[ℂ] L := (LieAlgebra.ad ℂ L).toLinearMap
  have hweights (α β : Module.Dual ℂ H) (hαβ : 0 < φ (α + β)) :
      Submodule.map₂ bracket (rootSpace H α) (rootSpace H β) ≤ positives H φ := by
    have hne : α + β ≠ 0 := by
      intro he
      simp [he] at hαβ
    by_cases hr : α + β ∈ rootSet H
    · exact (Submodule.map₂_le.mpr fun x hx y hy =>
        rootSpace_bracket H α β x y hx hy).trans
        (le_iSup (fun γ : PositiveRoot H φ => rootSpace H γ.val) ⟨α + β, hr, hαβ⟩)
    · exact Submodule.map₂_le.mpr fun x hx y hy => by
        have h := rootSpace_bracket H α β x y hx hy
        rw [rootSpace_eq_bot_of_not_mem H _ hne hr, Submodule.mem_bot] at h
        rw [show bracket x y = ⁅x, y⁆ from rfl, h]
        exact Submodule.zero_mem _
  change x ∈ H.toSubmodule ⊔ positives H φ at hx
  change y ∈ H.toSubmodule ⊔ positives H φ at hy
  apply (show Submodule.map₂ bracket (H.toSubmodule ⊔ positives H φ)
      (H.toSubmodule ⊔ positives H φ) ≤ positives H φ from ?_)
    (Submodule.apply_mem_map₂ bracket hx hy)
  rw [Submodule.map₂_sup_left, Submodule.map₂_sup_right, Submodule.map₂_sup_right]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · letI : IsLieAbelian H := hH.1.1
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    have he : ⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆ = 0 := trivial_lie_zero H H _ _
    have he' : bracket x y = 0 := congrArg Subtype.val he
    rw [he']
    exact Submodule.zero_mem _
  · rw [Submodule.map₂_iSup_right]
    refine iSup_le fun α => ?_
    rw [← rootSpace_zero hss H hH]
    exact hweights 0 α.val (by simpa using α.property.2)
  · rw [Submodule.map₂_iSup_left]
    refine iSup_le fun α => ?_
    rw [← rootSpace_zero hss H hH]
    exact hweights α.val 0 (by simpa using α.property.2)
  · rw [Submodule.map₂_iSup_left]
    refine iSup_le fun α => ?_
    rw [Submodule.map₂_iSup_right]
    refine iSup_le fun β => hweights α.val β.val ?_
    rw [map_add]
    exact add_pos α.property.2 β.property.2

omit [FiniteDimensional ℂ L] in
private theorem pos_le_borel (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :
    positives H φ ≤ borel H φ := le_sup_right

private def standard (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) : LieSubalgebra ℂ L :=
  { borel H φ with
    lie_mem' := fun hx hy => pos_le_borel H φ (bracket_mem_positives hss H hH φ hx hy) }

private theorem killing_borel_positive (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    {x y : L} (hx : x ∈ borel H φ) (hy : y ∈ positives H φ) :
    killingForm ℂ L x y = 0 := by
  let K := killingForm ℂ L
  change x ∈ H.toSubmodule ⊔ positives H φ at hx
  have hk (α : PositiveRoot H φ) (z : L) (hz : z ∈ rootSpace H α.val) :
      borel H φ ≤ LinearMap.ker (K.flip z) := by
    change H.toSubmodule ⊔ positives H φ ≤ _
    refine sup_le (fun x hx => ?_) (iSup_le fun β x hx => ?_)
    · rw [← rootSpace_zero hss H hH] at hx
      exact rootSpace_killing_orthogonal H 0 α.val x z hx hz (by simpa using α.property.1.1)
    · refine rootSpace_killing_orthogonal H β.val α.val x z hx hz fun he => ?_
      have hr : 0 < φ (β.val + α.val) := by
        rw [map_add]
        exact add_pos β.property.2 α.property.2
      simp [he] at hr
  exact (iSup_le (f := fun α : PositiveRoot H φ => rootSpace H α.val)
    (a := LinearMap.ker (K x)) fun α z hz => hk α z hz hx) hy

private theorem borel_sup_negatives (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (hss : IsSemisimple ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    (hφ : ∀ α ∈ rootSet H, φ α ≠ 0) :
    borel H φ ⊔ negatives H φ = ⊤ := by
  apply eq_top_iff.mpr
  rw [← iSup_rootSpace_eq_top H hH.1]
  refine iSup_le fun α => ?_
  by_cases hzero : α = 0
  · subst α
    rw [rootSpace_zero hss H hH]
    exact (le_sup_left : H.toSubmodule ≤ borel H φ).trans le_sup_left
  by_cases hroot : α ∈ rootSet H
  · rcases lt_or_gt_of_ne (hφ α hroot) with hn | hp
    · exact (le_iSup (fun β : {a : Module.Dual ℂ H // a ∈ rootSet H ∧ φ a < 0} =>
        rootSpace H β.val) ⟨α, hroot, hn⟩).trans le_sup_right
    · exact (le_iSup (fun β : PositiveRoot H φ => rootSpace H β.val)
        ⟨α, hroot, hp⟩).trans ((pos_le_borel H φ).trans le_sup_left)
  · rw [rootSpace_eq_bot_of_not_mem H α hzero hroot]
    exact bot_le

private theorem mem_borel_of_killing_positive (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (hss : IsSemisimple ℂ L)
    (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) (hφ : ∀ α ∈ rootSet H, φ α ≠ 0)
    {x : L} (hx : ∀ y ∈ positives H φ, killingForm ℂ L x y = 0) :
    x ∈ borel H φ := by
  let K := killingForm ℂ L
  let I := {a : Module.Dual ℂ H // a ∈ rootSet H ∧ φ a < 0}
  have hx' : x ∈ borel H φ ⊔ negatives H φ := by
    rw [borel_sup_negatives H hH hss φ hφ]
    trivial
  obtain ⟨b, hb, n, hn, rfl⟩ := Submodule.mem_sup.mp hx'
  have hneg (β : Module.Dual ℂ H) (hβ : φ β ≤ 0) (z : L) (hz : z ∈ rootSpace H β) :
      K n z = 0 := by
    apply (iSup_le (f := fun α : I => rootSpace H α.val)
      (a := LinearMap.ker (K.flip z)) ?_) hn
    intro α y hy
    refine rootSpace_killing_orthogonal H α.val β y z hy hz fun he => ?_
    have hr : φ (α.val + β) < 0 := by
      rw [map_add]
      exact add_neg_of_neg_of_nonpos α.property.2 hβ
    simp [he] at hr
  have hzero : n = 0 := (semisimple_iff_killingForm_nondegenerate ℂ L).mp hss |>.1 n
    (fun y => (show (⊤ : Submodule ℂ L) ≤ LinearMap.ker (K n) from by
      rw [← borel_sup_negatives H hH hss φ hφ, show borel H φ = H.toSubmodule ⊔ positives H φ by rfl]
      refine sup_le (sup_le ?_ ?_) (iSup_le fun α z hz => hneg α.val α.property.2.le z hz)
      · rw [← rootSpace_zero hss H hH]
        exact fun z hz => hneg 0 (by simp) z hz
      · intro z hz
        change K n z = 0
        simpa only [K, map_add, LinearMap.add_apply, killing_borel_positive hss H hH φ hb hz,
          zero_add] using hx z hz) (Submodule.mem_top : y ∈ (⊤ : Submodule ℂ L)))
  simpa [hzero] using hb

private theorem positive_commutator (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) {A : LieSubalgebra ℂ L}
    (hA : borel H φ ≤ A.toSubmodule) (α : PositiveRoot H φ)
    (z : L) (hz : z ∈ rootSpace H α.val) :
    ∃ z' : A, (z' : L) = z ∧ z' ∈ LieAlgebra.derivedSeries ℂ A 1 := by
  obtain ⟨h, hh⟩ : ∃ h : H, α.val h ≠ 0 := by
    by_contra! h
    exact α.property.1.1 (LinearMap.ext (by simpa using h))
  have hhA : (h : L) ∈ A := hA (Submodule.mem_sup_left h.property)
  have hzA : z ∈ A := hA (pos_le_borel H φ (Submodule.mem_iSup_of_mem α hz))
  refine ⟨⟨z, hzA⟩, rfl, ?_⟩
  have hm : ⁅(⟨(h : L), hhA⟩ : A), (⟨z, hzA⟩ : A)⁆ ∈ LieAlgebra.derivedSeries ℂ A 1 := by
    change _ ∈ (LieAlgebra.derivedSeries ℂ A 1).toLieSubalgebra.toSubmodule
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  have he : ⁅(⟨(h : L), hhA⟩ : A), (⟨z, hzA⟩ : A)⁆ = α.val h • (⟨z, hzA⟩ : A) :=
    Subtype.ext ((mem_rootSpace H α.val z).mp hz h)
  rw [he] at hm
  simpa [smul_smul, inv_mul_cancel₀ hh] using
    (LieAlgebra.derivedSeries ℂ A 1).smul_mem (α.val h)⁻¹ hm

private theorem solvable_le_standard (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (hss : IsSemisimple ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    (hφ : ∀ α ∈ rootSet H, φ α ≠ 0) (A : LieSubalgebra ℂ L) [IsSolvable A]
    (hA : borel H φ ≤ A.toSubmodule) : A ≤ standard hss H hH φ := by
  intro x hx
  apply mem_borel_of_killing_positive H hH hss φ hφ
  have hk : positives H φ ≤ LinearMap.ker (killingForm ℂ L x) := by
    refine iSup_le fun α z hz => ?_
    obtain ⟨z', rfl, hz'⟩ := positive_commutator H φ hA α z hz
    rw [LinearMap.mem_ker, killingForm_symmetric]
    exact traceForm_eq_zero_of_solvable_of_isAlgClosed (V := L) z' hz' (⟨x, hx⟩ : A)
  exact fun z hz => hk hz

private theorem standard_self_normalizing (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    (hφ : ∀ α ∈ rootSet H, φ α ≠ 0) : (standard hss H hH φ).normalizer = standard hss H hH φ := by
  apply le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  apply mem_borel_of_killing_positive H hH hss φ hφ
  have hk : positives H φ ≤ LinearMap.ker (killingForm ℂ L x) := by
    refine iSup_le fun α z hz => ?_
    obtain ⟨h, hh⟩ : ∃ h : H, α.val h ≠ 0 := by
      by_contra! h
      exact α.property.1.1 (LinearMap.ext (by simpa using h))
    have hhB : (h : L) ∈ standard hss H hH φ := Submodule.mem_sup_left h.property
    have hb := (LieSubalgebra.mem_normalizer_iff _ x).mp hx h hhB
    have hk := killing_borel_positive hss H hH φ hb (Submodule.mem_iSup_of_mem α hz)
    rw [killingForm_invariant, (mem_rootSpace H α.val z).mp hz h,
      map_smul, smul_eq_mul, mul_eq_zero] at hk
    exact hk.resolve_left hh
  exact fun z hz => hk hz

private theorem standard_solvable (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :
    IsSolvable (standard hss H hH φ) := by
  let B := standard hss H hH φ
  let adB : B →ₗ⁅ℂ⁆ Module.End ℂ L := (LieAlgebra.ad ℂ L).comp B.incl
  have hfaithful : Function.Injective adB := by
    apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective adB.toLinearMap)
    rw [eq_bot_iff]
    intro x hx
    apply (Submodule.mem_bot ℂ).2
    apply Subtype.ext
    apply ((semisimple_iff_killingForm_nondegenerate ℂ L).1 hss).1
    intro y
    change LinearMap.trace ℂ L (adB x * LieAlgebra.ad ℂ L y) = 0
    rw [show adB x = 0 from hx, zero_mul, map_zero]
  have : IsSolvable adB.range := solvable_of_trace_orthogonal adB.range (by
    intro x hx y
    obtain ⟨y', hy'⟩ := adB.surjective_rangeRestrict y
    obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ LieAlgebra.derivedSeries ℂ B 1, adB.rangeRestrict x' = x := by
      rw [← LieIdeal.derivedSeries_map_eq 1 adB.surjective_rangeRestrict] at hx
      obtain ⟨q, hq⟩ := LieIdeal.mem_map_of_surjective adB.surjective_rangeRestrict hx
      exact ⟨q, q.property, hq⟩
    have hxpos : (x' : L) ∈ positives H φ := by
      change x' ∈ (positives H φ).comap B.incl.toLinearMap
      change x' ∈ (LieAlgebra.derivedSeries ℂ B 1).toLieSubalgebra.toSubmodule at hx'
      rw [LieAlgebra.coe_derivedSeries_one_eq] at hx'
      apply ((Submodule.span_le (s := {⁅a, b⁆ | (a : B) (b : B)})).mpr ?_) hx'
      rintro z ⟨a, b, rfl⟩
      exact bracket_mem_positives hss H hH φ a.property b.property
    rw [← hx'', ← hy']
    change killingForm ℂ L (x' : L) (y' : L) = 0
    rw [killingForm_symmetric]
    exact killing_borel_positive hss H hH φ y'.property hxpos)
  exact (adB.equivRangeOfInjective hfaithful).injective.lieAlgebra_isSolvable
    (f := (adB.equivRangeOfInjective hfaithful).toLieHom)

theorem standard_borel : standardBorelType := by
  intro L _ _ _ hss H hH φ hφ
  refine ⟨standard hss H hH φ, rfl, ⟨standard_solvable hss H hH φ, ?_⟩,
    standard_self_normalizing hss H hH φ hφ⟩
  intro A hA hBA
  exact solvable_le_standard H hH hss φ hφ A hBA


section ExteriorPower

open scoped LinearAlgebra.Projectivization
open exteriorPower

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable {d : ℕ}

private def exteriorCoordinates (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) :=
  (Module.finBasis ℂ (⋀[ℂ]^d V)).equivFun

private local instance : NormedAddCommGroup (⋀[ℂ]^d V) :=
  NormedAddCommGroup.induced _ _ (exteriorCoordinates V d).toAddMonoidHom
    (exteriorCoordinates V d).injective

private local instance : NormedSpace ℂ (⋀[ℂ]^d V) :=
  NormedSpace.induced ℂ _ _ (exteriorCoordinates V d).toLinearMap

private theorem continuous_exteriorForm :
    Continuous (ιMulti ℂ d : (Fin d → V) → (⋀[ℂ]^d V)) := by
  classical
  let b := Module.finBasis ℂ V
  have he (v : Fin d → V) :
      ιMulti ℂ d v = ∑ f : Fin d → Fin (Module.finrank ℂ V),
        (∏ i, b.coord (f i) (v i)) • ιMulti ℂ d (fun i => b (f i)) := by
    have hv : v = fun i => ∑ j, b.coord j (v i) • b j := by
      funext i
      exact (b.sum_repr (v i)).symm
    conv_lhs => rw [hv]
    change (ιMulti ℂ d).toMultilinearMap _ = _
    rw [MultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro f _
    exact (ιMulti ℂ d).toMultilinearMap.map_smul_univ (fun i => b.coord (f i) (v i)) _
  rw [show (ιMulti ℂ d : (Fin d → V) → (⋀[ℂ]^d V)) = _ from funext he]
  exact continuous_finsetSum _ fun f _ =>
    (continuous_finsetProd _ fun i _ =>
      (LinearMap.toContinuousLinearMap (b.coord (f i))).continuous.comp (continuous_apply i)).smul
      continuous_const

private def exteriorForm : V [⋀^Fin d]→L[ℂ] (⋀[ℂ]^d V) where
  toContinuousMultilinearMap :=
    { (ιMulti ℂ d).toMultilinearMap with cont := continuous_exteriorForm }
  map_eq_zero_of_eq' := (ιMulti ℂ d).map_eq_zero_of_eq'

private def exteriorDerivative (d : ℕ) : Module.End ℂ V →ₗ[ℂ] Module.End ℂ (⋀[ℂ]^d V) :=
  (alternatingMapLinearEquiv (R := ℂ) (n := d)).toLinearMap.comp
    ((ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ)).comp
      (((exteriorForm (V := V) (d := d)).fderivCompContinuousLinearMap
        (ContinuousLinearMap.id ℂ V)).toLinearMap.comp
        (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := V) (F' := V)).toLinearMap))

private theorem exteriorDerivative_apply (A : Module.End ℂ V) (v : Fin d → V) :
    exteriorDerivative d A (ιMulti ℂ d v) =
      ∑ i, ιMulti ℂ d (Function.update v i (A (v i))) := by
  classical
  simp only [exteriorDerivative, LinearMap.comp_apply, LinearEquiv.coe_coe,
    alternatingMapLinearEquiv_apply_ιMulti]
  change ((exteriorForm (V := V) (d := d)).fderivCompContinuousLinearMap _ _ : V [⋀^Fin d]→L[ℂ] _) v = _
  rw [ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (ιMulti ℂ d)
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h]

private def exteriorLieHom (d : ℕ) : Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (⋀[ℂ]^d V) where
  toLinearMap := exteriorDerivative d
  map_lie' := by
    intro A B
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorDerivative d ⁅A, B⁆ (ιMulti ℂ d v) =
      ⁅exteriorDerivative d A, exteriorDerivative d B⁆ (ιMulti ℂ d v)
    let ins (T : Module.End ℂ V) (w : Fin d → V) (i : Fin d) :=
      Function.update w i (T (w i))
    rw [Ring.lie_def, Ring.lie_def]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, exteriorDerivative_apply,
      map_sum]
    change (∑ i, ιMulti ℂ d (ins ⁅A, B⁆ v i)) =
      (∑ i, ∑ j, ιMulti ℂ d (ins A (ins B v i) j)) -
      ∑ i, ∑ j, ιMulti ℂ d (ins B (ins A v i) j)
    rw [Finset.sum_comm (f := fun i j => ιMulti ℂ d (ins B (ins A v i) j)),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp only [ins, Function.update_self, Function.update_idem, Ring.lie_def,
        LinearMap.sub_apply, Module.End.mul_apply, AlternatingMap.map_update_sub]
    · intro j _ hji
      have hij := Ne.symm hji
      simp only [ins, Function.update_of_ne hji, Function.update_of_ne hij]
      rw [Function.update_comm hij, sub_self]
    · simp

omit [FiniteDimensional ℂ V] in
private theorem wedge_ne_zero (v : Fin d → V) (hv : LinearIndependent ℂ v) :
    ιMulti ℂ d v ≠ 0 := by
  let s := Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin d)).toOrderEmbedding)
  have h := (ιMulti_family_linearIndependent_field (n := d) hv).ne_zero s
  simpa [ιMulti_family, s] using h

private def frameProjective (v : Frame V d) : ℙ ℂ (⋀[ℂ]^d V) :=
  Projectivization.mk ℂ (ιMulti ℂ d v.val) (wedge_ne_zero v.val v.property)

private def subspaceFrame (P : Grassmannian V d) : Frame V d :=
  ⟨P.subspace.subtype ∘ Module.finBasisOfFinrankEq ℂ P.subspace P.finrank_eq,
    (Module.finBasisOfFinrankEq ℂ P.subspace P.finrank_eq).linearIndependent.map'
      P.subspace.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)⟩

private theorem frameSpan_subspaceFrame (P : Grassmannian V d) :
    frameSpan (subspaceFrame P) = P := by
  apply Grassmannian.ext
  change Submodule.span ℂ (Set.range
    (P.subspace.subtype ∘ Module.finBasisOfFinrankEq ℂ P.subspace P.finrank_eq)) = P.subspace
  rw [Set.range_comp (P.subspace.subtype : P.subspace → V), ← Submodule.map_span,
    Module.Basis.span_eq]
  simp

private def plucker (P : Grassmannian V d) : ℙ ℂ (⋀[ℂ]^d V) :=
  frameProjective (subspaceFrame P)

private theorem frameProjective_eq (v w : Frame V d) (hvw : frameSpan v = frameSpan w) :
    frameProjective v = frameProjective w := by
  classical
  let P := (frameSpan w).subspace
  let b : Module.Basis (Fin d) ℂ P := Module.Basis.span w.property
  let alt := (ιMulti ℂ d (M := V)).compLinearMap P.subtype
  have halt : alt = b.det.smulRight (alt b) := by
    apply b.ext_alternating
    intro f hf
    let σ : Equiv.Perm (Fin d) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    change alt (b ∘ σ) = b.det.smulRight (alt b) (b ∘ σ)
    rw [AlternatingMap.map_perm]
    simp only [AlternatingMap.smulRight_apply, b.det.map_perm, b.det_self, Units.smul_def,
      ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, mul_one]
  have hv (i : Fin d) : v.val i ∈ P := by
    change v.val i ∈ (frameSpan w).subspace
    rw [← hvw]
    exact Submodule.subset_span (Set.mem_range_self i)
  let vv (i : Fin d) : P := ⟨v.val i, hv i⟩
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨b.det vv, ?_⟩
  have he := congrArg (fun f : P [⋀^Fin d]→ₗ[ℂ] (⋀[ℂ]^d V) => f vv) halt
  change ιMulti ℂ d v.val = b.det vv • ιMulti ℂ d (fun i => ((b i : P) : V)) at he
  have hb : (fun i => ((b i : P) : V)) = w.val := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply w.property i)
  rw [hb] at he
  exact he.symm

private theorem plucker_frameSpan (v : Frame V d) :
    plucker (frameSpan v) = frameProjective v :=
  frameProjective_eq _ _ (frameSpan_subspaceFrame _)

private theorem continuous_plucker : Continuous (plucker : Grassmannian V d → ℙ ℂ (⋀[ℂ]^d V)) := by
  apply frameSpan_isQuotientMap.continuous_iff.mpr
  change Continuous (fun v : Frame V d => plucker (frameSpan v))
  simp only [plucker_frameSpan]
  exact (SolvableProjectiveFixed.continuous_projective_mk (V := (⋀[ℂ]^d V))).comp
    ((continuous_exteriorForm.comp continuous_subtype_val).subtype_mk
      (fun v => wedge_ne_zero v.val v.property))

private theorem mem_span_iff_wedge (v : Frame V d) (x : V) :
    x ∈ (frameSpan v).subspace ↔ ιMulti ℂ (d + 1) (Fin.cons x v.val) = 0 := by
  change x ∈ Submodule.span ℂ (Set.range v.val) ↔ _
  constructor
  · intro hx
    apply (ιMulti ℂ (d + 1)).map_linearDependent
    intro h
    exact (linearIndependent_finCons.mp h).2 hx
  · contrapose!
    exact fun hx => wedge_ne_zero _ (v.property.finCons hx)

private theorem plucker_injective : Function.Injective (plucker : Grassmannian V d → ℙ ℂ (⋀[ℂ]^d V)) := by
  intro P Q h
  let v := subspaceFrame P
  let w := subspaceFrame Q
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h
  change a • ιMulti ℂ d w.val = ιMulti ℂ d v.val at ha
  apply Grassmannian.ext
  rw [← frameSpan_subspaceFrame P, ← frameSpan_subspaceFrame Q]
  ext x
  rw [mem_span_iff_wedge, mem_span_iff_wedge]
  let F := alternatingMapLinearEquiv ((ιMulti ℂ (d + 1) (M := V)).curryLeft x)
  have hF (v : Fin d → V) : F (ιMulti ℂ d v) = ιMulti ℂ (d + 1) (Fin.cons x v) := by
    rw [alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.curryLeft_apply_apply]
    rfl
  change (a : ℂ) • ιMulti ℂ d w.val = ιMulti ℂ d v.val at ha
  rw [← hF, ← hF, ← ha, map_smul, smul_eq_zero]
  exact or_iff_right (Units.ne_zero a)

private theorem frameSpan_map (g : (End V)ˣ) (P : Grassmannian V d) :
    frameSpan ⟨fun i => g.val ((subspaceFrame P).val i),
      (subspaceFrame P).property.map' (unitEquiv g).toLinearMap
        (LinearMap.ker_eq_bot.mpr (unitEquiv g).injective)⟩ =
      ⟨P.subspace.map g.val.toLinearMap, by
        exact (P.subspace.equivMapOfInjective (unitEquiv g).toLinearMap
          (unitEquiv g).injective).symm.finrank_eq.trans P.finrank_eq⟩ := by
  apply Grassmannian.ext
  change Submodule.span ℂ (Set.range (g.val.toLinearMap ∘ (subspaceFrame P).val)) =
    P.subspace.map g.val.toLinearMap
  rw [Set.range_comp (g.val.toLinearMap : V → V), ← Submodule.map_span]
  exact congrArg (Submodule.map g.val.toLinearMap)
    (congrArg Grassmannian.subspace (frameSpan_subspaceFrame P))

open SolvableProjectiveFixed

private theorem hasDerivAt_exterior_curve (A : Module.End ℂ V) (v : Fin d → V) (t : ℂ) :
    HasDerivAt (fun z => ιMulti ℂ d (fun i => exponential A z (v i)))
      (exteriorDerivative d A (ιMulti ℂ d (fun i => exponential A t (v i)))) t := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  let T : End V := LinearMap.toContinuousLinearMap A
  have h (i : Fin d) :
      HasDerivAt (fun z => exponential A z (v i)) (A (exponential A t (v i))) t := by
    exact (ContinuousLinearMap.apply ℂ V (v i)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_exp_smul_const' T t)
  let w (z : ℂ) (i : Fin d) := exponential A z (v i)
  have hw : HasDerivAt w (fun i => A (w t i)) t := hasDerivAt_pi.mpr h
  rw [exteriorDerivative_apply]
  have hd := ((exteriorForm (V := V) (d := d)).hasFDerivAt (w t)).comp_hasDerivAt t hw
  rw [ContinuousMultilinearMap.linearDeriv_apply] at hd
  exact hd

private theorem exterior_exponential_wedge (A : Module.End ℂ V) (v : Fin d → V) (z : ℂ) :
    ιMulti ℂ d (fun i => exponential A z (v i)) =
      exponential (exteriorDerivative d A) z (ιMulti ℂ d v) := by
  have : CompleteSpace (⋀[ℂ]^d V) := FiniteDimensional.complete ℂ _
  let D : End (⋀[ℂ]^d V) := LinearMap.toContinuousLinearMap (exteriorDerivative d A)
  let f (t : ℂ) := ιMulti ℂ d (fun i => exponential A t (v i))
  let g (t : ℂ) := NormedSpace.exp ((-t) • D) (f t)
  have hg (t : ℂ) : HasDerivAt g 0 t := by
    have ht := (hasDerivAt_exp_smul_const D (-t)).scomp t (hasDerivAt_neg t)
    have hf := hasDerivAt_exterior_curve A v t
    have hd := ht.clm_apply hf
    convert hd using 1
    · rfl
    · rw [neg_one_smul]
      change 0 = -(NormedSpace.exp (-t • D) (D (f t))) +
        NormedSpace.exp (-t • D) (D (f t))
      simp
  have he := is_const_of_deriv_eq_zero
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) z 0
  have hcancel : NormedSpace.exp (z • D) * NormedSpace.exp (-z • D) = 1 := by
    let : NormedAlgebra ℚ (End (⋀[ℂ]^d V)) := NormedAlgebra.restrictScalars ℚ ℂ _
    rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.refl (z • D)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have he' := congrArg (fun y => NormedSpace.exp (z • D) y) he
  change (NormedSpace.exp (z • D) * NormedSpace.exp (-z • D)) (f z) =
    NormedSpace.exp (z • D) (NormedSpace.exp (-(0 : ℂ) • D) (f 0)) at he'
  rw [hcancel] at he'
  simpa [f, D, exponential, NormedSpace.exp_zero] using he'

open ClosedMatrixGroups
open scoped Topology

section CompactNorm

variable [c : InnerProductSpace.Core ℂ L]
attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup
  InnerProductSpace.Core.toNormedSpace

local instance : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : CompleteSpace L := FiniteDimensional.complete ℂ L

private def adjointFlow (x : L) (z : ℂ) : (End L)ˣ :=
  expUnit (adjointEnd (z • x))

private theorem adjointFlow_mem (x : L) (z : ℂ) :
    adjointFlow x z ∈ (innerGroup : Subgroup (End L)ˣ) :=
  Subgroup.subset_closure ⟨z • x, rfl⟩

private theorem adjointFlow_val (x : L) (z : ℂ) :
    (adjointFlow x z).val = exponential (LieAlgebra.ad ℂ L x) z := by
  have he : adjointEnd (z • x) = z • adjointEnd x := by
    apply ContinuousLinearMap.ext
    intro y
    exact smul_lie z x y
  change (expUnit (adjointEnd (z • x))).val = _
  rw [he]
  rfl

private def movePlane (g : (End L)ˣ) (P : Grassmannian L d) : Grassmannian L d :=
  ⟨P.subspace.map g.val.toLinearMap, (P.subspace.equivMapOfInjective
    (unitEquiv g).toLinearMap (unitEquiv g).injective).symm.finrank_eq.trans P.finrank_eq⟩

omit [FiniteDimensional ℂ L] in
private theorem movePlane_flagMap (B : Submodule ℂ L) (g k : (End L)ˣ) :
    movePlane g (flagMap B k) = flagMap B (g * k) := by
  apply Grassmannian.ext
  change (B.map k.val.toLinearMap).map g.val.toLinearMap =
    B.map ((g * k).val.toLinearMap)
  exact (Submodule.map_comp k.val.toLinearMap g.val.toLinearMap B).symm

set_option maxHeartbeats 1000000 in
private theorem plucker_movePlane (x : L) (z : ℂ) (P : Grassmannian L d) :
    plucker (movePlane (adjointFlow x z) P) =
      projectiveFlow (exteriorDerivative d (LieAlgebra.ad ℂ L x)) z (plucker P) := by
  let g := adjointFlow x z
  let v := subspaceFrame P
  let w : Frame L d := ⟨fun i => g.val (v.val i),
    v.property.map' (unitEquiv g).toLinearMap
      (LinearMap.ker_eq_bot.mpr (unitEquiv g).injective)⟩
  have hw : frameSpan w = movePlane g P := frameSpan_map g P
  have he : ιMulti ℂ d w.val =
      exponential (exteriorDerivative d (LieAlgebra.ad ℂ L x)) z (ιMulti ℂ d v.val) := by
    change ιMulti ℂ d (fun i => g.val (v.val i)) = _
    rw [show g.val = _ from adjointFlow_val x z, exterior_exponential_wedge]
  calc
    plucker (movePlane g P) = frameProjective w :=
      (congrArg plucker hw).symm.trans (plucker_frameSpan w)
    _ = projectiveFlow (exteriorDerivative d (LieAlgebra.ad ℂ L x)) z (frameProjective v) := by
      change Projectivization.mk ℂ (ιMulti ℂ d w.val) _ = projectiveFlow _ _
        (Projectivization.mk ℂ (ιMulti ℂ d v.val) _)
      rw [projectiveFlow_mk]
      exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨1, (one_smul ℂ _).trans he.symm⟩

private theorem projectiveFlow_eq_of_eigenline (A : Module.End ℂ V) (z : ℂ)
    (p : ℙ ℂ V) (hp : IsEigenline A p) : projectiveFlow A z p = p := by
  have hx := exponential_mem_submodule A p.submodule hp z
    (p.submodule_eq ▸ Submodule.mem_span_singleton_self p.rep)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (p.submodule_eq ▸ hx)
  have he : projectiveFlow A z (Projectivization.mk ℂ p.rep p.rep_nonzero) =
      Projectivization.mk ℂ p.rep p.rep_nonzero := by
    rw [projectiveFlow_mk]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c, hc⟩
  rwa [p.mk_rep] at he

private theorem bracket_mem_of_eigenline (x : L) (P : Grassmannian L d)
    (h : IsEigenline (exteriorDerivative d (LieAlgebra.ad ℂ L x)) (plucker P))
    {y : L} (hy : y ∈ P.subspace) : ⁅x, y⁆ ∈ P.subspace := by
  have horbit (z : ℂ) : movePlane (adjointFlow x z) P = P := by
    apply plucker_injective
    rw [plucker_movePlane, projectiveFlow_eq_of_eigenline _ _ _ h]
  have hy' (z : ℂ) : exponential (LieAlgebra.ad ℂ L x) z y ∈ P.subspace := by
    rw [← horbit z]
    exact ⟨y, hy, congrArg (fun T : End L => T y) (adjointFlow_val x z)⟩
  have hder := (ContinuousLinearMap.apply ℂ L y).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const' (adjointEnd x) (0 : ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, mul_one, ContinuousLinearMap.apply_apply] at hder
  apply P.subspace.closed_of_finiteDimensional.mem_of_tendsto hder.tendsto_slope_zero
  refine Filter.Eventually.of_forall fun z => ?_
  exact P.subspace.smul_mem _ (P.subspace.sub_mem (hy' (0 + z)) (hy' 0))

private theorem solvable_normalizes_orbit (B : Submodule ℂ L)
    (hX : IsCompact (flagOrbit B (innerGroup : Subgroup (End L)ˣ)))
    (A : LieSubalgebra ℂ L) [IsSolvable A] :
    ∃ g ∈ (innerGroup : Subgroup (End L)ˣ),
      ∀ x ∈ A, ∀ y ∈ B.map g.val.toLinearMap, ⁅x, y⁆ ∈ B.map g.val.toLinearMap := by
  let d := Module.finrank ℂ B
  let X := plucker '' flagOrbit B (innerGroup : Subgroup (End L)ˣ)
  have hXne : X.Nonempty :=
    ⟨plucker (flagMap B 1), _, ⟨1, Subgroup.one_mem _, rfl⟩, rfl⟩
  have hXc : IsCompact X := hX.image continuous_plucker
  let ρ : A →ₗ⁅ℂ⁆ Module.End ℂ (⋀[ℂ]^d L) :=
    (exteriorLieHom d).comp ((LieAlgebra.ad ℂ L).comp A.incl)
  have hXi : IsInvariant ρ X := by
    rintro x z p ⟨P, ⟨g, hg, rfl⟩, rfl⟩
    change projectiveFlow (exteriorDerivative d (LieAlgebra.ad ℂ L x.val)) z
      (plucker (flagMap B g)) ∈ X
    rw [← plucker_movePlane, movePlane_flagMap]
    exact ⟨_, ⟨_, Subgroup.mul_mem _ (adjointFlow_mem x.val z) hg, rfl⟩, rfl⟩
  obtain ⟨p, ⟨P, ⟨g, hg, rfl⟩, rfl⟩, hp⟩ := solvable_projective_fixed ρ X hXne hXc hXi
  refine ⟨g, hg, fun x hx y hy => ?_⟩
  exact bracket_mem_of_eigenline x (flagMap B g) (hp ⟨x, hx⟩) hy

private def unitLieEquiv (g : (End L)ˣ)
    (hg : g ∈ automorphisms (fun v w : L => ⁅v, w⁆)) : L ≃ₗ⁅ℂ⁆ L :=
  { unitEquiv g with
    map_lie' := fun {x y} => hg x y }

omit [FiniteDimensional ℂ L] in
private theorem toSubmodule_map_unit (B : LieSubalgebra ℂ L) (g : (End L)ˣ)
    (hg : g ∈ automorphisms (fun v w : L => ⁅v, w⁆)) :
    (B.map (unitLieEquiv g hg).toLieHom).toSubmodule = B.toSubmodule.map g.val.toLinearMap := rfl

omit [FiniteDimensional ℂ L] c in
private theorem map_isSolvable (B : LieSubalgebra ℂ L) [IsSolvable B] (e : L ≃ₗ⁅ℂ⁆ L) :
    IsSolvable (B.map e.toLieHom) := by
  let f : B →ₗ⁅ℂ⁆ B.map e.toLieHom :=
    { B.toSubmodule.equivMapOfInjective e.toLinearMap e.injective with
      map_lie' := fun {x y} => Subtype.ext (e.map_lie x.val y.val) }
  exact (show Function.Surjective f from
    (B.toSubmodule.equivMapOfInjective e.toLinearMap e.injective).surjective).lieAlgebra_isSolvable

omit [FiniteDimensional ℂ L] c in
private theorem le_map_of_normalizes (B : LieSubalgebra ℂ L) (hB : B.normalizer = B)
    (e : L ≃ₗ⁅ℂ⁆ L) (A : LieSubalgebra ℂ L)
    (hA : ∀ x ∈ A, ∀ y ∈ B.map e.toLieHom, ⁅x, y⁆ ∈ B.map e.toLieHom) :
    A ≤ B.map e.toLieHom := by
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  change e.symm x ∈ B
  rw [← hB, LieSubalgebra.mem_normalizer_iff]
  intro y hy
  obtain ⟨z, hz, he⟩ := hA x hx (e y) ⟨y, hy, rfl⟩
  have hz' : z = ⁅e.symm x, y⁆ :=
    e.injective (by
      change e z = e ⁅e.symm x, y⁆
      rw [e.map_lie, e.apply_symm_apply]
      exact he)
  exact hz' ▸ hz

private theorem inner_is_automorphism (hG :
    identityComponent (automorphisms (fun v w : L => ⁅v, w⁆)) = innerGroup)
    {g : (End L)ˣ} (hg : g ∈ (innerGroup : Subgroup (End L)ˣ)) :
    g ∈ automorphisms (fun v w : L => ⁅v, w⁆) := by
  rw [← hG] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  exact k.property

end CompactNorm

end ExteriorPower

theorem borel_conjugacy : borelConjugacyType := by
  intro L _ _ _ hss H hH φ hφ
  obtain ⟨τ, hτ, hinv, hneg, hs, hp, hG, hK, hvel, hcomp⟩ :=
    CompactFlagOrbit.compact_flag_orbit hss H hH
  refine ⟨τ, hs, hp, ?_⟩
  let c := hermitianCore τ hs hp
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
  let : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
  let : CompleteSpace L := FiniteDimensional.complete ℂ L
  let B := standard hss H hH φ
  have hnorm := standard_self_normalizing hss H hH φ hφ
  let : IsSolvable B := standard_solvable hss H hH φ
  have hconj (A : LieSubalgebra ℂ L) [IsSolvable A] :
      ∃ g : (End L)ˣ, ∃ hg : g ∈ (innerGroup : Subgroup (End L)ˣ),
        A ≤ B.map (unitLieEquiv g (inner_is_automorphism hG hg)).toLieHom := by
    obtain ⟨g, hg, hg'⟩ := solvable_normalizes_orbit (borel H φ) (hcomp φ hφ).2.2 A
    let e := unitLieEquiv g (inner_is_automorphism hG hg)
    refine ⟨g, hg, le_map_of_normalizes B hnorm e A ?_⟩
    intro x hx y hy
    change y ∈ (B.map e.toLieHom).toSubmodule at hy
    change ⁅x, y⁆ ∈ (B.map e.toLieHom).toSubmodule
    rw [toSubmodule_map_unit] at hy ⊢
    exact hg' x hx y hy
  constructor
  · intro A hA
    obtain ⟨g, hg, hle⟩ := hconj A
    refine ⟨g, hg, ?_⟩
    have hh : A.toSubmodule ≤
        (B.map (unitLieEquiv g (inner_is_automorphism hG hg)).toLieHom).toSubmodule := hle
    rwa [toSubmodule_map_unit] at hh
  · have hconjMax (A : LieSubalgebra ℂ L) (hA : IsBorel A) :
        ∃ g ∈ (innerGroup : Subgroup (End L)ˣ),
          A.toSubmodule = B.toSubmodule.map g.val.toLinearMap := by
      let : IsSolvable A := hA.1
      obtain ⟨g, hg, hle⟩ := hconj A
      let e := unitLieEquiv g (inner_is_automorphism hG hg)
      have he := le_antisymm hle (hA.2 (map_isSolvable B e) hle)
      refine ⟨g, hg, ?_⟩
      exact (congrArg LieSubalgebra.toSubmodule he).trans (toSubmodule_map_unit B g _)
    intro A₁ A₂ hA₁ hA₂
    obtain ⟨g₁, hg₁, he₁⟩ := hconjMax A₁ hA₁
    obtain ⟨g₂, hg₂, he₂⟩ := hconjMax A₂ hA₂
    refine ⟨g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
    rw [he₁, he₂, ← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro y
    change g₂.val y = g₂.val (g₁.inv (g₁.val y))
    exact congrArg (fun T : End L => g₂.val (T y)) g₁.inv_val.symm

theorem all_borels_conjugate : allBorelsConjugateType := by
  intro L _ _ _ hss
  obtain ⟨H, hH⟩ := exists_maximal_toral L hss
  let : Finite (rootSet H) := (rootSet_finite H hH.1).to_subtype
  obtain ⟨φ, hφ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun α : rootSet H => α.val) (fun α => α.property.1)
  obtain ⟨τ, hs, hp, _, hconj⟩ := borel_conjugacy hss H hH φ (fun α hα => hφ ⟨α, hα⟩)
  exact ⟨τ, hs, hp, hconj⟩

end LieAlgebrasAndRepresentations.BorelSubalgebras
