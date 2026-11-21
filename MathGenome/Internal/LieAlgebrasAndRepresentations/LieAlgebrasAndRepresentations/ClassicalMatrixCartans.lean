import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsB
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsD
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! The classical matrix Cartans and their Killing-normalized coroots. -/

namespace LieAlgebrasAndRepresentations.ClassicalMatrixCartans

open scoped Polynomial
open Specs.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
open private toral_genWeightSpace_eq_weightSpace from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori
open private all_weight_spaces_span from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA

noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem maximalToral_of_weightSpaces (H : LieSubalgebra ℂ L)
    (hz : rootSpace H 0 = H.toSubmodule)
    (hspan : (⨆ a, rootSpace H a) = ⊤) : IsMaximalToral H := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩, fun h => ?_⟩, ?_⟩
  · have hy : (y : L) ∈ rootSpace H 0 := by rw [hz]; exact y.property
    simpa using (mem_rootSpace H 0 (y : L)).mp hy x
  · classical
    let f : Module.End ℂ L := LieAlgebra.ad ℂ L (h : L)
    let s := f.finite_hasEigenvalue.toFinset
    let p : ℂ[X] := ∏ c ∈ s, (Polynomial.X - Polynomial.C c)
    have hp : p.Separable :=
      Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ he => he)
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hspan]
    refine iSup_le fun a => ?_
    intro x hx
    apply LinearMap.mem_ker.mpr
    have he : f x = a h • x := (mem_rootSpace H a x).mp hx h
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul he]
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hc : a h ∈ s := f.finite_hasEigenvalue.mem_toFinset.mpr
        (Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr he, hx0⟩)
      have hp0 : p.eval (a h) = 0 := by
        simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        exact Finset.prod_eq_zero hc (sub_self _)
      simp [hp0]
  · intro K hK hHK x hx
    rw [← LieSubalgebra.mem_toSubmodule, ← hz, mem_rootSpace]
    intro h
    let : IsLieAbelian K := hK.1
    simpa using congrArg (fun z : K => (z : L))
      (trivial_lie_zero K K ⟨h, hHK h.property⟩ ⟨x, hx⟩)

omit [FiniteDimensional ℂ L] in
/-- A solvable ideal cannot contain the raising vector of a normalized root triple. -/
private theorem raising_not_mem_solvable (I : LieIdeal ℂ L)
    (hI : LieAlgebra.IsSolvable I) {x y z : L} (hx : x ≠ 0)
    (hxy : ⁅x, y⁆ = z) (hzx : ⁅z, x⁆ = (2 : ℂ) • x)
    (hzy : ⁅z, y⁆ = (-2 : ℂ) • y) : x ∉ I := by
  intro hxI
  have hzI : z ∈ I := hxy ▸ lie_mem_left ℂ L I x y hxI
  have hyI : y ∈ I := (I.toSubmodule.smul_mem_iff (by norm_num : (-2 : ℂ) ≠ 0)).mp
    (hzy ▸ lie_mem_left ℂ L I z y hzI)
  have hmem (k : ℕ) :
      x ∈ LieAlgebra.derivedSeriesOfIdeal ℂ L k I ∧
      y ∈ LieAlgebra.derivedSeriesOfIdeal ℂ L k I ∧
      z ∈ LieAlgebra.derivedSeriesOfIdeal ℂ L k I := by
    induction k with
    | zero => exact ⟨hxI, hyI, hzI⟩
    | succ k ih =>
      rw [LieAlgebra.derivedSeriesOfIdeal_succ]
      refine ⟨?_, ?_, hxy ▸ LieSubmodule.lie_mem_lie ih.1 ih.2.1⟩
      · exact (Submodule.smul_mem_iff (_ : Submodule ℂ L) (by norm_num : (2 : ℂ) ≠ 0)).mp
          (hzx ▸ LieSubmodule.lie_mem_lie ih.2.2 ih.1)
      · exact (Submodule.smul_mem_iff (_ : Submodule ℂ L) (by norm_num : (-2 : ℂ) ≠ 0)).mp
          (hzy ▸ LieSubmodule.lie_mem_lie ih.2.2 ih.2.1)
  obtain ⟨k, hk⟩ := (LieAlgebra.isSolvable_iff ℂ I).mp hI
  have hk' := (I.derivedSeries_eq_bot_iff k).mp hk
  exact hx ((LieSubmodule.mem_bot x).mp (hk' ▸ (hmem k).1))

private theorem semisimple_of_weightSpaces (H : LieSubalgebra ℂ L)
    (ht : IsToral H) (hz : rootSpace H 0 = H.toSubmodule)
    (hsep : ∀ h : H, (∀ a ∈ rootSet H, a h = 0) → h = 0)
    (hline : ∀ a ∈ rootSet H, Module.finrank ℂ (rootSpace H a) = 1)
    (htr : ∀ a ∈ rootSet H, ∃ (z : H) (x y : L),
      x ∈ rootSpace H a ∧ y ∈ rootSpace H (-a) ∧ ⁅x, y⁆ = (z : L) ∧ a z = 2) :
    IsSemisimple ℂ L := by
  rw [semisimple_iff_no_solvable_ideals]
  intro I hI
  let : IsLieAbelian H := ht.1
  have hroot (a : Module.Dual ℂ H) (ha : a ≠ 0) :
      I.toSubmodule ⊓ rootSpace H a = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    by_contra hn
    have hv0 : v ≠ 0 := fun he => hn ((Submodule.mem_bot ℂ).mpr he)
    have har : a ∈ rootSet H := ⟨ha, fun he => hv0 ((Submodule.mem_bot ℂ).mp (he ▸ hv.2))⟩
    obtain ⟨z, x, y, hx, hy, hb, hz'⟩ := htr a har
    have hx0 : x ≠ 0 := by
      intro hx0
      have hz0 : z = 0 := Subtype.ext (by simpa [hx0] using hb.symm)
      simp [hz0] at hz'
    have hw := eq_span_singleton_of_mem_of_finrank_eq_one (hline a har) hv.2 hv0
    have hle : rootSpace H a ≤ I.toSubmodule := by
      rw [hw, Submodule.span_singleton_le_iff_mem]
      exact hv.1
    have hzx : ⁅(z : L), x⁆ = (2 : ℂ) • x := by
      rw [(mem_rootSpace H a x).mp hx z, hz']
    have hzy : ⁅(z : L), y⁆ = (-2 : ℂ) • y := by
      rw [(mem_rootSpace H (-a) y).mp hy z, LinearMap.neg_apply, hz']
    exact raising_not_mem_solvable I hI hx0 hb hzx hzy (hle hx)
  have hzero : I.toSubmodule ⊓ rootSpace H 0 = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hvH : v ∈ H := by
      change v ∈ H.toSubmodule
      rw [← hz]
      exact hv.2
    let h : H := ⟨v, hvH⟩
    have hh : h = 0 := hsep h fun a ha => by
      obtain ⟨z, x, y, hx, hy, hb, hz'⟩ := htr a ha
      have hx0 : x ≠ 0 := by
        intro hx0
        have hz0 : z = 0 := Subtype.ext (by simpa [hx0] using hb.symm)
        simp [hz0] at hz'
      have hbr : a h • x ∈ I := by
        rw [← (mem_rootSpace H a x).mp hx h]
        exact lie_mem_left ℂ L I v x hv.1
      have he : a h • x ∈ I.toSubmodule ⊓ rootSpace H a :=
        ⟨hbr, (rootSpace H a).smul_mem _ hx⟩
      rw [hroot a ha.1] at he
      exact (smul_eq_zero.mp ((Submodule.mem_bot ℂ).mp he)).resolve_right hx0
    exact (Submodule.mem_bot ℂ).mpr (congrArg (fun h : H => (h : L)) hh)
  have hi := LieModule.eq_iSup_inf_genWeightSpace ℂ H L (I.restr H)
  apply le_bot_iff.mp
  change (I.restr H).toSubmodule ≤ ⊥
  rw [hi, LieSubmodule.iSup_toSubmodule]
  refine iSup_le fun a => ?_
  rw [LieSubmodule.inf_toSubmodule, toral_genWeightSpace_eq_weightSpace H ht]
  change I.toSubmodule ⊓ rootSpace H (a : Module.Dual ℂ H) ≤ ⊥
  by_cases ha : (a : Module.Dual ℂ H) = 0
  · rw [ha, hzero]
  · rw [hroot _ ha]

private theorem coroot_eq_of_opposite_bracket (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (ht : IsMaximalToral H)
    {a : Module.Dual ℂ H} (ha : a ∈ rootSet H)
    {z : H} {x y : L} (hx : x ∈ rootSpace H a) (hy : y ∈ rootSpace H (-a))
    (hb : ⁅x, y⁆ = (z : L)) (hz : a z = 2) : killingCoroot H a = z := by
  have h := opposite_root_bracket hss H ht a x y hx hy
  rw [hb] at h
  have he : z = killingForm ℂ L x y • tAlpha H a := Subtype.ext h
  have hw := congrArg a he
  rw [map_smul, smul_eq_mul, hz, ← rootForm_eq_apply hss H ht] at hw
  rw [killingCoroot_eq, he, eq_div_iff (rootForm_self_ne_zero hss H ht a ha) |>.mpr hw.symm]

section MatrixTransport

variable {M V : Type*} [LieRing M] [LieAlgebra ℂ M]
  [AddCommGroup V] [Module ℂ V]

private def transportWeight {S : LieSubalgebra ℂ M} {H : LieSubalgebra ℂ S}
    (e : V ≃ₗ[ℂ] H) (a : Module.Dual ℂ V) : Module.Dual ℂ H :=
  a.comp e.symm.toLinearMap

private theorem transportWeight_surjective {S : LieSubalgebra ℂ M} {H : LieSubalgebra ℂ S}
    (e : V ≃ₗ[ℂ] H) : Function.Surjective (transportWeight e) := by
  intro a
  refine ⟨a.comp e.toLinearMap, ?_⟩
  ext h
  exact congrArg a (e.apply_symm_apply h)

private theorem transportWeight_ne_zero {S : LieSubalgebra ℂ M} {H : LieSubalgebra ℂ S}
    (e : V ≃ₗ[ℂ] H) (a : Module.Dual ℂ V) : transportWeight e a ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h ha
    apply h
    simp [ha, transportWeight]
  · intro h ha
    apply h
    ext t
    simpa [transportWeight] using congrArg (fun b : Module.Dual ℂ H => b (e t)) ha

variable [FiniteDimensional ℂ M]

/-- Transport the ordinary matrix eigenspaces, then use their lines and opposite
brackets to identify the radical and the normalized Lie coroots. -/
private theorem matrix_cartan
    (S : LieSubalgebra ℂ M) (H : LieSubalgebra ℂ S) (e : V ≃ₗ[ℂ] H)
    (d : V →ₗ[ℂ] M) (he : ∀ t, ((e t : S) : M) = d t)
    (W : Module.Dual ℂ V → Submodule ℂ M)
    (hW : ∀ a, (rootSpace H (transportWeight e a)).map S.toSubmodule.subtype = W a)
    (hz : W 0 = d.range) (hs : (⨆ a, W a) = S.toSubmodule)
    (hsep : ∀ t : V, (∀ a, a ≠ 0 → W a ≠ ⊥ → a t = 0) → t = 0)
    (c : Module.Dual ℂ V → V)
    (hline : ∀ a, a ≠ 0 → W a ≠ ⊥ → Module.finrank ℂ (W a) = 1)
    (htr : ∀ a, a ≠ 0 → W a ≠ ⊥ → a (c a) = 2 ∧
      ∃ x y : M, x ∈ W a ∧ y ∈ W (-a) ∧ ⁅x, y⁆ = d (c a)) :
    IsSemisimple ℂ S ∧ IsMaximalToral H ∧
      (∀ a, transportWeight e a ∈ rootSet H ↔ a ≠ 0 ∧ W a ≠ ⊥) ∧
      ∀ a, a ≠ 0 → W a ≠ ⊥ →
        ((killingCoroot H (transportWeight e a) : S) : M) = d (c a) := by
  let i := S.toSubmodule.subtype
  have hi : Function.Injective i := Subtype.val_injective
  have hm := Submodule.map_injective_of_injective (f := i) hi
  have hb (a : Module.Dual ℂ V) :
      transportWeight e a ∈ rootSet H ↔ a ≠ 0 ∧ W a ≠ ⊥ := by
    have hbot : W a = ⊥ ↔ rootSpace H (transportWeight e a) = ⊥ := by
      constructor
      · intro h
        apply hm
        exact (hW a).trans (h.trans (Submodule.map_bot i).symm)
      · intro h
        exact (hW a).symm.trans
          ((congrArg (Submodule.map i) h).trans (Submodule.map_bot i))
    exact and_congr (transportWeight_ne_zero e a) hbot.not.symm
  have hz' : rootSpace H 0 = H.toSubmodule := by
    apply hm
    rw [← show transportWeight e 0 = 0 by simp [transportWeight], hW, hz]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(e t : S), (e t).property, he t⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := e.surjective ⟨y, hy⟩
      exact ⟨t, (he t).symm.trans (congrArg (fun h : H => ((h : S) : M)) ht)⟩
  have hs' : (⨆ a, rootSpace H a) = ⊤ := by
    apply hm
    calc
      _ = ⨆ a, (rootSpace H a).map i := Submodule.map_iSup i _
      _ = ⨆ a, (rootSpace H (transportWeight e a)).map i :=
        ((transportWeight_surjective e).iSup_comp _).symm
      _ = ⨆ a, W a := by simp only [hW, i]
      _ = _ := hs.trans S.toSubmodule.map_subtype_top.symm
  have ht := maximalToral_of_weightSpaces H hz' hs'
  have htr' (a : Module.Dual ℂ V) (ha : a ≠ 0) (hwa : W a ≠ ⊥) :
      ∃ x y : S, x ∈ rootSpace H (transportWeight e a) ∧
        y ∈ rootSpace H (-transportWeight e a) ∧ ⁅x, y⁆ = (e (c a) : S) ∧
        transportWeight e a (e (c a)) = 2 := by
    obtain ⟨hac, X, Y, hX, hY, hXY⟩ := htr a ha hwa
    rw [← hW] at hX hY
    obtain ⟨x, hx, rfl⟩ := hX
    obtain ⟨y, hy, rfl⟩ := hY
    refine ⟨x, y, hx, ?_, Subtype.ext (hXY.trans (he _).symm), ?_⟩
    · simpa [transportWeight] using hy
    · simpa [transportWeight] using hac
  have hss : IsSemisimple ℂ S := by
    apply semisimple_of_weightSpaces H ht.1 hz'
    · intro h hh
      obtain ⟨t, rfl⟩ := e.surjective h
      have ht0 : t = 0 := hsep t fun a ha hw => by
        simpa [transportWeight] using hh (transportWeight e a) ((hb a).mpr ⟨ha, hw⟩)
      simp [ht0]
    · intro a ha
      obtain ⟨b, rfl⟩ := transportWeight_surjective e a
      have hh := (hb b).mp ha
      calc
        _ = Module.finrank ℂ ((rootSpace H (transportWeight e b)).map i) :=
          (Submodule.equivMapOfInjective i hi _).finrank_eq
        _ = Module.finrank ℂ (W b) := congrArg (fun U : Submodule ℂ M => Module.finrank ℂ U) (hW b)
        _ = 1 := hline b hh.1 hh.2
    · intro a ha
      obtain ⟨b, rfl⟩ := transportWeight_surjective e a
      have hh := (hb b).mp ha
      obtain ⟨x, y, hx, hy, hxy, hz⟩ := htr' b hh.1 hh.2
      exact ⟨e (c b), x, y, hx, hy, hxy, hz⟩
  refine ⟨hss, ht, hb, fun a ha hw => ?_⟩
  obtain ⟨x, y, hx, hy, hxy, hac⟩ := htr' a ha hw
  rw [coroot_eq_of_opposite_bracket hss H ht ((hb a).mpr ⟨ha, hw⟩) hx hy hxy hac, he]

end MatrixTransport

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA ClassicalRootsA in
theorem type_a : type_a_type := by
  intro n
  have hz := zero_space n
  have hs := all_weight_spaces_span n
  have ht := maximalToral_of_weightSpaces (cartan n) hz hs
  refine ⟨semisimple_of_weightSpaces (cartan n) ht.1 hz ?_ ?_ ?_, ht⟩
  · intro h hh
    have hd (i j : Fin (n + 1)) : h.val.val i i = h.val.val j j := by
      by_cases hij : i = j
      · rw [hij]
      · exact sub_eq_zero.mp (hh _ ((root_set n _).mpr ⟨i, j, hij, rfl⟩))
    have htrace : (∑ i, h.val.val i i) = 0 := h.val.property
    have hh0 : h.val.val 0 0 = 0 := by
      simp_rw [hd _ 0] at htrace
      have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simpa [nsmul_eq_mul, hn] using htrace
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    by_cases hij : i = j
    · subst j
      exact (hd i 0).trans hh0
    · exact h.property hij
  · intro a ha
    obtain ⟨i, j, hij, rfl⟩ := (root_set n a).mp ha
    exact root_dimension n i j hij
  · intro a ha
    obtain ⟨i, j, hij, rfl⟩ := (root_set n a).mp ha
    refine ⟨coroot n i j, rootVector n i j hij, rootVector n j i hij.symm,
      rootVector_mem i j hij, ?_, opposite_bracket i j hij, ?_⟩
    · have he : -root n i j = root n j i := by simp [root, neg_sub]
      rw [he]
      exact rootVector_mem j i hij.symm
    · norm_num [Matrix.single, hij, hij.symm]

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] LieAlgebra.ofAssociativeAlgebra

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsB ClassicalRootsB in
theorem type_b : type_b_type := by
  intro n
  let e : Parameters n ≃ₗ[ℂ] cartan n :=
    (LinearEquiv.ofBijective (coordinates n) (cartan_identification n).1).symm
  have he (t : Parameters n) : ((e t : algebra n) : Mat n) = diagonal n t := by
    exact (cartan_reconstruction (e t)).symm.trans
      (congrArg (diagonal n) (e.symm_apply_apply t))
  obtain ⟨hss, ht, hr, hc⟩ :=
    matrix_cartan (algebra n) (cartan n) e (diagonal n) he weightSpace
      (root_space_bridge n) (zero_space n) (decomposition n).1
      (fun t ht => by
        ext i
        have ha : epsilon i ∈ roots n := by
          rw [roots_eq]
          exact Or.inl ⟨i, Or.inl rfl⟩
        exact ht (epsilon i) ha.1 ha.2)
      (fun a i => (2 / squaredLength a) * a (Pi.single i 1))
      (fun a ha hw => root_dimensions n a ⟨ha, hw⟩)
      (fun a ha hw => by
        obtain ⟨hlen, _, x, y, hx, hy, _, _, hb, _, _⟩ := coroot_triples n a ⟨ha, hw⟩
        exact ⟨coroot_evaluation a hlen, x, y, hx, hy, hb⟩)
  exact ⟨hss, ht, hr, fun a ha => hc a ha.1 ha.2⟩

private abbrev coordinateCoroot {n : ℕ} (a : Module.Dual ℂ (Fin n → ℂ)) : Fin n → ℂ :=
  let u : Fin n → ℂ := fun i => a (Pi.single i 1)
  (2 / ∑ i, u i * u i) • u

private theorem coordinateCoroot_apply {n : ℕ} (a : Module.Dual ℂ (Fin n → ℂ))
    (ha : (∑ i : Fin n, a (Pi.single i 1) * a (Pi.single i 1)) ≠ 0) :
    a (coordinateCoroot a) = 2 := by
  unfold coordinateCoroot
  rw [map_smul, ClassicalRootsB.evaluate_coefficients]
  exact div_mul_cancel₀ _ ha

private theorem finrank_of_spanning_root {M : Type*} [AddCommGroup M] [Module ℂ M]
    {W : Submodule ℂ M} {x : M} (hW : W ≠ ⊥) (hx : W = Submodule.span ℂ {x}) :
    Module.finrank ℂ W = 1 := by
  rw [hx]
  apply finrank_span_singleton
  intro hx0
  apply hW
  simp [hx, hx0]

section TypeC

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC ClassicalRootsC
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
  renaming rootSpace → matrixRootSpace, rootSet → matrixRootSet

private theorem euclidean_neg {n : ℕ} (a : Weight n) :
    euclidean (-a) (-a) = euclidean a a := by
  simp [euclidean, coordinates]

private theorem symplectic_root_data (n : ℕ) (a : Weight n) (ha : a ∈ matrixRootSet n) :
    Module.finrank ℂ (matrixRootSpace a) = 1 ∧ a (coordinateCoroot a) = 2 ∧
    ∃ x y : Mat n, x ∈ matrixRootSpace a ∧ y ∈ matrixRootSpace (-a) ∧ ⁅x, y⁆ = coroot a := by
  have hne := ha.2
  have hf {b : Weight n} {x : Mat n} (h : matrixRootSpace b = Submodule.span ℂ {x}) :
      x ∈ matrixRootSpace b := h.symm ▸ Submodule.subset_span (Set.mem_singleton x)
  rw [roots n] at ha
  change (∃ i, a = (2 : ℂ) • eps i ∨ a = -((2 : ℂ) • eps i)) ∨
    ∃ i j : Fin n, i < j ∧
      (a = eps i - eps j ∨ a = -(eps i - eps j) ∨
        a = eps i + eps j ∨ a = -(eps i + eps j)) at ha
  rcases ha with (⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩)
  · refine ⟨finrank_of_spanning_root hne (b_long_space n i),
      coordinateCoroot_apply _ (by change euclidean _ _ ≠ 0; rw [euclidean_long]; norm_num),
      bLong i, cLong i, hf (b_long_space n i), hf (c_long_space n i), (long_coroot n i).1⟩
  · refine ⟨finrank_of_spanning_root hne (c_long_space n i),
      coordinateCoroot_apply _ (by
        change euclidean _ _ ≠ 0; rw [euclidean_neg, euclidean_long]; norm_num),
      cLong i, bLong i, hf (c_long_space n i), ?_, ?_⟩
    · simpa only [neg_neg] using hf (b_long_space n i)
    · rw [neg_coroot n, ← (long_coroot n i).1, lie_skew]
  · have h := ne_of_lt hij
    refine ⟨finrank_of_spanning_root hne (a_space n i j h),
      coordinateCoroot_apply _ (by change euclidean _ _ ≠ 0; rw [euclidean_a i j h]; norm_num),
      aRoot i j, aRoot j i, hf (a_space n i j h), ?_, (a_coroot n i j h).1⟩
    simpa only [neg_sub] using hf (a_space n j i h.symm)
  · rw [neg_sub] at hne ⊢
    have h := (ne_of_lt hij).symm
    refine ⟨finrank_of_spanning_root hne (a_space n j i h),
      coordinateCoroot_apply _ (by change euclidean _ _ ≠ 0; rw [euclidean_a j i h]; norm_num),
      aRoot j i, aRoot i j, hf (a_space n j i h), ?_, (a_coroot n j i h).1⟩
    simpa only [neg_sub] using hf (a_space n i j h.symm)
  · have h := ne_of_lt hij
    exact ⟨finrank_of_spanning_root hne (b_space n i j h),
      coordinateCoroot_apply _ (by change euclidean _ _ ≠ 0; rw [euclidean_b i j h]; norm_num),
      bRoot i j, cRoot i j, hf (b_space n i j h), hf (c_space n i j h), (b_coroot n i j h).1⟩
  · have h := ne_of_lt hij
    refine ⟨finrank_of_spanning_root hne (c_space n i j h),
      coordinateCoroot_apply _ (by
        change euclidean _ _ ≠ 0; rw [euclidean_neg, euclidean_b i j h]; norm_num),
      cRoot i j, bRoot i j, hf (c_space n i j h), ?_, ?_⟩
    · simpa only [neg_neg] using hf (b_space n i j h)
    · rw [neg_coroot n, ← (b_coroot n i j h).1, lie_skew]

theorem type_c : type_c_type := by
  intro n
  obtain ⟨H, _, e, he, hW⟩ := cartan_transport n
  obtain ⟨hss, ht, hr, hc⟩ :=
    matrix_cartan (sp n) H e (diagonalMap n) he matrixRootSpace hW (zero_space n) (spanning n)
      (fun t ht => by
        ext i
        have ha : (2 : ℂ) • eps i ∈ matrixRootSet n := by
          rw [roots]
          exact Or.inl ⟨i, Or.inl rfl⟩
        have h := ht ((2 : ℂ) • eps i) ha.1 ha.2
        change 2 * t i = 0 at h
        exact (mul_eq_zero.mp h).resolve_left (by norm_num))
      coordinateCoroot
      (fun a ha hw => (symplectic_root_data n a ⟨ha, hw⟩).1)
      (fun a ha hw => (symplectic_root_data n a ⟨ha, hw⟩).2)
  exact ⟨hss, H, e, ht, he, hr, fun a ha => hc a ha.1 ha.2⟩

end TypeC

section TypeD

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsD ClassicalRootsD

private def diagonalMap (n : ℕ) : Params n →ₗ[ℂ] Mat n :=
  Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonalMap n

private theorem cartan_transport (n : ℕ) :
    ∃ (H : LieSubalgebra ℂ (algebra n)) (e : Params n ≃ₗ[ℂ] H),
      (∀ t, ((e t : algebra n) : Mat n) = diagonal n t) ∧
      ∀ a : Dual n, (rootSpace H (transportWeight e a)).map
        (algebra n).toSubmodule.subtype = weightSpace n a := by
  let d : Params n →ₗ[ℂ] algebra n := (diagonalMap n).codRestrict (algebra n).toSubmodule diagonal_mem
  have hd : Function.Injective d := fun _ _ h =>
    diagonal_injective (congrArg Subtype.val h)
  let H : LieSubalgebra ℂ (algebra n) :=
    { d.range with
      lie_mem' := by
        rintro _ _ ⟨t, rfl⟩ ⟨u, rfl⟩
        have h : ⁅d t, d u⁆ = 0 := by
          apply Subtype.ext
          change diagonal n t * diagonal n u - diagonal n u * diagonal n t = 0
          rw [diagonal, diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
          exact sub_eq_zero.mpr (congrArg Matrix.diagonal (funext fun _ => mul_comm _ _))
        rw [h]
        exact d.range.zero_mem }
  let e : Params n ≃ₗ[ℂ] H := LinearEquiv.ofInjective d hd
  have he (t : Params n) : ((e t : algebra n) : Mat n) = diagonal n t := rfl
  refine ⟨H, e, he, fun a => ?_⟩
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨Y.property, fun t => ?_⟩
    have h := congrArg (fun Z : algebra n => (Z : Mat n)) ((mem_rootSpace H _ Y).mp hY (e t))
    change ((e t : algebra n) : Mat n) * Y.val - Y.val * ((e t : algebra n) : Mat n) =
      a (e.symm (e t)) • Y.val at h
    change diagonal n t * Y.val - Y.val * diagonal n t = a t • Y.val
    simpa only [he, e.symm_apply_apply] using h
  · rintro ⟨hX, hwt⟩
    refine ⟨⟨X, hX⟩, ?_, rfl⟩
    apply (mem_rootSpace H (transportWeight e a) (⟨X, hX⟩ : algebra n)).mpr
    intro h
    obtain ⟨t, rfl⟩ := e.surjective h
    apply Subtype.ext
    change ((e t : algebra n) : Mat n) * X - X * ((e t : algebra n) : Mat n) =
      a (e.symm (e t)) • X
    simpa only [he, e.symm_apply_apply] using hwt t

private theorem even_orthogonal_root_data (n : ℕ) (a : Dual n) (ha : a ∈ roots n) :
    a (coordinateCoroot a) = 2 ∧
      ∃ x y : Mat n, x ∈ weightSpace n a ∧ y ∈ weightSpace n (-a) ∧
        ⁅x, y⁆ = coroot n (fun i => a (coordinate n i)) := by
  have he (i : Fin n) : (fun j => epsilon n i (coordinate n j)) = coordinate n i := by
    ext j
    simp [epsilon, coordinate, Pi.single_apply, eq_comm]
  have hn {b : Dual n} {v : Params n} (h : (fun k => b (coordinate n k)) = v)
      (hv : dot n v v ≠ 0) : b (coordinateCoroot b) = 2 := by
    apply coordinateCoroot_apply
    change dot n (fun k => b (coordinate n k)) (fun k => b (coordinate n k)) ≠ 0
    rwa [h]
  obtain ⟨i, j, hij, rfl | rfl | rfl⟩ := (roots_iff a).mp ha
  · have hc : (fun k => (epsilon n i - epsilon n j) (coordinate n k)) =
        coordinate n i - coordinate n j := by
      ext k
      exact congrArg₂ Sub.sub (congrFun (he i) k) (congrFun (he j) k)
    refine ⟨hn hc ?_, aVector n i j, aVector n j i, aVector_weight i j, ?_, ?_⟩
    · rw [(root_lengths i j hij).1]
      norm_num
    · simpa only [neg_sub] using aVector_weight j i
    · rw [hc]
      exact difference_bracket i j hij
  · have hc : (fun k => (epsilon n i + epsilon n j) (coordinate n k)) =
        coordinate n i + coordinate n j := by
      ext k
      exact congrArg₂ (· + ·) (congrFun (he i) k) (congrFun (he j) k)
    refine ⟨hn hc ?_, bVector n i j, -cVector n i j, bVector_weight i j,
      (weightSpace n _).neg_mem (cVector_weight i j), ?_⟩
    · rw [(root_lengths i j hij).2]
      norm_num
    · rw [hc]
      exact sum_bracket i j hij
  · have hc : (fun k => (-(epsilon n i + epsilon n j)) (coordinate n k)) =
        -(coordinate n i + coordinate n j) := by
      ext k
      exact congrArg Neg.neg (congrArg₂ (· + ·) (congrFun (he i) k) (congrFun (he j) k))
    refine ⟨hn hc ?_, cVector n i j, -bVector n i j, cVector_weight i j, ?_, ?_⟩
    · rw [show dot n (-(coordinate n i + coordinate n j)) (-(coordinate n i + coordinate n j)) =
        dot n (coordinate n i + coordinate n j) (coordinate n i + coordinate n j) by
          simp only [dot, Pi.neg_apply, neg_mul_neg],
        (root_lengths i j hij).2]
      norm_num
    · simpa only [neg_neg] using (weightSpace n _).neg_mem (bVector_weight i j)
    · rw [hc]
      exact neg_sum_bracket i j hij

theorem type_d : type_d_type := by
  intro n hn
  obtain ⟨H, e, he, hW⟩ := cartan_transport n
  have hz : weightSpace n 0 = (diagonalMap n).range := by
    ext X
    exact (zero_space X).trans ⟨fun ⟨t, h⟩ => ⟨t, h.symm⟩, fun ⟨t, h⟩ => ⟨t, h.symm⟩⟩
  obtain ⟨hss, ht, hr, hc⟩ :=
    matrix_cartan (algebra n) H e (diagonalMap n) he (weightSpace n) hW hz iSup_weightSpace
      (fun t ht => by
        ext i
        have hn' : 1 < n := by have := i.isLt; omega
        let : Nontrivial (Fin n) := ⟨⟨⟨0, by omega⟩, ⟨1, hn'⟩, by simp [Fin.mk.injEq]⟩⟩
        obtain ⟨j, hji⟩ := exists_ne i
        have ha := (roots_iff (epsilon n i - epsilon n j)).mpr ⟨i, j, hji.symm, Or.inl rfl⟩
        have hb := (roots_iff (epsilon n i + epsilon n j)).mpr ⟨i, j, hji.symm, Or.inr (Or.inl rfl)⟩
        have h₁ : t i - t j = 0 := ht _ ha.1 ha.2
        have h₂ : t i + t j = 0 := ht _ hb.1 hb.2
        change t i = 0
        linear_combination (h₁ + h₂) / 2)
      coordinateCoroot
      (fun a ha hw => root_space_finrank a ⟨ha, hw⟩)
      (fun a ha hw => even_orthogonal_root_data n a ⟨ha, hw⟩)
  exact ⟨hss, H, e, ht, he, hr, fun a ha => hc a ha.1 ha.2⟩

end TypeD

end
end LieAlgebrasAndRepresentations.ClassicalMatrixCartans
