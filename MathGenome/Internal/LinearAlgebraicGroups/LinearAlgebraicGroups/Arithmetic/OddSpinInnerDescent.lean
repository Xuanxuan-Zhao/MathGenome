import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent

open Specs.Arithmetic.OddSpinInnerDescent
open LinearAlgebraicGroups.Descent (SemilinearAction)
open LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open Module

noncomputable section

private theorem cartan_double {n : ℕ} {i j : Fin (n + 1)} :
    typeBCartan n i j = -2 ↔ i.val + 1 = j.val ∧ j.val = n := by
  unfold typeBCartan
  split_ifs with he hd ha <;> simp_all

private theorem cartan_adjacent {n : ℕ} {i j : Fin (n + 1)} :
    (typeBCartan n i j = -1 ∨ typeBCartan n i j = -2) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  unfold typeBCartan
  split_ifs with he hd ha <;> simp_all

theorem diagramRigidity : DiagramRigidity := by
  intro n p hp
  apply Equiv.ext
  intro i
  change p i = i
  by_cases hz : n = 0
  · subst n
    apply Fin.ext
    have h₁ := i.isLt
    have h₂ := (p i).isLt
    omega
  let l : Fin (n + 1) := ⟨n, by omega⟩
  let j : Fin (n + 1) := ⟨n - 1, by omega⟩
  have hl : p l = l := by
    have hd : typeBCartan n j l = -2 :=
      cartan_double.mpr ⟨by change n - 1 + 1 = n; omega, rfl⟩
    apply Fin.ext
    exact (cartan_double.mp ((hp j l).trans hd)).2
  suffices ∀ d : ℕ, ∀ i : Fin (n + 1), n - i.val = d → p i = i by
    exact this _ i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i hi
    by_cases hlast : i.val = n
    · have : i = l := Fin.ext hlast
      simpa [this] using hl
    let j : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
    have hjLt : n - j.val < d := by
      change n - (i.val + 1) < d
      have := i.isLt
      omega
    have hj := ih _ hjLt _ rfl
    have hAdj : (p i).val + 1 = j.val ∨ j.val + 1 = (p i).val := by
      apply cartan_adjacent.mp
      rw [← hj, hp]
      exact cartan_adjacent.mpr (Or.inl rfl)
    rcases hAdj with h | h
    · apply Fin.ext
      change (p i).val + 1 = i.val + 1 at h
      omega
    · have hpLt := (p i).isLt
      have hdLt : n - (p i).val < d := by
        change i.val + 1 + 1 = (p i).val at h
        omega
      exact p.injective (ih _ hdLt _ rfl)

private theorem fixes_of_spansRationally {L : Type u} [AddCommGroup L] [Module.Free ℤ L]
    {s : Set L} (hs : SpansRationally s) (g : L →ₗ[ℤ] L)
    (h : ∀ x ∈ s, g x = x) (x : L) : g x = x := by
  obtain ⟨m, hm, hx⟩ := hs x
  have hspan : ∀ y ∈ Submodule.span ℤ s, g y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, hy]
  have hmx := hspan _ hx
  rw [map_smul] at hmx
  exact (smul_right_injective L hm) hmx

theorem simpleCorootsSpan : SimpleCorootsSpan.{u} := by
  intro D n b h
  have hr : Set.range (fun i => D.datum.coroot (b i).val) =
      D.datum.coroot '' (D.base.support : Set D.I) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(b i).val, (b i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj⟩ := b.surjective ⟨i, hi⟩
      exact ⟨j, congrArg (fun z : D.base.support ↦ D.datum.coroot z.val) hj⟩
  intro x
  refine ⟨1, one_ne_zero, ?_⟩
  rw [hr, D.base.span_int_coroot_support, h]
  exact Submodule.mem_top

theorem basedDatumRigidity : BasedDatumRigidity.{u} := by
  intro D n b hB hY f
  let f₀ : Specs.Pinning.BasedIso D D := f.asIso.hom
  let e := f₀.val
  have hmem (i : D.base.support) : e.indexEquiv i.val ∈ D.base.support := by
    change e.indexEquiv i.val ∈ (D.base.support : Set D.I)
    rw [← f₀.property]
    exact ⟨i.val, i.property, rfl⟩
  let p₀ : D.base.support ≃ D.base.support :=
    Equiv.ofBijective (fun i => ⟨e.indexEquiv i.val, hmem i⟩)
      ⟨fun i j h => Subtype.ext (e.indexEquiv.injective (congrArg Subtype.val h)),
        fun j => by
          have hj : j.val ∈ e.indexEquiv '' (D.base.support : Set D.I) := by
            rw [f₀.property]
            exact j.property
          obtain ⟨i, hi, hij⟩ := hj
          exact ⟨⟨i, hi⟩, Subtype.ext hij⟩⟩
  let p : Equiv.Perm (Fin (n + 1)) := (b.trans p₀).trans b.symm
  have hp (i : Fin (n + 1)) : (b (p i)).val = e.indexEquiv (b i).val := by
    change (b (b.symm (p₀ (b i)))).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hid : p = Equiv.refl _ := diagramRigidity n p fun i j => by
    rw [← hB, ← hB, hp, hp]
    exact e.toHom.pairing
  have hfix (i : Fin (n + 1)) : e.indexEquiv (b i).val = (b i).val := by
    rw [← hp, hid]
    rfl
  let := D.freeY
  have hcoweight (x : D.Y) : e.coweightEquiv x = x := by
    apply fixes_of_spansRationally hY e.toHom.coweightMap _ x
    rintro _ ⟨i, rfl⟩
    rw [e.toHom.coroot_coweightMap_apply]
    have hi := congrArg e.indexEquiv.symm (hfix i)
    rw [Equiv.symm_apply_apply] at hi
    rw [← hi]
  have hweight (x : D.X) : e.weightEquiv x = x := by
    apply D.datum.toPerfPair.injective
    apply LinearMap.ext
    intro y
    have h := LinearMap.congr_fun (e.toHom.weight_coweight_transpose_apply D.datum D.datum y) x
    change (D.datum.flip.toPerfPair y) (e.weightEquiv x) =
      (D.datum.flip.toPerfPair (e.coweightEquiv y)) x at h
    rw [hcoweight] at h
    exact h
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  change e = RootPairing.Equiv.id D.datum
  apply RootPairing.Equiv.ext
  · ext x
    exact hweight x
  · ext x
    exact hcoweight x
  · ext i
    apply D.datum.root.injective
    rw [← e.toHom.root_weightMap_apply]
    exact hweight _

section Quadratic

variable {k K V : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [FiniteDimensional k K] [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]
  (a : SemilinearAction k K V) (Q : QuadraticForm K V)
  (hQ : ∀ σ x, Q (a.act σ x) = σ (Q x))

include hQ in
private theorem fixedNorm_exists (x : a.fixed) : Q x.val ∈ Set.range (algebraMap k K) := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  rw [← hQ, x.property σ]

private def fixedNorm (x : a.fixed) : k := Classical.choose (fixedNorm_exists a Q hQ x)

private theorem map_fixedNorm (x : a.fixed) :
    algebraMap k K (fixedNorm a Q hQ x) = Q x.val :=
  Classical.choose_spec (fixedNorm_exists a Q hQ x)

private theorem map_fixedPolar (x y : a.fixed) :
    algebraMap k K (QuadraticMap.polar (fixedNorm a Q hQ) x y) =
      QuadraticMap.polar Q x.val y.val := by
  simp only [QuadraticMap.polar, map_sub, map_fixedNorm, Submodule.coe_add]

private def fixedForm : QuadraticForm k a.fixed :=
  QuadraticMap.ofPolar (fixedNorm a Q hQ)
    (fun r x => by
      apply (algebraMap k K).injective
      simp only [smul_eq_mul, map_mul, map_fixedNorm, Submodule.coe_smul,
        ← IsScalarTower.algebraMap_smul K r (x : V), Q.map_smul])
    (fun x y z => by
      apply (algebraMap k K).injective
      simp only [map_add, map_fixedPolar, Submodule.coe_add, QuadraticMap.polar_add_left])
    (fun r x y => by
      apply (algebraMap k K).injective
      simp only [smul_eq_mul, map_mul, map_fixedPolar, Submodule.coe_smul,
        QuadraticMap.polar_smul_left_of_tower, Algebra.smul_def])

private theorem map_fixedForm (x : a.fixed) :
    algebraMap k K (fixedForm a Q hQ x) = Q x.val :=
  map_fixedNorm a Q hQ x

private theorem fixedForm_extension {I : Type u} [LinearOrder I] (b : Basis I k a.fixed) :
    Q.comp a.descentEquiv.toLinearMap = coefficientForm K (fixedForm a Q hQ) b := by
  apply (LinearAlgebraicGroups.Albert.CliffordModel.coefficient_form_unique K _ b _).mpr
  intro x
  change Q (a.descentEquiv ((1 : K) ⊗ₜ[k] x)) = _
  rw [SemilinearAction.descentEquiv_tmul, one_smul, map_fixedForm]

end Quadratic

section Regularity

variable {k K W V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup W] [AddCommGroup V] [Module k W] [Module K V]

private theorem polarRadicalComp (Q : QuadraticForm K V) (e : (K ⊗[k] W) ≃ₗ[K] V) :
    LinearMap.ker (Q.comp e.toLinearMap).polarBilin =
      (LinearMap.ker Q.polarBilin).comap e.toLinearMap := by
  rw [QuadraticMap.polarBilin_comp]
  apply Submodule.ext
  intro x
  simp only [Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · intro hx
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact LinearMap.congr_fun hx z
  · intro hx
    apply LinearMap.ext
    intro y
    exact LinearMap.congr_fun hx (e y)

private theorem regular_of_extension [Module.Finite k W]
    {I : Type u} [LinearOrder I] (q : QuadraticForm k W) (b : Basis I k W)
    (Q : QuadraticForm K V) (e : (K ⊗[k] W) ≃ₗ[K] V)
    (he : Q.comp e.toLinearMap = coefficientForm K q b) (hreg : IsRegular Q) : IsRegular q := by
  have hker := (LinearAlgebraicGroups.Arithmetic.SpinScalarExtension.polarRadicalExtension
    q b (F := K)).1
  rw [← he, polarRadicalComp] at hker
  rcases hreg with h | ⟨r, hr, h⟩
  · left
    apply Submodule.baseChange_injective (A := K)
    rw [← hker, h, Submodule.baseChange_bot, Submodule.comap_bot, LinearMap.ker_eq_bot]
    exact e.injective
  · let U := LinearMap.ker q.polarBilin
    let T := LinearMap.ker Q.polarBilin
    have hmap : (T.comap e.toLinearMap).map e.toLinearMap = T :=
      Submodule.map_comap_eq_of_surjective e.surjective _
    have hdim : finrank k U = 1 := by
      rw [← (Module.finrank_baseChange (R := K) (S := k) (M' := ↥U)),
        (Submodule.toBaseChange.toLinearEquiv K U).finrank_eq]
      change finrank K ((LinearMap.ker q.polarBilin).baseChange K) = 1
      rw [← hker]
      change finrank K (T.comap e.toLinearMap) = 1
      rw [(e.ofSubmodules _ _ hmap).finrank_eq]
      change finrank K (LinearMap.ker Q.polarBilin) = 1
      rw [h]
      exact finrank_span_singleton (by rintro rfl; exact hr (map_zero Q))
    have hatom := Submodule.isAtom_iff_finrank_eq_one.mpr hdim
    obtain ⟨z, hzmem, hz⟩ := (Submodule.ne_bot_iff U).mp hatom.ne_bot
    refine Or.inr ⟨z, ?_, eq_span_singleton_of_mem_of_finrank_eq_one hdim hzmem hz⟩
    intro hqz
    have hmem : (1 : K) ⊗ₜ[k] z ∈ U.baseChange K :=
      Submodule.tmul_mem_baseChange_of_mem 1 hzmem
    change (1 : K) ⊗ₜ[k] z ∈ (LinearMap.ker q.polarBilin).baseChange K at hmem
    rw [← hker] at hmem
    have hm : e ((1 : K) ⊗ₜ[k] z) ∈ K ∙ r := h ▸ hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have hne : e ((1 : K) ⊗ₜ[k] z) ≠ 0 := by
      intro hh
      apply hz
      apply Module.Flat.tensorProduct_mk_injective k W K
      change (1 : K) ⊗ₜ[k] z = (1 : K) ⊗ₜ[k] 0
      rw [TensorProduct.tmul_zero]
      exact e.injective (by simpa only [map_zero] using hh)
    have hcz : c ≠ 0 := by rintro rfl; exact hne (by simpa using hc.symm)
    have hzero : Q (e ((1 : K) ⊗ₜ[k] z)) = 0 := by
      have hh := QuadraticMap.congr_fun he ((1 : K) ⊗ₜ[k] z)
      change Q (e ((1 : K) ⊗ₜ[k] z)) = _ at hh
      rw [hh, LinearAlgebraicGroups.Albert.CliffordModel.coefficientForm_tmul, hqz]
      simp
    rw [← hc, Q.map_smul, smul_eq_mul] at hzero
    exact (mul_ne_zero (mul_ne_zero hcz hcz) hr) hzero

end Regularity

private theorem exists_fixed_quadratic_form {k K V : Type u} [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]
    (a : SemilinearAction k K V) (Q : QuadraticForm K V)
    (hQ : ∀ σ x, Q (a.act σ x) = σ (Q x)) :
    ∃ q : QuadraticForm k a.fixed,
      (∀ x, algebraMap k K (q x) = Q x.val) ∧
      (∀ {I : Type u} [LinearOrder I] (b : Basis I k a.fixed),
        ∃ e : (K ⊗[k] a.fixed) ≃ₗ[K] V,
          e.toLinearMap = a.descentMap ∧
          Q.comp e.toLinearMap = coefficientForm K q b) :=
  ⟨fixedForm a Q hQ, map_fixedForm a Q hQ, fun b =>
    ⟨a.descentEquiv, rfl, fixedForm_extension a Q hQ b⟩⟩

theorem quadraticDescent : QuadraticDescent.{u} := by
  intro k K V _ _ _ _ _ _ _ _ _ _ a Q hQ
  obtain ⟨q, hq, he⟩ := exists_fixed_quadratic_form a Q hQ
  obtain ⟨hfin, hdim⟩ := a.finiteDimensional_fixed
  refine ⟨q, hq, ?_, hdim, ?_⟩
  · intro I _ b
    obtain ⟨e, ham, hb⟩ := he b
    exact ⟨e, ham, fun x => QuadraticMap.congr_fun hb x⟩
  · intro hreg
    let b : Basis (ULift.{u} (Fin (finrank k a.fixed))) k a.fixed :=
      (finBasis k a.fixed).reindex Equiv.ulift.symm
    obtain ⟨e, _, hb⟩ := he b
    exact regular_of_extension q b Q e hb hreg

section Clifford

open CliffordAlgebra
open Albert.SpinSpecification
  (ScalarClifford vectors reversion evenPart spinUnits coefficientMap conjugate)

variable {k V W : Type u} [Field k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] {q : QuadraticForm k V} {Q : QuadraticForm k W}
    (e : q.IsometryEquiv Q)

private theorem isometry_reverse (x : CliffordAlgebra q) :
    equivOfIsometry e (reverse x) = reverse (equivOfIsometry e x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | «ι» v => simp [map_apply_ι]
  | mul x y hx hy => simp only [reverse.map_mul, map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem isometry_grade (j : ZMod 2) :
    (evenOdd q j).map (equivOfIsometry e).toLinearMap = evenOdd Q j := by
  change (evenOdd q j).map (CliffordAlgebra.map e.toIsometry).toLinearMap = _
  have hr : e.toIsometry.range = ⊤ := LinearMap.range_eq_top.mpr e.toLinearEquiv.surjective
  simp_rw [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_map, hr,
    Submodule.map_top]

private def scalarIsometryClifford (S : TestAlgebra k) :
    ScalarClifford q S ≃ₐ[S] ScalarClifford Q S :=
  Algebra.TensorProduct.congr AlgEquiv.refl (equivOfIsometry e)

private theorem scalarIsometryClifford_vectors (S : TestAlgebra k) (x : S ⊗[k] V) :
    scalarIsometryClifford e S (vectors q S x) =
      vectors Q S (LinearEquiv.baseChange k S V W e.toLinearEquiv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => simp [scalarIsometryClifford, map_apply_ι]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem scalarIsometryClifford_reverse (S : TestAlgebra k) (x : ScalarClifford q S) :
    scalarIsometryClifford e S (reversion q S x) =
      reversion Q S (scalarIsometryClifford e S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    change s ⊗ₜ[k] equivOfIsometry e (reverse x) =
      s ⊗ₜ[k] reverse (equivOfIsometry e x)
    rw [isometry_reverse]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem scalarIsometryClifford_grade (S : TestAlgebra k) :
    (evenPart q S).map (scalarIsometryClifford e S).toLinearMap = evenPart Q S := by
  change ((evenOdd q 0).baseChange S).map (scalarIsometryClifford e S).toLinearMap =
    (evenOdd Q 0).baseChange S
  rw [← isometry_grade e, Submodule.baseChange_eq_span, Submodule.map_span,
    Submodule.baseChange_eq_span]
  simp only [Submodule.map_coe, Set.image_image]
  rfl

private theorem scalarIsometryClifford_spin (S : TestAlgebra k) (a : (ScalarClifford q S)ˣ) :
    Units.map (scalarIsometryClifford e S).toMonoidHom a ∈ spinUnits Q S ↔ a ∈ spinUnits q S := by
  let E := scalarIsometryClifford e S
  let U := LinearEquiv.baseChange k S V W e.toLinearEquiv
  let φ := Units.map E.toMonoidHom
  have hvec (x : S ⊗[k] V) : E (vectors q S x) = vectors Q S (U x) :=
    scalarIsometryClifford_vectors e S x
  have hrange (x : ScalarClifford q S) :
      E x ∈ LinearMap.range (vectors Q S) ↔ x ∈ LinearMap.range (vectors q S) := by
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := U.surjective y
      exact ⟨z, E.injective ((hvec z).trans hy)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨U z, (hvec z).symm⟩
  have hconj (g : (ScalarClifford q S)ˣ) (x : ScalarClifford q S) :
      E (conjugate q S g x) = conjugate Q S (φ g) (E x) := by
    simp only [conjugate, map_mul, φ, Units.coe_map, Units.coe_map_inv]
    rfl
  have hnormal (g : (ScalarClifford q S)ˣ) :
      Set.MapsTo (conjugate Q S (φ g)) (LinearMap.range (vectors Q S))
        (LinearMap.range (vectors Q S)) ↔
      Set.MapsTo (conjugate q S g) (LinearMap.range (vectors q S))
        (LinearMap.range (vectors q S)) := by
    constructor
    · intro h x hx
      exact (hrange _).mp (hconj g x ▸ h ((hrange x).mpr hx))
    · intro h y hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [← hconj]
      exact (hrange _).mpr (h ((hrange x).mp hy))
  have hnorm : reversion Q S (φ a).val * (φ a).val = 1 ↔
      reversion q S a.val * a.val = 1 := by
    change reversion Q S (E a.val) * E a.val = 1 ↔ _
    rw [← scalarIsometryClifford_reverse e S, ← map_mul, ← E.map_one]
    exact E.injective.eq_iff
  have hgrade : E a.val ∈ evenPart Q S ↔ a.val ∈ evenPart q S := by
    rw [← scalarIsometryClifford_grade e S, Submodule.mem_map_equiv]
    exact Iff.of_eq (congrArg (fun y => y ∈ evenPart q S) (E.symm_apply_apply a.val))
  change (E a.val ∈ evenPart Q S ∧ reversion Q S (φ a).val * (φ a).val = 1 ∧
    _ ∧ Set.MapsTo (conjugate Q S (φ a)⁻¹) _ _) ↔ _
  rw [hgrade, hnorm, hnormal, ← φ.map_inv, hnormal]
  rfl

theorem cliffordIsometryComparison : CliffordIsometryComparison.{u} := by
  intro k V W _ _ _ _ _ q Q e
  refine ⟨scalarIsometryClifford e, scalarIsometryClifford_vectors e,
    scalarIsometryClifford_reverse e, scalarIsometryClifford_grade e,
    scalarIsometryClifford_spin e, ?_⟩
  intro S T f x
  induction x using TensorProduct.inductionOn with
  | tmul s a => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

open Albert.SpinSpecification (IsSpinPointRepresentation)
open Specs.AdjointRepresentation (GroupPoints)

set_option maxHeartbeats 1000000 in
theorem spinIsometryGroupComparison : SpinIsometryGroupComparison.{u} := by
  intro k V W _ _ _ _ _ q Q e G H g h hg hh
  let E := scalarIsometryClifford e
  let φ (S : TestAlgebra k) := Units.mapEquiv (E S).toMulEquiv
  have hr (S : TestAlgebra k) : ((g S).range.map (φ S).toMonoidHom) = (h S).range := by
    apply SetLike.ext
    intro y
    change y ∈ (φ S) '' Set.range (g S) ↔ y ∈ Set.range (h S)
    rw [(hg.1 S).2, (hh.1 S).2]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (scalarIsometryClifford_spin e S a).2 ha
    · intro hy
      obtain ⟨a, rfl⟩ := (φ S).surjective y
      exact ⟨a, (scalarIsometryClifford_spin e S a).1 hy, rfl⟩
  let f (S : TestAlgebra k) : GroupPoints G.val S ≃* GroupPoints H.val S :=
    (MonoidHom.ofInjective (hg.1 S).1).trans <| ((φ S).subgroupMap (g S).range).trans <|
      (MulEquiv.subgroupCongr (hr S)).trans (MonoidHom.ofInjective (hh.1 S).1).symm
  have hf (S : TestAlgebra k) (x : GroupPoints G.val S) : h S (f S x) = φ S (g S x) := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective (hh.1 S).1).apply_symm_apply
        ((MulEquiv.subgroupCongr (hr S)) ((φ S).subgroupMap (g S).range
          (MonoidHom.ofInjective (hg.1 S).1 x))))
  have hnat {S T : TestAlgebra k} (m : S ⟶ T) (x : GroupPoints G.val S) :
      f T (mapPoints m x) = mapPoints m (f S x) := by
    apply (hh.1 T).1
    have hleft := hf T (mapPoints m x)
    have hg' := hg.2 m x
    have hh' := hh.2 m (f S x)
    have hright := congrArg (Units.map (coefficientMap Q S m.hom).toMonoidHom) (hf S x)
    apply hleft.trans
    apply (congrArg (φ T) hg').trans
    apply Eq.trans _ (hh'.trans hright).symm
    apply Units.ext
    change E T (coefficientMap q S m.hom (g S x).val) =
      coefficientMap Q S m.hom (E S (g S x).val)
    generalize (g S x).val = a
    induction a using TensorProduct.inductionOn with
    | tmul s a => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  let natIso : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj H.val :=
    NatIso.ofComponents (fun S => (f S).toGrpIso) (by
      intro S T m
      apply GrpCat.ext
      intro x
      exact hnat m x)
  let F := groupPointsFunctor k
  let toScheme := LinearAlgebraicGroups.groupHomEquiv G.val H.val G.property.1
  let fromScheme := LinearAlgebraicGroups.groupHomEquiv H.val G.val H.property.1
  let i := toScheme.symm natIso.hom
  let j := fromScheme.symm natIso.inv
  have hi : F.map i = natIso.hom := toScheme.apply_symm_apply _
  have hj : F.map j = natIso.inv := fromScheme.apply_symm_apply _
  refine ⟨⟨i, j, ?_, ?_⟩, ?_⟩
  · apply (LinearAlgebraicGroups.groupHomComparison k G.val G.val G.property.1).1
    change F.map (i ≫ j) = F.map (𝟙 G.val)
    rw [F.map_comp, F.map_id, hi, hj, natIso.hom_inv_id]
  · apply (LinearAlgebraicGroups.groupHomComparison k H.val H.val H.property.1).1
    change F.map (j ≫ i) = F.map (𝟙 H.val)
    rw [F.map_comp, F.map_id, hi, hj, natIso.inv_hom_id]
  · intro S x
    have hix := DFunLike.congr_fun (congrArg (fun n ↦ (n.app S).hom) hi) x
    change x ≫ i.hom.hom = f S x at hix
    rw [hix]
    exact hf S x

end Clifford

section Isotropy

open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open RationalRepresentations (trivialLinearMap)
open WeightDecomposition (weightSpace mem_weightSpace weightDecomposition)

theorem isotropicOfOrthogonalCoaction : IsotropicOfOrthogonalCoaction.{u} := by
  classical
  intro k V I _ _ _ _ q b A ρ hρ hnorm
  have hwt : ∃ (m : IntegerCharacters) (v : V), m ≠ 1 ∧ v ≠ 0 ∧ v ∈ weightSpace ρ m := by
    by_contra! h
    apply hρ
    let f := ρ.coaction - trivialLinearMap A
    have hker : (⨆ m, weightSpace ρ m) ≤ LinearMap.ker f :=
      iSup_le fun m v hv => by
        by_cases hm : m = 1
        · subst m
          simp only [LinearMap.mem_ker, f, LinearMap.sub_apply, sub_eq_zero]
          exact (mem_weightSpace.mp hv).trans
            (by simp [trivialLinearMap, TensorProduct.comm_tmul, ← MonoidAlgebra.one_def])
        · have hzero : v = 0 := by
            by_contra hne
            exact h m v hm hne hv
          simp [hzero]
    have htop := @DirectSum.IsInternal.submodule_iSup_eq_top k _ IntegerCharacters
      (Classical.decEq _) V _ _ (weightSpace ρ) (weightDecomposition ρ)
    rw [htop, top_le_iff, LinearMap.ker_eq_top] at hker
    exact sub_eq_zero.mp hker
  obtain ⟨m, v, hm, hv, hvw⟩ := hwt
  refine ⟨v, hv, ?_⟩
  have hn := hnorm v
  rw [mem_weightSpace.mp hvw, TensorProduct.comm_tmul,
    Albert.CliffordModel.coefficientForm_tmul, Albert.CliffordModel.coefficientForm_tmul,
    one_mul, one_mul] at hn
  by_contra hq
  have ha : IsUnit (algebraMap k A (q v)) := (isUnit_iff_ne_zero.mpr hq).map (algebraMap k A)
  have hsq : (MonoidAlgebra.of k IntegerCharacters m : A) *
      MonoidAlgebra.of k IntegerCharacters m = 1 :=
    ha.mul_right_cancel (hn.trans (one_mul _).symm)
  rw [← map_mul, ← (MonoidAlgebra.of k IntegerCharacters).map_one] at hsq
  have hm2 := MonoidAlgebra.of_injective hsq
  apply hm
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  change m.down.toAdd = 0
  have hh := congrArg (fun x : IntegerCharacters => x.down.toAdd) hm2
  change m.down.toAdd + m.down.toAdd = 0 at hh
  omega


open Specs.CharacterDescent (Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)
open Albert.SpinSpecification (ScalarClifford IsSpinPointRepresentation)
open Albert.SpinFunctor (Spin spinSubgroup vectorAction)
open RationalRepresentations (pointsCoactionEquiv coefficients coaction_apply_basis)
open private changeModule from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private pointMatrix pointMatrix_isCoactionMatrix from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

section PointAction

variable {k V I : Type u} [Field k] [AddCommGroup V] [Module k V] [LinearOrder I]
  [Fintype I] {q : QuadraticForm k V} (b : Basis I k V) {G : Specs.AffineAlgebraicGroup k}
  {spinRep : ∀ S : TestAlgebra k, GroupPoints G.val S →* (ScalarClifford q S)ˣ}
  (hspinRep : IsSpinPointRepresentation q G.val spinRep)

private def spinOfPoint (S : TestAlgebra k) : GroupPoints G.val S →* Spin q S b :=
  (spinRep S).codRestrict (spinSubgroup q S b) fun x => by
    change spinRep S x ∈ Albert.SpinSpecification.spinUnits q S
    rw [← (hspinRep.1 S).2]
    exact Set.mem_range_self x

omit [Fintype I] in
private theorem spinOfPoint_natural {S T : TestAlgebra k} (f : S ⟶ T) (a : GroupPoints G.val S) :
    spinOfPoint b hspinRep T (mapPoints f a) =
      Albert.SpinFunctor.map q b f.hom (spinOfPoint b hspinRep S a) := by
  apply Subtype.ext
  exact hspinRep.2 f a

private def toUnitMatrix (S : TestAlgebra k) :
    ((S ⊗[k] V) ≃ₗ[S] (S ⊗[k] V)) →* Matrix.GeneralLinearGroup I S :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange S)).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv S (S ⊗[k] V)).symm.toMonoidHom

private theorem toUnitMatrix_entry (S : TestAlgebra k)
    (f : (S ⊗[k] V) ≃ₗ[S] (S ⊗[k] V)) (i j : I) :
    (toUnitMatrix b S f).val i j = (b.baseChange S).repr (f (1 ⊗ₜ[k] b j)) i := by
  change LinearMap.toMatrixAlgEquiv (b.baseChange S) f.toLinearMap i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply, Basis.baseChange_apply]
  rfl

omit [LinearOrder I] [Fintype I] in
private theorem baseChange_repr_map {S T : TestAlgebra k} (f : S ⟶ T)
    (x : S ⊗[k] V) (i : I) :
    (b.baseChange T).repr (changeModule f.hom x) i = f.hom ((b.baseChange S).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    change (b.baseChange T).repr (f.hom s ⊗ₜ[k] v) i = _
    simp [Basis.baseChange_repr_tmul, Algebra.smul_def, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

private def spinMatrixPoints : (groupPointsFunctor k).obj G.val ⟶
    Specs.StandardGroups.generalLinearPoints k I where
  app S := GrpCat.ofHom ((toUnitMatrix b S).comp
    ((vectorAction q S b).comp (spinOfPoint b hspinRep S)))
  naturality S T f := by
    apply GrpCat.ext
    intro a
    apply Units.ext
    ext i j
    change (toUnitMatrix b T (vectorAction q T b (spinOfPoint b hspinRep T (mapPoints f a)))).val i j =
      f.hom ((toUnitMatrix b S (vectorAction q S b (spinOfPoint b hspinRep S a))).val i j)
    rw [spinOfPoint_natural, toUnitMatrix_entry, toUnitMatrix_entry,
      ← baseChange_repr_map b f]
    have hOne : changeModule f.hom ((1 : S) ⊗ₜ[k] b j) = (1 : T) ⊗ₜ[k] b j := by
      change (f.hom 1) ⊗ₜ[k] b j = _
      rw [map_one]
    rw [← hOne, ← Albert.SpinFunctor.vectorAction_naturality]

include hspinRep in
private theorem commutes_of_scalar_universal (c : Cocharacter G.val)
    (h : let A := groupAlgebra k IntegerCharacters
         let R := CommAlgCat.of k A
         ∃ s : R, (spinRep R (c.hom.hom : GroupPoints G.val R)).val =
           algebraMap R (ScalarClifford q R) s) :
    ∀ (X : SchemeOver k) (g : X ⟶ G.val.X), Centralizes c g := by
  let A := groupAlgebra k IntegerCharacters
  let R := CommAlgCat.of k A
  obtain ⟨s, hs⟩ := h
  have htest (S : TestAlgebra k)
      (t : GroupPoints (specGroup A) S) (p : GroupPoints G.val S) :
      Commute (t ≫ c.hom.hom) p := by
    let f : op S ⟶ op R := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t
    have hf : (testSpec k).map f = t := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage t
    have hspinRepf := hspinRep.2 f.unop (c.hom.hom : GroupPoints G.val R)
    change spinRep S ((testSpec k).map f ≫ c.hom.hom) = _ at hspinRepf
    rw [hf] at hspinRepf
    let z : GroupPoints G.val S := t ≫ c.hom.hom
    change Commute z p
    change spinRep S z = _ at hspinRepf
    show z * p = p * z
    apply (hspinRep.1 S).1
    refine ((spinRep S).map_mul z p).trans (Eq.trans ?_ ((spinRep S).map_mul p z).symm)
    rw [hspinRepf]
    apply Units.ext
    change ((Albert.SpinSpecification.coefficientMap q R f.unop.hom) (spinRep R c.hom.hom).val) *
        (spinRep S p).val =
      (spinRep S p).val *
        ((Albert.SpinSpecification.coefficientMap q R f.unop.hom) (spinRep R c.hom.hom).val)
    have hs' : (spinRep R c.hom.hom).val = algebraMap R (ScalarClifford q R) s := hs
    rw [hs']
    change algebraMap S _ (f.unop.hom s) * (spinRep S p).val =
      (spinRep S p).val * algebraMap S _ (f.unop.hom s)
    exact Algebra.commutes _ _
  let H := specGroup A
  let M := H.X ⊗ G.val.X
  have hM : IsAffine M.left := by
    let : IsAffine H.X.left := AlgebraicGeometry.isAffine_Spec _
    let : IsAffine G.val.X.left := G.property.1
    change IsAffine (CategoryTheory.Limits.pullback H.X.hom G.val.X.hom)
    infer_instance
  obtain ⟨B, ⟨o⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hM
  have h := htest B.unop (o.hom ≫ fst H.X G.val.X) (o.hom ≫ snd H.X G.val.X)
  have hm : Commute (fst H.X G.val.X ≫ c.hom.hom) (snd H.X G.val.X) := by
    apply (cancel_epi o.hom).mp
    simp only [MonObj.comp_mul]
    exact h.eq
  intro X g
  apply (centralizes_iff c g).2
  intro U v t
  let z : U ⟶ M := lift t (v ≫ g)
  have hv := congrArg (fun a : M ⟶ G.val.X => z ≫ a) hm.eq
  have hh : Commute (t ≫ c.hom.hom) (v ≫ g) := by
    change (t ≫ c.hom.hom) * (v ≫ g) = (v ≫ g) * (t ≫ c.hom.hom)
    simpa only [z, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd] using hv
  exact hh.symm

set_option maxHeartbeats 900000 in
theorem spinCocharacterIsotropy : SpinCocharacterIsotropy.{u} := by
  classical
  intro k V I _ _ _ _ _ q b G spinRep hreg hspinRep c hnoncentral
  let A := groupAlgebra k IntegerCharacters
  let R := CommAlgCat.of k A
  let H := specGroup A
  obtain ⟨E, hE, _⟩ := hopfSpecPoints k
  let α := (E A).hom ≫ (groupPointsFunctor k).map c ≫ spinMatrixPoints b hspinRep
  let ρ := pointsCoactionEquiv A b α
  let p : GroupPoints G.val R := c.hom.hom
  have hgeneric : (E A).hom.app R (toConv (AlgHom.id k A)) = 𝟙 H.X := by
    apply Over.OverMorphism.ext
    rw [hE]
    change Spec.map (𝟙 _) = 𝟙 (Spec (CommRingCat.of A))
    simp
  have hcoeff : coefficients A b ρ = (toUnitMatrix b R (vectorAction q R b (spinOfPoint b hspinRep R p))).val := by
    change coefficients A b (RationalRepresentations.coactionOfMatrix A b (pointMatrix A α)
      (pointMatrix_isCoactionMatrix A α)) = _
    rw [RationalRepresentations.coefficients_coactionOfMatrix]
    change ((spinMatrixPoints b hspinRep).app R
      (((groupPointsFunctor k).map c).app R ((E A).hom.app R (toConv (AlgHom.id k A))))).val = _
    rw [hgeneric]
    rfl
  have hact (x : V) : (TensorProduct.comm k V A) (ρ.coaction x) =
      vectorAction q R b (spinOfPoint b hspinRep R p) (1 ⊗ₜ[k] x) := by
    let lin : V →ₗ[k] R ⊗[k] V :=
      ((vectorAction q R b (spinOfPoint b hspinRep R p)).toLinearMap.restrictScalars k).comp
        (TensorProduct.mk k R V 1)
    change ((TensorProduct.comm k V A).toLinearMap.comp ρ.coaction) x = lin x
    suffices he : (TensorProduct.comm k V A).toLinearMap.comp ρ.coaction = lin by rw [he]
    apply b.ext
    intro j
    change (TensorProduct.comm k V A) (ρ.coaction (b j)) =
      vectorAction q R b (spinOfPoint b hspinRep R p) (1 ⊗ₜ[k] b j)
    rw [coaction_apply_basis A b, hcoeff, map_sum]
    calc
      _ = ∑ i, (b.baseChange R).repr (vectorAction q R b (spinOfPoint b hspinRep R p)
          (1 ⊗ₜ[k] b j)) i • (b.baseChange R i) := by
        simp only [TensorProduct.comm_tmul, toUnitMatrix_entry, Basis.baseChange_apply,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = _ := (b.baseChange R).sum_repr _
  apply isotropicOfOrthogonalCoaction q b ρ
  · intro ht
    have hv : vectorAction q R b (spinOfPoint b hspinRep R p) = 1 := by
      apply LinearEquiv.toLinearMap_injective
      apply (b.baseChange R).ext
      intro j
      have h := hact (b j)
      rw [ht] at h
      simpa [trivialLinearMap, TensorProduct.comm_tmul, Basis.baseChange_apply] using h.symm
    obtain ⟨F, hF⟩ := Albert.SpinFunctor.regularKernelSpecification q b hreg R
      (spinSubgroup q R b) (vectorAction q R b) rfl (Albert.SpinFunctor.vectorAction_characterization q R b)
    obtain ⟨ζ, hζ⟩ := F.surjective ⟨spinOfPoint b hspinRep R p, hv⟩
    have hh := hF ζ
    rw [hζ] at hh
    have hscalar : ∃ s : R, (spinRep R p).val = algebraMap R _ s := ⟨ζ.val.val, hh⟩
    obtain ⟨X, g, hg⟩ := hnoncentral
    exact hg (commutes_of_scalar_universal hspinRep c hscalar X g)
  · intro x
    rw [hact]
    exact Albert.SpinFunctor.vectorAction_preserves q R b _ _

end PointAction
end Isotropy

section InnerForms

open Specs.AutomorphismSequence
open Specs.RelativeFormComparison
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open LinearAlgebraicGroups.Descent.QuasiSplitInnerForms (splitKernel liftInnerCocycle)

theorem typeBInnerDisplacement : TypeBInnerDisplacement.{u} := by
  intro k S _ _ _ A P D l Q E n b hm hy H i σ
  apply (splitKernel E _).mp
  exact basedDatumRigidity D.toBased n b hm hy _

set_option maxHeartbeats 900000 in
theorem finiteInnerCocycle : FiniteInnerCocycle.{u} := by
  intro k S _ _ _ _ G H Q inn i L₀ hinj hinner
  obtain ⟨j, _⟩ :=
    LinearAlgebraicGroups.Descent.RelativeFormComparison.schemeIsomorphismComparison
      (S := S) G.val H.val
  obtain ⟨C⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification
    (S := S) G
  obtain ⟨a, ha, _⟩ := C.computes ⟨H, ⟨j.symm i⟩⟩ i
  obtain ⟨d, hd, _⟩ := liftInnerCocycle G.val Q.val inn hinj a (by simpa only [ha] using hinner)
  let : TopologicalSpace (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points k S Q.val.X) := ⊥
  let : DiscreteTopology (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points k S Q.val.X) := ⟨rfl⟩
  obtain ⟨L, c, hle, hc⟩ := finiteLevel L₀ d
  obtain ⟨e, he, heAct⟩ := finitePointsIdentification (H := Q.val.X) L
  refine ⟨L, fun σ => e.symm (c σ), hle, ?_, ?_⟩
  · intro σ τ
    apply e.injective
    rw [e.apply_symm_apply, map_mul, heAct, e.apply_symm_apply, e.apply_symm_apply]
    exact c.property.2 σ τ
  · intro σ
    have h : pointMap k L Q.val.X L.toIntermediateField.val (e.symm (c (restriction L σ))) =
        d σ := by rw [← he, e.apply_symm_apply, hc σ]
    rw [h, hd σ, ha σ]

open LinearAlgebraicGroups.Descent.Forms (raiseIso scalarTowerIso)
open private applyIso applyIso_left inLevel inLevel_tmul raiseIso_ext raiseIso_inLevel from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms

private theorem raiseIso_apply {k L K : Type u} [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    {P B : HopfAlgebraCategory k} (j : extendedHopf L P ≅ extendedHopf L B)
    (x : extendedHopf L P) :
    applyIso (raiseIso (S := K) j) (applyIso (scalarTowerIso P) ((1 : K) ⊗ₜ[L] x)) =
      applyIso (scalarTowerIso B) ((1 : K) ⊗ₜ[L] applyIso j x) := by
  change applyIso (scalarTowerIso B) ((extendedHopfMap K j.hom).hom
    (applyIso (scalarTowerIso P).symm (applyIso (scalarTowerIso P) ((1 : K) ⊗ₜ[L] x)))) = _
  rw [applyIso_left]
  rfl

set_option maxHeartbeats 1000000 in
private theorem raiseIso_tower {k S : Type u} [Field k] [Field S] [Algebra k S]
    (L₀ L : FiniteGaloisIntermediateField k S)
    [Algebra L₀ L] [IsScalarTower k L₀ L] [IsScalarTower L₀ L S]
    {P B : HopfAlgebraCategory k} (j : extendedHopf L₀ P ≅ extendedHopf L₀ B) :
    raiseIso (L := L) (S := S) (raiseIso (S := L) j) = raiseIso j := by
  have hbase (C : HopfAlgebraCategory k) (x : extendedHopf L₀ C) :
      inLevel L C (applyIso (scalarTowerIso C) ((1 : L) ⊗ₜ[L₀] x)) = inLevel L₀ C x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      have h₁ {F : FiniteGaloisIntermediateField k S} (a b : extendedHopf F C) :
          inLevel F C (a + b) = inLevel F C a + inLevel F C b := by
        change applyIso (scalarTowerIso C) ((1 : S) ⊗ₜ[F] (a + b)) = _
        simp only [TensorProduct.tmul_add, map_add]
      rw [TensorProduct.tmul_add, show applyIso (scalarTowerIso C)
          ((1 : L) ⊗ₜ[L₀] x + (1 : L) ⊗ₜ[L₀] y) =
        applyIso (scalarTowerIso C) ((1 : L) ⊗ₜ[L₀] x) +
          applyIso (scalarTowerIso C) ((1 : L) ⊗ₜ[L₀] y) from
            (scalarTowerIso C).hom.hom.map_add _ _, h₁, h₁, hx, hy]
    | tmul l y =>
      change inLevel L C ((l • (1 : L)) ⊗ₜ[k] y) = _
      rw [Algebra.smul_def, mul_one, inLevel_tmul, inLevel_tmul,
        ← IsScalarTower.algebraMap_apply L₀ L S]
  apply raiseIso_ext L₀
  intro x
  conv_lhs => rw [← hbase]
  rw [raiseIso_inLevel, raiseIso_apply, hbase, raiseIso_inLevel]

set_option maxHeartbeats 1300000 in
theorem finiteInnerTrivialization : FiniteInnerTrivialization.{u} := by
  intro k S _ _ _ _ G H Q inn i P B g h t hP hB ht hinj hinner
  obtain ⟨e, he, _⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.hopfIsomorphismComparison t ht g h
  let jₛ := e.symm i
  have hjₛ : e jₛ = i := e.apply_symm_apply i
  obtain ⟨L₀, j, _, hj⟩ := LinearAlgebraicGroups.Descent.Forms.finiteLevelIsomorphisms
    P B hP hB ⊥ jₛ
  obtain ⟨L, d, hLL, hd, htop⟩ := finiteInnerCocycle G H Q inn i L₀ hinj hinner
  let f := IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff _ _).mp hLL)
  let : Algebra L₀ L := f.toRingHom.toAlgebra
  let : IsScalarTower k L₀ L := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let : IsScalarTower L₀ L S := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨L, raiseIso (S := L) j, d, ?_, hd, htop⟩
  rw [raiseIso_tower L₀ L, hj]
  exact (he jₛ i).2 hjₛ

private theorem coefficientForm_galois {k K V I : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [LinearOrder I] (q : QuadraticForm k V)
    (b : Basis I k V) (σ : Gal(K/k)) (x : K ⊗[k] V) :
    coefficientForm K q b ((SemilinearAction.scalarExtension V).act σ x) =
      σ (coefficientForm K q b x) := by
  let a := SemilinearAction.scalarExtension (k := k) (K := K) V
  let B := LinearMap.BilinForm.baseChange K (q.toBilin b)
  change B (a.act σ x) (a.act σ x) = σ (B x x)
  have h (x y : K ⊗[k] V) : B (a.act σ x) (a.act σ y) = σ (B x y) := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
    | tmul r v =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul s w =>
        change B ((σ r) ⊗ₜ[k] v) ((σ s) ⊗ₜ[k] w) = σ (B (r ⊗ₜ[k] v) (s ⊗ₜ[k] w))
        simp [B, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact h x x

theorem adjointQuadraticDescent : AdjointQuadraticDescent.{u} := by
  intro k K V I _ _ _ _ _ _ _ _ _ q₀ b₀ J Q a₀ ρ hρ hn d hd
  have hd₁ : d 1 = 1 := by
    have h : d 1 = d 1 * d 1 := by simpa using hd 1 1
    exact mul_left_cancel (a := d 1) (by simpa using h.symm)
  let a : SemilinearAction k K (K ⊗[k] V) :=
    { act := fun σ => (a₀.act σ).trans ((ρ (d σ)).toAddEquiv)
      one_act := fun x => by
        change ρ (d 1) (a₀.act 1 x) = x
        rw [hd₁, map_one, a₀.one_act]
        rfl
      mul_act := fun σ τ x => by
        change ρ (d (σ * τ)) (a₀.act (σ * τ) x) =
          ρ (d σ) (a₀.act σ (ρ (d τ) (a₀.act τ x)))
        rw [hd, map_mul, a₀.mul_act, hn]
        rfl
      map_smul := fun σ r x => by
        change ρ (d σ) (a₀.act σ (r • x)) = σ r • ρ (d σ) (a₀.act σ x)
        rw [a₀.map_smul, map_smul] }
  have hinv (σ : Gal(K/k)) (x : K ⊗[k] V) : Q (a.act σ x) = σ (Q x) := by
    change Q (ρ (d σ) (a₀.act σ x)) = _
    rw [hρ]
    exact coefficientForm_galois q₀ b₀ σ x
  obtain ⟨q, hq, he, hdim, hr⟩ := quadraticDescent a Q hinv
  exact ⟨a, fun _ _ => rfl, q, hq, he, hdim.trans Module.finrank_baseChange, hr⟩

open Specs.Unipotent (baseChangedAlgebraicGroup)
open Albert.SpinSpecification (SchemePoints ScalarClifford IsSpinPointRepresentation
  spinUnits coefficientMap vectors)
open LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
  (polarRadicalExtension spinRepresentationExtension)

private theorem spin_scheme_of_form {k W I : Type u} [Field k] [AddCommGroup W]
    [Module k W] [LinearOrder I] [Fintype I] (q : QuadraticForm k W) (b : Basis I k W) :
    ∃ (H : Specs.AffineAlgebraicGroup k)
      (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ),
      IsSpinPointRepresentation q H.val h := by
  obtain ⟨A, _, H₀, hH₀, ha, hfp, h, hh⟩ := Albert.SpinFunctor.affineRepresentation q b
  have hAff : IsAffine H₀.X.left :=
    AlgebraicGeometry.essImage_algSpec.mp ⟨op A, ⟨eqToIso hH₀.symm⟩⟩
  let : LocallyOfFinitePresentation H₀.X.hom := hfp
  let : IsAffineHom H₀.X.hom := ha
  exact ⟨⟨H₀, hAff, inferInstance, inferInstance⟩, h, hh⟩

private theorem regular_coefficientForm {k K V I : Type u} [Field k] [Field K]
    [Algebra k K] [AddCommGroup V] [Module k V] [Module.Finite k V] [LinearOrder I]
    (q : QuadraticForm k V) (b : Basis I k V) (hreg : IsRegular q) :
    IsRegular (coefficientForm K q b) := by
  rcases hreg with h | ⟨r, hr, hh⟩
  · exact Or.inl ((polarRadicalExtension q b (F := K)).2.1 h)
  · exact Or.inr ⟨1 ⊗ₜ[k] r, (polarRadicalExtension q b (F := K)).2.2 r hr hh⟩

open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso)
open LinearAlgebraicGroups.Descent.Forms (spectrumIso)
open private extendedGroupIso extendedSpecIso_hom_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private descend_standard_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms

set_option maxHeartbeats 1200000 in
theorem descendCompatibleSpinComparison : DescendCompatibleSpinComparison.{u} := by
  intro k K W _ _ _ _ _ _ q H G h hh i hi
  let t := extendedGroupIso (k := k) K
  have ht : LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t :=
    fun A => extendedSpecIso_hom_fst K A
  obtain ⟨e, _, he⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.hopfIsomorphismComparison
    t ht (coordinateHopfIso H) (coordinateHopfIso G)
  let f := e.symm i
  have hf : e f = i := e.apply_symm_apply i
  have hf' (σ : Gal(K/k)) : HopfConjugates σ f f := by
    apply (he σ f f).2
    rw [hf, hi]
  obtain ⟨f₀, _⟩ := descend_standard_iso f hf'
  let j := (coordinateHopfIso H).symm ≪≫ spectrumIso f₀ ≪≫ coordinateHopfIso G
  let E := (groupPointsFunctor k).mapIso j.symm
  let g (R : TestAlgebra k) := (h R).comp (E.hom.app R).hom
  have hE (R : TestAlgebra k) (x : SchemePoints G.val R) :
      E.hom.app R x = x ≫ j.inv.hom.hom := rfl
  have hbij (R : TestAlgebra k) : Function.Bijective (E.hom.app R) := by
    let eR := E.app R
    exact ⟨fun x y hxy => by
      have hx := ConcreteCategory.congr_hom eR.hom_inv_id x
      have hy := ConcreteCategory.congr_hom eR.hom_inv_id y
      exact hx.symm.trans ((congrArg eR.inv hxy).trans hy),
      fun x => ⟨eR.inv x, ConcreteCategory.congr_hom eR.inv_hom_id x⟩⟩
  refine ⟨j, g, ⟨fun R => ⟨(hh.1 R).1.comp (hbij R).1, ?_⟩, ?_⟩, ?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      rw [← (hh.1 R).2]
      exact ⟨E.hom.app R x, rfl⟩
    · intro y hy
      rw [← (hh.1 R).2] at hy
      obtain ⟨z, rfl⟩ := hy
      obtain ⟨x, hx⟩ := (hbij R).2 z
      exact ⟨x, congrArg (h R) hx⟩
  · intro R S f x
    change h S (E.hom.app S ((testSpec k).map f.op ≫ x)) =
      Units.map (coefficientMap q R f.hom).toMonoidHom (h R (E.hom.app R x))
    rw [hE, Category.assoc]
    exact hh.2 f _
  · intro R x
    change h R (E.hom.app R (x ≫ j.hom.hom.hom)) = h R x
    have hx := ConcreteCategory.congr_hom (E.app R).inv_hom_id x
    exact congrArg (h R) hx

open Specs.Arithmetic.SpinScalarExtension (restricted vectorComparison)
open CategoryTheory.Limits (pullback)
open private schemeIsoEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private relativeSectionEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

section CliffordDescent

set_option maxRecDepth 180

section ScalarComparison

private def fieldAlgebraInclusion {k K : Type u} [Field k] [Field K] [Algebra k K]
    (R : TestAlgebra K) : CommAlgCat.of k K ⟶ restricted k R :=
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  ConcreteCategory.ofHom (C := CommAlgCat k)
    ({ toRingHom := algebraMap K R, commutes' := fun _ => rfl } : K →ₐ[k] R)

private abbrev fieldAlgebraSlice {k K : Type u} [Field k] [Field K] [Algebra k K]
    (R : TestAlgebra K) : Over (fieldTest k K) :=
  Over.mk ((testSpec k).map (fieldAlgebraInclusion (k := k) R).op)

private def mapVector {k : Type u} [Field k] {R T : TestAlgebra k}
    (f : R ⟶ T) (V : Type u) [AddCommGroup V] [Module k V] :
    (R ⊗[k] V) →ₗ[k] (T ⊗[k] V) :=
  TensorProduct.map f.hom.toLinearMap LinearMap.id

private theorem mapVector_comp {k : Type u} [Field k] {R T U : TestAlgebra k}
    (f : R ⟶ T) (g : T ⟶ U) {V : Type u} [AddCommGroup V] [Module k V]
    (x : R ⊗[k] V) :
    mapVector g V (mapVector f V x) = mapVector (f ≫ g) V x := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mapVector_galois {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] (σ : Gal(K/k)) (x : K ⊗[k] V) :
    mapVector (CommAlgCat.ofHom σ.toAlgHom) V x =
      (SemilinearAction.scalarExtension (k := k) (K := K) V).act σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem coefficientMap_vectors_natural {k V : Type u} [Field k] [AddCommGroup V]
    [Module k V] (q : QuadraticForm k V) {R T : TestAlgebra k} (f : R ⟶ T) (x : R ⊗[k] V) :
    coefficientMap q R f.hom (vectors q R x) = vectors q T (mapVector f V x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem vectorComparison_one {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] (R : TestAlgebra K) (x : K ⊗[k] V) :
    vectorComparison (R := R) ((1 : R) ⊗ₜ[K] x) =
      mapVector (fieldAlgebraInclusion R) V x := by
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    let : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
    change (r • (1 : R)) ⊗ₜ[k] v = (algebraMap K R r) ⊗ₜ[k] v
    rw [Algebra.smul_def, mul_one]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem relativeComparison_apply {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H G : GroupScheme k} (j : (groupBaseChange k K).obj H ≅ (groupBaseChange k K).obj G)
    (R : TestAlgebra K) (p : SchemePoints ((groupBaseChange k K).obj H) R) :
    ((schemeIsoEquiv K H G j).hom.app (op (fieldAlgebraSlice R))).hom
        (baseChangePoint k K H.X R p) =
      baseChangePoint k K G.X R (p ≫ j.hom.hom.hom) := by
  let U := fieldAlgebraSlice (k := k) R
  let bH := relativeSectionEquiv U H.X
  let bG := relativeSectionEquiv U G.X
  change bG (bH.symm (bH p) ≫ j.hom.hom.hom) = bG (p ≫ j.hom.hom.hom)
  rw [Equiv.symm_apply_apply]

end ScalarComparison

section RelativeSpin

variable {k K W V I J : Type u} [Field k] [Field K] [Algebra k K]
  [AddCommGroup W] [AddCommGroup V] [Module k W] [Module k V] [LinearOrder I] [LinearOrder J]
  {q : QuadraticForm k W} {q₀ : QuadraticForm k V}
  {b : Basis I k W} {b₀ : Basis J k V}

set_option maxRecDepth 180 in
set_option maxHeartbeats 150000 in
private theorem relativeSpinComparison
    (e : (coefficientForm K q b).IsometryEquiv (coefficientForm K q₀ b₀))
    (H G₀ : Specs.AffineAlgebraicGroup k)
    (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ)
    (g₀ : ∀ R : TestAlgebra k, SchemePoints G₀.val R →* (ScalarClifford q₀ R)ˣ)
    (hh : IsSpinPointRepresentation q H.val h) (hg₀ : IsSpinPointRepresentation q₀ G₀.val g₀) :
    ∃ (j : relativePoints H.val (fieldTest k K) ≅ relativePoints G₀.val (fieldTest k K))
      (C : ∀ R : TestAlgebra K, ScalarClifford q (restricted k R) ≃ₐ[R]
        ScalarClifford q₀ (restricted k R)),
      (∀ (R : TestAlgebra K) (w : W), C R (vectors q (restricted k R) (1 ⊗ₜ[k] w)) =
        vectors q₀ (restricted k R) (mapVector (fieldAlgebraInclusion R) V (e (1 ⊗ₜ[k] w)))) ∧
      ∀ (R : TestAlgebra K) (x : SchemePoints H.val (restricted k R)),
        g₀ (restricted k R) ((j.hom.app (op (fieldAlgebraSlice R))).hom x) =
          Units.map (C R).toMonoidHom (h (restricted k R) x) := by
  obtain ⟨B, hK, hB, _, _, _, _, hpoint, hhK, _⟩ :=
    spinRepresentationExtension (F := K) q b H h hh
  obtain ⟨D, gK, hD, _, _, _, _, gpoint, hgK, _⟩ :=
    spinRepresentationExtension (F := K) q₀ b₀ G₀ g₀ hg₀
  obtain ⟨j, hj⟩ := spinIsometryGroupComparison _ _ e
    (baseChangedAlgebraicGroup K H) (baseChangedAlgebraicGroup K G₀) hK gK hhK hgK
  let C (R : TestAlgebra K) := (B R).trans ((scalarIsometryClifford e R).trans (D R).symm)
  refine ⟨schemeIsoEquiv K H.val G₀.val j, C, ?_, ?_⟩
  · intro R w
    apply (D R).injective
    change (D R) ((D R).symm (scalarIsometryClifford e R (B R
      (vectors q (restricted k R) (1 ⊗ₜ[k] w))))) = _
    rw [AlgEquiv.apply_symm_apply]
    have hv := hB R ((1 : R) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] w))
    rw [vectorComparison_one] at hv
    have hone : mapVector (fieldAlgebraInclusion R) W ((1 : K) ⊗ₜ[k] w) =
        (1 : restricted k R) ⊗ₜ[k] w := by
      let : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
      change (algebraMap K R 1 : R) ⊗ₜ[k] w = _
      rw [map_one]
    rw [hone] at hv
    rw [hv, scalarIsometryClifford_vectors]
    change vectors (coefficientForm K q₀ b₀) R ((1 : R) ⊗ₜ[K] e (1 ⊗ₜ[k] w)) = _
    rw [← vectorComparison_one]
    exact (hD R _).symm
  · intro R x
    let p := (baseChangePointGroupEquiv K H.val R).symm x
    let p' := p ≫ j.hom.hom.hom
    let B' := B R
    let D' := D R
    let E' := scalarIsometryClifford e R
    have hx : baseChangePoint k K H.val.X R p = x :=
      (baseChangePointGroupEquiv K H.val R).apply_symm_apply x
    have hrel := relativeComparison_apply j R p
    rw [hx] at hrel
    have h₁ : (hK R p).val = B' (h (restricted k R) x).val :=
      (congrArg Units.val (hpoint R p)).trans
        (congrArg (fun x => B' (h (restricted k R) x).val) hx)
    have h₂ : (gK R p').val = E' (hK R p).val := congrArg Units.val (hj R p)
    have h₃ : (gK R p').val = D' (g₀ (restricted k R)
        (baseChangePoint k K G₀.val.X R p')).val := congrArg Units.val (gpoint R p')
    apply Units.ext
    apply D'.injective
    change D' (g₀ (restricted k R)
      (((schemeIsoEquiv K H.val G₀.val j).hom.app (op (fieldAlgebraSlice R))).hom x)).val =
        D' (D'.symm (E' (B' (h (restricted k R) x).val)))
    rw [AlgEquiv.apply_symm_apply, hrel]
    exact h₃.symm.trans (h₂.trans (congrArg E' h₁))

end RelativeSpin

section UniversalPoint

open private scalarSpec_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

set_option backward.isDefEq.respectTransparency false in
/-- The universal affine point determines every morphism of the relative group functors. -/
private theorem relativeHom_ext_of_iso {k : Type u} [Field k] {T : SchemeOver k}
    {H G : GroupScheme k} (U : Over T)
    (p : (Over.iteratedSliceForward T).obj U ≅ (Over.pullback T.hom).obj H.X)
    (m n : relativePoints H T ⟶ relativePoints G T)
    (he : (m.app (op U)).hom (relativeSectionEquiv U H.X p.hom) =
      (n.app (op U)).hom (relativeSectionEquiv U H.X p.hom)) : m = n := by
  apply NatTrans.ext
  funext V
  apply GrpCat.ext
  intro x
  let F := T.iteratedSliceEquiv.functor
  let a := (relativeSectionEquiv V.unop H.X).symm x
  let f := F.preimage (a ≫ p.inv)
  have hf : f.left ≫ relativeSectionEquiv U H.X p.hom = x := by
    apply Over.OverMorphism.ext
    change (F.map f).left ≫ p.hom.left ≫ CategoryTheory.Limits.pullback.fst H.X.hom T.hom =
      x.left
    rw [Functor.map_preimage, Over.comp_left, Category.assoc]
    have idp : p.inv.left ≫ p.hom.left ≫ CategoryTheory.Limits.pullback.fst H.X.hom T.hom =
        CategoryTheory.Limits.pullback.fst H.X.hom T.hom := by
      rw [← Category.assoc, ← Over.comp_left, p.inv_hom_id, Over.id_left, Category.id_comp]
    rw [idp]
    exact CategoryTheory.Limits.pullback.lift_fst ..
  have hm := ConcreteCategory.congr_hom (m.naturality f.op)
    (relativeSectionEquiv U H.X p.hom)
  have hn := ConcreteCategory.congr_hom (n.naturality f.op)
    (relativeSectionEquiv U H.X p.hom)
  change (m.app V).hom (f.left ≫ relativeSectionEquiv U H.X p.hom) =
    f.left ≫ (m.app (op U)).hom (relativeSectionEquiv U H.X p.hom) at hm
  change (n.app V).hom (f.left ≫ relativeSectionEquiv U H.X p.hom) =
    f.left ≫ (n.app (op U)).hom (relativeSectionEquiv U H.X p.hom) at hn
  rw [hf] at hm hn
  exact hm.trans ((congrArg (f.left ≫ ·) he).trans hn.symm)

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private abbrev coordinateTest (P : HopfAlgebraCategory k) : TestAlgebra S :=
  CommAlgCat.of S (extendedHopf S P)

private def coordinateGaloisMap (P : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    restricted k (coordinateTest (S := S) P) ⟶ restricted k (coordinateTest (S := S) P) :=
  let z := (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k P)).toRingHom
  letI : Algebra k (extendedHopf S P) :=
    ((algebraMap S (extendedHopf S P)).comp (algebraMap k S)).toAlgebra
  let h : extendedHopf S P →ₐ[k] extendedHopf S P :=
    { toRingHom := z
      commutes' := fun r => by
        change σ (algebraMap k S r) ⊗ₜ[k] (1 : P) = (algebraMap k S r) ⊗ₜ[k] (1 : P)
        rw [AlgEquiv.commutes] }
  ConcreteCategory.ofHom (C := CommAlgCat k) h

set_option backward.isDefEq.respectTransparency false in
private def coordinateUniversalIso (H : Specs.AffineAlgebraicGroup k) :
    (Over.iteratedSliceForward (fieldTest k S)).obj
        (fieldAlgebraSlice (coordinateTest (S := S) (Specs.AdjointCocharacters.coordinateHopf H))) ≅
      (Over.pullback (fieldTest k S).hom).obj H.val.X :=
  (Grp.forget _).mapIso
    (extendedGroupIso S (Specs.AdjointCocharacters.coordinateHopf H) ≪≫ (groupBaseChange k S).mapIso (coordinateHopfIso H))

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateUniversal_fixed (H : Specs.AffineAlgebraicGroup k) (σ : Gal(S/k)) :
    let R := coordinateTest (S := S) (Specs.AdjointCocharacters.coordinateHopf H)
    let U := fieldAlgebraSlice R
    let x := relativeSectionEquiv U H.val.X (coordinateUniversalIso H).hom
    mapPoints (coordinateGaloisMap (Specs.AdjointCocharacters.coordinateHopf H) σ) x = x := by
  intro R U x
  let P := Specs.AdjointCocharacters.coordinateHopf H
  let p := (coordinateHopfIso H).hom.hom.hom
  let π := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : P →ₐ[k] S ⊗[k] P).toRingHom)
  have hx : x.left = π ≫ p.left := by
    change ((extendedGroupIso S P).hom.hom.hom.left ≫ ((baseChange k S).map p).left) ≫
      pullback.fst H.val.X.hom (fieldSpecMap k S) = _
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ p.left) (extendedSpecIso_hom_fst S P)
  apply Over.OverMorphism.ext
  change ((testSpec k).map (coordinateGaloisMap P σ).op).left ≫ x.left = x.left
  rw [hx, ← Category.assoc]
  exact congrArg (· ≫ p.left) (scalarSpec_projection P σ)


private theorem coordinateGaloisMap_inclusion (P : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    fieldAlgebraInclusion (coordinateTest P) ≫ coordinateGaloisMap P σ =
      CommAlgCat.ofHom σ.toAlgHom ≫ fieldAlgebraInclusion (coordinateTest P) := by
  apply ConcreteCategory.hom_ext
  intro r
  change (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k P))
      ((r : S) ⊗ₜ[k] (1 : P)) = (σ r) ⊗ₜ[k] (1 : P)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

private def sliceGaloisMap {R : TestAlgebra k} (f : CommAlgCat.of k S ⟶ R) (z : R ⟶ R)
    (σ : Gal(S/k)) (hc : f ≫ z = CommAlgCat.ofHom σ.toAlgHom ≫ f) :
    let U := Over.mk ((testSpec k).map f.op)
    (Over.map (fieldMap k S σ)).obj U ⟶ U := by
  intro U
  refine Over.homMk ((testSpec k).map z.op) ?_
  rw [Over.map_obj_hom]
  change (testSpec k).map z.op ≫ (testSpec k).map f.op =
    (testSpec k).map f.op ≫ (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
  have he := congrArg (fun f : CommAlgCat.of k S ⟶ R => (testSpec k).map f.op) hc
  simpa only [op_comp, Functor.map_comp] using he

private def coordinateSliceGalois (P : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    let U := fieldAlgebraSlice (coordinateTest (S := S) P)
    (Over.map (fieldMap k S σ)).obj U ⟶ U :=
  sliceGaloisMap _ _ _ (coordinateGaloisMap_inclusion P σ)

end UniversalPoint

section CliffordTwist

variable {k K W V I : Type u} [Field k] [Field K] [Algebra k K]
  [AddCommGroup W] [AddCommGroup V] [Module k W] [Module k V] [LinearOrder I]
  {q : QuadraticForm k W} {q₀ : QuadraticForm k V} {b₀ : Basis I k V}
  {G J : Specs.AffineAlgebraicGroup k} {inn : groupSections J.val ⟶ automorphisms G.val}
  {g₀ : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q₀ R)ˣ}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The Clifford comparison intertwines the twisted action because it does so on the
fixed vector generators and on scalars. -/
private theorem cliffordTwist_compatibility (A : SpinAdjointAction q₀ b₀ G J inn g₀)
    {R : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) (g : R ⟶ R)
    (σ : Gal(K/k)) (hf : f ≫ g = CommAlgCat.ofHom σ.toAlgHom ≫ f)
    (d : SchemePoints J.val (CommAlgCat.of k K)) (v : W → K ⊗[k] V)
    (hv : ∀ w, A.linear (CommAlgCat.of k K) d
        ((SemilinearAction.scalarExtension V).act σ (v w)) = v w)
    (C : ScalarClifford q R ≃ₐ[R] ScalarClifford q₀ R)
    (hC : ∀ w, C (vectors q R (1 ⊗ₜ[k] w)) = vectors q₀ R (mapVector f V (v w)))
    (x : ScalarClifford q R) :
    A.clifford R (mapPoints f d) (coefficientMap q₀ R g.hom (C x)) =
      C (coefficientMap q R g.hom x) := by
  let A₁ := A.clifford R (mapPoints f d)
  let L := (A₁.toAlgHom.restrictScalars k).comp
    ((coefficientMap q₀ R g.hom).comp (C.toAlgHom.restrictScalars k))
  let M := (C.toAlgHom.restrictScalars k).comp (coefficientMap q R g.hom)
  suffices h : L = M from DFunLike.congr_fun h x
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro r
    change A₁ (coefficientMap q₀ R g.hom (C (algebraMap R (ScalarClifford q R) r))) =
      C (coefficientMap q R g.hom (algebraMap R (ScalarClifford q R) r))
    rw [C.commutes]
    change A₁ (algebraMap R (ScalarClifford q₀ R) (g.hom r)) =
      C (algebraMap R (ScalarClifford q R) (g.hom r))
    rw [A₁.commutes, C.commutes]
  · apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro w
    change A₁ (coefficientMap q₀ R g.hom (C (vectors q R (1 ⊗ₜ[k] w)))) =
      C (coefficientMap q R g.hom (vectors q R (1 ⊗ₜ[k] w)))
    have hg : coefficientMap q R g.hom (vectors q R (1 ⊗ₜ[k] w)) =
        vectors q R (1 ⊗ₜ[k] w) := by
      rw [coefficientMap_vectors_natural]
      change vectors q R (g.hom 1 ⊗ₜ[k] w) = _
      rw [map_one]
    rw [hg, hC, coefficientMap_vectors_natural, mapVector_comp, hf, ← mapVector_comp]
    change A.clifford R (mapPoints f d) (vectors q₀ R
      (mapVector f V (mapVector (CommAlgCat.ofHom σ.toAlgHom) V (v w)))) =
      vectors q₀ R (mapVector f V (v w))
    rw [A.generators, mapVector_galois]
    have hnat := A.natural f d ((SemilinearAction.scalarExtension V).act σ (v w))
    change mapVector f V (A.linear (CommAlgCat.of k K) d
        ((SemilinearAction.scalarExtension V).act σ (v w))) =
      A.linear R (mapPoints f d)
        (mapVector f V ((SemilinearAction.scalarExtension V).act σ (v w))) at hnat
    rw [← hnat, hv]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem spinPoint_twist {S : Type u} [Field S] [Algebra k S]
    {H : Specs.AffineAlgebraicGroup k}
    {h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ}
    (A : SpinAdjointAction q₀ b₀ G J inn g₀)
    (hh : IsSpinPointRepresentation q H.val h) (hg₀ : IsSpinPointRepresentation q₀ G.val g₀)
    {R : TestAlgebra k}
    (f : CommAlgCat.of k K ⟶ R) (fₛ : CommAlgCat.of k S ⟶ R) (z : R ⟶ R)
    (d : SchemePoints J.val (CommAlgCat.of k K)) (p : SchemePoints J.val (CommAlgCat.of k S))
    (hp : mapPoints fₛ p = mapPoints f d)
    (σ : Gal(K/k)) (hf : f ≫ z = CommAlgCat.ofHom σ.toAlgHom ≫ f)
    (v : W → K ⊗[k] V)
    (hv : ∀ w, A.linear (CommAlgCat.of k K) d
        ((SemilinearAction.scalarExtension V).act σ (v w)) = v w)
    (C : ScalarClifford q R ≃ₐ[R] ScalarClifford q₀ R)
    (hC : ∀ w, C (vectors q R (1 ⊗ₜ[k] w)) = vectors q₀ R (mapVector f V (v w)))
    (x : SchemePoints H.val R) (y : SchemePoints G.val R)
    (hx : mapPoints z x = x)
    (hy : g₀ R y = Units.map C.toMonoidHom (h R x)) :
    let U := Over.mk ((testSpec k).map fₛ.op)
    let a := inn.app (op (fieldTest k S)) ⟨p⟩
    (a.asIso.hom.app (op U)).hom (mapPoints z y) = y := by
  intro U a
  apply (hg₀.1 R).1
  have hfix := hh.2 z x
  change h R (mapPoints z x) = _ at hfix
  rw [hx] at hfix
  have hmap := hg₀.2 z y
  change g₀ R (mapPoints z y) = _ at hmap
  have ha := A.innerAction fₛ p (mapPoints z y)
  change g₀ R ((a.asIso.hom.app (op U)).hom (mapPoints z y)) =
    Units.map (A.clifford R (mapPoints fₛ p)).toMonoidHom (g₀ R (mapPoints z y)) at ha
  rw [ha, hp, hmap, hy]
  apply Units.ext
  exact (cliffordTwist_compatibility A f z σ hf d v hv C hC (h R x).val).trans
    (congrArg C (congrArg Units.val hfix.symm))

end CliffordTwist

section InvariantComparison

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
variable (K : FiniteGaloisIntermediateField k S)

private abbrev fieldInclusion : CommAlgCat.of k K ⟶ CommAlgCat.of k S :=
  CommAlgCat.ofHom K.toIntermediateField.val

private abbrev fieldInclusionSpec : fieldTest k S ⟶ fieldTest k K :=
  (testSpec k).map (fieldInclusion K).op

private theorem fieldAlgebraInclusion_comp (R : TestAlgebra S) :
    fieldInclusion K ≫ fieldAlgebraInclusion R =
      fieldAlgebraInclusion (restricted K R) := by
  apply ConcreteCategory.hom_ext
  intro r
  rfl

private theorem fieldInclusion_galois (σ : Gal(S/k)) :
    fieldInclusion K ≫ CommAlgCat.ofHom σ.toAlgHom =
      CommAlgCat.ofHom (restriction K σ).toAlgHom ≫ fieldInclusion K := by
  apply ConcreteCategory.hom_ext
  intro r
  exact (AlgEquiv.restrictNormalHom_apply K.toIntermediateField σ r).symm

private theorem restrictHom_apply_eq {T S₀ X : SchemeOver k} {H G : GroupScheme k}
    (j : relativePoints H S₀ ≅ relativePoints G S₀)
    (f : X ⟶ T) (a : T ⟶ S₀) (g : X ⟶ S₀) (e : f ≫ a = g)
    (x : X ⟶ H.X) :
    ((restrictIso a j).hom.app (op (Over.mk f))).hom x =
      (j.hom.app (op (Over.mk g))).hom x := by
  subst g
  rfl

private theorem restrictComparison_apply {H G : GroupScheme k}
    (j : relativePoints H (fieldTest k K) ≅ relativePoints G (fieldTest k K))
    (R : TestAlgebra S) (x : SchemePoints H (restricted k R)) :
    ((restrictIso (fieldInclusionSpec K) j).hom.app (op (fieldAlgebraSlice R))).hom x =
      (j.hom.app (op (fieldAlgebraSlice (restricted K R)))).hom x := by
  have he : (testSpec k).map (fieldAlgebraInclusion R).op ≫
      (testSpec k).map (fieldInclusion K).op =
        (testSpec k).map (fieldAlgebraInclusion (restricted K R)).op := by
    rw [← (testSpec k).map_comp, ← op_comp, fieldAlgebraInclusion_comp]
    rfl
  exact restrictHom_apply_eq (H := H) (G := G) j _ _ _ he x

variable {W V I : Type u} [AddCommGroup W] [AddCommGroup V] [Module k W] [Module k V]
  [LinearOrder I]
  {q : QuadraticForm k W} {q₀ : QuadraticForm k V} {b₀ : Basis I k V}
  {H G₀ G J : Specs.AffineAlgebraicGroup k}
  {inn : groupSections J.val ⟶ automorphisms G₀.val}
  {h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ}
  {g₀ : ∀ R : TestAlgebra k, SchemePoints G₀.val R →* (ScalarClifford q₀ R)ˣ}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- Composing the Clifford comparison with the original trivialization cancels
the two displacements at the universal point. -/
private theorem invariantSpinComparison
    (A : SpinAdjointAction q₀ b₀ G₀ J inn g₀)
    (hh : IsSpinPointRepresentation q H.val h) (hg₀ : IsSpinPointRepresentation q₀ G₀.val g₀)
    (i : relativePoints G₀.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (d : Gal(K/k) → SchemePoints J.val (CommAlgCat.of k K))
    (htop : ∀ σ, inn.app (op (fieldTest k S))
        ⟨pointMap k K J.val.X K.toIntermediateField.val (d (restriction K σ))⟩ =
      transportedAut k S i σ)
    (v : W → K ⊗[k] V)
    (hv : ∀ σ w, A.linear (CommAlgCat.of k K) (d σ)
        ((SemilinearAction.scalarExtension V).act σ (v w)) = v w)
    (j : relativePoints H.val (fieldTest k K) ≅ relativePoints G₀.val (fieldTest k K))
    (C : ∀ R : TestAlgebra K, ScalarClifford q (restricted k R) ≃ₐ[R]
        ScalarClifford q₀ (restricted k R))
    (hC : ∀ (R : TestAlgebra K) w, C R (vectors q (restricted k R) (1 ⊗ₜ[k] w)) =
      vectors q₀ (restricted k R) (mapVector (fieldAlgebraInclusion R) V (v w)))
    (hj : ∀ (R : TestAlgebra K) (x : SchemePoints H.val (restricted k R)),
      g₀ (restricted k R) ((j.hom.app (op (fieldAlgebraSlice R))).hom x) =
        Units.map (C R).toMonoidHom (h (restricted k R) x)) :
    ∀ σ, let r := restrictIso (fieldInclusionSpec K) j ≪≫ i
      restrictIso (fieldMap k S σ) r = r := by
  intro σ r
  let P := Specs.AdjointCocharacters.coordinateHopf H
  let R := coordinateTest (S := S) P
  let U := fieldAlgebraSlice (k := k) R
  let x := relativeSectionEquiv U H.val.X (coordinateUniversalIso H).hom
  let z := coordinateGaloisMap P σ
  let jₛ := restrictIso (fieldInclusionSpec K) j
  let p := pointMap k K J.val.X K.toIntermediateField.val (d (restriction K σ))
  let a := inn.app (op (fieldTest k S)) ⟨p⟩
  let y := (jₛ.hom.app (op U)).hom x
  have hfix : mapPoints z x = x := coordinateUniversal_fixed H σ
  have hsrc : g₀ (restricted k R) y = Units.map (C (restricted K R)).toMonoidHom (h _ x) :=
    (congrArg (g₀ (restricted k R)) (restrictComparison_apply K j R x)).trans
      (hj (restricted K R) x)
  have hmp : mapPoints (fieldAlgebraInclusion R) p =
      mapPoints (fieldAlgebraInclusion (restricted K R)) (d (restriction K σ)) := by
    rw [← fieldAlgebraInclusion_comp K R, CocharacterDynamics.mapPoints_comp]
    rfl
  have hf : fieldAlgebraInclusion (k := k) (restricted K R) ≫ z =
      CommAlgCat.ofHom (restriction K σ).toAlgHom ≫ fieldAlgebraInclusion (k := k) (restricted K R) := by
    rw [← fieldAlgebraInclusion_comp K R, Category.assoc, coordinateGaloisMap_inclusion,
      ← Category.assoc, fieldInclusion_galois, Category.assoc]
  have hval : (a.asIso.hom.app (op U)).hom (mapPoints z y) = y :=
    spinPoint_twist A hh hg₀ _ _ z _ _ hmp _ hf v (hv _) _ (hC _) x y hfix hsrc
  have hja : restrictIso (fieldMap k S σ) jₛ ≪≫ a.asIso = jₛ := by
    apply Iso.ext
    refine relativeHom_ext_of_iso (H := H.val) (G := G₀.val) U (coordinateUniversalIso H) _ _ ?_
    let ℓ := coordinateSliceGalois P σ
    have hnat := ConcreteCategory.congr_hom (jₛ.hom.naturality ℓ.op) x
    change (jₛ.hom.app (op ((Over.map (fieldMap k S σ)).obj U))).hom (mapPoints z x) =
      mapPoints z y at hnat
    rw [hfix] at hnat
    change (a.asIso.hom.app (op U)).hom
        ((jₛ.hom.app (op ((Over.map (fieldMap k S σ)).obj U))).hom x) = y
    rw [hnat]
    exact hval
  have ha : restrictIso (fieldMap k S σ) i = a.asIso ≪≫ i := by
    have hend := congrArg (fun t : RelativeAut G₀.val (fieldTest k S) => t.asIso) (htop σ)
    change a.asIso = restrictIso (fieldMap k S σ) i ≪≫ i.symm at hend
    rw [hend, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have he : restrictIso (fieldMap k S σ) r =
      restrictIso (fieldMap k S σ) jₛ ≪≫ restrictIso (fieldMap k S σ) i := by
    apply Iso.ext
    rfl
  rw [he, ha, ← Iso.trans_assoc, hja]

end InvariantComparison

open private exists_coordinate_model from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms

private theorem fixedFormBasis {k K V I : Type u} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] [FiniteDimensional k K] [AddCommGroup V] [Module k V]
    [Module.Finite k V] [LinearOrder I] (q₀ : QuadraticForm k V) (b₀ : Basis I k V)
    (a : SemilinearAction k K (K ⊗[k] V)) (q : QuadraticForm k a.fixed)
    (he : ∀ {L : Type u} [LinearOrder L] (b : Basis L k a.fixed),
      ∃ e : (K ⊗[k] a.fixed) ≃ₗ[K] (K ⊗[k] V), e.toLinearMap = a.descentMap ∧
        ∀ x, coefficientForm K q₀ b₀ (e x) = coefficientForm K q b x) :
    ∃ (n : ℕ) (b : Basis (ULift.{u} (Fin n)) k a.fixed)
      (e : (coefficientForm K q b).IsometryEquiv (coefficientForm K q₀ b₀)),
      ∀ w : a.fixed, e ((1 : K) ⊗ₜ[k] w) = w.val := by
  classical
  obtain ⟨T, c, hc⟩ := a.exists_fixed_basis
  have := c.linearIndependent.finite
  let _ : Fintype T := Fintype.ofFinite T
  let b : Basis (ULift.{u} (Fin (Fintype.card T))) k a.fixed :=
    (a.fixedBasis c hc).reindex ((Fintype.equivFin T).trans Equiv.ulift.symm)
  obtain ⟨e, he₀, hq⟩ := he b
  refine ⟨_, b, ⟨e, ?_⟩, ?_⟩
  · intro x
    exact hq x
  · intro w
    change e.toLinearMap ((1 : K) ⊗ₜ[k] w) = w.val
    rw [he₀, SemilinearAction.descentMap_tmul, one_smul]

section FixedForm

variable {k S V I : Type u} [Field k] [Field S] [Algebra k S]
    [AddCommGroup V] [Module k V] [LinearOrder I]
    {q₀ : QuadraticForm k V} {b₀ : Basis I k V}
    {G₀ G J : Specs.AffineAlgebraicGroup k}
    {inn : groupSections J.val ⟶ automorphisms G₀.val}
    {g₀ : ∀ R : TestAlgebra k, SchemePoints G₀.val R →* (ScalarClifford q₀ R)ˣ}

private theorem adjointAction_galois {K : Type u} [Field K] [Algebra k K]
    (A : SpinAdjointAction q₀ b₀ G₀ J inn g₀) (σ : Gal(K/k))
    (p : SchemePoints J.val (CommAlgCat.of k K)) (x : K ⊗[k] V) :
    let ρ := A.linear (CommAlgCat.of k K)
    (SemilinearAction.scalarExtension V).act σ (ρ p x) =
      ρ (pointAction k K J.val.X σ p) ((SemilinearAction.scalarExtension V).act σ x) := by
  intro ρ
  have h := A.natural (CommAlgCat.ofHom σ.toAlgHom) p x
  change mapVector (CommAlgCat.ofHom σ.toAlgHom) V (ρ p x) =
    ρ (pointAction k K J.val.X σ p) (mapVector (CommAlgCat.ofHom σ.toAlgHom) V x) at h
  have h₁ := mapVector_galois (k := k) (K := K) σ (ρ p x)
  have h₂ := mapVector_galois (k := k) (K := K) σ x
  exact h₁.symm.trans (h.trans (congrArg (ρ (pointAction k K J.val.X σ p)) h₂))

set_option maxRecDepth 300 in
set_option maxHeartbeats 500000 in
private theorem fixedSpinRepresentation [IsGalois k S] [Module.Finite k V]
    (K : FiniteGaloisIntermediateField k S)
    (A : SpinAdjointAction q₀ b₀ G₀ J inn g₀)
    (hg₀ : IsSpinPointRepresentation q₀ G₀.val g₀)
    (i : relativePoints G₀.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (d : Gal(K/k) → SchemePoints J.val (CommAlgCat.of k K))
    (htop : ∀ σ, inn.app (op (fieldTest k S))
        ⟨pointMap k K J.val.X K.toIntermediateField.val (d (restriction K σ))⟩ =
      transportedAut k S i σ)
    (a : SemilinearAction k K (K ⊗[k] V)) (q : QuadraticForm k a.fixed)
    (ha : ∀ σ x, a.act σ x = A.linear (CommAlgCat.of k K) (d σ)
        ((SemilinearAction.scalarExtension V).act σ x))
    {n : ℕ} (b : Basis (ULift.{u} (Fin n)) k a.fixed)
    (eQ : (coefficientForm K q b).IsometryEquiv (coefficientForm K q₀ b₀))
    (he₀ : ∀ w : a.fixed, eQ ((1 : K) ⊗ₜ[k] w) = w.val) :
    ∃ (g : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q R)ˣ),
      IsSpinPointRepresentation q G.val g ∧
      ∃ (H : Specs.AffineAlgebraicGroup k)
        (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ)
        (l : H.val ≅ G.val), IsSpinPointRepresentation q H.val h ∧
        ∀ (R : TestAlgebra k) (x : SchemePoints H.val R), g R (x ≫ l.hom.hom.hom) = h R x := by
  obtain ⟨H, h, hh⟩ := spin_scheme_of_form (k := k) (W := a.fixed)
    (I := ULift.{u} (Fin n)) q b
  obtain ⟨j, C, hC, hj⟩ := relativeSpinComparison (k := k) (K := K)
    (W := a.fixed) (V := V) (q := q) (q₀ := q₀) (b := b) (b₀ := b₀) eQ H G₀ h g₀ hh hg₀
  let v (w : a.fixed) := eQ (1 ⊗ₜ[k] w)
  have hv (σ : Gal(K/k)) (w : a.fixed) :
      A.linear (CommAlgCat.of k K) (d σ) ((SemilinearAction.scalarExtension V).act σ (v w)) = v w := by
    rw [← ha]
    have hw : v w = w.val := he₀ w
    rw [hw]
    exact w.property σ
  let r := restrictIso (fieldInclusionSpec K) j ≪≫ i
  have hr : ∀ σ, restrictIso (fieldMap k S σ) r = r :=
    invariantSpinComparison (W := a.fixed) (V := V) (q := q) (q₀ := q₀)
      (b₀ := b₀) (H := H) (G₀ := G₀) (G := G) (J := J) (inn := inn)
      (h := h) (g₀ := g₀) K A hh hg₀ i d htop v hv j C hC hj
  obtain ⟨l, g, hg, hl⟩ := descendCompatibleSpinComparison (k := k) (K := S) (W := a.fixed)
    q H G h hh r hr
  exact ⟨g, hg, H, h, l, hh, hl⟩

end FixedForm


set_option Elab.async false in
set_option maxRecDepth 320 in
set_option maxHeartbeats 900000 in
theorem effectiveOddSpinDescent : EffectiveOddSpinDescent.{u} := by
  classical
  intro k S V I _ _ _ _ _ _ _ _ q₀ b₀ G₀ G J O E g₀ A i hreg _ hg₀ hinner
  obtain ⟨P, hP, ⟨p⟩⟩ := exists_coordinate_model G₀
  obtain ⟨B, hB, ⟨b⟩⟩ := exists_coordinate_model G
  let t := extendedGroupIso (k := k) S
  have ht : LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t :=
    fun D => extendedSpecIso_hom_fst S D
  obtain ⟨K, jK, d, hjK, hd, htop⟩ :=
    finiteInnerTrivialization G₀ G J.quotient E.inner i P B p b t hP hB ht
      (E.innerInjective _) hinner
  obtain ⟨a, ha, q, hq, he, hdim, hqreg⟩ :=
    adjointQuadraticDescent q₀ b₀ J.quotient (A.linear (CommAlgCat.of k K))
      (A.preserves _) (adjointAction_galois A) d hd
  have hregq := hqreg (regular_coefficientForm (K := K) q₀ b₀ hreg)
  have hfin := (a.finiteDimensional_fixed).1
  obtain ⟨n, bq, e, he₀⟩ := fixedFormBasis (k := k) (K := K) (V := V) (I := I) q₀ b₀ a q
    (by
      intro L hL bL
      exact @he L hL bL)
  obtain ⟨g, hg, hmodel⟩ := fixedSpinRepresentation (k := k) (S := S) (V := V) (I := I)
    (G₀ := G₀) (G := G) (J := J.quotient) (inn := E.inner) (g₀ := g₀)
    (q₀ := q₀) (b₀ := b₀) K A hg₀ i d htop a q ha (n := n) bq e (fun w => he₀ w)
  refine ⟨K, d, a, q, g, ?_, hd, htop, ha, hq, ?_, hregq, hfin, hdim, hg, hmodel⟩
  · exact ⟨P, B, p, b, t, jK, hP, hB, ht, hjK⟩
  · intro L hL bL
    exact @he L hL bL


end CliffordDescent

end InnerForms

end

end LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
