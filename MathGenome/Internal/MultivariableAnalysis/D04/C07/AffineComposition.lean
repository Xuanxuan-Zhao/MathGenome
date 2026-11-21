import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.AffineComposition
import MathGenome.Internal.MultivariableAnalysis.D04.C07.OneCoordinate
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import Mathlib.LinearAlgebra.Matrix.Transvection

noncomputable section
open Set Function Topology
open scoped BigOperators
namespace D04.AffineComposition
open JordanRegions
open Specs.D04.C07.AffineComposition.Model

lemma continuous_jacobian {n : ℕ} {U : Set (E n)} (φ : E n → E n)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) :
    Continuous (fun x : U => |(fderiv ℝ φ x).det|) :=
  (ContinuousLinearMap.continuous_det.comp
    (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).domRestrict).abs

lemma jacobian_comp {n : ℕ} {U V : Set (E n)} (s : U ≃ₜ V)
    (S T : E n → E n) (hU : IsOpen U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ 1 S U) (hT : ContDiffOn ℝ 1 T V)
    (hs : ∀ x : U, S x = s x) (x : U) :
    |(fderiv ℝ (T ∘ S) x).det| =
      |(fderiv ℝ T (S x)).det| * |(fderiv ℝ S x).det| := by
  have hdS := hS.differentiableOn (by norm_num) |>.differentiableAt (hU.mem_nhds x.property)
  have hSx : S x ∈ V := hs x ▸ (s x).property
  have hdT := hT.differentiableOn (by norm_num) |>.differentiableAt (hV.mem_nhds hSx)
  rw [fderiv_comp (x : E n) hdT hdS]
  change |LinearMap.det ((fderiv ℝ T (S x)).toLinearMap.comp
    (fderiv ℝ S x).toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul]

theorem composition : Specs.D04.C07.AffineComposition.compositionType := by
  intro n U V W s t S T hU hV hW hS hT hs _ht hsubS hsubT
  have hJ := jacobian_comp s S T hU hV hS hT hs
  refine ⟨hJ, ?_⟩
  intro f hf hfc
  let g : V → ℝ := fun y => f (t y) * |(fderiv ℝ T y).det|
  have hp := Localization.pullback_support t f univ hf hfc (by simp)
  have hg : Continuous g := hp.1.mul (continuous_jacobian T hV hT)
  have hgc : HasCompactSupport g := hp.2.1.mul_right
  have hgi := Localization.compact_support_integrable g hV hg hgc
  have hfi := Localization.compact_support_integrable f hW hf hfc
  let k : U → ℝ := fun x => g (s x) * |(fderiv ℝ S x).det|
  have hp' := Localization.pullback_support s g univ hg hgc (by simp)
  have hki := Localization.compact_support_integrable k hU
    (hp'.1.mul (continuous_jacobian S hU hS)) hp'.2.1.mul_right
  have hk : k = fun x : U => f ((s.trans t) x) * |(fderiv ℝ (T ∘ S) x).det| := by
    funext x
    dsimp [k, g]
    rw [hJ x, hs x, mul_assoc]
  refine ⟨hg, hgc, hgi.1, hgi.2, hfi.1, hfi.2, ?_, ?_, ?_⟩
  · rw [← hk]; exact hki.1
  · rw [← hk]; exact hki.2
  · rw [← hk]
    exact (hsubT f hf hfc).trans (hsubS g hg hgc)

theorem affine_jacobian : Specs.D04.C07.AffineComposition.affine_jacobianType := by
  intro n A b x
  change (fderiv ℝ (fun y => matrixLinearEquiv n n A y + b) x).det = A.det
  let L := (matrixLinearEquiv n n A).toContinuousLinearMap
  have hd : HasFDerivAt (fun y => matrixLinearEquiv n n A y + b) L x :=
    L.hasFDerivAt.add_const b
  rw [hd.fderiv]
  change LinearMap.det (matrixLinearEquiv n n A) = A.det
  rw [show matrixLinearEquiv n n A = Matrix.toLin (standardBasis n) (standardBasis n) A from rfl]
  exact LinearMap.det_toLin _ _


/-- The whole-space version uses precisely the same Darboux integral. -/
def wholeIntegral {n : ℕ} (F : E n → ℝ) : ℝ :=
  openIntegral (fun x : (univ : Set (E n)) => F x)

lemma zeroExtension_univ {n : ℕ} (F : E n → ℝ) :
    zeroExtension (fun x : (univ : Set (E n)) => F x) = F := by
  ext x
  simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension]

lemma openIntegral_eq_whole {n : ℕ} {U : Set (E n)} (f : U → ℝ) :
    openIntegral f = wholeIntegral (zeroExtension f) := by
  change Darboux.lowerIntegral (zeroExtension f) (enclosingBox (support (zeroExtension f))) =
    Darboux.lowerIntegral (zeroExtension (fun x : (univ : Set (E n)) => zeroExtension f x))
      (enclosingBox (support (zeroExtension (fun x : (univ : Set (E n)) => zeroExtension f x))))
  rw [zeroExtension_univ]

/-- An identity for all continuous compactly supported tests on all of space. -/
def GlobalSubstitution {n : ℕ} (e : E n ≃ₜ E n) (J : ℝ) : Prop :=
  ∀ F : E n → ℝ, Continuous F → HasCompactSupport F →
    wholeIntegral F = wholeIntegral (fun x => F (e x) * J)

lemma global_comp {n : ℕ} {s t : E n ≃ₜ E n} {J K : ℝ}
    (hs : GlobalSubstitution s J) (ht : GlobalSubstitution t K) :
    GlobalSubstitution (s.trans t) (K * J) := by
  intro F hF hFc
  have hg : Continuous (fun x => F (t x) * K) := (hF.comp t.continuous).mul continuous_const
  have hgc : HasCompactSupport (fun x => F (t x) * K) :=
    (hFc.comp_homeomorph t).mul_right
  calc
    wholeIntegral F = wholeIntegral (fun x => F (t x) * K) := ht F hF hFc
    _ = wholeIntegral (fun x => (F (t (s x)) * K) * J) := hs _ hg hgc
    _ = wholeIntegral (fun x => F ((s.trans t) x) * (K * J)) := by
      congr 1; funext x; exact mul_assoc _ _ _

lemma global_refl {n : ℕ} : GlobalSubstitution (Homeomorph.refl (E n)) 1 := by
  intro F _ _
  simp only [Homeomorph.refl_apply, id_eq, mul_one]

/-- Transfer an identity on all of space to any open pair identified by e.
This is an identity of zero extensions, so no region-volume result is used. -/
lemma global_restrict {n : ℕ} {H : E n ≃ₜ E n} {J : ℝ}
    (hH : GlobalSubstitution H J) {U V : Set (E n)} (e : U ≃ₜ V)
    (_hU : IsOpen U) (hV : IsOpen V) (he : ∀ x : U, H x = e x)
    (f : V → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    openIntegral f = openIntegral (fun x : U => f (e x) * J) := by
  have hF := Localization.compact_support_integrable f hV hf hfc
  have hext : zeroExtension (fun x : U => f (e x) * J) =
      fun x => zeroExtension f (H x) * J := by
    funext x
    by_cases hx : x ∈ U
    · rw [show x = (⟨x, hx⟩ : U).val from rfl]
      rw [zeroExtension_apply, he, zeroExtension_apply]
    · have hy : H x ∉ V := by
        intro hy
        let y : V := ⟨H x, hy⟩
        have hxy : H (e.symm y) = H x := by rw [he, e.apply_symm_apply]
        exact hx (H.injective hxy ▸ (e.symm y).property)
      rw [zeroExtension_of_not_mem _ hx, zeroExtension_of_not_mem _ hy, zero_mul]
  rw [openIntegral_eq_whole f, openIntegral_eq_whole, hext]
  exact hH _ hF.1 (Localization.zeroExtension_compact hfc)

/-- One-coordinate C¹ maps supply whole-space substitution. -/
lemma global_coordinate {n : ℕ} (j : Fin n) (e : E n ≃ₜ E n) (ψ : E n → ℝ)
    (he : ∀ x, OneCoordinate.coordinateChange j ψ x = e x)
    (hψ : ContDiff ℝ 1 (OneCoordinate.coordinateChange j ψ))
    (hinv : ContDiff ℝ 1 (fun x => e.symm x)) (J : ℝ)
    (hJ : ∀ x, |(fderiv ℝ (fun y => e y) x).det| = J) :
    GlobalSubstitution e J := by
  intro F hF hFc
  let u := Homeomorph.Set.univ (E n)
  let e' := (u.trans e).trans u.symm
  have h := OneCoordinate.substitution j univ univ e' ψ (fun y => e.symm y)
    isOpen_univ isOpen_univ hψ.contDiffOn hinv.contDiffOn
    (fun x => he x) (fun _ => rfl) (fun y => F y)
    (hF.comp continuous_subtype_val) (hFc.comp_homeomorph u)
  have hd : ∀ x, |OneCoordinate.coordinatePartial j ψ x| = J := by
    intro x
    change |Specs.D04.C07.OneCoordinate.Model.coordinatePartial j ψ x| = J
    rw [← OneCoordinate.determinant j ψ x
      ((OneCoordinate.regularity j ψ univ).mp hψ.contDiffOn |>.differentiableOn (by norm_num)
        |>.differentiableAt (isOpen_univ.mem_nhds (mem_univ x)))]
    have heq : OneCoordinate.coordinateChange j ψ = (fun y => e y) := funext he
    change |(fderiv ℝ (OneCoordinate.coordinateChange j ψ) x).det| = J
    rw [heq, hJ]
  have hval : wholeIntegral F = wholeIntegral
      (fun x => F (e x) * |OneCoordinate.coordinatePartial j ψ x|) := h.2.2.2.2
  simpa only [hd] using hval


/-- The continuous linear map represented by a matrix in the fixed Euclidean basis. -/
def matrixMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : E n →L[ℝ] E n :=
  (matrixLinearEquiv n n A).toContinuousLinearMap

lemma matrixMap_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (matrixMap A).det = A.det := by
  change LinearMap.det (Matrix.toLin (standardBasis n) (standardBasis n) A) = A.det
  exact LinearMap.det_toLin _ _

def matrixEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    E n ≃L[ℝ] E n :=
  (matrixMap A).toContinuousLinearEquivOfDetNeZero (by rw [matrixMap_det]; exact hA)

@[simp] lemma matrixEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (x : E n) : matrixEquiv A hA x = matrixLinearEquiv n n A x := rfl

lemma matrixEquiv_jacobian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (x : E n) :
    |(fderiv ℝ (fun y => matrixEquiv A hA y) x).det| = |A.det| := by
  rw [(matrixEquiv A hA).hasFDerivAt.fderiv]
  exact congrArg abs (matrixMap_det A)

/-- Algebraic induction predicate: an actual linear homeomorphism together
with the proved integral identity. -/
def MatrixSubstitution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ e : E n ≃L[ℝ] E n, (∀ x, e x = matrixLinearEquiv n n A x) ∧
    GlobalSubstitution e.toHomeomorph |A.det|

lemma matrix_substitution_one {n : ℕ} : MatrixSubstitution (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨ContinuousLinearEquiv.refl ℝ (E n), ?_, ?_⟩
  · intro x; ext i; simp [matrix_apply, Matrix.one_apply, ite_mul]
  · rw [show (ContinuousLinearEquiv.refl ℝ (E n)).toHomeomorph = Homeomorph.refl (E n) by ext; rfl]
    simpa only [Matrix.det_one, abs_one] using (global_refl (n := n))

lemma matrix_substitution_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : MatrixSubstitution A) (hB : MatrixSubstitution B) :
    MatrixSubstitution (A * B) := by
  obtain ⟨a, ha, hsa⟩ := hA
  obtain ⟨b, hb, hsb⟩ := hB
  refine ⟨b.trans a, ?_, ?_⟩
  · intro x
    change a (b x) = _
    rw [ha, hb, matrix_composition]
    rfl
  · rw [show (b.trans a).toHomeomorph = b.toHomeomorph.trans a.toHomeomorph by ext; rfl]
    simpa only [Matrix.det_mul, abs_mul] using global_comp hsb hsa

lemma matrix_substitution_transvection {n : ℕ} (t : Matrix.TransvectionStruct (Fin n) ℝ) :
    MatrixSubstitution t.toMatrix := by
  let e := matrixEquiv t.toMatrix (by simp)
  have he : ∀ x, OneCoordinate.coordinateChange t.i (fun y => y t.i + t.c * y t.j) x = e x := by
    intro x
    ext k
    change Function.update (fun k => x k) t.i (x t.i + t.c * x t.j) k = _
    rw [matrixEquiv_apply, matrix_apply]
    by_cases hk : k = t.i
    · subst k
      simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single,
        Matrix.one_apply, add_mul, ite_mul, Finset.sum_add_distrib]
    · simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single,
        Matrix.one_apply, hk, Ne.symm hk, ite_mul]
  refine ⟨e, fun _ => rfl, ?_⟩
  apply global_coordinate t.i e.toHomeomorph (fun y => y t.i + t.c * y t.j) he
  · rw [funext he]; exact e.contDiff
  · exact e.symm.contDiff
  · exact matrixEquiv_jacobian t.toMatrix (by simp)

/-- Scaling a single coordinate by any nonzero real factor. -/
lemma matrix_substitution_scale {n : ℕ} (j : Fin n) (c : ℝ) (hc : c ≠ 0) :
    MatrixSubstitution (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : ℝ)) j c)) := by
  let A := Matrix.diagonal (Function.update (fun _ : Fin n => (1 : ℝ)) j c)
  have hA : A.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases hi : i = j <;> simp [Function.update, hi, hc]
  let e := matrixEquiv A hA
  have he : ∀ x, OneCoordinate.coordinateChange j (fun y => c * y j) x = e x := by
    intro x
    ext k
    change Function.update (fun k => x k) j (c * x j) k = _
    rw [matrixEquiv_apply, matrix_apply]
    by_cases hk : k = j
    · subst k; simp [A, Matrix.diagonal_apply, ite_mul]
    · simp [A, Matrix.diagonal_apply, hk, ite_mul]
  refine ⟨e, fun _ => rfl, ?_⟩
  apply global_coordinate j e.toHomeomorph (fun y => c * y j) he
  · rw [funext he]; exact e.contDiff
  · exact e.symm.contDiff
  · exact matrixEquiv_jacobian A hA


lemma matrix_substitution_diagonal {n : ℕ} (D : Fin n → ℝ)
    (hD : (Matrix.diagonal D).det ≠ 0) : MatrixSubstitution (Matrix.diagonal D) := by
  have hne : ∀ i, D i ≠ 0 := by
    simpa only [Matrix.det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ,
      forall_const] using hD
  have hpartial : ∀ s : Finset (Fin n),
      MatrixSubstitution (Matrix.diagonal (fun i => if i ∈ s then D i else 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (matrix_substitution_one (n := n))
    | @insert a s ha ih =>
      have hmat : Matrix.diagonal (fun i => if i ∈ insert a s then D i else 1) =
          Matrix.diagonal (Function.update (fun _ : Fin n => (1 : ℝ)) a (D a)) *
            Matrix.diagonal (fun i => if i ∈ s then D i else 1) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        by_cases hi : i = a
        · subst i; simp [ha]
        · simp [hi]
      rw [hmat]
      exact matrix_substitution_mul _ _ (matrix_substitution_scale a (D a) (hne a)) ih
  simpa only [Finset.mem_univ, ite_true] using hpartial Finset.univ

/-- Noncircular linear substitution: the only integration inputs in the
algebraic generation argument are the proved one-coordinate identities. -/
lemma matrix_substitution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    MatrixSubstitution A := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero MatrixSubstitution A hA
  · exact matrix_substitution_diagonal
  · exact matrix_substitution_transvection
  · intro B C _ _ hB hC
    exact matrix_substitution_mul B C hB hC

lemma global_linear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    GlobalSubstitution (matrixEquiv A hA).toHomeomorph |A.det| := by
  obtain ⟨e, he, hsub⟩ := matrix_substitution A hA
  have heq : e.toHomeomorph = (matrixEquiv A hA).toHomeomorph := by
    apply Homeomorph.ext
    intro x
    exact he x
  rwa [heq] at hsub

lemma global_coordinate_translation {n : ℕ} (j : Fin n) (c : ℝ) :
    GlobalSubstitution (Homeomorph.addRight (c • standardBasis n j)) 1 := by
  let e := Homeomorph.addRight (c • standardBasis n j)
  have he : ∀ x, OneCoordinate.coordinateChange j (fun y => y j + c) x = e x := by
    intro x
    ext i
    change Function.update (fun k => x k) j (x j + c) i =
      (x + c • standardBasis n j) i
    by_cases hi : i = j
    · subst i; simp [standardBasis_apply]
    · simp [hi, standardBasis_apply]
  apply global_coordinate j e (fun y => y j + c) he
  · rw [funext he]
    exact contDiff_id.add contDiff_const
  · exact contDiff_id.sub contDiff_const
  · intro x
    change |(fderiv ℝ (fun y : E n => y + c • standardBasis n j) x).det| = 1
    have hd : HasFDerivAt (fun y : E n => y + c • standardBasis n j)
        (ContinuousLinearMap.id ℝ (E n)) x := (hasFDerivAt_id x).add_const _
    rw [hd.fderiv]
    change |LinearMap.det (LinearMap.id : E n →ₗ[ℝ] E n)| = 1
    rw [LinearMap.det_id, abs_one]

lemma global_translation {n : ℕ} (b : E n) :
    GlobalSubstitution (Homeomorph.addRight b) 1 := by
  have hpartial : ∀ s : Finset (Fin n),
      GlobalSubstitution (Homeomorph.addRight (∑ j ∈ s, b j • standardBasis n j)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : Homeomorph.addRight (0 : E n) = Homeomorph.refl (E n) := by ext; simp
      simpa only [Finset.sum_empty, he] using (global_refl (n := n))
    | @insert j s hj ih =>
      have hcomp := global_comp ih (global_coordinate_translation j (b j))
      have he : (Homeomorph.addRight (∑ i ∈ s, b i • standardBasis n i)).trans
          (Homeomorph.addRight (b j • standardBasis n j)) =
          Homeomorph.addRight (∑ i ∈ insert j s, b i • standardBasis n i) := by
        apply Homeomorph.ext
        intro x
        change (x + ∑ i ∈ s, b i • standardBasis n i) + b j • standardBasis n j =
          x + ∑ i ∈ insert j s, b i • standardBasis n i
        rw [Finset.sum_insert hj]
        abel
      simpa only [one_mul, he] using hcomp
  have hb : (∑ j : Fin n, b j • standardBasis n j) = b := by
    ext i
    simp [standardBasis_apply, apply_ite]
  simpa only [hb] using hpartial Finset.univ


/-- Affine substitution for every nonsingular real matrix. The proof uses
algebraic matrix generation, scalar substitution, and Riemann localization;
no linear or nonlinear geometric volume scaling is a premise. -/
theorem affine_substitution : Specs.D04.C07.AffineComposition.affine_substitutionType := by
  intro n A b hA U V e hU hV he f hf hfc
  let H := (matrixEquiv A hA).toHomeomorph.trans (Homeomorph.addRight b)
  have hglobal : GlobalSubstitution H |A.det| := by
    simpa only [one_mul] using global_comp (global_linear A hA) (global_translation b)
  have hHe : ∀ x : U, H x = e x := he
  have hp := Localization.pullback_support e f univ hf hfc (by simp)
  have hfi := Localization.compact_support_integrable f hV hf hfc
  have hgi := Localization.compact_support_integrable (fun x : U => f (e x) * |A.det|)
    hU (hp.1.mul continuous_const) hp.2.1.mul_right
  exact ⟨hfi.1, hgi.1, hfi.2, hgi.2,
    global_restrict hglobal e hU hV hHe f hf hfc⟩

end D04.AffineComposition
