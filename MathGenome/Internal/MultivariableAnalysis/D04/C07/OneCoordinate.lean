import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.OneCoordinate
import MathGenome.Internal.MultivariableAnalysis.D04.C07.Localization
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SlicingAndMoments
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Function Topology
open scoped BigOperators
namespace D04.OneCoordinate
open JordanRegions
abbrev coordinateChange := @Specs.D04.C07.OneCoordinate.Model.coordinateChange
abbrev coordinatePartial := @Specs.D04.C07.OneCoordinate.Model.coordinatePartial
abbrev permute := @Specs.D04.C07.OneCoordinate.Model.permute

@[simp] lemma coordinateChange_apply {n : ℕ} (j : Fin n) (ψ : E n → ℝ)
    (x : E n) (i : Fin n) :
    coordinateChange j ψ x i = Function.update (fun k => x k) j (ψ x) i := rfl
@[simp] lemma permute_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n) (i : Fin n) :
    permute σ x i = x (σ i) := rfl

lemma continuous_partial {n : ℕ} (j : Fin n) {U : Set (E n)}
    (ψ : E n → ℝ) (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U) :
    Continuous (fun x : U => coordinatePartial j ψ x) := by
  exact ((hψ.continuousOn_fderiv_of_isOpen hU le_rfl).domRestrict.clm_apply
    continuous_const)

theorem integrability : Specs.D04.C07.OneCoordinate.integrabilityType := by
  intro n j U V e ψ hU hV hψ f hf hfc
  have hp := Localization.pullback_support e f Set.univ hf hfc (by simp)
  have hg : Continuous (fun x : U => f (e x) * |coordinatePartial j ψ x|) :=
    hp.1.mul (continuous_partial j ψ hU hψ).abs
  have hgc : HasCompactSupport (fun x : U => f (e x) * |coordinatePartial j ψ x|) :=
    hp.2.1.mul_right
  have h₁ := Localization.compact_support_integrable f hV hf hfc
  have h₂ := Localization.compact_support_integrable _ hU hg hgc
  exact ⟨h₁.1, h₂.1, h₁.2, h₂.2⟩


/-- A coordinate permutation as an actual linear isometry. -/
def permutationEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) : E n ≃ₗᵢ[ℝ] E n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm

@[simp] lemma permutationEquiv_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n) :
    permutationEquiv σ x = permute σ x := rfl

@[simp] lemma permute_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n) :
    permute σ.symm (permute σ x) = x := by ext i; simp
@[simp] lemma permute_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n) :
    permute σ (permute σ.symm x) = x := by ext i; simp

namespace Permutation
open Darboux
variable {n : ℕ} (σ : Equiv.Perm (Fin n))
/-- Reorder the bounds and partitions, never the values on a cell face. -/
def box (Q : Box n) : Box n where
  lower := permute σ Q.lower
  upper := permute σ Q.upper
  ordered i := Q.ordered (σ i)

def grid {Q : Box n} (P : Grid Q) : Grid (box σ Q) := fun i => P (σ i)

def indexEquiv {Q : Box n} (P : Grid Q) : CellIndex P ≃ CellIndex (grid σ P) :=
  Equiv.piCongrLeft' (fun i => Fin (P i).n) σ.symm

@[simp] lemma indexEquiv_apply {Q : Box n} (P : Grid Q) (c : CellIndex P) (i : Fin n) :
    indexEquiv σ P c i = c (σ i) := rfl

lemma mem_box {Q : Box n} {x : E n} :
    permute σ x ∈ carrier (box σ Q) ↔ x ∈ carrier Q := by
  constructor
  · intro h i
    simpa [box] using h (σ.symm i)
  · intro h i
    exact h (σ i)

lemma mem_cell {Q : Box n} (P : Grid Q) (c : CellIndex P) (x : E n) :
    permute σ x ∈ cell (grid σ P) (indexEquiv σ P c) ↔ x ∈ cell P c := by
  change (∀ i, x (σ i) ∈ Icc ((P (σ i)).point (c (σ i)).castSucc)
    ((P (σ i)).point (c (σ i)).succ)) ↔
      ∀ i, x i ∈ Icc ((P i).point (c i).castSucc) ((P i).point (c i).succ)
  constructor
  · intro h i
    obtain ⟨k, rfl⟩ := σ.surjective i
    exact h k
  · intro h i
    exact h (σ i)

lemma content_box (Q : Box n) : content (box σ Q) = content Q := by
  exact Equiv.prod_comp σ (fun i => Q.upper i - Q.lower i)

lemma content_cell {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    cellContent (grid σ P) (indexEquiv σ P c) = cellContent P c := by
  exact Equiv.prod_comp σ (fun i => (P i).point (c i).succ - (P i).point (c i).castSucc)

lemma cell_image {Q : Box n} (P : Grid Q) (c : CellIndex P) (f : E n → ℝ) :
    (fun x => f (permute σ.symm x)) '' cell (grid σ P) (indexEquiv σ P c) =
      f '' cell P c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨permute σ.symm x, ?_, rfl⟩
    apply (mem_cell σ P c _).mp
    simpa using hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨permute σ x, (mem_cell σ P c x).mpr hx, by simp⟩

lemma lower_sum {Q : Box n} (P : Grid Q) (f : E n → ℝ) :
    lowerSum (fun x => f (permute σ.symm x)) (grid σ P) = lowerSum f P := by
  symm
  apply Fintype.sum_equiv (indexEquiv σ P)
  intro c
  change cellInfimum f P c * cellContent P c = cellInfimum _ _ _ * cellContent _ _
  rw [show cellInfimum (fun x => f (permute σ.symm x)) (grid σ P) (indexEquiv σ P c) =
    cellInfimum f P c from congrArg sInf (cell_image σ P c f), content_cell]

lemma upper_sum {Q : Box n} (P : Grid Q) (f : E n → ℝ) :
    upperSum (fun x => f (permute σ.symm x)) (grid σ P) = upperSum f P := by
  symm
  apply Fintype.sum_equiv (indexEquiv σ P)
  intro c
  change cellSupremum f P c * cellContent P c = cellSupremum _ _ _ * cellContent _ _
  rw [show cellSupremum (fun x => f (permute σ.symm x)) (grid σ P) (indexEquiv σ P c) =
    cellSupremum f P c from congrArg sSup (cell_image σ P c f), content_cell]

/-- Undo a permutation of a dependent endpoint-indexed partition family. -/
def inverseGrid {Q : Box n} (R : Grid (box σ Q)) : Grid Q := fun i =>
  { n := (R (σ.symm i)).n
    point := (R (σ.symm i)).point
    strictMono := (R (σ.symm i)).strictMono
    first := by simpa [box] using (R (σ.symm i)).first
    last := by simpa [box] using (R (σ.symm i)).last }

lemma grid_surjective (Q : Box n) : Function.Surjective (@grid n σ Q) := by
  intro R
  refine ⟨inverseGrid σ R, ?_⟩
  funext i
  apply eq_of_heq
  apply HEq.trans (b := R (σ.symm (σ i)))
  · exact Fubini.partition_heq _ _ rfl HEq.rfl
  · exact Fubini.dependent_congr R (σ.symm_apply_apply i)

lemma lower_integral (Q : Box n) (f : E n → ℝ) :
    lowerIntegral (fun x => f (permute σ.symm x)) (box σ Q) = lowerIntegral f Q := by
  change sSup _ = sSup _
  congr 1
  ext a
  constructor
  · rintro ⟨R, rfl⟩
    obtain ⟨P, rfl⟩ := grid_surjective σ Q R
    exact ⟨P, (lower_sum σ P f).symm⟩
  · rintro ⟨P, rfl⟩
    exact ⟨grid σ P, lower_sum σ P f⟩

lemma upper_integral (Q : Box n) (f : E n → ℝ) :
    upperIntegral (fun x => f (permute σ.symm x)) (box σ Q) = upperIntegral f Q := by
  change sInf _ = sInf _
  congr 1
  ext a
  constructor
  · rintro ⟨R, rfl⟩
    obtain ⟨P, rfl⟩ := grid_surjective σ Q R
    exact ⟨P, (upper_sum σ P f).symm⟩
  · rintro ⟨P, rfl⟩
    exact ⟨grid σ P, upper_sum σ P f⟩
end Permutation

lemma derivative {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (x : E n)
    (hψ : DifferentiableAt ℝ ψ x) :
    ∃ A : E n →L[ℝ] E n, HasFDerivAt (coordinateChange j ψ) A x ∧
    ∀ v i, A v i = if i = j then fderiv ℝ ψ x v else v i := by
  let A : E n →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi
    (fun i => if i = j then fderiv ℝ ψ x else PiLp.proj 2 (fun _ : Fin n => ℝ) i)
  let B : E n →L[ℝ] E n := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp A
  refine ⟨B, ?_, ?_⟩
  · apply (PiLp.hasFDerivAt_toLp 2 _).comp x
    apply hasFDerivAt_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simpa [A] using hψ.hasFDerivAt
    · simpa [A, hi, Function.update_of_ne hi] using PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i
  · intro v i
    change (if i = j then fderiv ℝ ψ x else PiLp.proj 2 (fun _ : Fin n => ℝ) i) v = _
    split_ifs <;> rfl

lemma determinant_update_identity {n : ℕ} (j : Fin n) (c : Fin n → ℝ) :
    (Matrix.updateRow (1 : Matrix (Fin n) (Fin n) ℝ) j c).det = c j := by
  have hc : (∑ k, c k • (1 : Matrix (Fin n) (Fin n) ℝ) k) = c := by
    ext i
    simp [Matrix.one_apply]
  simpa [hc] using Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) j c


theorem determinant : Specs.D04.C07.OneCoordinate.determinantType := by
  intro n j ψ x hψ
  obtain ⟨A, hA, hAi⟩ := derivative j ψ x hψ
  rw [hA.fderiv]
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix (D04.standardBasis n)]
  have hm : LinearMap.toMatrix (D04.standardBasis n) (D04.standardBasis n) A.toLinearMap =
      Matrix.updateRow (1 : Matrix (Fin n) (Fin n) ℝ) j
        (fun k => fderiv ℝ ψ x (D04.standardBasis n k)) := by
    ext i k
    rw [LinearMap.toMatrix_apply]
    change A (D04.standardBasis n k) i = _
    rw [hAi]
    by_cases hi : i = j
    · subst i; simp
    · simp [hi, Matrix.updateRow, Function.update, Matrix.one_apply, D04.standardBasis_apply]
  rw [hm, determinant_update_identity]
  rfl

lemma permutation_derivative {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n) :
    fderiv ℝ (permute σ) x = (permutationEquiv σ).toContinuousLinearEquiv.toContinuousLinearMap := by
  exact (permutationEquiv σ).toContinuousLinearEquiv.hasFDerivAt.fderiv

theorem permutation_jacobian : Specs.D04.C07.OneCoordinate.permutation_jacobianType := by
  intro n σ x
  rw [permutation_derivative]
  change |LinearMap.det (permutationEquiv σ).toLinearEquiv.toLinearMap| = 1
  rw [← LinearMap.det_toMatrix (D04.standardBasis n)]
  have hm : LinearMap.toMatrix (D04.standardBasis n) (D04.standardBasis n)
      (permutationEquiv σ).toLinearEquiv.toLinearMap =
      (1 : Matrix (Fin n) (Fin n) ℝ).submatrix σ id := by
    ext i k
    rw [LinearMap.toMatrix_apply]
    change D04.standardBasis n k (σ i) = _
    simp [D04.standardBasis_apply, Matrix.one_apply]
  rw [hm, Matrix.det_permute, Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]


lemma domain_preimage {n : ℕ} (σ : Equiv.Perm (Fin n)) {U V : Set (E n)}
    (e : U ≃ₜ V) (he : ∀ x : U, permute σ x = e x) :
    U = permute σ ⁻¹' V := by
  ext x
  constructor
  · intro hx
    rw [mem_preimage, he ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  · intro hx
    let y : V := ⟨permute σ x, hx⟩
    have h : permute σ (e.symm y) = permute σ x := by
      rw [he, e.apply_symm_apply]
    have hx' : (e.symm y : E n) = x := (permutationEquiv σ).injective h
    exact hx' ▸ (e.symm y).property

lemma zeroExtension_permutation {n : ℕ} (σ : Equiv.Perm (Fin n)) {U V : Set (E n)}
    (e : U ≃ₜ V) (he : ∀ x : U, permute σ x = e x) (f : V → ℝ) :
    zeroExtension (f ∘ e) = fun x => zeroExtension f (permute σ x) := by
  funext x
  by_cases hx : x ∈ U
  · have hp : permute σ x ∈ V := by
      have h := hx
      rw [domain_preimage σ e he] at h
      exact h
    rw [zeroExtension_apply (f ∘ e) ⟨x, hx⟩, zeroExtension_apply f ⟨permute σ x, hp⟩]
    change f (e ⟨x, hx⟩) = f ⟨permute σ x, hp⟩
    congr 1
    exact Subtype.ext (he ⟨x, hx⟩).symm
  · have hp : permute σ x ∉ V := by
      intro h
      apply hx
      rw [domain_preimage σ e he]
      exact h
    rw [zeroExtension_of_not_mem _ hx, zeroExtension_of_not_mem _ hp]

lemma permuted_enclosure {n : ℕ} (σ : Equiv.Perm (Fin n))
    (F : E n → ℝ) (Q : Darboux.Box n) (hQ : Encloses (support F) Q) :
    Encloses (support (fun x => F (permute σ x))) (Permutation.box σ.symm Q) := by
  let h := (permutationEquiv σ).toHomeomorph
  have hc : Darboux.carrier (Permutation.box σ.symm Q) = h ⁻¹' Darboux.carrier Q := by
    ext x
    have hh := Permutation.mem_box σ.symm (Q := Q) (x := permute σ x)
    change x ∈ Darboux.carrier (Permutation.box σ.symm Q) ↔ permute σ x ∈ Darboux.carrier Q
    simpa using hh
  have hs : support (fun x => F (permute σ x)) = h ⁻¹' support F := rfl
  change closure (support (fun x => F (permute σ x))) ⊆
    interior (Darboux.carrier (Permutation.box σ.symm Q))
  rw [hs, hc, ← h.preimage_closure, ← h.preimage_interior]
  exact preimage_mono hQ

theorem permutation_substitution :
    Specs.D04.C07.OneCoordinate.permutation_substitutionType := by
  intro n σ U V e hU hV he f hf hfc
  have hp := Localization.pullback_support e f Set.univ hf hfc (by simp)
  have h₁ := Localization.compact_support_integrable f hV hf hfc
  have h₂ := Localization.compact_support_integrable (f ∘ e) hU hp.1 hp.2.1
  refine ⟨h₁.1, h₂.1, h₁.2, h₂.2, ?_⟩
  obtain ⟨Q, hQ, _⟩ := h₁.2.2.2
  obtain ⟨hi, hv⟩ := open_integral_eq_on_enclosing_box f h₁.2 Q hQ
  have hext := zeroExtension_permutation σ e he f
  have hq := permuted_enclosure σ (zeroExtension f) Q hQ
  rw [← hext] at hq
  obtain ⟨hj, hw⟩ := open_integral_eq_on_enclosing_box (f ∘ e) h₂.2
    (Permutation.box σ.symm Q) hq
  change openIntegral f = openIntegral (f ∘ e)
  rw [hv, hw]
  change Darboux.lowerIntegral (zeroExtension f) Q =
    Darboux.lowerIntegral (zeroExtension (f ∘ e)) (Permutation.box σ.symm Q)
  rw [hext]
  exact (Permutation.lower_integral σ.symm Q (zeroExtension f)).symm


namespace Scalar
open Darboux
open SingleVariableAnalysis.Riemann

lemma strict_mono {φ dφ : ℝ → ℝ} {a b : ℝ}
    (h : C1OnInterval φ dφ a b) (hpos : ∀ t ∈ Icc a b, 0 < dφ t) :
    StrictMonoOn φ (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) h.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(h.hasDerivAt ht).deriv]
  exact hpos t ⟨ht.1.le, ht.2.le⟩

lemma strict_anti {φ dφ : ℝ → ℝ} {a b : ℝ}
    (h : C1OnInterval φ dφ a b) (hneg : ∀ t ∈ Icc a b, dφ t < 0) :
    StrictAntiOn φ (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) h.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(h.hasDerivAt ht).deriv]
  exact hneg t ⟨ht.1.le, ht.2.le⟩

lemma image_interval {φ dφ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : C1OnInterval φ dφ a b)
    (hsign : (∀ t ∈ Icc a b, 0 < dφ t) ∨ (∀ t ∈ Icc a b, dφ t < 0)) :
    φ '' Icc a b = Icc (min (φ a) (φ b)) (max (φ a) (φ b)) := by
  rcases hsign with hp | hn
  · have hm := (strict_mono h hp).monotoneOn
    have he := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simpa only [min_eq_left he, max_eq_right he] using
      h.continuousOn.image_Icc_of_monotoneOn hab hm
  · have hm := (strict_anti h hn).antitoneOn
    have he := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simpa only [min_eq_right he, max_eq_left he] using
      h.continuousOn.image_Icc_of_antitoneOn hab hm
end Scalar



theorem scalar_substitution : Specs.D04.C07.OneCoordinate.scalar_substitutionType := by
  intro φ dφ f a b hab h hsign hf
  let A := Darboux.intervalBox a b hab.le
  let B := Darboux.intervalBox (min (φ a) (φ b)) (max (φ a) (φ b)) min_le_max
  let F : E 1 → ℝ := fun y => f (y 0)
  let H : E 1 → ℝ := fun y => dφ (y 0) * f (φ (y 0))
  let G : E 1 → ℝ := fun y => |dφ (y 0)| * f (φ (y 0))
  have hF : Darboux.Integrable F B := SlicingAndMoments.continuous_box_integrable F
    (hf.comp (PiLp.continuous_apply 2 _ 0)) B
  obtain ⟨hfs, hFval⟩ := (Darboux.scalar_integral F _ _ min_le_max).2 hF
  have hfo : SingleVariableAnalysis.Riemann.OrientedRealIntegrable f (φ a) (φ b) := hfs
  have hmono : MonotoneOn φ (Icc a b) ∨ AntitoneOn φ (Icc a b) := by
    rcases hsign with hp | hn
    · exact Or.inl (Scalar.strict_mono h hp).monotoneOn
    · exact Or.inr (Scalar.strict_anti h hn).antitoneOn
  obtain ⟨hhs, hHval⟩ := SingleVariableAnalysis.Riemann.real_monotone_substitution
    φ dφ f hab.le h hmono hfo
  have hH : Darboux.Integrable H A := (Darboux.scalar_integral H a b hab.le).1.mpr hhs
  obtain ⟨_, hHv⟩ := (Darboux.scalar_integral H a b hab.le).2 hH
  have hv : Darboux.lowerIntegral H A =
      SingleVariableAnalysis.Riemann.orientedRealIntegral f hfo := hHv.trans hHval
  rcases hsign with hp | hn
  · have he : φ a < φ b := Scalar.strict_mono h hp ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
    have heq : EqOn G H (Darboux.carrier A) := by
      intro y hy
      change |dφ (y 0)| * _ = dφ (y 0) * _
      rw [abs_of_pos (hp (y 0) (hy 0))]
    have hG : Darboux.Integrable G A := (integrable_congr heq).mpr hH
    refine ⟨hG, hF, ?_⟩
    change Darboux.lowerIntegral G A = Darboux.lowerIntegral F B
    rw [lowerIntegral_congr heq, hv]
    exact (show SingleVariableAnalysis.Riemann.orientedRealIntegral f hfo =
      SingleVariableAnalysis.Riemann.realIntegral f hfs from by
        simp only [SingleVariableAnalysis.Riemann.orientedRealIntegral,
          SingleVariableAnalysis.Riemann.O.realIntegralValue, ite_eq_left he.le]).trans hFval.symm
  · have he : φ b < φ a := Scalar.strict_anti h hn ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
    have heq : EqOn G (fun y => (-1 : ℝ) * H y) (Darboux.carrier A) := by
      intro y hy
      change |dφ (y 0)| * _ = (-1 : ℝ) * (dφ (y 0) * _)
      rw [abs_of_neg (hn (y 0) (hy 0))]
      ring
    have hN := Darboux.integrable_smul (-1) hH
    have hG : Darboux.Integrable G A := (integrable_congr heq).mpr hN
    refine ⟨hG, hF, ?_⟩
    change Darboux.lowerIntegral G A = Darboux.lowerIntegral F B
    rw [lowerIntegral_congr heq]
    change Darboux.integral (fun y => (-1 : ℝ) * H y) A hN = _
    rw [Darboux.integral_smul (-1) hH hN]
    change (-1 : ℝ) * Darboux.lowerIntegral H A = _
    rw [hv]
    have ho : SingleVariableAnalysis.Riemann.orientedRealIntegral f hfo =
        -SingleVariableAnalysis.Riemann.realIntegral f hfs := by
      simp only [SingleVariableAnalysis.Riemann.orientedRealIntegral,
        SingleVariableAnalysis.Riemann.O.realIntegralValue, ite_eq_right (not_le.mpr he)]
    rw [ho]
    rw [neg_one_mul, neg_neg]
    exact hFval.symm


theorem nonvanishing : Specs.D04.C07.OneCoordinate.nonvanishingType := by
  intro n j U V e ψ S hU hV hψ hS he hSe x hx
  change coordinatePartial j ψ x ≠ 0
  have he' : ∀ z : U, coordinateChange j ψ z = e z := he
  have hdψ : DifferentiableAt ℝ ψ x :=
    (hψ.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨A, hA, _⟩ := derivative j ψ x hdψ
  have hTx : coordinateChange j ψ x ∈ V := by
    rw [he' ⟨x, hx⟩]; exact (e ⟨x, hx⟩).property
  have hdS : DifferentiableAt ℝ S (coordinateChange j ψ x) :=
    (hS.differentiableOn (by simp) _ hTx).differentiableAt (hV.mem_nhds hTx)
  have hinv : (fun z => S (coordinateChange j ψ z)) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with z hz
    rw [he' ⟨z, hz⟩, hSe (e ⟨z, hz⟩), e.symm_apply_apply]
    rfl
  have hcomp := hdS.hasFDerivAt.comp x hA
  have hId := hcomp.congr_of_eventuallyEq hinv.symm
  have hEq := hId.unique (hasFDerivAt_id x)
  have hdet := congrArg (fun L : E n →L[ℝ] E n => LinearMap.det L.toLinearMap) hEq
  change LinearMap.det ((fderiv ℝ S (coordinateChange j ψ x)).toLinearMap.comp
    A.toLinearMap) = LinearMap.det (LinearMap.id : E n →ₗ[ℝ] E n) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  have hAdet : LinearMap.det A.toLinearMap = coordinatePartial j ψ x := by
    rw [← hA.fderiv]
    exact determinant j ψ x hdψ
  rw [hAdet] at hdet
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

/-- Either derivative sign persists on a genuine ambient open neighborhood. -/
lemma local_sign {n : ℕ} (j : Fin n) {U : Set (E n)} (ψ : E n → ℝ)
    (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U) (x : E n) (hx : x ∈ U)
    (hne : coordinatePartial j ψ x ≠ 0) :
    ∃ W : Set (E n), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ((∀ y ∈ W, 0 < coordinatePartial j ψ y) ∨
        (∀ y ∈ W, coordinatePartial j ψ y < 0)) := by
  have hc : ContinuousOn (coordinatePartial j ψ) U :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_partial j ψ hU hψ)
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact ⟨U ∩ coordinatePartial j ψ ⁻¹' Iio 0,
      hc.isOpen_inter_preimage hU isOpen_Iio, ⟨hx, hn⟩, inter_subset_left,
      Or.inr (fun _ hy => hy.2)⟩
  · exact ⟨U ∩ coordinatePartial j ψ ⁻¹' Ioi 0,
      hc.isOpen_inter_preimage hU isOpen_Ioi, ⟨hx, hp⟩, inter_subset_left,
      Or.inl (fun _ hy => hy.2)⟩

/-- Hold the other coordinates fixed and vary coordinate j. -/
def coordinateLine {n : ℕ} (j : Fin n) (x : E n) (t : ℝ) : E n :=
  WithLp.toLp 2 (Function.update (fun i => x i) j t)

lemma coordinateLine_affine {n : ℕ} (j : Fin n) (x : E n) (t : ℝ) :
    coordinateLine j x t = x + (t - x j) • D04.standardBasis n j := by
  ext i
  by_cases hi : i = j
  · subst i; simp [coordinateLine, D04.standardBasis_apply]
  · simp [coordinateLine, D04.standardBasis_apply, hi]

lemma coordinateLine_derivative {n : ℕ} (j : Fin n) (x : E n) (t : ℝ) :
    HasDerivAt (coordinateLine j x) (D04.standardBasis n j) t := by
  have h := (hasDerivAt_const t x).add
    (((hasDerivAt_id t).sub_const (x j)).smul_const (D04.standardBasis n j))
  have heq : coordinateLine j x = (fun _ => x) +
      (fun t => (id t - x j) • D04.standardBasis n j) := by
    funext s
    exact coordinateLine_affine j x s
  rw [heq]
  simpa only [one_smul, zero_add] using h

lemma coordinateLine_continuous {n : ℕ} (j : Fin n) (x : E n) :
    Continuous (coordinateLine j x) :=
  continuous_iff_continuousAt.mpr (fun t => (coordinateLine_derivative j x t).continuousAt)

lemma slice_c1 {n : ℕ} (j : Fin n) {U : Set (E n)} (ψ : E n → ℝ)
    (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U) (x : E n) (a b : ℝ)
    (hline : ∀ t ∈ Icc a b, coordinateLine j x t ∈ U) :
    SingleVariableAnalysis.Riemann.C1OnInterval
      (fun t => ψ (coordinateLine j x t))
      (fun t => coordinatePartial j ψ (coordinateLine j x t)) a b := by
  have hc : ContinuousOn (coordinatePartial j ψ) U :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_partial j ψ hU hψ)
  refine ⟨hc.comp (coordinateLine_continuous j x).continuousOn hline, ?_⟩
  intro t ht
  have hdψ := (hψ.differentiableOn (by simp) _ (hline t ht)).differentiableAt
    (hU.mem_nhds (hline t ht))
  exact (hdψ.hasFDerivAt.comp_hasDerivAt t (coordinateLine_derivative j x t)).hasDerivWithinAt

lemma coordinateChange_line {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (x : E n) (t : ℝ) :
    coordinateChange j ψ (coordinateLine j x t) =
      coordinateLine j x (ψ (coordinateLine j x t)) := by
  ext i
  by_cases hi : i = j <;> simp [coordinateLine, coordinateChange_apply, hi]


namespace Cylinder
open Darboux SlicingAndMoments
variable {p : ℕ}

lemma stackPoint_castSucc (x : E p) (t : ℝ) (i : Fin p) :
    stackPoint x t i.castSucc = x i := by
  exact Darboux.Fubini.blockPoint_left finSumFinEquiv x (scalarPoint t) i

lemma stackPoint_last (x : E p) (t : ℝ) :
    stackPoint x t (Fin.last p) = t := height_stackPoint x t

lemma coordinateLine_stackPoint (x : E p) (s t : ℝ) :
    coordinateLine (Fin.last p) (stackPoint x s) t = stackPoint x t := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [coordinateLine, stackPoint_last]
  | cast i =>
    simp [coordinateLine, Fin.castSucc_ne_last, stackPoint_castSucc]

lemma coordinateChange_stackPoint (ψ : E (p+1) → ℝ) (x : E p) (t : ℝ) :
    coordinateChange (Fin.last p) ψ (stackPoint x t) = stackPoint x (ψ (stackPoint x t)) := by
  have h := coordinateChange_line (Fin.last p) ψ (stackPoint x 0) t
  simpa only [coordinateLine_stackPoint] using h

lemma continuous_stackPoint_base (t : ℝ) : Continuous (fun x : E p => stackPoint x t) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  dsimp only [stackPoint, Specs.D04.C06.SlicingAndMoments.Model.stackPoint,
    Specs.D04.C06.DarbouxFubini.Model.productPoint,
    Specs.D04.C06.DarbouxFubini.Model.blockPoint]
  cases finSumFinEquiv.symm i with
  | inl j => exact PiLp.continuous_apply 2 _ j
  | inr j => exact continuous_const

lemma slice_c1 {U : Set (E (p+1))} (ψ : E (p+1) → ℝ)
    (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U) (x : E p) (a b : ℝ)
    (hline : ∀ t ∈ Icc a b, stackPoint x t ∈ U) :
    SingleVariableAnalysis.Riemann.C1OnInterval
      (fun t => ψ (stackPoint x t))
      (fun t => coordinatePartial (Fin.last p) ψ (stackPoint x t)) a b := by
  have h := OneCoordinate.slice_c1 (Fin.last p) ψ hU hψ (stackPoint x 0) a b
    (by simpa only [coordinateLine_stackPoint] using hline)
  simpa only [coordinateLine_stackPoint] using h

/-- The image is a region between graphs, with the endpoints sorted separately
in every fiber. No assertion that it is a rectangular box occurs here. -/
lemma image_between (A : Set (E p)) {U : Set (E (p+1))} (ψ : E (p+1) → ℝ)
    (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U) (a b : ℝ) (hab : a ≤ b)
    (hline : ∀ x ∈ A, ∀ t ∈ Icc a b, stackPoint x t ∈ U)
    (hsign : (∀ x ∈ A, ∀ t ∈ Icc a b, 0 < coordinatePartial (Fin.last p) ψ (stackPoint x t)) ∨
      (∀ x ∈ A, ∀ t ∈ Icc a b, coordinatePartial (Fin.last p) ψ (stackPoint x t) < 0)) :
    coordinateChange (Fin.last p) ψ '' between A (fun _ => a) (fun _ => b) =
      between A (fun x => min (ψ (stackPoint x a)) (ψ (stackPoint x b)))
        (fun x => max (ψ (stackPoint x a)) (ψ (stackPoint x b))) := by
  have hi (x : E p) (hx : x ∈ A) := Scalar.image_interval hab
    (slice_c1 ψ hU hψ x a b (hline x hx))
    (hsign.imp (fun hp => hp x hx) (fun hn => hn x hx))
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : basePoint w ∈ A ∧ height w ∈ Icc a b := ⟨hw.1, hw.2.1, hw.2.2⟩
    have himg : ψ (stackPoint (basePoint w) (height w)) ∈
        Icc (min (ψ (stackPoint (basePoint w) a)) (ψ (stackPoint (basePoint w) b)))
          (max (ψ (stackPoint (basePoint w) a)) (ψ (stackPoint (basePoint w) b))) := by
      rw [← hi (basePoint w) hw'.1]
      exact ⟨height w, hw'.2, rfl⟩
    have heq := coordinateChange_stackPoint ψ (basePoint w) (height w)
    rw [stackPoint_base_height] at heq
    rw [heq]
    exact ⟨by simpa using hw'.1, by simpa using himg.1, by simpa using himg.2⟩
  · intro hz
    have hh : height z ∈ Icc
        (min (ψ (stackPoint (basePoint z) a)) (ψ (stackPoint (basePoint z) b)))
        (max (ψ (stackPoint (basePoint z) a)) (ψ (stackPoint (basePoint z) b))) :=
      ⟨hz.2.1, hz.2.2⟩
    rw [← hi (basePoint z) hz.1] at hh
    obtain ⟨t, ht, hval⟩ := hh
    refine ⟨stackPoint (basePoint z) t, ?_, ?_⟩
    · exact ⟨by simpa using hz.1, by simpa using ht.1, by simpa using ht.2⟩
    · change ψ (stackPoint (basePoint z) t) = height z at hval
      rw [coordinateChange_stackPoint, hval, stackPoint_base_height]

/-- Riemann substitution on one closed cylinder, proved by the scalar theorem
and the upstream pointwise Riemann slicing theorem. The latter supplies the
continuous-graph boundary control and all zero-extension integrability claims. -/
lemma integral_between (A : Set (E p)) (hA : Jordan A)
    {U : Set (E (p+1))} (ψ : E (p+1) → ℝ) (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 1 ψ U) (a b : ℝ) (hab : a < b)
    (hline : ∀ x ∈ closure A, ∀ t ∈ Icc a b, stackPoint x t ∈ U)
    (hsign : (∀ x ∈ closure A, ∀ t ∈ Icc a b,
        0 < coordinatePartial (Fin.last p) ψ (stackPoint x t)) ∨
      (∀ x ∈ closure A, ∀ t ∈ Icc a b,
        coordinatePartial (Fin.last p) ψ (stackPoint x t) < 0))
    (F : E (p+1) → ℝ) (hF : Continuous F) :
    let L := fun x => min (ψ (stackPoint x a)) (ψ (stackPoint x b))
    let H := fun x => max (ψ (stackPoint x a)) (ψ (stackPoint x b))
    let G := fun z => F (coordinateChange (Fin.last p) ψ z) *
      |coordinatePartial (Fin.last p) ψ z|
    Jordan (between A L H) ∧
    RegionIntegrable (fun z : between A L H => F z) ∧
    RegionIntegrable (fun z : between A (fun _ => a) (fun _ => b) => G z) ∧
    regionIntegral (fun z : between A L H => F z) =
      regionIntegral (fun z : between A (fun _ => a) (fun _ => b) => G z) := by
  let L := fun x => min (ψ (stackPoint x a)) (ψ (stackPoint x b))
  let H := fun x => max (ψ (stackPoint x a)) (ψ (stackPoint x b))
  let G := fun z => F (coordinateChange (Fin.last p) ψ z) *
    |coordinatePartial (Fin.last p) ψ z|
  have hca : ContinuousOn (fun x => ψ (stackPoint x a)) (closure A) :=
    hψ.continuousOn.comp (continuous_stackPoint_base a).continuousOn
      (fun x hx => hline x hx a ⟨le_rfl, hab.le⟩)
  have hcb : ContinuousOn (fun x => ψ (stackPoint x b)) (closure A) :=
    hψ.continuousOn.comp (continuous_stackPoint_base b).continuousOn
      (fun x hx => hline x hx b ⟨hab.le, le_rfl⟩)
  have hL : ContinuousOn L (closure A) := hca.inf hcb
  have hH : ContinuousOn H (closure A) := hca.sup hcb
  have hR := slicing A L H hA hL hH (fun _ _ => min_le_max)
  have hS := slicing A (fun _ => a) (fun _ => b) hA continuousOn_const continuousOn_const
    (fun _ _ => hab.le)
  have hsub : closure (between A (fun _ => a) (fun _ => b)) ⊆ U := by
    intro z hz
    have hh := closure_between_subset A (fun _ => a) (fun _ => b)
      continuousOn_const continuousOn_const hz
    have hh' := hline (basePoint z) hh.1 (height z) ⟨hh.2.1, hh.2.2⟩
    simpa only [stackPoint_base_height] using hh'
  have hT : ContinuousOn (coordinateChange (Fin.last p) ψ) U := by
    intro x hx
    have hdψ := (hψ.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
    obtain ⟨_, hd, _⟩ := derivative (Fin.last p) ψ x hdψ
    exact hd.continuousAt.continuousWithinAt
  have hJ : ContinuousOn (coordinatePartial (Fin.last p) ψ) U :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_partial (Fin.last p) ψ hU hψ)
  have hG : ContinuousOn G (closure (between A (fun _ => a) (fun _ => b))) :=
    ((hF.comp_continuousOn hT).mul hJ.abs).mono hsub
  have hRf := hR.2.2 F hF.continuousOn
  have hSg := hS.2.2 G hG
  refine ⟨hR.2.1, hRf.1, hSg.1, ?_⟩
  have hslices : (fun x : A => sliceIntegral (fun _ => a) (fun _ => b) G x) =
      (fun x : A => sliceIntegral L H F x) := by
    funext x
    let φ := fun t => ψ (stackPoint (x : E p) t)
    let dφ := fun t => coordinatePartial (Fin.last p) ψ (stackPoint (x : E p) t)
    let f := fun t => F (stackPoint (x : E p) t)
    have hc := slice_c1 ψ hU hψ x a b (hline x (subset_closure x.property))
    have hs := scalar_substitution φ dφ f a b hab hc
      (hsign.imp (fun hp => hp x (subset_closure x.property))
        (fun hn => hn x (subset_closure x.property)))
      (hF.comp (continuous_stackPoint (x : E p)))
    change lowerIntegral (fun y => G (productPoint (x : E p) y))
        (sliceBox (fun _ => a) (fun _ => b) (x : E p)) =
      lowerIntegral (fun y => F (productPoint (x : E p) y)) (sliceBox L H (x : E p))
    rw [sliceBox_eq_interval (fun _ => a) (fun _ => b) (x : E p) hab.le,
      sliceBox_eq_interval L H (x : E p) min_le_max]
    have hGs : (fun y => G (productPoint (x : E p) y)) =
        (fun y : E 1 => |dφ (y 0)| * f (φ (y 0))) := by
      funext y
      simp only [G, productPoint_eq_stackPoint, coordinateChange_stackPoint, dφ, f, φ]
      exact mul_comm _ _
    have hFs : (fun y => F (productPoint (x : E p) y)) =
        (fun y : E 1 => f (y 0)) := by
      funext y
      rw [productPoint_eq_stackPoint]
    rw [hGs, hFs]
    exact hs.2.2
  rw [hRf.2.2.2, hSg.2.2.2, hslices]
end Cylinder


/-- Equal zero extensions give the same integral, even though open-domain and
bounded-region integrals use different enclosing-box conventions. -/
lemma open_eq_region {n : ℕ} {V R : Set (E n)} (f : V → ℝ) (g : R → ℝ)
    (hf : OpenIntegrable f) (hg : RegionIntegrable g)
    (hext : zeroExtension f = zeroExtension g) : openIntegral f = regionIntegral g := by
  obtain ⟨Q, hQ, hgQ⟩ := hg.2
  have hs : support (zeroExtension f) ⊆ R := by
    intro x hx
    by_contra hn
    apply hx
    rw [hext, zeroExtension_of_not_mem g hn]
  have hQs : Encloses (support (zeroExtension f)) Q := (closure_mono hs).trans hQ
  obtain ⟨hfQ, hv⟩ := open_integral_eq_on_enclosing_box f hf Q hQs
  rw [hv, integral_eq_on_enclosing_box g hg hQ hgQ]
  change Darboux.lowerIntegral (zeroExtension f) Q = Darboux.lowerIntegral (zeroExtension g) Q
  rw [hext]

namespace Cylinder
open Darboux SlicingAndMoments
variable {p : ℕ}

/-- The local identity for compact-supported functions on the full target
open set. This is the form required by finite continuous localization. -/
lemma localized_integral (A : Set (E p)) (hA : Jordan A) {U V : Set (E (p+1))}
    (e : U ≃ₜ V) (ψ : E (p+1) → ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hψ : ContDiffOn ℝ 1 ψ U)
    (he : ∀ x : U, coordinateChange (Fin.last p) ψ x = e x)
    (a b : ℝ) (hab : a < b)
    (hline : ∀ x ∈ closure A, ∀ t ∈ Icc a b, stackPoint x t ∈ U)
    (hsign : (∀ x ∈ closure A, ∀ t ∈ Icc a b,
        0 < coordinatePartial (Fin.last p) ψ (stackPoint x t)) ∨
      (∀ x ∈ closure A, ∀ t ∈ Icc a b,
        coordinatePartial (Fin.last p) ψ (stackPoint x t) < 0))
    (f : V → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Subtype.val ⁻¹'
      (coordinateChange (Fin.last p) ψ '' between A (fun _ => a) (fun _ => b))) :
    openIntegral f = openIntegral (fun x : U => f (e x) * |coordinatePartial (Fin.last p) ψ x|) := by
  let C := between A (fun _ => a) (fun _ => b)
  let T := coordinateChange (Fin.last p) ψ
  let R := T '' C
  let F := zeroExtension f
  let g : U → ℝ := fun x => f (e x) * |coordinatePartial (Fin.last p) ψ x|
  let G := fun z => F (T z) * |coordinatePartial (Fin.last p) ψ z|
  have hCF : Continuous F := (Localization.compact_support_integrable f hV hf hfc).1
  have hCsub : C ⊆ U := by
    intro z hz
    have hh := hline (basePoint z) (subset_closure hz.1) (height z) ⟨hz.2.1, hz.2.2⟩
    simpa only [stackPoint_base_height] using hh
  have himage := image_between A ψ hU hψ a b hab.le
    (fun x hx => hline x (subset_closure hx))
    (hsign.imp (fun hp x hx => hp x (subset_closure hx))
      (fun hn x hx => hn x (subset_closure hx)))
  have hint := integral_between A hA ψ hU hψ a b hab hline hsign F hCF
  change R = _ at himage
  have hfr : RegionIntegrable (fun z : R => F z) := by
    rw [himage]
    exact hint.2.1
  have hgc : RegionIntegrable (fun z : C => G z) := hint.2.2.1
  have hval : regionIntegral (fun z : R => F z) = regionIntegral (fun z : C => G z) := by
    rw [himage]
    exact hint.2.2.2
  have hfext : zeroExtension f = zeroExtension (fun z : R => F z) := by
    funext z
    by_cases hz : z ∈ R
    · exact (zeroExtension_apply (fun z : R => F z) ⟨z, hz⟩).symm
    · have hfz : zeroExtension f z = 0 := by
        by_cases hzV : z ∈ V
        · rw [zeroExtension_apply f ⟨z, hzV⟩]
          exact image_eq_zero_of_notMem_tsupport (fun hh => hz (hsupp hh))
        · exact zeroExtension_of_not_mem f hzV
      rw [zeroExtension_of_not_mem _ hz, hfz]
  have hgext : zeroExtension g = zeroExtension (fun z : C => G z) := by
    funext z
    by_cases hz : z ∈ C
    · have hzU := hCsub hz
      rw [zeroExtension_apply g ⟨z, hzU⟩, zeroExtension_apply (fun z : C => G z) ⟨z, hz⟩]
      change f (e ⟨z, hzU⟩) * _ = zeroExtension f (T z) * _
      have hTz : T z = e ⟨z, hzU⟩ := he ⟨z, hzU⟩
      rw [hTz, zeroExtension_apply f (e ⟨z, hzU⟩)]
    · rw [zeroExtension_of_not_mem _ hz]
      by_cases hzU : z ∈ U
      · rw [zeroExtension_apply g ⟨z, hzU⟩]
        change f (e ⟨z, hzU⟩) * _ = 0
        have hfz : f (e ⟨z, hzU⟩) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hh
          obtain ⟨w, hw, hwe⟩ := hsupp hh
          have hwU := hCsub hw
          have hew : e ⟨w, hwU⟩ = e ⟨z, hzU⟩ := by
            apply Subtype.ext
            exact (he ⟨w, hwU⟩).symm.trans hwe
          have hwz : w = z := congrArg Subtype.val (e.injective hew)
          exact hz (hwz ▸ hw)
        rw [hfz, zero_mul]
      · exact zeroExtension_of_not_mem g hzU
  have hintg := integrability (Fin.last p) e ψ hU hV hψ f hf hfc
  calc
    openIntegral f = regionIntegral (fun z : R => F z) :=
      open_eq_region f _ hintg.2.2.1 hfr hfext
    _ = regionIntegral (fun z : C => G z) := hval
    _ = openIntegral g := (open_eq_region g _ hintg.2.2.2 hgc hgext).symm
end Cylinder

namespace Boxes
open Darboux NullCovers SlicingAndMoments

def base {p : ℕ} (Q : Box (p+1)) : Box p where
  lower := basePoint Q.lower
  upper := basePoint Q.upper
  ordered i := Q.ordered i.castSucc

lemma split {p : ℕ} (Q : Box (p+1)) :
    productBox (base Q) (intervalBox (height Q.lower) (height Q.upper) (Q.ordered (Fin.last p))) = Q := by
  apply Darboux.Subdivision.box_ext
  · change stackPoint (basePoint Q.lower) (height Q.lower) = Q.lower
    exact stackPoint_base_height Q.lower
  · change stackPoint (basePoint Q.upper) (height Q.upper) = Q.upper
    exact stackPoint_base_height Q.upper

lemma carrier_split {p : ℕ} (Q : Box (p+1)) :
    carrier Q = between (carrier (base Q)) (fun _ => height Q.lower) (fun _ => height Q.upper) := by
  ext z
  have h := productBox_mem_iff z (base Q) (height Q.lower) (height Q.upper) (Q.ordered (Fin.last p))
  rw [split Q] at h
  exact h

lemma jordan_carrier {n : ℕ} (Q : Box n) : Jordan (carrier Q) := by
  induction n with
  | zero => exact jordan_zero_dim _
  | succ p ih =>
    rw [carrier_split Q]
    exact between_jordan _ (ih (base Q)) _ _ continuousOn_const continuousOn_const
      (fun _ _ => Q.ordered (Fin.last p))

/-- Closed coordinate boxes form a neighborhood basis, including R⁰. -/
lemma exists_closed_box {n : ℕ} {W : Set (E n)} (hW : IsOpen W) (x : E n) (hx : x ∈ W) :
    ∃ Q : Box n, x ∈ interior (carrier Q) ∧ Nondegenerate Q ∧ carrier Q ⊆ W := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW x hx
  let d := r / (Real.sqrt n + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdeq : d * (Real.sqrt n + 1) = r := div_mul_cancel₀ _ (by positivity)
  let Q : Box n := {
    lower := WithLp.toLp 2 (fun i => x i - d)
    upper := WithLp.toLp 2 (fun i => x i + d)
    ordered i := by change x i - d ≤ x i + d; linarith }
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [interior_carrier]
    intro i
    change x i - d < x i ∧ x i < x i + d
    constructor <;> linarith
  · intro i
    change x i - d < x i + d
    linarith
  · intro y hy
    apply hball
    have hmax : D04.maxNorm (y-x) ≤ d := by
      rw [D04.maxNorm_eq_coordinate_norm]
      apply (pi_norm_le_iff_of_nonneg hd.le).mpr
      intro i
      change |y i - x i| ≤ d
      have hhi : x i - d ≤ y i ∧ y i ≤ x i + d := hy i
      exact abs_le.mpr ⟨by linarith [hhi.1], by linarith [hhi.2]⟩
    have hn := (D04.norm_le_sqrt_mul_maxNorm (y-x)).trans
      (mul_le_mul_of_nonneg_left hmax (Real.sqrt_nonneg _))
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith
end Boxes

/-- Substitution when the changed coordinate is last; the nonzero-partial
hypothesis is subsequently discharged from the inverse regularity. -/
lemma last_integral {p : ℕ} {U V : Set (E (p+1))} (e : U ≃ₜ V)
    (ψ : E (p+1) → ℝ) (hU : IsOpen U) (hV : IsOpen V) (hψ : ContDiffOn ℝ 1 ψ U)
    (he : ∀ x : U, coordinateChange (Fin.last p) ψ x = e x)
    (hne : ∀ x ∈ U, coordinatePartial (Fin.last p) ψ x ≠ 0)
    (f : V → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    openIntegral f = openIntegral (fun x : U => f (e x) * |coordinatePartial (Fin.last p) ψ x|) := by
  classical
  let ι := {Q : Darboux.Box (p+1) // Darboux.carrier Q ⊆ U ∧ Darboux.Nondegenerate Q ∧
    ((∀ x ∈ Darboux.carrier Q, 0 < coordinatePartial (Fin.last p) ψ x) ∨
      (∀ x ∈ Darboux.carrier Q, coordinatePartial (Fin.last p) ψ x < 0))}
  let T := coordinateChange (Fin.last p) ψ
  let W : ι → Set (E (p+1)) := fun Q => T '' interior (Darboux.carrier Q.val)
  have hW (Q : ι) : IsOpen (W Q) := by
    have himg : W Q = Subtype.val ''
        (e '' ((Subtype.val : U → E (p+1)) ⁻¹' interior (Darboux.carrier Q.val))) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxU := Q.property.1 (interior_subset hx)
        exact ⟨e ⟨x, hxU⟩, ⟨⟨x, hxU⟩, hx, rfl⟩, (he ⟨x, hxU⟩).symm⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, he x⟩
    rw [himg]
    exact hV.isOpenMap_subtype_val _
      (e.isOpenMap _ (isOpen_interior.preimage continuous_subtype_val))
  have hcover : V ⊆ ⋃ Q, W Q := by
    intro y hy
    let x : U := e.symm ⟨y, hy⟩
    obtain ⟨O, hO, hxO, hOU, hsign⟩ := local_sign (Fin.last p) ψ hU hψ x x.property
      (hne x x.property)
    obtain ⟨Q, hxQ, hQnd, hQO⟩ := Boxes.exists_closed_box hO x hxO
    let i : ι := ⟨Q, hQO.trans hOU, hQnd,
      hsign.imp (fun hp z hz => hp z (hQO hz)) (fun hn z hz => hn z (hQO hz))⟩
    apply mem_iUnion.mpr
    refine ⟨i, x, hxQ, ?_⟩
    exact (he x).trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))
  have hlocal (Q : ι) (g : V → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgs : tsupport g ⊆ Subtype.val ⁻¹' W Q) :
      openIntegral g = openIntegral (fun x : U => g (e x) * |coordinatePartial (Fin.last p) ψ x|) := by
    let B := Boxes.base Q.val
    let a := SlicingAndMoments.height Q.val.lower
    let b := SlicingAndMoments.height Q.val.upper
    have hB : closure (Darboux.carrier B) = Darboux.carrier B :=
      NullCovers.isClosed_carrier B |>.closure_eq
    have hstack (x : E p) (hx : x ∈ closure (Darboux.carrier B)) (t : ℝ) (ht : t ∈ Icc a b) :
        SlicingAndMoments.stackPoint x t ∈ Darboux.carrier Q.val := by
      have hh := (SlicingAndMoments.stackPoint_mem_productBox x t B a b (Q.val.ordered (Fin.last p))).mpr
        ⟨hB ▸ hx, ht⟩
      simpa only [B, a, b, Boxes.split] using hh
    apply Cylinder.localized_integral (Darboux.carrier B) (Boxes.jordan_carrier B)
      e ψ hU hV hψ he a b (Q.property.2.1 (Fin.last p))
      (fun x hx t ht => Q.property.1 (hstack x hx t ht))
      (Q.property.2.2.imp (fun hp x hx t ht => hp _ (hstack x hx t ht))
        (fun hn x hx t ht => hn _ (hstack x hx t ht))) g hg hgc
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hgs hy
    refine ⟨x, ?_, hxy⟩
    have hxQ := interior_subset hx
    rw [Boxes.carrier_split Q.val] at hxQ
    exact hxQ
  have h := Localization.weighted_localization e
    (fun x : U => |coordinatePartial (Fin.last p) ψ x|) W hU hV
    (continuous_partial (Fin.last p) ψ hU hψ).abs hW hcover hlocal f hf hfc
  exact h.2.2.1

/-- Restrict a coordinate permutation to the preimage of any domain. -/
def permutationDomain {n : ℕ} (σ : Equiv.Perm (Fin n)) (U : Set (E n)) :
    (permute σ ⁻¹' U) ≃ₜ U where
  toFun x := ⟨permute σ x, x.property⟩
  invFun y := ⟨permute σ.symm y, by simpa using y.property⟩
  left_inv x := Subtype.ext (permute_inv σ x)
  right_inv y := Subtype.ext (permute_inv' σ y)
  continuous_toFun := ((permutationEquiv σ).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((permutationEquiv σ.symm).continuous.comp continuous_subtype_val).subtype_mk _

lemma permute_basis {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    permute σ.symm (D04.standardBasis n k) = D04.standardBasis n (σ k) := by
  ext i
  by_cases hi : i = σ k
  · subst i
    simp [D04.standardBasis_apply]
  · have hn : σ.symm i ≠ k := by
      intro h
      exact hi ((σ.apply_symm_apply i).symm.trans (congrArg σ h))
    simp [D04.standardBasis_apply, hi, hn]

lemma conjugate_change {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n)
    (ψ : E n → ℝ) (x : E n) :
    coordinateChange k (ψ ∘ permute σ.symm) x =
      permute σ (coordinateChange (σ k) ψ (permute σ.symm x)) := by
  ext i
  by_cases hi : i = k
  · subst i
    simp [coordinateChange_apply]
  · have hn : σ i ≠ σ k := fun h => hi (σ.injective h)
    simp [coordinateChange_apply, Function.update, hi, hn]

lemma partial_conjugate {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n)
    (ψ : E n → ℝ) (x : E n) (hψ : DifferentiableAt ℝ ψ (permute σ.symm x)) :
    coordinatePartial k (ψ ∘ permute σ.symm) x =
      coordinatePartial (σ k) ψ (permute σ.symm x) := by
  have hd := hψ.hasFDerivAt.comp x
    (permutationEquiv σ.symm).toContinuousLinearEquiv.hasFDerivAt
  change fderiv ℝ (ψ ∘ permute σ.symm) x (D04.standardBasis n k) = _
  rw [hd.fderiv]
  change (fderiv ℝ ψ (permute σ.symm x)) (permute σ.symm (D04.standardBasis n k)) = _
  rw [permute_basis]
  rfl

/-- Arbitrary changed coordinate, reduced to the last-coordinate calculation
by the already-proved permutation substitution theorem. -/
lemma coordinate_integral {n : ℕ} (j : Fin n) {U V : Set (E n)} (e : U ≃ₜ V)
    (ψ : E n → ℝ) (hU : IsOpen U) (hV : IsOpen V) (hψ : ContDiffOn ℝ 1 ψ U)
    (he : ∀ x : U, coordinateChange j ψ x = e x)
    (hne : ∀ x ∈ U, coordinatePartial j ψ x ≠ 0)
    (f : V → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    openIntegral f = openIntegral (fun x : U => f (e x) * |coordinatePartial j ψ x|) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ p =>
    let k := Fin.last p
    let σ : Equiv.Perm (Fin (p+1)) := Equiv.swap j k
    have hσ : σ k = j := Equiv.swap_apply_right _ _
    let U' := permute σ.symm ⁻¹' U
    let V' := permute σ.symm ⁻¹' V
    let aU : U' ≃ₜ U := permutationDomain σ.symm U
    let aV : V' ≃ₜ V := permutationDomain σ.symm V
    let e' : U' ≃ₜ V' := aU.trans (e.trans aV.symm)
    let ψ' := ψ ∘ permute σ.symm
    let f' := f ∘ aV
    have hU' : IsOpen U' := hU.preimage (permutationEquiv σ.symm).continuous
    have hV' : IsOpen V' := hV.preimage (permutationEquiv σ.symm).continuous
    have hψ' : ContDiffOn ℝ 1 ψ' U' :=
      hψ.comp (permutationEquiv σ.symm).contDiff.contDiffOn (fun _ hx => hx)
    have he' (x : U') : coordinateChange k ψ' x = e' x := by
      rw [show coordinateChange k ψ' x = permute σ (coordinateChange j ψ (permute σ.symm x)) from by
        simpa only [hσ] using conjugate_change σ k ψ x]
      change permute σ (coordinateChange j ψ (aU x)) = permute σ (e (aU x))
      rw [he (aU x)]
    have hpartial (x : E (p+1)) (hx : x ∈ U') :
        coordinatePartial k ψ' x = coordinatePartial j ψ (permute σ.symm x) := by
      have hdψ := (hψ.differentiableOn (by simp) _ hx).differentiableAt (hU.mem_nhds hx)
      simpa only [hσ] using partial_conjugate σ k ψ x hdψ
    have hne' (x : E (p+1)) (hx : x ∈ U') : coordinatePartial k ψ' x ≠ 0 := by
      rw [hpartial x hx]
      exact hne _ hx
    have hf' : Continuous f' := hf.comp aV.continuous
    have hfc' : HasCompactSupport f' :=
      (Localization.pullback_support aV f univ hf hfc (by simp)).2.1
    have hlast := last_integral e' ψ' hU' hV' hψ' he' hne' f' hf' hfc'
    have hfv := permutation_substitution σ.symm V' V aV hV' hV (fun _ => rfl) f hf hfc
    let g : U → ℝ := fun x => f (e x) * |coordinatePartial j ψ x|
    have hp := Localization.pullback_support e f univ hf hfc (by simp)
    have hg : Continuous g := hp.1.mul (continuous_partial j ψ hU hψ).abs
    have hgc : HasCompactSupport g := hp.2.1.mul_right
    have hgv := permutation_substitution σ.symm U' U aU hU' hU (fun _ => rfl) g hg hgc
    have heq : (fun x : U' => f' (e' x) * |coordinatePartial k ψ' x|) = g ∘ aU := by
      funext x
      have hmap : aV (e' x) = e (aU x) := by
        change aV (aV.symm (e (aU x))) = e (aU x)
        exact aV.apply_symm_apply _
      change f (aV (e' x)) * |coordinatePartial k ψ' x| = _
      rw [hmap, hpartial x x.property]
      rfl
    calc
      openIntegral f = openIntegral f' := hfv.2.2.2.2
      _ = openIntegral (fun x : U' => f' (e' x) * |coordinatePartial k ψ' x|) := hlast
      _ = openIntegral (g ∘ aU) := congrArg openIntegral heq
      _ = openIntegral g := hgv.2.2.2.2.symm


theorem regularity : Specs.D04.C07.OneCoordinate.regularityType := by
  intro n j ψ U
  constructor
  · intro h
    have hp : ContDiffOn ℝ 1 (fun x => coordinateChange j ψ x j) U :=
      (EuclideanSpace.proj j : E n →L[ℝ] ℝ).contDiff.comp_contDiffOn h
    simpa only [coordinateChange_apply, Function.update_self] using hp
  · intro h
    change ContDiffOn ℝ 1 (fun x => WithLp.toLp 2 (Function.update (fun i => x i) j (ψ x))) U
    apply PiLp.contDiff_toLp.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [Function.update_self] using h
    · have hp : ContDiffOn ℝ 1 (fun x : E n => x i) U :=
        (PiLp.proj 2 (fun _ : Fin n => ℝ) i : E n →L[ℝ] ℝ).contDiff.contDiffOn
      simpa only [Function.update_of_ne hi] using! hp

theorem partial_derivative : Specs.D04.C07.OneCoordinate.partial_derivativeType := by
  intro n j ψ x hψ
  have hl : HasDerivAt (fun t : ℝ => x + t • D04.standardBasis n j) (D04.standardBasis n j) 0 := by
    simpa only [one_smul, zero_add] using! (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (D04.standardBasis n j))
  have hdψ : HasFDerivAt ψ (fderiv ℝ ψ x) (x + (0 : ℝ) • D04.standardBasis n j) := by
    simpa using hψ.hasFDerivAt
  exact (hdψ.comp_hasDerivAt 0 hl).deriv.symm

theorem substitution : Specs.D04.C07.OneCoordinate.substitutionType := by
  intro n j U V e ψ S hU hV hT hS he hSe f hf hfc
  have hψ := (regularity j ψ U).mp hT
  have hi := integrability j e ψ hU hV hψ f hf hfc
  refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, ?_⟩
  exact coordinate_integral j e ψ hU hV hψ he
    (nonvanishing j e ψ S hU hV hψ hS he hSe) f hf hfc
end D04.OneCoordinate
