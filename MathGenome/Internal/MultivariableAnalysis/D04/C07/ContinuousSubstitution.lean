import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.ContinuousSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C07.AffineComposition
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Function Filter Topology
namespace D04.ContinuousSubstitution
open JordanRegions
open Specs.D04.C07.AffineComposition.Model
open private inverse_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

/-- The actual inverse on V, extended arbitrarily outside V. -/
def inverseOn {n : ℕ} {U V : Set (E n)} (φ : E n → E n)
    (hbij : BijOn φ U V) (y : E n) : E n :=
  by
  classical
  exact if hy : y ∈ V then (hbij.surjOn hy).choose else 0

lemma inverseOn_mem {n : ℕ} {U V : Set (E n)} (φ : E n → E n)
    (hbij : BijOn φ U V) {y : E n} (hy : y ∈ V) : inverseOn φ hbij y ∈ U := by
  simp only [inverseOn, dite_eq_left hy]
  exact (hbij.surjOn hy).choose_spec.1

lemma inverseOn_right {n : ℕ} {U V : Set (E n)} (φ : E n → E n)
    (hbij : BijOn φ U V) {y : E n} (hy : y ∈ V) : φ (inverseOn φ hbij y) = y := by
  simp only [inverseOn, dite_eq_left hy]
  exact (hbij.surjOn hy).choose_spec.2

lemma inverseOn_left {n : ℕ} {U V : Set (E n)} (φ : E n → E n)
    (hbij : BijOn φ U V) {x : E n} (hx : x ∈ U) : inverseOn φ hbij (φ x) = x :=
  hbij.injOn (inverseOn_mem φ hbij (hbij.mapsTo hx)) hx
    (inverseOn_right φ hbij (hbij.mapsTo hx))

lemma inverseOn_contDiff {n : ℕ} {U V : Set (E n)} (φ : E n → E n)
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ U)
    (hbij : BijOn φ U V) (hdet : ∀ x ∈ U, (fderiv ℝ φ x).det ≠ 0) :
    ContDiffOn ℝ 1 (inverseOn φ hbij) V := by
  intro y hy
  let x := inverseOn φ hbij y
  have hx : x ∈ U := inverseOn_mem φ hbij hy
  let A := (fderiv ℝ φ x).toContinuousLinearEquivOfDetNeZero (hdet x hx)
  obtain ⟨X, Y, g, hgeom, hg⟩ := inverse_neighborhood U φ x A (by norm_num) hU hφ hx rfl
  rcases hgeom with ⟨hX, hY, hxX, hφxY, hXU, hXY, hgX, hleft, hright, hrest⟩
  have hyY : y ∈ Y := inverseOn_right φ hbij hy ▸ hφxY
  have heq : inverseOn φ hbij =ᶠ[𝓝 y] g := by
    filter_upwards [hV.mem_nhds hy, hY.mem_nhds hyY] with z hzV hzY
    exact hbij.injOn (inverseOn_mem φ hbij hzV) (hXU (hgX hzY))
      ((inverseOn_right φ hbij hzV).trans (hright hzY).symm)
  exact ((hg.contDiffAt (hY.mem_nhds hyY)).congr_of_eventuallyEq heq).contDiffWithinAt

theorem global_inverse : Specs.D04.C07.ContinuousSubstitution.global_inverseType := by
  intro n U V φ hU hV hφ hbij hdet
  let S := inverseOn φ hbij
  have hS := inverseOn_contDiff φ hU hV hφ hbij hdet
  let e : U ≃ₜ V :=
    { toFun := fun x => ⟨φ x, hbij.mapsTo x.property⟩
      invFun := fun y => ⟨S y, inverseOn_mem φ hbij y.property⟩
      left_inv := fun x => Subtype.ext (inverseOn_left φ hbij x.property)
      right_inv := fun y => Subtype.ext (inverseOn_right φ hbij y.property)
      continuous_toFun := hφ.continuousOn.domRestrict.codRestrict _
      continuous_invFun := hS.continuousOn.domRestrict.codRestrict _ }
  exact ⟨e, S, fun _ => rfl, fun _ => rfl, hS⟩



/-- Replace the first k output coordinates, retaining all the others. -/
def partialMap {n : ℕ} (F : E n → E n) (k : ℕ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => if i.val < k then F x i else x i)

@[simp] lemma partialMap_apply {n : ℕ} (F : E n → E n) (k : ℕ)
    (x : E n) (i : Fin n) : partialMap F k x i = if i.val < k then F x i else x i := rfl

@[simp] lemma partialMap_zero {n : ℕ} (F : E n → E n) : partialMap F 0 = id := by
  funext x; ext i; simp

@[simp] lemma partialMap_top {n : ℕ} (F : E n → E n) : partialMap F n = F := by
  funext x; ext i; simp [i.isLt]

lemma partialMap_contDiff {n : ℕ} {U : Set (E n)} (F : E n → E n)
    (hF : ContDiffOn ℝ 1 F U) (k : ℕ) : ContDiffOn ℝ 1 (partialMap F k) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  by_cases hi : i.val < k
  · simpa only [partialMap_apply, ite_eq_left hi] using (contDiffOn_piLp 2).mp hF i
  · simpa only [partialMap_apply, ite_eq_right hi, id_eq] using
      (contDiffOn_piLp 2).mp (contDiffOn_id (𝕜 := ℝ) (E := E n)) i

lemma partialMap_derivative {n : ℕ} (F : E n → E n) (a : E n)
    (hF : HasFDerivAt F (ContinuousLinearMap.id ℝ (E n)) a) (k : ℕ) :
    HasFDerivAt (partialMap F k) (ContinuousLinearMap.id ℝ (E n)) a := by
  apply hasFDerivWithinAt_univ.mp
  apply (hasFDerivWithinAt_piLp 2).mpr
  intro i
  by_cases hi : i.val < k
  · simpa only [partialMap_apply, ite_eq_left hi, Function.comp_def, ContinuousLinearMap.comp_id] using
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F a) i).comp a hF).hasFDerivWithinAt
  · simpa only [partialMap_apply, ite_eq_right hi, ContinuousLinearMap.comp_id] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 a i).hasFDerivWithinAt

/-- A local C¹ chart from an actual invertible derivative. -/
lemma local_chart {n : ℕ} {U : Set (E n)} (F : E n → E n) (a : E n)
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (ha : a ∈ U)
    (A : E n ≃L[ℝ] E n) (hd : HasFDerivAt F A.toContinuousLinearMap a) :
    ∃ e : OpenPartialHomeomorph (E n) (E n),
      (⇑e = F) ∧ a ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ 1 (e : E n → E n) e.source ∧
      ContDiffOn ℝ 1 (e.symm : E n → E n) e.target := by
  obtain ⟨X, Y, g, hgeom, hg⟩ := inverse_neighborhood U F a A (by norm_num) hU hF ha hd.fderiv.symm
  rcases hgeom with ⟨hX, hY, haX, _, hXU, hXY, hgX, hleft, hright, _⟩
  let e : OpenPartialHomeomorph (E n) (E n) :=
    { toFun := F
      invFun := g
      source := X
      target := Y
      map_source' := hXY.mapsTo
      map_target' := hgX
      left_inv' := hleft
      right_inv' := hright
      open_source := hX
      open_target := hY
      continuousOn_toFun := hF.continuousOn.mono hXU
      continuousOn_invFun := hg.continuousOn }
  exact ⟨e, rfl, haX, hXU, hF.mono hXU, hg⟩

/-- Equality on an open domain identifies the actual derivatives and therefore
identifies substitution statements. -/
lemma substitution_congr {n : ℕ} {U V : Set (E n)} (e : U ≃ₜ V)
    {F G : E n → E n} (hU : IsOpen U) (h : EqOn F G U)
    (hf : Substitution e F) : Substitution e G := by
  intro f hc hk
  have hd (x : U) : fderiv ℝ F x = fderiv ℝ G x :=
    (h.eventuallyEq_of_mem (hU.mem_nhds x.property)).fderiv_eq
  simpa only [hd] using hf f hc hk



/-- On a neighborhood of a point where DF is the identity, substitution follows
by successively replacing coordinates. No image-volume estimate is used. -/
lemma normalized_local {n : ℕ} {U : Set (E n)} (F : E n → E n) (a : E n)
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (ha : a ∈ U)
    (hd : HasFDerivAt F (ContinuousLinearMap.id ℝ (E n)) a) :
    ∃ (O W : Set (E n)) (e : O ≃ₜ W),
      IsOpen O ∧ IsOpen W ∧ a ∈ O ∧ O ⊆ U ∧
      (∀ x : O, F x = e x) ∧ Substitution e F := by
  classical
  have hcharts (k : Fin (n + 1)) := local_chart (partialMap F k) a hU
    (partialMap_contDiff F hF k) ha (ContinuousLinearEquiv.refl ℝ (E n))
    (partialMap_derivative F a hd k)
  choose c hc hca hcU hcF hcG using hcharts
  let O : Set (E n) := ⋂ k, (c k).source
  have hO : IsOpen O := isOpen_iInter_of_finite fun k => (c k).open_source
  have haO : a ∈ O := mem_iInter.mpr hca
  have hOc (k : Fin (n + 1)) : O ⊆ (c k).source := iInter_subset _ k
  have hOU : O ⊆ U := (hOc ⟨0, by omega⟩).trans (hcU _)
  let r (k : Fin (n + 1)) := (c k).restrOpen O hO
  have hsrc (k : Fin (n + 1)) : (r k).source = O :=
    inter_eq_right.mpr (hOc k)
  let W (k : Fin (n + 1)) := (r k).target
  let e (k : Fin (n + 1)) : O ≃ₜ W k :=
    (Homeomorph.setCongr (hsrc k).symm).trans (r k).toHomeomorphSourceTarget
  let G (k : Fin (n + 1)) : E n → E n := (r k).symm
  have he (k : Fin (n + 1)) (x : O) : partialMap F k x = e k x := by
    change partialMap F k x = c k x
    rw [hc k]
  have heG (k : Fin (n + 1)) (y : W k) : G k y = (e k).symm y := rfl
  have hG (k : Fin (n + 1)) : ContDiffOn ℝ 1 (G k) (W k) :=
    (hcG k).mono (fun _ hy => hy.1)
  have hGO (k : Fin (n + 1)) : MapsTo (G k) (W k) O := by
    intro y hy
    rw [heG k ⟨y, hy⟩]
    exact ((e k).symm ⟨y, hy⟩).property
  have hH (k : Fin (n + 1)) : ContDiffOn ℝ 1 (partialMap F k) O :=
    (partialMap_contDiff F hF k).mono hOU
  have hstep (k : ℕ) (hk : k < n) (hs : Substitution (e ⟨k, by omega⟩) (partialMap F k)) :
      Substitution (e ⟨k + 1, by omega⟩) (partialMap F (k + 1)) := by
    let p : Fin (n + 1) := ⟨k, by omega⟩
    let q : Fin (n + 1) := ⟨k + 1, by omega⟩
    let j : Fin n := ⟨k, hk⟩
    let t := (e p).symm.trans (e q)
    let ψ : E n → ℝ := fun y => F (G p y) j
    let T := OneCoordinate.coordinateChange j ψ
    let R : E n → E n := partialMap F k ∘ G q
    have hψ : ContDiffOn ℝ 1 ψ (W p) :=
      ((contDiffOn_piLp 2).mp hF j).comp (hG p) (fun y hy => hOU (hGO p hy))
    have hT : ContDiffOn ℝ 1 T (W p) := (OneCoordinate.regularity j ψ (W p)).mpr hψ
    have hR : ContDiffOn ℝ 1 R (W q) := (hH p).comp (hG q) (hGO q)
    have ht (y : W p) : T y = t y := by
      let x : O := (e p).symm y
      have hy : partialMap F k x = y := (he p x).trans (congrArg Subtype.val ((e p).apply_symm_apply y))
      have hx : G p y = x := rfl
      change OneCoordinate.coordinateChange j ψ y = e q x
      rw [← he q x]
      ext i
      by_cases hij : i = j
      · subst i
        simp [ψ, hx, j, q, partialMap_apply]
      · have hik : i.val ≠ k := fun h => hij (Fin.ext h)
        have hyi := congrArg (fun z : E n => z i) hy
        simp only [partialMap_apply] at hyi
        simp only [OneCoordinate.coordinateChange_apply, Function.update_of_ne hij]
        rw [← hyi]
        simp only [partialMap_apply, q]
        have hiff : i.val < k + 1 ↔ i.val < k := by omega
        simp only [hiff]
    have htr (y : W q) : R y = t.symm y := by
      change partialMap F k (G q y) = (e p) ((e q).symm y)
      exact he p ((e q).symm y)
    have hsubT : Substitution t T := by
      intro f hf hfc
      have h := OneCoordinate.substitution j (W p) (W q) t ψ R
        (r p).open_target (r q).open_target hT hR ht htr f hf hfc
      have hdet (x : W p) : (fderiv ℝ T x).det = OneCoordinate.coordinatePartial j ψ x :=
        OneCoordinate.determinant j ψ x
          (hψ.differentiableOn (by norm_num) |>.differentiableAt ((r p).open_target.mem_nhds x.property))
      simpa only [hdet] using h.2.2.2.2
    have hcomp := (AffineComposition.composition (e p) t (partialMap F k) T hO
      (r p).open_target (r q).open_target (hH p) hT (he p) ht hs hsubT).2
    have het : (e p).trans t = e q := by ext x; simp [t]
    have hscomp : Substitution (e q) (T ∘ partialMap F k) := by
      intro f hf hfc
      simpa only [het] using (hcomp f hf hfc).2.2.2.2.2.2.2.2
    apply substitution_congr (e q) hO ?_ hscomp
    intro x hx
    have hh := ht (e p ⟨x, hx⟩)
    rw [← he p ⟨x, hx⟩] at hh
    have hh' : T (partialMap F k x) = e q ⟨x, hx⟩ := by
      simpa only [t, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] using hh
    exact hh'.trans (he q ⟨x, hx⟩).symm
  have hbase : Substitution (e ⟨0, by omega⟩) (partialMap F 0) := by
    let A : Matrix (Fin n) (Fin n) ℝ := 1
    have hA (x : E n) : matrixLinearEquiv n n A x + 0 = x := by
      ext i
      simp [A, matrix_apply, Matrix.one_apply, ite_mul]
    have h := AffineComposition.affine_substitution A 0 (by simp [A])
      (e ⟨0, by omega⟩) hO (r ⟨0, by omega⟩).open_target
      (fun x => (hA x).trans (by simpa using he ⟨0, by omega⟩ x))
    apply substitution_congr (e ⟨0, by omega⟩) hO
      (F := fun y => matrixLinearEquiv n n A y + 0) (G := partialMap F 0) ?_ ?_
    · intro x _; simpa only [partialMap_zero, id_eq] using hA x
    · intro f hf hfc
      change openIntegral f = openIntegral (fun x : O =>
        f (e ⟨0, by omega⟩ x) * |(fderiv ℝ (fun y => matrixLinearEquiv n n A y + 0) x).det|)
      have hfun : (fun y => matrixLinearEquiv n n A y + 0) = id := funext hA
      rw [hfun]
      have hid : (ContinuousLinearMap.id ℝ (E n)).det = 1 := LinearMap.det_id
      simpa [A, hid] using (h f hf hfc).2.2.2.2
  have hall : ∀ (k : ℕ) (hk : k ≤ n), Substitution (e ⟨k, by omega⟩) (partialMap F k) := by
    intro k
    induction k with
    | zero => intro _; exact hbase
    | succ k ih => intro hk; exact hstep k (by omega) (ih (by omega))
  refine ⟨O, W ⟨n, by omega⟩, e ⟨n, by omega⟩, hO,
    (r ⟨n, by omega⟩).open_target, haO, hOU, ?_, ?_⟩
  · simpa only [partialMap_top] using he ⟨n, by omega⟩
  · simpa only [partialMap_top] using hall n le_rfl



lemma linear_substitution {n : ℕ} {W Z : Set (E n)} (A : E n ≃L[ℝ] E n)
    (e : W ≃ₜ Z) (hW : IsOpen W) (hZ : IsOpen Z)
    (he : ∀ x : W, A x = e x) : Substitution e A := by
  let M := matrixOfLinearMap A.toLinearMap
  have hM : matrixLinearEquiv n n M = A.toLinearMap := matrix_linear_roundtrip _
  have hMd : M.det = A.toLinearMap.det := by
    calc
      M.det = (matrixLinearEquiv n n M).det := (LinearMap.det_toLin (standardBasis n) M).symm
      _ = A.toLinearMap.det := congrArg LinearMap.det hM
  have hM0 : M.det ≠ 0 := by
    rw [hMd]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  intro f hf hfc
  have h := AffineComposition.affine_substitution M 0 hM0 e hW hZ
    (fun x => by change matrixLinearEquiv n n M x + 0 = e x; rw [hM, add_zero]; exact he x) f hf hfc
  have hd (x : E n) : (fderiv ℝ (fun y => A y) x).det = M.det := by
    rw [A.hasFDerivAt.fderiv]
    exact hMd.symm
  change openIntegral f = openIntegral (fun x : W => f (e x) * |(fderiv ℝ (fun y => A y) x).det|)
  simp_rw [hd]
  exact h.2.2.2.2

/-- Local substitution for an arbitrary C¹ map at any nonsingular point. -/
lemma local_substitution {n : ℕ} {U : Set (E n)} (φ : E n → E n) (a : E n)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (ha : a ∈ U)
    (hdet : (fderiv ℝ φ a).det ≠ 0) :
    ∃ (O Z : Set (E n)) (e : O ≃ₜ Z),
      IsOpen O ∧ IsOpen Z ∧ a ∈ O ∧ O ⊆ U ∧
      (∀ x : O, φ x = e x) ∧ Substitution e φ := by
  let A := (fderiv ℝ φ a).toContinuousLinearEquivOfDetNeZero hdet
  let F : E n → E n := fun x => A.symm (φ x)
  have hF : ContDiffOn ℝ 1 F U := A.symm.contDiff.comp_contDiffOn hφ
  have hφd : HasFDerivAt φ A.toContinuousLinearMap a :=
    hφ.differentiableOn (by norm_num) |>.differentiableAt (hU.mem_nhds ha) |>.hasFDerivAt
  have hd : HasFDerivAt F (ContinuousLinearMap.id ℝ (E n)) a := by
    have h := A.symm.hasFDerivAt.comp a hφd
    have hid : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (E n) := by
      apply ContinuousLinearMap.ext
      intro v
      exact A.symm_apply_apply v
    change HasFDerivAt F (A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap) a at h
    rwa [hid] at h
  obtain ⟨O, W, e, hO, hW, haO, hOU, he, hs⟩ := normalized_local F a hU hF ha hd
  let Z : Set (E n) := A '' W
  let t : W ≃ₜ Z := A.toHomeomorph.image W
  have hZ : IsOpen Z := A.toHomeomorph.isOpenMap _ hW
  have ht (y : W) : A y = t y := rfl
  have hsubt : Substitution t A := linear_substitution A t hW hZ ht
  have hcomp := (AffineComposition.composition e t F A hO hW hZ
    (hF.mono hOU) A.contDiff.contDiffOn he ht hs hsubt).2
  have hAF : (fun y => A y) ∘ F = φ := by
    funext x; exact A.apply_symm_apply (φ x)
  refine ⟨O, Z, e.trans t, hO, hZ, haO, hOU, ?_, ?_⟩
  · intro x
    change φ x = A (e x)
    rw [← he x]
    exact (A.apply_symm_apply (φ x)).symm
  · intro f hf hfc
    simpa only [hAF] using (hcomp f hf hfc).2.2.2.2.2.2.2.2



/-- A local chart for a globally injective map has exactly the source preimage
of its target. This identifies the source domains required by localization. -/
lemma chart_source_preimage {n : ℕ} {U V O W : Set (E n)}
    (φ : E n → E n) (hbij : BijOn φ U V) (l : O ≃ₜ W)
    (hOU : O ⊆ U) (hl : ∀ x : O, φ x = l x) :
    U ∩ φ ⁻¹' W = O := by
  ext x
  constructor
  · rintro ⟨hxU, hxW⟩
    let z := l.symm ⟨φ x, hxW⟩
    have hz : φ z = φ x := (hl z).trans (congrArg Subtype.val (l.apply_symm_apply ⟨φ x, hxW⟩))
    exact hbij.injOn (hOU z.property) hxU hz ▸ z.property
  · intro hx
    refine ⟨hOU hx, ?_⟩
    change φ x ∈ W
    rw [hl ⟨x, hx⟩]
    exact (l ⟨x, hx⟩).property

/-- The local identity expressed on the source preimage used by localization. -/
lemma local_preimage_identity {n : ℕ} {U V O W : Set (E n)}
    (φ : E n → E n) (hbij : BijOn φ U V) (l : O ≃ₜ W)
    (hOU : O ⊆ U) (hl : ∀ x : O, φ x = l x) (hs : Substitution l φ)
    (f : W → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    openIntegral f = openIntegral (fun x : (U ∩ φ ⁻¹' W : Set (E n)) =>
      f ⟨φ x, x.property.2⟩ * |(fderiv ℝ φ x).det|) := by
  have hPO := chart_source_preimage φ hbij l hOU hl
  have hsub := hs f hf hfc
  apply hsub.trans
  change openIntegral _ = openIntegral _
  rw [AffineComposition.openIntegral_eq_whole, AffineComposition.openIntegral_eq_whole]
  apply congrArg AffineComposition.wholeIntegral
    (show zeroExtension (fun x : O => f (l x) * |(fderiv ℝ φ x).det|) =
      zeroExtension (fun x : (U ∩ φ ⁻¹' W : Set (E n)) =>
        f ⟨φ x, x.property.2⟩ * |(fderiv ℝ φ x).det|) from ?_)
  ext x
  by_cases hxO : x ∈ O
  · have hxP : x ∈ U ∩ φ ⁻¹' W := hPO.symm ▸ hxO
    simp only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
      dite_eq_left hxO, dite_eq_left hxP]
    congr 2
    exact Subtype.ext (hl ⟨x, hxO⟩).symm
  · have hxP : x ∉ U ∩ φ ⁻¹' W := by rwa [hPO]
    rw [zeroExtension_of_not_mem _ hxO, zeroExtension_of_not_mem _ hxP]

/-- Global scalar substitution obtained from the finite continuous localization
principle and the local coordinate factorization. -/
theorem scalar_substitution : Specs.D04.C07.ContinuousSubstitution.scalar_substitutionType := by
  intro n U V e φ _hn hU hV hφ he hdet f hf hfc
  classical
  have hbij : BijOn φ U V := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; rw [he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).property
    · intro x hx y hy hxy
      have h : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext ((he ⟨x, hx⟩).symm.trans (hxy.trans (he ⟨y, hy⟩)))
      exact congrArg Subtype.val (e.injective h)
    · intro y hy
      exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property,
        (he (e.symm ⟨y, hy⟩)).trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
  have hlocal (a : U) := local_substitution φ a hU hφ a.property (hdet a a.property)
  choose O W l hO hW haO hOU hl hs using hlocal
  have hWV (a : U) : W a ⊆ V := by
    intro y hy
    let x := (l a).symm ⟨y, hy⟩
    have hx : φ x = y := (hl a x).trans (congrArg Subtype.val ((l a).apply_symm_apply ⟨y, hy⟩))
    exact hx ▸ hbij.mapsTo (hOU a x.property)
  have hcover : V ⊆ ⋃ a : U, W a := by
    intro y hy
    let a := e.symm ⟨y, hy⟩
    refine mem_iUnion.mpr ⟨a, ?_⟩
    have hφa : φ a = y := (he a).trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))
    have hla : φ a ∈ W a := by
      rw [hl a ⟨a, haO a⟩]
      exact (l a ⟨a, haO a⟩).property
    exact hφa ▸ hla
  have h := Localization.c1_localization_on_cover e φ W hU hV hφ he hW hWV hcover
    (fun a g hg hgc => local_preimage_identity φ hbij (l a) (hOU a) (hl a) (hs a) g hg hgc)
    f hf hfc
  have hp := Localization.pullback_support e f univ hf hfc (by simp)
  have hg : Continuous (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) :=
    hp.1.mul (AffineComposition.continuous_jacobian φ hU hφ)
  have hgc : HasCompactSupport (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) := hp.2.1.mul_right
  exact ⟨(Localization.compact_support_integrable f hV hf hfc).1,
    Localization.zeroExtension_compact hfc,
    (Localization.compact_support_integrable _ hU hg hgc).1,
    Localization.zeroExtension_compact hgc, h.1, h.2.1, h.2.2⟩



/-- The zero extension construction also preserves continuity and compact
support for the finite vector targets used in the source. -/
lemma vector_compact_extension {n k : ℕ} {V : Set (E n)} (f : V → E k)
    (hV : IsOpen V) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (zeroExtension f) ∧ HasCompactSupport (zeroExtension f) := by
  have hext : zeroExtension f = (Subtype.val : V → E n).extend f 0 := by
    funext x
    by_cases hx : x ∈ V
    · exact (zeroExtension_apply f ⟨x, hx⟩).trans
        (Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩).symm
    · rw [zeroExtension_of_not_mem f hx,
        extend_apply' (f := (Subtype.val : V → E n)) f (0 : E n → E k) x]
      · rfl
      · rintro ⟨y, rfl⟩; exact hx y.property
  rw [hext]
  exact ⟨HasCompactSupport.continuous_extend_zero hV hf hfc,
    hfc.extend_zero continuous_subtype_val⟩

/-- Continuous compact-supported change of variables, with the inverse and
all coordinatewise finite-dimensional conclusions under the original C¹ hypotheses. -/
theorem continuous_substitution : Specs.D04.C07.ContinuousSubstitution.continuous_substitutionType := by
  intro n U V φ hn hU hV hφ hbij hdet
  obtain ⟨e, S, he, hS, hcS⟩ := global_inverse φ hU hV hφ hbij hdet
  refine ⟨e, S, he, hS, hcS, scalar_substitution e φ hn hU hV hφ he hdet, ?_⟩
  intro k f hf hfc
  let J : U → ℝ := fun x => |(fderiv ℝ φ x).det|
  let g : U → E k := fun x => J x • f (e x)
  have hJ : Continuous J := AffineComposition.continuous_jacobian φ hU hφ
  have hg : Continuous g := hJ.smul (hf.comp e.continuous)
  have hp : HasCompactSupport (f ∘ e) := hfc.comp_homeomorph e
  have hgc : HasCompactSupport g := hp.mono (support_smul_subset_right J (f ∘ e))
  have hextf := vector_compact_extension f hV hf hfc
  have hextg := vector_compact_extension g hU hg hgc
  refine ⟨hextf.1, hextf.2, hextg.1, hextg.2, ?_⟩
  intro i
  have hfi : Continuous (fun y => f y i) := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) i).continuous.comp hf
  have hfci : HasCompactSupport (fun y => f y i) := hfc.comp_left (g := fun z : E k => z i) rfl
  have h := scalar_substitution e φ hn hU hV hφ he hdet (fun y => f y i) hfi hfci
  have hgi : (fun x : U => g x i) = (fun x : U => f (e x) i * |(fderiv ℝ φ x).det|) := by
    funext x
    change J x * f (e x) i = f (e x) i * J x
    exact mul_comm _ _
  change OpenIntegrable (fun y => f y i) ∧ OpenIntegrable (fun x => g x i) ∧
    openIntegral (fun y => f y i) = openIntegral (fun x => g x i)
  rw [hgi]
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end D04.ContinuousSubstitution
