import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.MatrixGroupCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.LineStabilizerRepresentation
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.TensorProduct.Maps

namespace GaloisFormalization.PV.LineStabilizerRepresentation

open MatrixGroupCoordinates
open scoped MatrixGroupCoordinates.Specs TensorProduct

universe u

noncomputable section

variable {C : Type u} [Field C] {n : ℕ}

private abbrev Polynomial (C : Type u) [Field C] (n : ℕ) :=
  CoordinatePolynomial C n

private def entries (C : Type u) [Field C] (n : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial C n) :=
  Matrix.of fun i j => MvPolynomial.X (.inl (i, j))

private theorem eval_entries (g : GL (Fin n) C) :
    (evalAt (C := C) g).mapMatrix (entries C n) = g.val := by
  ext i j
  exact evalAt_entry g i j

private theorem inverseDeterminant_mul (x y : GL (Fin n) C) :
    inverseDeterminant (x * y) = inverseDeterminant x * inverseDeterminant y := by
  simp [MatrixGroupCoordinates.Specs.inverseDeterminant, map_mul, mul_comm]

variable (G : Subgroup (GL (Fin n) C))

private def restrictPolynomial : Polynomial C n →ₐ[C] (G → C) :=
  AlgHom.pi fun x : G => evalAt (C := C) x.val

private theorem regular_iff_mem_range (f : G → C) :
    IsRegular (S := (G : Set (GL (Fin n) C))) f ↔ f ∈ (restrictPolynomial G).range := by
  change (∃ p, ∀ x, restrictPolynomial G p x = f x) ↔
    ∃ p, restrictPolynomial G p = f
  simp only [funext_iff]

/-- Polynomials for the coordinates of a product of two matrices. -/
private def productPolynomial : Polynomial C n →ₐ[C]
    (Polynomial C n ⊗[C] Polynomial C n) :=
  MvPolynomial.aeval fun
    | .inl (i, j) => ∑ k : Fin n, entries C n i k ⊗ₜ[C] entries C n k j
    | .inr () => MvPolynomial.X (.inr ()) ⊗ₜ[C] MvPolynomial.X (.inr ())

/-- Evaluate the right tensor factor at a point and the left factor as a function. -/
private def evaluateSecond (g : G) : (Polynomial C n ⊗[C] Polynomial C n) →ₐ[C] (G → C) :=
  Algebra.TensorProduct.lift (restrictPolynomial G)
    ((Algebra.ofId C (G → C)).comp (evalAt g.val)) (fun _ _ => Commute.all _ _)

private theorem evaluateSecond_tmul (g : G) (a b : Polynomial C n) :
    evaluateSecond G g (a ⊗ₜ[C] b) = evalAt (C := C) g.val b • restrictPolynomial G a := by
  ext x
  rw [evaluateSecond, Algebra.TensorProduct.lift_tmul]
  change evalAt (C := C) x.val a * evalAt (C := C) g.val b =
    evalAt (C := C) g.val b * evalAt (C := C) x.val a
  exact mul_comm _ _

private theorem evaluateSecond_product (x g : G) (p : Polynomial C n) :
    evaluateSecond G g (productPolynomial p) x = restrictPolynomial G p (x * g) := by
  let e := (Pi.evalAlgHom C (fun _ : G => C) x).comp
    ((evaluateSecond G g).comp (productPolynomial (C := C) (n := n)))
  have he : e = evalAt (C := C) (x * g).val := by
    apply MvPolynomial.algHom_ext
    intro i
    change evaluateSecond G g (productPolynomial (MvPolynomial.X i)) x = _
    rcases i with ⟨i, j⟩ | i
    · rw [show productPolynomial (MvPolynomial.X (.inl (i, j))) =
          ∑ k : Fin n, entries C n i k ⊗ₜ[C] entries C n k j from MvPolynomial.aeval_X _ _,
        map_sum, Finset.sum_apply, evalAt_entry]
      change _ = ∑ k : Fin n, x.val i k * g.val k j
      apply Finset.sum_congr rfl
      intro k _
      rw [evaluateSecond_tmul]
      change evalAt (C := C) g.val (MvPolynomial.X (.inl (k, j))) *
        evalAt (C := C) x.val (MvPolynomial.X (.inl (i, k))) = _
      rw [evalAt_entry, evalAt_entry, mul_comm]
    · cases i
      rw [show productPolynomial (MvPolynomial.X (.inr ()) : Polynomial C n) =
          MvPolynomial.X (.inr ()) ⊗ₜ[C] MvPolynomial.X (.inr ())
            from MvPolynomial.aeval_X _ _,
        evaluateSecond_tmul]
      change evalAt (C := C) g.val (MvPolynomial.X (.inr ())) *
        evalAt (C := C) x.val (MvPolynomial.X (.inr ())) =
          evalAt (C := C) (x.val * g.val) (MvPolynomial.X (.inr ()))
      simp only [evalAt_inverseDeterminant, inverseDeterminant_mul, mul_comm]
  exact DFunLike.congr_fun he p

private theorem evaluateSecond_mem_range (t : Polynomial C n ⊗[C] Polynomial C n) (g : G) :
    evaluateSecond G g t ∈ (restrictPolynomial G).range := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      rw [evaluateSecond_tmul]
      exact (restrictPolynomial G).range.smul_mem (show restrictPolynomial G a ∈ _ from ⟨a, rfl⟩) _
  | add t s ht hs =>
      rw [map_add]
      exact Subalgebra.add_mem _ ht hs

private theorem evaluateSecond_finite (t : Polynomial C n ⊗[C] Polynomial C n) :
    ∃ V : Submodule C (G → C), V.FG ∧ ∀ g : G, evaluateSecond G g t ∈ V := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      refine ⟨C ∙ restrictPolynomial G a, Submodule.fg_span_singleton _, fun g => ?_⟩
      rw [evaluateSecond_tmul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  | add t s ht hs =>
      obtain ⟨V, hV, hVmem⟩ := ht
      obtain ⟨W, hW, hWmem⟩ := hs
      refine ⟨V ⊔ W, hV.sup hW, fun g => ?_⟩
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hVmem g)) (Submodule.mem_sup_right (hWmem g))

private theorem regular_evaluateSecond (t : Polynomial C n ⊗[C] Polynomial C n)
    (a : (G → C) →ₗ[C] C) :
    IsRegular (S := (G : Set (GL (Fin n) C))) (fun g => a (evaluateSecond G g t)) := by
  rw [regular_iff_mem_range]
  induction t using TensorProduct.inductionOn with
  | tmul p q =>
      let c := a (restrictPolynomial G p)
      have he : (fun g => a (evaluateSecond G g (p ⊗ₜ[C] q))) =
          c • restrictPolynomial G q := by
        funext g
        rw [evaluateSecond_tmul, map_smul]
        change evalAt (C := C) g.val q * c = c * evalAt (C := C) g.val q
        exact mul_comm _ _
      exact he ▸ (restrictPolynomial G).range.smul_mem
        (show restrictPolynomial G q ∈ _ from ⟨q, rfl⟩) c
  | add t s ht hs =>
      have he : (fun g => a (evaluateSecond G g (t + s))) =
          (fun g => a (evaluateSecond G g t)) + (fun g => a (evaluateSecond G g s)) := by
        funext g
        simp
      exact he ▸ Subalgebra.add_mem _ ht hs

private def inversePolynomial : Polynomial C n →ₐ[C] Polynomial C n :=
  MvPolynomial.aeval fun
    | .inl (i, j) => MvPolynomial.X (.inr ()) * (entries C n).adjugate i j
    | .inr () => (entries C n).det

private theorem eval_inversePolynomial (g : GL (Fin n) C) (p : Polynomial C n) :
    evalAt (C := C) g (inversePolynomial p) = evalAt (C := C) g⁻¹ p := by
  have h : (evalAt (C := C) g).comp inversePolynomial = evalAt (C := C) g⁻¹ := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with ⟨i, j⟩ | ⟨⟩
    · change evalAt (C := C) g (inversePolynomial (MvPolynomial.X (.inl (i, j)))) = _
      rw [show inversePolynomial (MvPolynomial.X (.inl (i, j))) =
          MvPolynomial.X (.inr ()) * (entries C n).adjugate i j from MvPolynomial.aeval_X _ _,
        map_mul, evalAt_inverseDeterminant, evalAt_entry]
      have ha : evalAt (C := C) g ((entries C n).adjugate i j) = g.val.adjugate i j := by
        change ((evalAt (C := C) g).mapMatrix (entries C n).adjugate) i j = _
        rw [AlgHom.map_adjugate, eval_entries]
      rw [ha]
      change inverseDeterminant g * g.val.adjugate i j = (g⁻¹).val i j
      rw [show (g⁻¹).val = g.val⁻¹ from Matrix.GeneralLinearGroup.coe_inv g]
      let hdet : IsUnit g.val.det := ⟨Matrix.GeneralLinearGroup.det g, rfl⟩
      rw [Matrix.nonsing_inv_apply _ hdet]
      have hu : hdet.unit = Matrix.GeneralLinearGroup.det g := Units.ext hdet.unit_spec
      rw [hu]
      rfl
    · change evalAt (C := C) g (inversePolynomial (MvPolynomial.X (.inr ()))) = _
      rw [show inversePolynomial (MvPolynomial.X (.inr ()) : Polynomial C n) =
          (entries C n).det from MvPolynomial.aeval_X _ _,
        AlgHom.map_det, eval_entries, evalAt_inverseDeterminant]
      simp [MatrixGroupCoordinates.Specs.inverseDeterminant]
  exact DFunLike.congr_fun h p

private theorem regular_inverse {f : G → C}
    (hf : IsRegular (S := (G : Set (GL (Fin n) C))) f) :
    IsRegular (S := (G : Set (GL (Fin n) C))) (fun g => f g⁻¹) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨inversePolynomial p, fun g => (eval_inversePolynomial _ p).trans (hp g⁻¹)⟩

private theorem regular_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : G → Matrix ι ι C) (hM : IsRegularMatrix (S := (G : Set (GL (Fin n) C))) M) :
    IsRegular (S := (G : Set (GL (Fin n) C))) (fun g => (M g).det) := by
  choose p hp using hM
  refine ⟨(Matrix.of p).det, fun g => ?_⟩
  rw [AlgHom.map_det]
  congr 1
  ext i j
  exact hp i j g

private def rightTranslate (g : G) : Module.End C (G → C) where
  toFun f x := f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rightTranslate_polynomial (p : Polynomial C n) (g : G) :
    rightTranslate G g (restrictPolynomial G p) = evaluateSecond G g (productPolynomial p) :=
  funext fun x => (evaluateSecond_product G x g p).symm

private theorem finite_equations (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ t : Finset (Polynomial C n),
      ∀ g : G, (∀ p ∈ t, restrictPolynomial G p g = 0) ↔ g ∈ H := by
  obtain ⟨s, hs⟩ := (isClosed_subtype_iff_zeroLocus _ _).mp hH
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (Ideal.span s)
  refine ⟨t, fun g => ?_⟩
  change (∀ p ∈ (↑t : Set (Polynomial C n)), evalAt (C := C) g.val p = 0) ↔ g ∈ (H : Set G)
  rw [hs]
  change (∀ p ∈ (↑t : Set (Polynomial C n)), evalAt (C := C) g.val p = 0) ↔
    ∀ p ∈ s, evalAt (C := C) g.val p = 0
  have he (a : Set (Polynomial C n)) : (∀ p ∈ a, evalAt (C := C) g.val p = 0) ↔
      Ideal.span a ≤ RingHom.ker (evalAt (C := C) g.val).toRingHom := by
    rw [Ideal.span_le]
    exact Iff.rfl
  change Ideal.span (↑t : Set (Polynomial C n)) = Ideal.span s at ht
  rw [he, he, ht]

private def translatedSpan (t : Finset (Polynomial C n)) : Submodule C (G → C) :=
  Submodule.span C (Set.range fun a : (↑t : Set (Polynomial C n)) × G =>
    rightTranslate G a.2 (restrictPolynomial G a.1.val))

private theorem polynomial_mem_translatedSpan (t : Finset (Polynomial C n))
    {p : Polynomial C n} (hp : p ∈ t) : restrictPolynomial G p ∈ translatedSpan G t := by
  apply Submodule.subset_span
  refine ⟨(⟨p, hp⟩, 1), ?_⟩
  funext x
  exact congrArg (restrictPolynomial G p) (mul_one x)

private theorem translatedSpan_finite (t : Finset (Polynomial C n)) :
    FiniteDimensional C (translatedSpan G t) := by
  choose U hU hmem using fun p : (↑t : Set (Polynomial C n)) =>
    evaluateSecond_finite G (productPolynomial p.val)
  let S := ⨆ p, U p
  have hS : FiniteDimensional C S :=
    (Submodule.fg_iff_finiteDimensional _).mp (Submodule.fg_iSup U hU)
  have hle : translatedSpan G t ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨p, g⟩, rfl⟩
    change rightTranslate G g (restrictPolynomial G p.val) ∈ S
    rw [rightTranslate_polynomial]
    exact (show U p ≤ S from le_iSup U p) (hmem p g)
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

private theorem translatedSpan_mem_range (t : Finset (Polynomial C n)) {f : G → C}
    (hf : f ∈ translatedSpan G t) : f ∈ (restrictPolynomial G).range := by
  have hle : translatedSpan G t ≤ (restrictPolynomial G).range.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨p, g⟩, rfl⟩
    change rightTranslate G g (restrictPolynomial G p.val) ∈ (restrictPolynomial G).range
    rw [rightTranslate_polynomial]
    exact evaluateSecond_mem_range G (productPolynomial p.val) g
  exact hle hf

private theorem rightTranslate_preserves (t : Finset (Polynomial C n)) (g : G) :
    ∀ f ∈ translatedSpan G t, rightTranslate G g f ∈ translatedSpan G t := by
  change translatedSpan G t ≤ Submodule.comap (rightTranslate G g) (translatedSpan G t)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨p, h⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨(p, g * h), ?_⟩
  funext x
  exact congrArg (restrictPolynomial G p.val) (mul_assoc x g h).symm

private def translationRepresentation (t : Finset (Polynomial C n)) :
    G →* Module.End C (translatedSpan G t) where
  toFun g := (rightTranslate G g).restrict (rightTranslate_preserves G t g)
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

private theorem translationRepresentation_regular (t : Finset (Polynomial C n))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι C (translatedSpan G t)) :
    IsRegularMatrix (S := (G : Set (GL (Fin n) C)))
      (fun g => LinearMap.toMatrix b b (translationRepresentation G t g)) := by
  intro i j
  obtain ⟨p, hp⟩ := translatedSpan_mem_range G t (b j).property
  change restrictPolynomial G p = (b j).val at hp
  obtain ⟨a, ha⟩ := (b.coord i).exists_extend
  have hc (g : G) : a (evaluateSecond G g (productPolynomial p)) =
      LinearMap.toMatrix b b (translationRepresentation G t g) i j := by
    rw [← rightTranslate_polynomial, hp, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
    exact DFunLike.congr_fun ha (translationRepresentation G t g (b j))
  obtain ⟨q, hq⟩ := regular_evaluateSecond G (productPolynomial p) a
  exact ⟨q, fun g => (hq g).trans (hc g)⟩

private def vanishingSubspace (H : Subgroup G) (V : Submodule C (G → C)) :
    Submodule C V where
  carrier := {f | ∀ x ∈ H, f.val x = 0}
  zero_mem' := by simp
  add_mem' {f h} hf hh x hx := by
    change f.val x + h.val x = 0
    rw [hf x hx, hh x hx, add_zero]
  smul_mem' c f hf x hx := by
    change c * f.val x = 0
    rw [hf x hx, mul_zero]

private theorem vanishingSubspace_stabilizer (H : Subgroup G) (t : Finset (Polynomial C n))
    (ht : ∀ g : G, (∀ p ∈ t, restrictPolynomial G p g = 0) ↔ g ∈ H) (g : G) :
    let W := vanishingSubspace G H (translatedSpan G t)
    (∀ f ∈ W, translationRepresentation G t g f ∈ W) ↔ g ∈ H := by
  constructor
  · intro h
    apply (ht g).mp
    intro p hp
    let f : translatedSpan G t := ⟨restrictPolynomial G p, polynomial_mem_translatedSpan G t hp⟩
    have hf : f ∈ vanishingSubspace G H (translatedSpan G t) :=
      fun x hx => (ht x).mpr hx p hp
    have hzero := h f hf
    change ∀ x ∈ H, restrictPolynomial G p (x * g) = 0 at hzero
    simpa only [one_mul] using hzero 1 H.one_mem
  · intro hg f hf x hx
    exact hf (x * g) (H.mul_mem hx hg)

section ExteriorPower

variable {V : Type*} [AddCommGroup V] [Module C V] {d : ℕ}

/-- An independent tuple has nonzero exterior product, as witnessed by a determinant
on coordinates of a linear retraction. -/
private theorem wedge_ne_zero {a : Fin d → V} (ha : LinearIndependent C a) :
    exteriorPower.ιMulti C d a ≠ 0 := by
  let F := Fintype.linearCombination C a
  have hF : Function.Injective F := linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  let b := Pi.basisFun C (Fin d)
  have hFa (i : Fin d) : F (b i) = a i := by
    simp [F, b, Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  have hLa : L ∘ a = b := by
    funext i
    change L (a i) = b i
    rw [← hFa]
    exact DFunLike.congr_fun hL (b i)
  let D := exteriorPower.alternatingMapLinearEquiv (b.det.compLinearMap L)
  have hD : D (exteriorPower.ιMulti C d a) = 1 := by
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      AlternatingMap.compLinearMap_apply]
    change b.det (L ∘ a) = 1
    rw [hLa, Module.Basis.det_self]
  intro hz
  rw [hz, map_zero] at hD
  exact zero_ne_one hD

private theorem wedge_cons (a : Fin d → V) (v : V) :
    (exteriorPower.ιMulti C (d + 1) (Fin.cons v a)).val =
      ExteriorAlgebra.ι C v * (exteriorPower.ιMulti C d a).val := by
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

private theorem wedge_annihilator {a : Fin d → V} (ha : LinearIndependent C a) (v : V) :
    ExteriorAlgebra.ι C v * (exteriorPower.ιMulti C d a).val = 0 ↔
      v ∈ Submodule.span C (Set.range a) := by
  constructor
  · intro hz
    by_contra hv
    apply wedge_ne_zero (linearIndependent_finCons.mpr ⟨ha, hv⟩)
    exact Subtype.ext ((wedge_cons a v).trans hz)
  · intro hv
    let F := (LinearMap.mulRight C (exteriorPower.ιMulti C d a).val).comp (ExteriorAlgebra.ι C)
    have hker : Submodule.span C (Set.range a) ≤ LinearMap.ker F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change ExteriorAlgebra.ι C (a i) * _ = 0
      rw [← wedge_cons]
      have hrep : exteriorPower.ιMulti C (d + 1) (Fin.cons (a i) a) = 0 :=
        AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ)
          (by simp) (Fin.succ_ne_zero _).symm
      rw [hrep]
      rfl
    exact hker hv

private theorem top_wedge_formula {W : Submodule C V} (b : Module.Basis (Fin d) C W)
    (v : Fin d → W) :
    exteriorPower.ιMulti C d (W.subtype ∘ v) =
      b.det v • exteriorPower.ιMulti C d (W.subtype ∘ b) := by
  let A := (exteriorPower.ιMulti C d (M := V)).compLinearMap W.subtype
  let w := A b
  let T := (LinearMap.id (R := C) (M := C)).smulRight w
  have he : A = T.compAlternatingMap b.det := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin d) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change A (b ∘ σ) = T (b.det (b ∘ σ))
    simp [AlternatingMap.map_perm, Module.Basis.det_self, T, w]
  exact DFunLike.congr_fun he v

private theorem wedge_line_stabilizer (W : Submodule C V) (b : Module.Basis (Fin d) C W)
    (F : Module.End C V) (hF : Function.Injective F) :
    let w := exteriorPower.ιMulti C d (W.subtype ∘ b)
    (Submodule.span C {w}).map (exteriorPower.map d F) = Submodule.span C {w} ↔
      ∀ v ∈ W, F v ∈ W := by
  let a : Fin d → V := W.subtype ∘ b
  let w := exteriorPower.ιMulti C d a
  have ha : LinearIndependent C a := b.linearIndependent.map' W.subtype W.ker_subtype
  have hspan : Submodule.span C (Set.range a) = W := by
    change Submodule.span C (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp W.subtype b, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have hnonzero : exteriorPower.map d F w ≠ 0 := by
    rw [exteriorPower.map_apply_ιMulti]
    exact wedge_ne_zero (ha.map' F (LinearMap.ker_eq_bot.mpr hF))
  change (Submodule.span C {w}).map (exteriorPower.map d F) = _ ↔ _
  rw [Submodule.map_span, Set.image_singleton]
  constructor
  · intro h v hv
    have hm : exteriorPower.map d F w ∈ Submodule.span C {w} :=
      h ▸ Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have hc0 : c ≠ 0 := by
      intro hz
      exact hnonzero (hc.symm.trans (by rw [hz, zero_smul]))
    have hz : ExteriorAlgebra.ι C v * w.val = 0 := (wedge_annihilator ha v).mpr (hspan ▸ hv)
    have hz' := congrArg (ExteriorAlgebra.map F) hz
    rw [map_mul, map_zero, ExteriorAlgebra.map_apply_ι, ← exteriorPower.coe_map, ← hc] at hz'
    change ExteriorAlgebra.ι C (F v) * (c • w.val) = 0 at hz'
    rw [mul_smul_comm, smul_eq_zero] at hz'
    rw [← hspan]
    exact (wedge_annihilator ha (F v)).mp (hz'.resolve_left hc0)
  · intro h
    let v (i : Fin d) : W := ⟨F (b i), h _ (b i).property⟩
    have he : exteriorPower.map d F w = b.det v • w := by
      rw [exteriorPower.map_apply_ιMulti]
      exact top_wedge_formula b v
    have hc : b.det v ≠ 0 := by
      intro hz
      apply hnonzero
      rw [he, hz, zero_smul]
    rw [he, Submodule.span_singleton_smul_eq hc.isUnit]

private def exteriorEnd (C : Type u) [Field C] (V : Type*) [AddCommGroup V] [Module C V]
    (d : ℕ) : Module.End C V →* Module.End C (⋀[C]^d V) where
  toFun := exteriorPower.map d
  map_one' := exteriorPower.map_id
  map_mul' _ _ := exteriorPower.map_comp _ _

/-- An exterior-power matrix coefficient is the corresponding minor in the
original representation matrix. -/
private theorem exterior_matrix_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (b : Module.Basis ι C V) (F : Module.End C V)
    (s t : Set.powersetCard ι d) :
    LinearMap.toMatrix (b.exteriorPower d) (b.exteriorPower d) (exteriorPower.map d F) s t =
      ((LinearMap.toMatrix b b F).submatrix
        (Set.powersetCard.ofFinEmbEquiv.symm s) (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  rw [LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, exteriorPower.basis_coord,
    exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose]
  apply congrArg Matrix.det
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end ExteriorPower

private theorem regular_representation_of_entries {m : ℕ} (ρ : G →* GL (Fin m) C)
    (hρ : IsRegularMatrix (S := (G : Set (GL (Fin n) C))) (fun g => (ρ g).val)) :
    IsRegularRepresentation ρ := by
  refine ⟨hρ, ?_⟩
  obtain ⟨p, hp⟩ := regular_inverse G (regular_det G (fun g => (ρ g).val) hρ)
  refine ⟨p, fun g => (hp g).trans ?_⟩
  change (↑(Matrix.GeneralLinearGroup.det (ρ g⁻¹)) : C) =
    ↑((Matrix.GeneralLinearGroup.det (ρ g))⁻¹)
  rw [map_inv, map_inv]

private theorem map_line_to_coordinates {V : Type*} [AddCommGroup V] [Module C V]
    {m : ℕ} (b : Module.Basis (Fin m) C V) (F : Module.End C V) (w : V) :
    (Submodule.span C {b.equivFun w}).map (Matrix.toLin' (LinearMap.toMatrix b b F)) =
      Submodule.span C {b.equivFun w} ↔
      (Submodule.span C {w}).map F = Submodule.span C {w} := by
  let L := b.equivFun.toLinearMap
  have hL : (Matrix.toLin' (LinearMap.toMatrix b b F)).comp L = L.comp F := by
    ext v : 1
    change Matrix.toLin' (LinearMap.toMatrix b b F) (b.equivFun v) = b.equivFun (F v)
    rw [Matrix.toLin'_apply', Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b F v
  have hspan : (Submodule.span C {w}).map L = Submodule.span C {b.equivFun w} := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  rw [← hspan, ← Submodule.map_comp, hL, Submodule.map_comp]
  exact (Submodule.map_injective_of_injective b.equivFun.injective).eq_iff

private theorem exterior_line_representation {V : Type*} [AddCommGroup V] [Module C V]
    {m d : ℕ} (b : Module.Basis (Fin m) C V) (W : Submodule C V)
    (bW : Module.Basis (Fin d) C W) (r : G →* Module.End C V)
    (hr : IsRegularMatrix (S := (G : Set (GL (Fin n) C))) (fun g => LinearMap.toMatrix b b (r g))) :
    ∃ (k : ℕ) (ρ : G →* GL (Fin k) C) (w : Fin k → C),
      IsRegularRepresentation ρ ∧ w ≠ 0 ∧
      ∀ g : G, (Submodule.span C {w}).map (Matrix.toLin' (ρ g).val) =
        Submodule.span C {w} ↔ ∀ v ∈ W, r g v ∈ W := by
  classical
  let e₀ := b.exteriorPower d
  let k := Fintype.equivFin (Set.powersetCard (Fin m) d)
  let e := e₀.reindex k
  let E := (exteriorEnd C V d).comp r
  let ρ := ((LinearMap.toMatrixAlgEquiv e).toAlgHom.toMonoidHom.comp E).toHomUnits
  let w := exteriorPower.ιMulti C d (W.subtype ∘ bW)
  have hw : w ≠ 0 := wedge_ne_zero (bW.linearIndependent.map' W.subtype W.ker_subtype)
  have hρ (g : G) : (ρ g).val = LinearMap.toMatrix e e (exteriorPower.map d (r g)) := rfl
  refine ⟨_, ρ, e.equivFun w, regular_representation_of_entries G ρ ?_, ?_, ?_⟩
  · intro i j
    have he (g : G) : (ρ g).val i j = ((LinearMap.toMatrix b b (r g)).submatrix
          (Set.powersetCard.ofFinEmbEquiv.symm (k.symm i))
          (Set.powersetCard.ofFinEmbEquiv.symm (k.symm j))).det := by
      rw [hρ g, LinearMap.toMatrix_apply]
      change (e₀.reindex k).repr _ i = _
      rw [Module.Basis.repr_reindex_apply]
      change e₀.repr (exteriorPower.map d (r g) ((e₀.reindex k) j)) (k.symm i) = _
      rw [Module.Basis.reindex_apply, ← LinearMap.toMatrix_apply]
      exact exterior_matrix_entry b (r g) (k.symm i) (k.symm j)
    obtain ⟨p, hp⟩ := regular_det G (fun g => (LinearMap.toMatrix b b (r g)).submatrix
      (Set.powersetCard.ofFinEmbEquiv.symm (k.symm i))
      (Set.powersetCard.ofFinEmbEquiv.symm (k.symm j))) (fun a b' =>
        hr _ _)
    exact ⟨p, fun g => (hp g).trans (he g).symm⟩
  · intro hz
    apply hw
    exact e.equivFun.injective (hz.trans (map_zero _).symm)
  · intro g
    have hinj : Function.Injective (r g) := by
      apply Function.LeftInverse.injective (g := r g⁻¹)
      intro v
      change (r g⁻¹ * r g) v = v
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hρ, map_line_to_coordinates]
    exact wedge_line_stabilizer W bW (r g) hinj

/-- A closed subgroup of an algebraic matrix group is the stabilizer of a line
in a finite-dimensional regular representation. -/
theorem exists_lineStabilizerRepresentation :
    Specs.ExistsLineStabilizerRepresentation.{u} := by
  classical
  intro C _ _ _ n G _ H hH
  obtain ⟨t, ht⟩ := finite_equations G H hH
  let V := translatedSpan G t
  let : FiniteDimensional C V := translatedSpan_finite G t
  let W : Submodule C V := vanishingSubspace G H V
  let : FiniteDimensional C W := FiniteDimensional.finiteDimensional_submodule W
  let : Module.Free C W := Module.Free.of_divisionRing C W
  let b := Module.finBasis C V
  let bW := Module.finBasis C W
  obtain ⟨m, ρ, w, hρ, hw, h⟩ := exterior_line_representation G b W bW
    (translationRepresentation G t) (translationRepresentation_regular G t b)
  exact ⟨m, ρ, w, hρ, hw, fun g => (h g).trans (vanishingSubspace_stabilizer G H t ht g)⟩

end

end GaloisFormalization.PV.LineStabilizerRepresentation
