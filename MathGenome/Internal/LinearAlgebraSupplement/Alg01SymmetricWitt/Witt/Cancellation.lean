import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.LineCancellation

namespace Alg01SymmetricWitt.Witt.Cancellation

open QuadraticMap

universe u v w x y

section

variable {k : Type u} [Field k]
  {U : Type v} [AddCommGroup U] [Module k U]
  {V : Type w} [AddCommGroup V] [Module k V]
  {W : Type x} [AddCommGroup W] [Module k W]

private def prodAssoc (qU : QuadraticForm k U) (qV : QuadraticForm k V)
    (qW : QuadraticForm k W) :
    ((qU.prod qV).prod qW).IsometryEquiv (qU.prod (qV.prod qW)) where
  toLinearEquiv := LinearEquiv.prodAssoc k U V W
  map_app' z := by
    change qU z.1.1 + (qV z.1.2 + qW z.2) = (qU z.1.1 + qV z.1.2) + qW z.2
    exact (add_assoc _ _ _).symm

private def prodDiagonalZero (q : QuadraticForm k U) (a : Fin 0 → k) :
    (q.prod (weightedSumSquares k a)).IsometryEquiv q where
  toLinearEquiv := LinearEquiv.prodUnique
  map_app' z := by
    change q z.1 = q z.1 + weightedSumSquares k a z.2
    simp

private def splitDiagonal {n : ℕ} (a : Fin (n + 1) → k) :
    (weightedSumSquares k a).IsometryEquiv
      ((weightedSumSquares k (a ∘ Fin.succ)).prod
        (a 0 • (sq : QuadraticForm k k))) where
  toLinearEquiv :=
    (LinearEquiv.piCongrLeft' k (fun _ => k) (finSuccEquiv n)).trans
      ((LinearEquiv.piOptionEquivProd k).trans (LinearEquiv.prodComm k k (Fin n → k)))
  map_app' z := by
    change weightedSumSquares k (a ∘ Fin.succ)
        (fun i => z ((finSuccEquiv n).symm (some i))) +
      a 0 • (z ((finSuccEquiv n).symm none) * z ((finSuccEquiv n).symm none)) =
        weightedSumSquares k a z
    simp only [weightedSumSquares_apply, finSuccEquiv_symm_none, finSuccEquiv_symm_some,
      Function.comp_apply]
    rw [Fin.sum_univ_succ, add_comm]

variable [Invertible (2 : k)]

private theorem diagonalNondegenerate {n : ℕ} {a : Fin n → k} (ha : ∀ i, a i ≠ 0) :
    (weightedSumSquares k a).Nondegenerate := by
  apply nondegenerate_iff_radical_eq_bot.2
  rw [QuadraticForm.radical_weightedSumSquares]
  ext z
  simp [Pi.mem_spanSubset_iff, ha, funext_iff]

variable [FiniteDimensional k U] [FiniteDimensional k V]

private theorem cancelDiagonal (qU : QuadraticForm k U) (qV : QuadraticForm k V)
    (hU : qU.Nondegenerate) (hV : qV.Nondegenerate) {n : ℕ} (a : Fin n → k)
    (ha : ∀ i, a i ≠ 0)
    (h : (qU.prod (weightedSumSquares k a)).Equivalent (qV.prod (weightedSumSquares k a))) :
    qU.Equivalent qV := by
  induction n with
  | zero =>
    obtain ⟨e⟩ := h
    exact ⟨((prodDiagonalZero qU a).symm.trans e).trans (prodDiagonalZero qV a)⟩
  | succ n ih =>
    let qTail := weightedSumSquares k (a ∘ Fin.succ)
    let qLine := a 0 • (sq : QuadraticForm k k)
    let eU := (prodAssoc qU qTail qLine).trans
      ((IsometryEquiv.refl qU).prod (splitDiagonal a).symm)
    let eV := (prodAssoc qV qTail qLine).trans
      ((IsometryEquiv.refl qV).prod (splitDiagonal a).symm)
    obtain ⟨e⟩ := h
    have hTail : qTail.Nondegenerate := diagonalNondegenerate fun i => ha i.succ
    apply ih (a ∘ Fin.succ) (fun i => ha i.succ)
    exact LineCancellation.cancelLine _ _
      (LineCancellation.nondegenerate_prod hU hTail)
      (LineCancellation.nondegenerate_prod hV hTail)
      (ha 0) ((eU.trans e).trans eV.symm)

end

/-- Witt cancellation of the same finite-dimensional nondegenerate space. -/
theorem cancel {k : Type u} {U : Type v} {V : Type w} {W : Type x}
    [Field k] [Invertible (2 : k)]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (qU : QuadraticForm k U) (qV : QuadraticForm k V) (qW : QuadraticForm k W)
    (hU : qU.Nondegenerate) (hV : qV.Nondegenerate) (hW : qW.Nondegenerate)
    (h : (qU.prod qW).Equivalent (qV.prod qW)) : qU.Equivalent qV := by
  obtain ⟨a, ha⟩ := qW.equivalent_weightedSumSquares_units_of_nondegenerate'
    ((Coordinates.nondegenerate_iff_associated_separatingLeft qW).1 hW)
  let w := fun i => (a i : k)
  have hw : qW.Equivalent (weightedSumSquares k w) := by
    have hweights : weightedSumSquares k a = weightedSumSquares k w := by
      ext z
      simp only [weightedSumSquares_apply, Units.smul_def, w, smul_eq_mul]
    rwa [← hweights]
  exact cancelDiagonal qU qV hU hV w (fun i => (a i).ne_zero)
    (((Equivalent.refl qU).prod hw.symm).trans (h.trans ((Equivalent.refl qV).prod hw)))

/-- Witt cancellation of two isometric finite-dimensional nondegenerate spaces. -/
theorem cancelEquivalent {k : Type u} {U : Type v} {V : Type w} {W : Type x} {W' : Type y}
    [Field k] [Invertible (2 : k)]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    (qU : QuadraticForm k U) (qV : QuadraticForm k V)
    (qW : QuadraticForm k W) (qW' : QuadraticForm k W')
    (hU : qU.Nondegenerate) (hV : qV.Nondegenerate)
    (hW : qW.Nondegenerate) (_hW' : qW'.Nondegenerate)
    (hWW' : qW.Equivalent qW') (h : (qU.prod qW).Equivalent (qV.prod qW')) :
    qU.Equivalent qV :=
  cancel qU qV qW hU hV hW (h.trans ((Equivalent.refl qV).prod hWW'.symm))

end Alg01SymmetricWitt.Witt.Cancellation
