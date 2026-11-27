import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.MatrixGroupCoordinates

/-!
# Matrix group coordinate algebras

Use `open scoped GaloisFormalization.PV.MatrixGroupCoordinates.Specs` for the
Zariski topology on the matrix group and its subgroups.
-/

namespace GaloisFormalization.PV.MatrixGroupCoordinates

open scoped Specs

universe u v

noncomputable section

abbrev CoordinateVariable := Specs.CoordinateVariable
abbrev CoordinatePolynomial := @Specs.CoordinatePolynomial
abbrev determinantRelation := @Specs.determinantRelation
abbrev inverseDeterminant := @Specs.inverseDeterminant
abbrev evalAt := @Specs.evalAt
abbrev zeroLocus := @Specs.zeroLocus
abbrev vanishingIdeal := @Specs.vanishingIdeal
abbrev CoordinateRing := @Specs.CoordinateRing
abbrev coordinateMap := @Specs.coordinateMap
abbrev Points := @Specs.Points
abbrev MatrixSolutions := @Specs.MatrixSolutions
abbrev IsRegular := @Specs.IsRegular
abbrev IsRegularMatrix := @Specs.IsRegularMatrix
abbrev IsRegularGL := @Specs.IsRegularGL
abbrev IsRegularRepresentation := @Specs.IsRegularRepresentation
abbrev zariskiTopology := @Specs.zariskiTopology
abbrev IsAlgebraicSubgroup := @Specs.IsAlgebraicSubgroup
abbrev evalSolution := @Specs.evalSolution
abbrev evalCoordinate := @Specs.evalCoordinate

section Algebra

variable {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A]
variable {n : ℕ}

@[simp] theorem evalAt_entry (g : GL (Fin n) A) (i j : Fin n) :
    evalAt (C := C) g (MvPolynomial.X (Sum.inl (i, j))) = g i j := by
  simp [Specs.evalAt]

@[simp] theorem evalAt_inverseDeterminant (g : GL (Fin n) A) :
    evalAt (C := C) g (MvPolynomial.X (Sum.inr ())) = inverseDeterminant g := by
  simp [Specs.evalAt]

@[simp] theorem evalAt_determinantRelation (g : GL (Fin n) A) :
    evalAt (C := C) g (determinantRelation C n) = 0 := by
  change evalAt (C := C) g (Specs.determinantRelation C n) = 0
  unfold Specs.determinantRelation
  rw [map_sub, map_mul, map_one, evalAt_inverseDeterminant, AlgHom.map_det]
  have h : (evalAt (C := C) g).toRingHom.mapMatrix
      (Matrix.of fun i j => MvPolynomial.X (Sum.inl (i, j))) = g.val := by
    ext i j
    exact evalAt_entry g i j
  change inverseDeterminant g * ((evalAt (C := C) g).toRingHom.mapMatrix
    (Matrix.of fun i j => MvPolynomial.X (Sum.inl (i, j)))).det - 1 = 0
  rw [h]
  change (↑((Matrix.GeneralLinearGroup.det g)⁻¹) : A) *
    ↑(Matrix.GeneralLinearGroup.det g) - 1 = 0
  rw [Units.inv_mul, sub_self]

theorem mem_vanishingIdeal (S : Set (GL (Fin n) C)) (p : CoordinatePolynomial C n) :
    p ∈ vanishingIdeal S ↔ ∀ g : S, evalAt (C := C) g.1 p = 0 := by
  change p ∈ ⨅ g : S, RingHom.ker (evalAt (C := C) g.1) ↔ _
  simp only [Ideal.mem_iInf, RingHom.mem_ker]

theorem determinantRelation_mem_vanishingIdeal (S : Set (GL (Fin n) C)) :
    determinantRelation C n ∈ vanishingIdeal S :=
  (mem_vanishingIdeal _ _).mpr fun g => evalAt_determinantRelation g.1

@[simp] theorem evalSolution_mk (I : Ideal (CoordinatePolynomial C n)) (g : MatrixSolutions I A)
    (p : CoordinatePolynomial C n) :
    evalSolution I g (Ideal.Quotient.mkₐ C I p) = evalAt (C := C) g.1 p :=
  rfl

private theorem eval_determinantRelation_eq_zero (f : CoordinatePolynomial C n →ₐ[C] A)
    (h : f (determinantRelation C n) = 0) :
    f (MvPolynomial.X (Sum.inr ())) *
      (Matrix.of fun i j : Fin n => f (MvPolynomial.X (Sum.inl (i, j)))).det = 1 := by
  apply sub_eq_zero.mp
  change f (Specs.determinantRelation C n) = 0 at h
  rw [Specs.determinantRelation, map_sub, map_mul, map_one, AlgHom.map_det] at h
  exact h

/-- The invertible matrix recovered from an evaluation annihilating the determinant relation. -/
private def matrixOfEvaluation (f : CoordinatePolynomial C n →ₐ[C] A)
    (h : f (determinantRelation C n) = 0) : GL (Fin n) A :=
  let M : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => f (MvPolynomial.X (Sum.inl (i, j)))
  let hdet := eval_determinantRelation_eq_zero f h
  Matrix.GeneralLinearGroup.mk'' M ⟨⟨M.det, f (MvPolynomial.X (Sum.inr ())),
    (mul_comm _ _).trans hdet, hdet⟩, rfl⟩

private theorem evalAt_matrixOfEvaluation (f : CoordinatePolynomial C n →ₐ[C] A)
    (h : f (determinantRelation C n) = 0) :
    evalAt (matrixOfEvaluation f h) = f := by
  apply MvPolynomial.algHom_ext
  intro ij
  rcases ij with ⟨i, j⟩ | ⟨⟩
  · rw [evalAt_entry]
    rfl
  · rw [evalAt_inverseDeterminant]
    let d := Matrix.GeneralLinearGroup.det (matrixOfEvaluation f h)
    change (↑d⁻¹ : A) = f (MvPolynomial.X (Sum.inr ()))
    apply d.mul_left_inj.mp
    rw [Units.inv_mul]
    exact (eval_determinantRelation_eq_zero f h).symm

theorem evalSolution_bijective (I : Ideal (CoordinatePolynomial C n))
    (hI : determinantRelation C n ∈ I) : Function.Bijective (evalSolution (A := A) I) := by
  constructor
  · intro g g' h
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have he := DFunLike.congr_fun h (Ideal.Quotient.mkₐ C I (MvPolynomial.X (Sum.inl (i, j))))
    simpa only [evalSolution_mk, evalAt_entry] using he
  · intro φ
    let f := φ.comp (Ideal.Quotient.mkₐ C I)
    have hf (p : CoordinatePolynomial C n) (hp : p ∈ I) : f p = 0 := by
      change φ (Ideal.Quotient.mk I p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    let g := matrixOfEvaluation f (hf _ hI)
    have hg : evalAt g = f := evalAt_matrixOfEvaluation f (hf _ hI)
    refine ⟨⟨g, fun p hp => show evalAt g p = 0 by rw [hg, hf p hp]⟩, ?_⟩
    apply Ideal.Quotient.algHom_ext
    exact hg

/-- Base change points of a coordinate ring can be read as invertible matrices satisfying
the same equations. -/
def matrixSolutionsEquiv (S : Set (GL (Fin n) C)) :
    MatrixSolutions (vanishingIdeal S) A ≃ Points S A :=
  Equiv.ofBijective (evalSolution (vanishingIdeal S))
    (evalSolution_bijective _ (determinantRelation_mem_vanishingIdeal S))

@[simp] theorem evalCoordinate_mk {S : Set (GL (Fin n) C)} (x : S)
    (p : CoordinatePolynomial C n) :
    evalCoordinate x (coordinateMap S p) = evalAt (C := C) x.1 p :=
  rfl

theorem coordinateMap_surjective (S : Set (GL (Fin n) C)) :
    Function.Surjective (coordinateMap S) :=
  Ideal.Quotient.mkₐ_surjective C (vanishingIdeal S)

theorem coordinate_ext (S : Set (GL (Fin n) C)) (a b : CoordinateRing S)
    (h : ∀ x : S, evalCoordinate x a = evalCoordinate x b) : a = b := by
  obtain ⟨p, hp⟩ := coordinateMap_surjective S (a - b)
  have hpzero : p ∈ vanishingIdeal S := (mem_vanishingIdeal S p).mpr fun x => by
    rw [← evalCoordinate_mk, hp, map_sub, h x, sub_self]
  have hzero : coordinateMap S p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpzero
  exact sub_eq_zero.mp (hp ▸ hzero)

theorem regular_iff_coordinate (S : Set (GL (Fin n) C)) (f : S → C) :
    IsRegular f ↔ ∃ a : CoordinateRing S, ∀ x : S, evalCoordinate x a = f x := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨coordinateMap S p, hp⟩
  · rintro ⟨a, ha⟩
    obtain ⟨p, rfl⟩ := coordinateMap_surjective S a
    exact ⟨p, ha⟩

end Algebra

section Topology

variable {C : Type u} [Field C] {n : ℕ}

theorem isClosed_iff_zeroLocus (S : Set (GL (Fin n) C)) :
    IsClosed S ↔ ∃ s : Set (CoordinatePolynomial C n), S = zeroLocus s := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus T).mp hT
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨PrimeSpectrum.zeroLocus s, PrimeSpectrum.isClosed_zeroLocus s, rfl⟩

theorem isClosed_subtype_iff_zeroLocus (S : Set (GL (Fin n) C)) (T : Set S) :
    IsClosed T ↔ ∃ s : Set (CoordinatePolynomial C n), T = Subtype.val ⁻¹' zeroLocus s := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨s, rfl⟩ := (isClosed_iff_zeroLocus U).mp hU
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨zeroLocus s, (isClosed_iff_zeroLocus _).mpr ⟨s, rfl⟩, rfl⟩

theorem zeroLocus_vanishingIdeal (S : Set (GL (Fin n) C)) (hS : IsClosed S) :
    zeroLocus (vanishingIdeal S : Set _) = S := by
  obtain ⟨s, hs⟩ := (isClosed_iff_zeroLocus S).mp hS
  ext g
  constructor
  · intro hg
    rw [hs]
    intro p hp
    apply hg p
    apply (mem_vanishingIdeal S p).mpr
    intro x
    have hx : x.1 ∈ zeroLocus s := hs ▸ x.2
    exact hx p hp
  · intro hg p hp
    exact (mem_vanishingIdeal S p).mp hp ⟨g, hg⟩

theorem zariski_noetherian : TopologicalSpace.NoetherianSpace (GL (Fin n) C) :=
  (show Topology.IsInducing (Specs.evaluationPrime (n := n) (C := C)) from ⟨rfl⟩).noetherianSpace

theorem evalCoordinate_bijective (S : Set (GL (Fin n) C)) (hS : IsClosed S) :
    Function.Bijective (evalCoordinate (S := S)) := by
  let toSolution (g : S) : MatrixSolutions (vanishingIdeal S) C :=
    ⟨g.1, fun p hp => (mem_vanishingIdeal S p).mp hp g⟩
  have h : Function.Bijective toSolution := by
    constructor
    · intro g g' e
      exact Subtype.ext (congrArg (fun x : MatrixSolutions (vanishingIdeal S) C => x.1) e)
    · intro g
      have hg : g.1 ∈ zeroLocus (vanishingIdeal S : Set _) := g.2
      rw [zeroLocus_vanishingIdeal S hS] at hg
      exact ⟨⟨g.1, hg⟩, Subtype.ext rfl⟩
  exact (evalSolution_bijective _ (determinantRelation_mem_vanishingIdeal S)).comp h

end Topology

end

end GaloisFormalization.PV.MatrixGroupCoordinates
