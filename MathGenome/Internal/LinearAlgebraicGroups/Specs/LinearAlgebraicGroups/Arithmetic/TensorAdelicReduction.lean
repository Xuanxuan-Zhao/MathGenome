import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.Multilinear.Basis

open scoped NumberField Polynomial RatFunc LaurentSeries RestrictedProduct
open IsDedekindDomain

namespace LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

open AdelicLatticeBounds

/-- The reference lattice in a fixed free coordinate system. -/
noncomputable def referenceLattice (A K I : Type*) [CommRing A] [Field K] [Algebra A K]
    [Fintype I] [DecidableEq I] : Submodule A (I → K) :=
  matrixLattice (1 : Matrix.GeneralLinearGroup I K)

/-- Finite matrix adeles in the coordinates of the reference lattice. -/
abbrev FiniteMatrices (A K I : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I] :=
  FiniteBasisAdeles A K I

/-- The local lattice cut out by requiring that the transformed vector be integral. -/
noncomputable def transportedLattice {A K I : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I]
    (v : HeightOneSpectrum A) (g : Matrix.GeneralLinearGroup I (v.adicCompletion K)) :
    Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K) :=
  matrixLattice g⁻¹

/-- The scalar adele ring in the coordinates of a base PID with one
distinguished completion. -/
abbrev BaseScalarAdeles (R k B : Type*) [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] :=
  FiniteAdeleRing R k × B

/-- The base-field diagonal includes every finite factor and the distinguished
completion. -/
noncomputable def baseScalarDiagonal {R k B : Type*} [CommRing R] [IsDedekindDomain R]
    [Field k] [Algebra R k] [IsFractionRing R k] [CommRing B] (f : k →+* B) :
    k →+* BaseScalarAdeles R k B :=
  (algebraMap k (FiniteAdeleRing R k)).prod f

/-- Coordinate arrays for tensors with an arbitrary finite list of input slots
and with output in an independent coordinate space. -/
abbrev TensorCoefficients (A X I O : Type*) := (X → I) → O → A

open scoped BigOperators Classical in
/-- Evaluate the tensor given by its coefficients on the standard basis. -/
noncomputable def coordinateTensor {A X I O : Type*} [CommRing A] [Fintype X] [Fintype I]
    (c : TensorCoefficients A X I O) : MultilinearMap A (fun _ : X => I → A) (O → A) :=
  ∑ w : X → I, (((MultilinearMap.mkPiAlgebra A X A).compLinearMap
    (fun x => LinearMap.proj (w x))).smulRight (c w))

/-- The array in a new input and output basis. A fixed output space is
represented by putting the identity in the output slot. -/
noncomputable def transformedTensor {A X I O : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (c : TensorCoefficients A X I O) (m : Matrix.GeneralLinearGroup I A)
    (u : Matrix.GeneralLinearGroup O A) : TensorCoefficients A X I O :=
  fun w => u⁻¹.val.mulVec (coordinateTensor c (fun x => m.val.col (w x)))

/-- Preserving a tensor means intertwining its input and output actions. -/
def PreservesTensor {A X I O : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (T : TensorCoefficients A X I O) (m : Matrix.GeneralLinearGroup I A)
    (u : Matrix.GeneralLinearGroup O A) : Prop :=
  ∀ v : X → I → A, coordinateTensor T (fun x => m.val.mulVec (v x)) =
    u.val.mulVec (coordinateTensor T v)

/-- Scalar restriction amounts to recording the values of the original tensor
on tuples of base-field basis vectors, in base-field output coordinates. -/
noncomputable def restrictedTensor {k K X I O N M : Type*} [Field k] [Field K]
    [Algebra k K] [Fintype X] [Fintype I] [Fintype N] [Fintype M]
    (b : Module.Basis N k (I → K)) (c : Module.Basis M k (O → K))
    (T : TensorCoefficients K X I O) : TensorCoefficients k X N M :=
  fun w => c.equivFun (coordinateTensor T (fun x => b (w x)))

/-- The finite base prime below an original finite prime. -/
def primeBelow {R A : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    (v : HeightOneSpectrum A) : HeightOneSpectrum R :=
  ⟨v.asIdeal.under R, Ideal.IsPrime.comap _, Ideal.IsIntegral.under_ne_bot R v.ne_bot⟩

/-- Both the matrix and its inverse are integral at the given finite factor. -/
abbrev integralMatrices {I L : Type*} [CommRing L] [Fintype I] [DecidableEq I]
    (O : Subring L) : Subgroup (Matrix.GeneralLinearGroup I L) :=
  (Matrix.GeneralLinearGroup.map O.subtype).range

/-- Restriction of a rational invertible matrix to the base field in a chosen basis. -/
noncomputable def restrictMatrix {k K I N : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K)) :
    Matrix.GeneralLinearGroup I K → Matrix.GeneralLinearGroup N k :=
  fun m => Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (b.equivFun.symm.trans
        (((Matrix.GeneralLinearGroup.toLin m).toLinearEquiv.restrictScalars k).trans b.equivFun)))

/-- The full matrix restricted product over the intrinsic function-field places. -/
abbrev FunctionMatrixAdeles (K I : Type*) [Field K] [Fintype I] [DecidableEq I] :=
  Πʳ v : FunctionPlace K, [Matrix.GeneralLinearGroup I v.Completion,
    ↑(integralMatrices (I := I) v.integers.toSubring)]

/-- The finite matrix restricted product together with the ordinary product of
the distinguished factors. -/
abbrev SplitMatrixAdeles (A K I : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I] {W : Type*}
    (L : W → Type*) [∀ w, Field (L w)] :=
  FiniteMatrices A K I × (∀ w, Matrix.GeneralLinearGroup I (L w))

/-- The full number-field matrix adeles, in coordinates over the number field. -/
abbrev NumberMatrixAdeles (K I : Type*) [Field K] [NumberField K] [Fintype I] [DecidableEq I] :=
  SplitMatrixAdeles (𝓞 K) K I (fun w : NumberField.InfinitePlace K => w.Completion)

universe u

/-- Tensors with output in the matrix representation and tensors with a fixed
output space. Each input slot is a copy of the matrix representation. -/
structure TensorSystem (K I : Type*) {J H : Type*}
    (X : J → Type u) (Y : H → Type u) (O : H → Type*) where
  moving : ∀ j, TensorCoefficients K (X j) I I
  fixed : ∀ h, TensorCoefficients K (Y h) I (O h)

namespace TensorSystem

variable {K I J H : Type*} {X : J → Type u} {Y : H → Type u} {O : H → Type*}
    [Fintype I] [DecidableEq I] [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)]

/-- Preserve each tensor after extending coefficients. The action on the
output of a fixed tensor is the identity. -/
def Preserves {L : Type*} [CommRing K] [CommRing L]
    (T : TensorSystem K I X Y O) (e : K →+* L) (m : Matrix.GeneralLinearGroup I L) : Prop :=
  (∀ j, PreservesTensor (fun w i => e (T.moving j w i)) m m) ∧
  (∀ h v, coordinateTensor (fun w o => e (T.fixed h w o))
    (fun x => m.val.mulVec (v x)) = coordinateTensor (fun w o => e (T.fixed h w o)) v)

/-- The tensor equations at every factor of a split matrix adelic product. -/
def PreservesSplit {A : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] {W : Type*} {L : W → Type*} [∀ w, Field (L w)]
    (T : TensorSystem K I X Y O) (e : ∀ w, K →+* L w)
    (g : SplitMatrixAdeles A K I L) : Prop :=
  (∀ v : HeightOneSpectrum A, T.Preserves (algebraMap K (v.adicCompletion K)) (g.1 v)) ∧
  ∀ w, T.Preserves (e w) (g.2 w)

end TensorSystem

end LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

namespace LinearAlgebraicGroups.Specs.TensorAdelicReduction

open Arithmetic Arithmetic.AdelicLatticeBounds Arithmetic.TensorAdelicReduction

/-- Normalize the coefficients of each polynomial by a nonzero scalar. This preserves
its degree condition, vanishing locus, and invariance under every local matrix. -/
def integralInvariantPolynomials : Prop :=
  ∀ {A K I P : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I]
    (p : P → MvPolynomial I K) (d : P → ℕ),
    (∀ j, 0 < d j ∧ (p j).IsHomogeneous (d j)) →
    ∃ q : P → MvPolynomial I K,
      (∀ j, 0 < d j ∧ (q j).IsHomogeneous (d j)) ∧
      IntegralOnReference (referenceLattice A K I) q ∧
      (∀ j x, (q j).eval x = 0 ↔ (p j).eval x = 0) ∧
      (∀ {J : Type*} {L : J → Type*} [∀ j, Field (L j)] (e : ∀ j, K →+* L j)
        (g : ∀ j, Matrix.GeneralLinearGroup I (L j)),
        PreservesPolynomials e p g → PreservesPolynomials e q g)

/-- The transported local lattices are full and differ from the reference at
only finitely many places. Each is carried onto the completed reference by
the corresponding local matrix. -/
def transportedLattices : Prop :=
  ∀ {A K I : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I]
    (g : FiniteMatrices A K I),
    let Q v := transportedLattice v (g v)
    (∀ v, Submodule.IsLattice (v.adicCompletion K) (Q v)) ∧
    {v | Q v ≠ completedLattice v (referenceLattice A K I)}.Finite ∧
    ∀ v, (g v).val.mulVec '' (Q v : Set (I → v.adicCompletion K)) =
      (completedLattice v (referenceLattice A K I) : Set (I → v.adicCompletion K))

/-- The actual number-field matrices, acting on their own completion factors,
admit reduced bases in one compact set in the restriction of scalars. -/
def numberBoundedTensorBases : Prop :=
  ∀ {K I P : Type*} [Field K] [NumberField K] [Fintype I] [DecidableEq I] [Fintype P]
    (p : P → MvPolynomial I K) (d : P → ℕ),
    (∀ r, 0 < d r ∧ (p r).IsHomogeneous (d r)) →
    (∀ x, x ≠ 0 → ∃ r, (p r).eval x ≠ 0) →
    let N := Fin (Module.finrank ℚ (I → K))
    ∃ (b : Module.Basis N ℚ (I → K)) (a : ∀ w : NumberField.InfinitePlace K, Algebra ℝ w.Completion),
      letI := a
      ∃ E : (N → ℝ) ≃L[ℝ] (∀ w : NumberField.InfinitePlace K, I → w.Completion),
        IsBasisMatrix ℤ b (referenceLattice (𝓞 K) K I : Set (I → K)) 1 ∧
        (∀ x w, E (embedCoordinates (algebraMap ℚ ℝ) (b.equivFun x)) w =
          embedCoordinates (algebraMap K w.Completion) x) ∧
        ∃ C : Set (BasisAdeles ℤ ℚ ℝ N), IsCompact C ∧
          ∀ (g : FiniteMatrices (𝓞 K) K I)
            (gInf : ∀ w : NumberField.InfinitePlace K, Matrix.GeneralLinearGroup I w.Completion),
            (∀ v, (g v).det = 1) → (∀ w, (gInf w).det = 1) →
            PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g →
            PreservesPolynomials (fun w => algebraMap K w.Completion) p gInf →
            ∃ (G : ∀ q : HeightOneSpectrum ℤ, Matrix.GeneralLinearGroup N (q.adicCompletion ℚ))
              (GInf : Matrix.GeneralLinearGroup N ℝ) (M : Matrix.GeneralLinearGroup N ℚ)
              (h : FiniteBasisIntegral G M),
              (∀ q, (G q).det = 1 ∧ FiniteMatrixAction b g q (G q)) ∧
              GInf.det = 1 ∧
              (∀ z w, E (GInf.val.mulVec z) w = (gInf w).val.mulVec (E z w)) ∧
              IsBasisMatrix ℤ b (rationalLatticeIntersection
                (fun v => transportedLattice v (g v)) : Set (I → K)) M ∧
              M.det = 1 ∧
              (finiteBasisRepresentative G M h,
                GInf * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M) ∈ C

open Classical Arithmetic.LatticeCompletionDecompositionSpec in
/-- The function-field bounded-basis assertion uses all places above the
parameter's infinity together, with the finite factors of its integral closure. -/
def functionBoundedTensorBases : Prop :=
  ∀ {F K I P : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I] [Fintype P] (t : SeparatingParameter F K)
    (p : P → MvPolynomial I K) (d : P → ℕ),
    (∀ r, 0 < d r ∧ (p r).IsHomogeneous (d r)) →
    (∀ x, x ≠ 0 → ∃ r, (p r).eval x ≠ 0) →
    letI := t.rationalAlgebra
    letI := parameterIntegerRing_torsionFree t
    let N := Fin (Module.finrank F⟮X⟯ (I → K))
    let B := infinityField F
    let J := {w : FunctionPlace K // t.element ∉ w.val}
    letI (w : J) : Field w.val.Completion := inferInstance
    ∃ (b : Module.Basis N F⟮X⟯ (I → K)) (a : ∀ w : J, Algebra B w.val.Completion),
      letI := a
      ∃ (E : (N → B) ≃L[B] (∀ w : J, I → w.val.Completion))
        (e : B ≃+* F⸨X⸩) (h : B ≃ₜ F⸨X⸩),
        let f := e.toRingHom.comp (infinityEmbedding F)
        IsBasisMatrix F[X] b (referenceLattice t.integerRing K I : Set (I → K)) 1 ∧
        (∀ x w, E (embedCoordinates (infinityEmbedding F) (b.equivFun x)) w =
          embedCoordinates w.val.embedding x) ∧
        (⇑e = ⇑h) ∧ f.comp (algebraMap F[X] F⟮X⟯) = LaurentLattice.polynomialEmbedding F ∧
        ∃ C : Set (BasisAdeles F[X] F⟮X⟯ F⸨X⸩ N), IsCompact C ∧
          ∀ (g : FiniteMatrices t.integerRing K I)
            (gInf : ∀ w : J, Matrix.GeneralLinearGroup I w.val.Completion),
            (∀ v, (g v).det = 1) → (∀ w, (gInf w).det = 1) →
            PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g →
            PreservesPolynomials (fun w => w.val.embedding) p gInf →
            ∃ (G : ∀ q : HeightOneSpectrum F[X], Matrix.GeneralLinearGroup N (q.adicCompletion F⟮X⟯))
              (GInf : Matrix.GeneralLinearGroup N B) (M : Matrix.GeneralLinearGroup N F⟮X⟯)
              (hI : FiniteBasisIntegral G M),
              (∀ q, (G q).det = 1 ∧ FiniteMatrixAction b g q (G q)) ∧
              GInf.det = 1 ∧
              (∀ z w, E (GInf.val.mulVec z) w = (gInf w).val.mulVec (E z w)) ∧
              IsBasisMatrix F[X] b (rationalLatticeIntersection
                (fun v => transportedLattice v (g v)) : Set (I → K)) M ∧
              M.det = 1 ∧
              (finiteBasisRepresentative G M hI,
                Matrix.GeneralLinearGroup.map e.toRingHom GInf * Matrix.GeneralLinearGroup.map f M) ∈ C

/-- Compact matrix bounds over a base completion bound the original local
matrices, with their inverses, through the continuous product comparison. -/
def compactLocalMatrixTransport : Prop :=
  ∀ {B I N J : Type*} [Field B] [TopologicalSpace B] [IsTopologicalRing B]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    {L : J → Type*} [∀ j, Field (L j)] [∀ j, TopologicalSpace (L j)]
    [∀ j, T1Space (L j)] [∀ j, IsTopologicalRing (L j)] [∀ j, Algebra B (L j)]
    (E : (N → B) ≃L[B] (∀ j, I → L j))
    (C : Set (Matrix.GeneralLinearGroup N B)), IsCompact C →
    ∃ D : ∀ j, Set (Matrix.GeneralLinearGroup I (L j)), (∀ j, IsCompact (D j)) ∧
      ∀ (M : Matrix.GeneralLinearGroup N B)
        (m : ∀ j, Matrix.GeneralLinearGroup I (L j)), M ∈ C →
        (∀ z j, E (M.val.mulVec z) j = (m j).val.mulVec (E z j)) →
        ∀ j, m j ∈ D j

/-- Equality of the transformed labels permits right multiplication in the
rational stabilizer. This yields compact representatives in the original
adelic stabilizer whenever the corresponding representatives in the larger
matrix space form a compact set. -/
def compactRepresentativesOfFiniteLabels : Prop :=
  ∀ {B H P T X : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [Group H] [Group P] (S : Subgroup B) (i : H →* B) (j : H → P)
    (G : X → S) (r : X → P) (t : P → T),
    IsClosed (S : Set B) → (Set.range (t ∘ r)).Finite →
    (∀ x y : X, t (r x) = t (r y) → ∃ h : H, j h = r x * (r y)⁻¹) →
    (∀ h, i h ∈ S) →
    (∀ y : X, ∃ C : Set B, IsCompact C ∧
      ∀ x : X, t (r x) = t (r y) → ∀ h : H,
        j h = r x * (r y)⁻¹ → (G x : B) * i h ∈ C) →
    ∃ C : Set B, IsCompact C ∧ C ⊆ S ∧ ∀ x : X, ∃ h : H, (G x : B) * i h ∈ C

/-- A neighborhood isolating the embedded integer ring at the distinguished
completion, together with integrality at all finite places, isolates the
base-field diagonal. -/
def baseDiagonalClosedDiscrete : Prop :=
  ∀ {R k B : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Field B] [TopologicalSpace B] [T2Space B]
    [IsTopologicalRing B] (f : k →+* B) (U : Set B),
    IsOpen U → 0 ∈ U → (∀ x : R, f (algebraMap R k x) ∈ U → x = 0) →
    IsClosed (Set.range (baseScalarDiagonal (R := R) f)) ∧
      IsDiscrete (Set.range (baseScalarDiagonal (R := R) f))

/-- A compact set in the finite product of full base scalar adele rings
contains only finitely many diagonal rational tuples. -/
def finiteDiagonalTuples : Prop :=
  ∀ {k A J : Type*} [TopologicalSpace A] [Finite J]
    (f : k → A), Function.Injective f → IsClosed (Set.range f) → IsDiscrete (Set.range f) →
    ∀ C : Set (J → A), IsCompact C → {x : J → k | f ∘ x ∈ C}.Finite

/-- Matrix entries and inverse entries of the full base matrix adeles are
continuous in the scalar adelic topology. -/
def adelicMatrixEntries : Prop :=
  ∀ {R k B N : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Field B] [TopologicalSpace B]
    [IsTopologicalRing B] [Fintype N] [DecidableEq N],
    ∃ g : BasisAdeles R k B N →* Matrix.GeneralLinearGroup N (BaseScalarAdeles R k B),
      Continuous g ∧ Function.Injective g ∧
      (∀ (a : BasisAdeles R k B N) p i j, ((g a).val i j).1 p = (a.1 p).val i j) ∧
      (∀ (a : BasisAdeles R k B N) i j, ((g a).val i j).2 = a.2.val i j)

/-- Extension of a tensor in coordinates commutes with evaluation. -/
def coordinateTensorMap : Prop :=
  ∀ {A B X I O : Type*} [CommRing A] [CommRing B] [Fintype X] [Fintype I]
    (f : A →+* B) (c : TensorCoefficients A X I O) (v : X → I → A),
    coordinateTensor (fun w o => f (c w o)) (fun x i => f (v x i)) =
      fun o => f (coordinateTensor c v o)

/-- The bounded-basis orbit in finite coordinates is continuous, including
for tensors with fixed output and tensors with moving output. -/
def transformedTensorContinuous : Prop :=
  ∀ {A X I O : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (c : TensorCoefficients A X I O),
    Continuous (fun a : Matrix.GeneralLinearGroup I A × Matrix.GeneralLinearGroup O A =>
      transformedTensor c a.1 a.2)

/-- Restricting scalars on finite tensor arrays commutes with the local
decomposition whenever the comparisons identify the rational diagonal. -/
def localTensorComparison : Prop :=
  ∀ {k K B X I O N M J : Type*} [Field k] [Field K] [Algebra k K] [Field B]
    [Fintype X] [Fintype I] [Fintype N] [Fintype M]
    {L : J → Type*} [∀ j, Field (L j)] [∀ j, Algebra B (L j)]
    (f : k →+* B) (e : ∀ j, K →+* L j)
    (b : Module.Basis N k (I → K)) (c : Module.Basis M k (O → K))
    (E : (N → B) ≃ₗ[B] (∀ j, I → L j)) (F : (M → B) ≃ₗ[B] (∀ j, O → L j)),
    (∀ x j i, E (fun n => f (b.equivFun x n)) j i = e j (x i)) →
    (∀ x j o, F (fun m => f (c.equivFun x m)) j o = e j (x o)) →
    ∀ (T : TensorCoefficients K X I O) (v : X → N → B) j,
      F (coordinateTensor (fun w o => f (restrictedTensor b c T w o)) v) j =
        coordinateTensor (fun w o => e j (T w o)) (fun x => E (v x) j)

/-- Transformed tensors commute with coefficient maps and are unchanged
by prepending any operator preserving the original tensor. -/
def tensorTransport : Prop :=
  ∀ {A B X I O : Type*} [CommRing A] [CommRing B] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (e : A →+* B) (T : TensorCoefficients A X I O)
    (m : Matrix.GeneralLinearGroup I A) (u : Matrix.GeneralLinearGroup O A),
    (∀ w o, transformedTensor (fun v i => e (T v i))
        (Matrix.GeneralLinearGroup.map e m) (Matrix.GeneralLinearGroup.map e u) w o =
      e (transformedTensor T m u w o)) ∧
    ∀ (g : Matrix.GeneralLinearGroup I A) (v : Matrix.GeneralLinearGroup O A),
      PreservesTensor T g v → transformedTensor T (g * m) (v * u) = transformedTensor T m u

/-- Equality of the rational transforms makes the relative basis change
preserve the original tensor, with the correct output action. -/
def tensorLabelComparison : Prop :=
  ∀ {A X I O : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (T : TensorCoefficients A X I O)
    (m n : Matrix.GeneralLinearGroup I A) (u v : Matrix.GeneralLinearGroup O A),
    transformedTensor T m u = transformedTensor T n v →
      PreservesTensor T (m * n⁻¹) (u * v⁻¹)

open Arithmetic.LatticeCompletionDecompositionSpec in
/-- Grouping the original finite places above the base primes has finite
fibres and covers every original finite place. -/
def finitePrimeFibres : Prop :=
  ∀ {R A : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Module.Finite R A],
    Function.Bijective (fun z : Σ p : HeightOneSpectrum R, p.asIdeal.primesOver A =>
      primeAbove z.1 z.2) ∧
    Filter.Tendsto (primeBelow (R := R) (A := A)) Filter.cofinite Filter.cofinite

/-- A scalar restriction comparison carrying the base integer box to
the product boxes detects integrality of both a matrix and its inverse. -/
def integralMatrixTransport : Prop :=
  ∀ {B N I J : Type*} [Field B] [Fintype N] [DecidableEq N] [Fintype I] [DecidableEq I]
    {L : J → Type*} [∀ j, Field (L j)] [∀ j, Algebra B (L j)]
    (E : (N → B) ≃ₗ[B] (∀ j, I → L j))
    (O : Subring B) (U : ∀ j, Subring (L j)),
    (∀ x, (∀ n, x n ∈ O) ↔ ∀ j i, E x j i ∈ U j) →
    ∀ (M : Matrix.GeneralLinearGroup N B) (m : ∀ j, Matrix.GeneralLinearGroup I (L j)),
      (∀ z j, E (M.val.mulVec z) j = (m j).val.mulVec (E z j)) →
      (M ∈ integralMatrices O ↔ ∀ j, m j ∈ integralMatrices (U j))

/-- A compact bound at every original finite place, which is integral
at almost every place, gives a compact box in the original restricted
product. The distinguished factors are retained in the ordinary product. -/
def compactOriginalMatrixBox : Prop :=
  ∀ {A K I J : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I]
    {L : J → Type*} [∀ j, Field (L j)] [∀ j, TopologicalSpace (L j)]
    (D : ∀ v : HeightOneSpectrum A, Set (Matrix.GeneralLinearGroup I (v.adicCompletion K)))
    (E : ∀ j, Set (Matrix.GeneralLinearGroup I (L j))),
    (∀ v, IsCompact (D v)) → (∀ j, IsCompact (E j)) →
    (∀ᶠ v in Filter.cofinite, D v ⊆ (↑(integralMatrices (I := I) (v.adicCompletionIntegers K).toSubring) :
      Set (Matrix.GeneralLinearGroup I (v.adicCompletion K)))) →
    IsCompact {g : FiniteMatrices A K I × (∀ j, Matrix.GeneralLinearGroup I (L j)) |
      (∀ v, g.1 v ∈ D v) ∧ (∀ j, g.2 j ∈ E j)}

/-- Closed discreteness in the two base adelic models used for the tensor labels. -/
def arithmeticBaseDiagonals : Prop :=
  (IsClosed (Set.range (baseScalarDiagonal (R := ℤ) (algebraMap ℚ ℝ))) ∧
    IsDiscrete (Set.range (baseScalarDiagonal (R := ℤ) (algebraMap ℚ ℝ)))) ∧
  ∀ (F : Type*) [Field F] [Finite F] (f : F⟮X⟯ →+* F⸨X⸩),
    f.comp (algebraMap F[X] F⟮X⟯) = LaurentLattice.polynomialEmbedding F →
    IsClosed (Set.range (baseScalarDiagonal (R := F[X]) f)) ∧
      IsDiscrete (Set.range (baseScalarDiagonal (R := F[X]) f))

/-- Compact subsets of a restricted product with open reference subsets
have a common finite set of exceptions to the reference condition. -/
def compactUniformIntegrality : Prop :=
  ∀ {J : Type*} {G : J → Type*} [∀ j, TopologicalSpace (G j)] (U : ∀ j, Set (G j)),
    (∀ j, IsOpen (U j)) → ∀ C : Set (Πʳ j, [G j, U j]), IsCompact C →
    ∀ᶠ j in Filter.cofinite, ∀ x ∈ C, x j ∈ U j

open Arithmetic.LatticeCompletionDecompositionSpec in
/-- Compact bounds on the finite original matrices follow from bounds in the finite
restriction of scalars, using the completed integral reference lattice. -/
def compactFiniteMatrixTransport : Prop :=
  ∀ {R A k K I N : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Module.Finite R A]
    [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K] [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K)),
    IsBasisMatrix R b (referenceLattice A K I : Set (I → K)) 1 →
    ∀ C : Set (FiniteMatrices R k N), IsCompact C →
      ∃ D : Set (FiniteMatrices A K I), IsCompact D ∧
        ∀ (G : FiniteMatrices R k N) (g : FiniteMatrices A K I),
          G ∈ C → (∀ p, FiniteMatrixAction b g p (G p)) → g ∈ D

/-- A rational basis change commutes with the decomposition of every completed
scalar restriction. -/
def rationalMatrixComparison : Prop :=
  ∀ {k K B N I J : Type*} [Field k] [Field K] [Algebra k K] [Field B]
    [Fintype N] [DecidableEq N] [Fintype I] [DecidableEq I]
    {L : J → Type*} [∀ j, Field (L j)] [∀ j, Algebra B (L j)]
    (f : k →+* B) (e : ∀ j, K →+* L j) (b : Module.Basis N k (I → K))
    (E : (N → B) ≃ₗ[B] (∀ j, I → L j)),
    (∀ x j, E (embedCoordinates f (b.equivFun x)) j = embedCoordinates (e j) x) →
    ∀ (m : Matrix.GeneralLinearGroup I K) z j,
      E ((Matrix.GeneralLinearGroup.map f (restrictMatrix b m)).val.mulVec z) j =
        (Matrix.GeneralLinearGroup.map (e j) m).val.mulVec (E z j)

/-- Intertwining completed input and output operators transports invariance of
the tensors on all original factors to invariance in base coordinates. -/
def localTensorPreservation : Prop :=
  ∀ {k K B X I O N M J : Type*} [Field k] [Field K] [Algebra k K] [Field B]
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
    {L : J → Type*} [∀ j, Field (L j)] [∀ j, Algebra B (L j)]
    (f : k →+* B) (e : ∀ j, K →+* L j)
    (b : Module.Basis N k (I → K)) (c : Module.Basis M k (O → K))
    (E : (N → B) ≃ₗ[B] (∀ j, I → L j)) (F : (M → B) ≃ₗ[B] (∀ j, O → L j)),
    (∀ x j i, E (fun n => f (b.equivFun x n)) j i = e j (x i)) →
    (∀ x j o, F (fun m => f (c.equivFun x m)) j o = e j (x o)) →
    ∀ (T : TensorCoefficients K X I O)
      (g : ∀ j, Matrix.GeneralLinearGroup I (L j))
      (h : ∀ j, Matrix.GeneralLinearGroup O (L j))
      (G : Matrix.GeneralLinearGroup N B) (H : Matrix.GeneralLinearGroup M B),
    (∀ z j, E (G.val.mulVec z) j = (g j).val.mulVec (E z j)) →
    (∀ z j, F (H.val.mulVec z) j = (h j).val.mulVec (F z j)) →
    (∀ j, PreservesTensor (fun w o => e j (T w o)) (g j) (h j)) →
    PreservesTensor (fun w o => f (restrictedTensor b c T w o)) G H

/-- Every rational invertible matrix defines a full adelic matrix, including
integrality of the inverse outside the same finite exceptional set. -/
def finiteMatrixDiagonal : Prop :=
  ∀ {R k N : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N],
    ∃ e : Matrix.GeneralLinearGroup N k →* FiniteMatrices R k N,
      ∀ m (p : HeightOneSpectrum R), e m p =
        Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) m

/-- For a finite family of base-coordinate tensors, bounded basis
representatives and invariance in each completion force finitely many rational
transformed tuples. -/
def finiteTransformedTensorLabels : Prop :=
  ∀ {R k B N J : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Field B] [TopologicalSpace B] [IsTopologicalRing B]
    [Fintype N] [DecidableEq N] [Finite J] {X : J → Type*} [∀ j, Fintype (X j)]
    (f : k →+* B), IsClosed (Set.range (baseScalarDiagonal (R := R) f)) →
    IsDiscrete (Set.range (baseScalarDiagonal (R := R) f)) →
    ∀ {S : Type*} (C : Set (BasisAdeles R k B N)), IsCompact C →
    ∀ (T : ∀ j, TensorCoefficients k (X j) N N)
      (r : S → Matrix.GeneralLinearGroup N k)
      (G H : S → BasisAdeles R k B N),
      (∀ x, H x ∈ C) →
      (∀ x p, (H x).1 p = (G x).1 p *
        Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) (r x)) →
      (∀ x, (H x).2 = (G x).2 * Matrix.GeneralLinearGroup.map f (r x)) →
      (∀ j x p, PreservesTensor
        (fun w i => algebraMap k (p.adicCompletion k) (T j w i)) ((G x).1 p) ((G x).1 p)) →
      (∀ j x, PreservesTensor (fun w i => f (T j w i)) ((G x).2) ((G x).2)) →
      (Set.range fun x => fun j => transformedTensor (T j) (r x) (r x)).Finite

/-- Commuting with multiplication by a base-field basis of scalars suffices
for a rational change of basis to be linear over the original field. -/
def scalarLinearMatrix : Prop :=
  ∀ {k K I N A : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N] [Fintype A]
    (b : Module.Basis N k (I → K)) (c : Module.Basis A k K)
    (m : Matrix.GeneralLinearGroup N k),
    (∀ j x, b.equivFun.symm (m.val.mulVec (b.equivFun (c j • x))) =
      c j • b.equivFun.symm (m.val.mulVec (b.equivFun x))) →
    ∃ g : Matrix.GeneralLinearGroup I K, restrictMatrix b g = m

/-- Separating a finite set of places from a restricted product preserves
the full topology, with the separated factors in the ordinary product. -/
def restrictedProductSplit : Prop :=
  ∀ {J : Type*} {G : J → Type*} [∀ j, TopologicalSpace (G j)]
    (U : ∀ j, Set (G j)) (S : Set J), Sᶜ.Finite →
    (∀ j, IsOpen (U j)) →
    ∃ e : (Πʳ j, [G j, U j]) ≃ₜ
        ((Πʳ j : S, [G j, U j]) × (∀ j : (Sᶜ : Set J), G j)),
      (∀ a j, (e a).1 j = a j) ∧ ∀ a j, (e a).2 j = a j

/-- The chart at the separating parameter plus all its poles presents the
full intrinsic matrix restricted product, with the original completion maps. -/
def functionMatrixAdeleComparison : Prop :=
  ∀ {F K I : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I] (t : SeparatingParameter F K),
    let P := {w : FunctionPlace K // t.element ∉ w.val}
    ∃ e : FunctionMatrixAdeles K I ≃ₜ
        (FiniteMatrices t.integerRing K I × (∀ w : P, Matrix.GeneralLinearGroup I w.val.Completion)),
      (∀ g w, (e g).2 w = g w.val) ∧
      ∀ v : HeightOneSpectrum t.integerRing,
        ∃ c : (GlobalPlacesSpec.placeOfPrimeValue t v).Completion ≃+* v.adicCompletion K,
          (∀ x, c ((GlobalPlacesSpec.placeOfPrimeValue t v).embedding x) =
            algebraMap K (v.adicCompletion K) x) ∧
          ∀ g, (e g).1 v = Matrix.GeneralLinearGroup.map c.toRingHom
            (g (GlobalPlacesSpec.placeOfPrimeValue t v))

universe u

/-- Determinant-one number-field adeles preserving the anisotropy polynomials
and the tensors reduce into a single compact set in the full tensor stabilizer. -/
def numberTensorAdelicReduction : Prop :=
  ∀ {K I P J H : Type*} [Field K] [NumberField K] [Fintype I] [DecidableEq I] [Fintype P]
    [Finite J] [Finite H] {X : J → Type u} {Y : H → Type u} {O : H → Type*}
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] [∀ h, Finite (O h)]
    (p : P → MvPolynomial I K) (d : P → ℕ) (T : TensorSystem K I X Y O),
    (∀ r, 0 < d r ∧ (p r).IsHomogeneous (d r)) →
    (∀ x, x ≠ 0 → ∃ r, (p r).eval x ≠ 0) →
    let e := fun w : NumberField.InfinitePlace K => algebraMap K w.Completion
    ∃ δ : Matrix.GeneralLinearGroup I K →* NumberMatrixAdeles K I,
      (∀ r v, (δ r).1 v = Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) r) ∧
      (∀ r w, (δ r).2 w = Matrix.GeneralLinearGroup.map (e w) r) ∧
      ∃ C : Set (NumberMatrixAdeles K I), IsCompact C ∧
        (∀ h ∈ C, T.PreservesSplit e h) ∧
        ∀ g : NumberMatrixAdeles K I,
          (∀ v, (g.1 v).det = 1) → (∀ w, (g.2 w).det = 1) →
          PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g.1 →
          PreservesPolynomials e p g.2 → T.PreservesSplit e g →
          ∃ r : Matrix.GeneralLinearGroup I K, T.Preserves (RingHom.id K) r ∧ g * δ r ∈ C

/-- The same compact reduction in the intrinsic function-field restricted
product, retaining every place above the chosen parameter's infinity. -/
def functionTensorAdelicReduction : Prop :=
  ∀ {F K I P J H : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I] [Fintype P] [Finite J] [Finite H]
    {X : J → Type u} {Y : H → Type u} {O : H → Type*}
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] [∀ h, Finite (O h)]
    (t : SeparatingParameter F K) (p : P → MvPolynomial I K) (d : P → ℕ)
    (T : TensorSystem K I X Y O),
    (∀ r, 0 < d r ∧ (p r).IsHomogeneous (d r)) →
    (∀ x, x ≠ 0 → ∃ r, (p r).eval x ≠ 0) →
    letI (j : FunctionPlace K) : Field j.Completion := inferInstance
    ∃ δ : Matrix.GeneralLinearGroup I K →* FunctionMatrixAdeles K I,
      (∀ r v, δ r v = Matrix.GeneralLinearGroup.map v.embedding r) ∧
      ∃ C : Set (FunctionMatrixAdeles K I), IsCompact C ∧
        (∀ h ∈ C, ∀ v, T.Preserves v.embedding (h v)) ∧
        ∀ g : FunctionMatrixAdeles K I,
          (∀ v, (g v).det = 1) → PreservesPolynomials (fun v : FunctionPlace K => v.embedding) p g →
          (∀ v, T.Preserves v.embedding (g v)) →
          ∃ r : Matrix.GeneralLinearGroup I K, T.Preserves (RingHom.id K) r ∧ g * δ r ∈ C

end LinearAlgebraicGroups.Specs.TensorAdelicReduction
