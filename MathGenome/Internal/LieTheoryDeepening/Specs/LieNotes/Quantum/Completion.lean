import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.TriangularPBW
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Hopf
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.Completion

open Presentation
open Algebra.TensorProduct (assoc lid rid)

universe u

/-- The positive truncation levels in the formal presentation. -/
abbrev Level := {N : ℕ // 1 ≤ N}

/-- The tensor powers used for the algebra, its coproduct, and coassociativity. -/
inductive TensorPower
  | single | square | leftCube | rightCube

abbrev PBWIndex := TriangularPBW.PBWIndex (Root → ℕ)

/-- The root and Cartan exponent indices, in the order of the tensor factors. -/
abbrev Index : TensorPower → Type
  | .single => PBWIndex
  | .square => PBWIndex × PBWIndex
  | .leftCube => (PBWIndex × PBWIndex) × PBWIndex
  | .rightCube => PBWIndex × (PBWIndex × PBWIndex)

variable (k : Type u) [Field k] [CharZero k]

abbrev A (N : Level) := Truncations.A k N

abbrev U (N : Level) := Uₙ k N

abbrev Square (N : Level) := U k N ⊗[A k N] U k N

abbrev LeftCube (N : Level) := Square k N ⊗[A k N] U k N

abbrev RightCube (N : Level) := U k N ⊗[A k N] Square k N

abbrev AtLevel (p : TensorPower) (N : Level) : Type u :=
  match p with
  | .single => U k N
  | .square => Square k N
  | .leftCube => LeftCube k N
  | .rightCube => RightCube k N

instance levelRing (p : TensorPower) (N : Level) : Ring (AtLevel k p N) := by
  cases p <;> dsimp [AtLevel] <;> infer_instance

instance levelAlgebra (p : TensorPower) (N : Level) : Algebra (A k N) (AtLevel k p N) := by
  cases p <;> dsimp [AtLevel] <;> infer_instance

/-- The finite associativity identification over the actual truncated scalar ring. -/
def assocAt (N : Level) :
    LeftCube k N ≃ₐ[A k N] RightCube k N :=
  assoc (A k N) (A k N) (A k N) (U k N) (U k N) (U k N)

variable {k} {M N : Level}

private theorem squareReduce_scalar (e : M ≤ N) (a : A k N) :
    Coproduct.tensorReduce e (algebraMap (A k N) (Square k N) a) =
      algebraMap (A k M) (Square k M) (Truncations.reduce e a) := by
  change Coproduct.tensorReduce e ((algebraMap (A k N) (U k N) a) ⊗ₜ[A k N] (1 : U k N)) =
    (algebraMap (A k M) (U k M) (Truncations.reduce e a)) ⊗ₜ[A k M] (1 : U k M)
  rw [Coproduct.tensorReduce_tmul, Presentation.reduce_scalar, map_one]

section ChangeScalars

variable {R S B C B' C' : Type u}
  [CommRing R] [CommRing S] [Ring B] [Ring C] [Ring B'] [Ring C']
  [Algebra R B] [Algebra R C] [Algebra S B'] [Algebra S C']

open Algebra.TensorProduct (includeLeft includeRight lift)

/-- Tensoring algebra reductions whose coefficient rings also change. -/
def tensorChange (r : R →+* S) (f : B →+* B') (g : C →+* C')
    (hf : ∀ a, f (algebraMap R B a) = algebraMap S B' (r a))
    (hg : ∀ a, g (algebraMap R C a) = algebraMap S C' (r a)) :
    B ⊗[R] C →+* B' ⊗[S] C' :=
  letI : Algebra R (B' ⊗[S] C') := Algebra.compHom _ r
  let l : B' →ₐ[S] B' ⊗[S] C' := includeLeft
  let t : C' →ₐ[S] B' ⊗[S] C' := includeRight
  let lf : B →ₐ[R] B' ⊗[S] C' :=
    ⟨l.toRingHom.comp f, fun a => (congrArg l (hf a)).trans (l.commutes (r a))⟩
  let tg : C →ₐ[R] B' ⊗[S] C' :=
    ⟨t.toRingHom.comp g, fun a => (congrArg t (hg a)).trans (t.commutes (r a))⟩
  (lift lf tg (fun b c => (Commute.one_right (f b)).tmul (Commute.one_left (g c)))).toRingHom

@[simp] theorem tensorChange_tmul (r : R →+* S) (f : B →+* B') (g : C →+* C')
    (hf : ∀ a, f (algebraMap R B a) = algebraMap S B' (r a))
    (hg : ∀ a, g (algebraMap R C a) = algebraMap S C' (r a)) (b : B) (c : C) :
    tensorChange r f g hf hg (b ⊗ₜ[R] c) = f b ⊗ₜ[S] g c := by
  let : Algebra R (B' ⊗[S] C') := Algebra.compHom _ r
  simp only [tensorChange, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul]
  change (f b ⊗ₜ[S] (1 : C')) * ((1 : B') ⊗ₜ[S] g c) = f b ⊗ₜ[S] g c
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp] theorem tensorChange_scalar (r : R →+* S) (f : B →+* B') (g : C →+* C')
    (hf : ∀ a, f (algebraMap R B a) = algebraMap S B' (r a))
    (hg : ∀ a, g (algebraMap R C a) = algebraMap S C' (r a)) (a : R) :
    tensorChange r f g hf hg (algebraMap R (B ⊗[R] C) a) =
      algebraMap S (B' ⊗[S] C') (r a) := by
  change tensorChange r f g hf hg (algebraMap R B a ⊗ₜ[R] (1 : C)) =
    algebraMap S B' (r a) ⊗ₜ[S] (1 : C')
  rw [tensorChange_tmul, hf, map_one]

end ChangeScalars

/-- Simultaneous reduction of all the tensor factors, over the change of scalars. -/
def reduce (p : TensorPower) (e : M ≤ N) : AtLevel k p N →+* AtLevel k p M :=
  match p with
  | .single => Presentation.reduce e
  | .square => Coproduct.tensorReduce e
  | .leftCube =>
      tensorChange (Truncations.reduce (R := k) e).toRingHom
        (Coproduct.tensorReduce e) (Presentation.reduce e)
        (squareReduce_scalar (k := k) e) (Presentation.reduce_scalar e)
  | .rightCube =>
      tensorChange (Truncations.reduce (R := k) e).toRingHom
        (Presentation.reduce e) (Coproduct.tensorReduce e)
        (Presentation.reduce_scalar e) (squareReduce_scalar (k := k) e)

private theorem reduce_scalar (p : TensorPower) (e : M ≤ N) (a : A k N) :
    reduce p e (algebraMap (A k N) (AtLevel k p N) a) =
      algebraMap (A k M) (AtLevel k p M) (Truncations.reduce e a) := by
  cases p
  · exact Presentation.reduce_scalar e a
  · exact squareReduce_scalar e a
  · exact tensorChange_scalar (Truncations.reduce (R := k) e).toRingHom
      (Coproduct.tensorReduce e) (Presentation.reduce e)
      (squareReduce_scalar (k := k) e) (Presentation.reduce_scalar e) a
  · exact tensorChange_scalar (Truncations.reduce (R := k) e).toRingHom
      (Presentation.reduce e) (Coproduct.tensorReduce e)
      (Presentation.reduce_scalar e) (squareReduce_scalar (k := k) e) a

omit [CharZero k] in
private theorem reduce_truncate (e : M ≤ N) (f : PowerSeries k) :
    Truncations.reduce e (Truncations.truncate N f) = Truncations.truncate M f := by
  change Ideal.Quotient.mk (Truncations.truncationIdeal k M) (PowerSeries.trunc N f) =
    Ideal.Quotient.mk (Truncations.truncationIdeal k M) (PowerSeries.trunc M f)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Truncations.truncationIdeal,
    Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro j hj
  simp [PowerSeries.coeff_trunc, hj, lt_of_lt_of_le hj e]

variable (k)

/-- The scalar action at each level is through truncation of scalar power series. -/
instance levelPowerSeriesAlgebra (p : TensorPower) (N : Level) :
    Algebra (PowerSeries k) (AtLevel k p N) :=
  Algebra.compHom _ (Truncations.truncate N).toRingHom

/-- The subalgebra of the product consisting of compatible tuples. -/
def compatibleTuples (p : TensorPower) :
    Subalgebra (PowerSeries k) (∀ N : Level, AtLevel k p N) where
  carrier := {x | ∀ (M N : Level) (e : M ≤ N), reduce (k := k) p e (x N) = x M}
  zero_mem' := fun _ _ _ => map_zero _
  one_mem' := fun _ _ _ => map_one _
  add_mem' := fun hx hy M N e => by rw [Pi.add_apply, Pi.add_apply, map_add, hx M N e, hy M N e]
  mul_mem' := fun hx hy M N e => by rw [Pi.mul_apply, Pi.mul_apply, map_mul, hx M N e, hy M N e]
  algebraMap_mem' f M N e := by
    change reduce p e (algebraMap (A k N) (AtLevel k p N) (Truncations.truncate N f)) =
      algebraMap (A k M) (AtLevel k p M) (Truncations.truncate M f)
    rw [reduce_scalar, reduce_truncate]

/-- The inverse limit, with pointwise algebra operations on compatible tuples. -/
abbrev Limit (p : TensorPower) : Type u := compatibleTuples k p

abbrev Uh := Limit k .single
abbrev CompletedSquare := Limit k .square
abbrev CompletedLeftCube := Limit k .leftCube
abbrev CompletedRightCube := Limit k .rightCube

/-- Projection to the finite truncation level. -/
def project (p : TensorPower) (N : Level) : Limit k p →ₐ[PowerSeries k] AtLevel k p N :=
  (Pi.evalAlgHom (PowerSeries k) (fun n : Level => AtLevel k p n) N).comp
    (compatibleTuples k p).val

/-- The inverse-limit topology, with each quotient given the discrete topology. -/
instance limitTopology (p : TensorPower) : TopologicalSpace (Limit k p) :=
  ⨅ N : Level, TopologicalSpace.induced (project k p N) ⊥

/-- Module-valued formal series, with finite support in the PBW indices at each degree. -/
def Series (ι : Type) := HahnModule ℕ k (ι →₀ k)
deriving AddCommGroup

instance seriesModule (ι : Type) : Module (PowerSeries k) (Series k ι) :=
  Module.compHom (HahnModule ℕ k (ι →₀ k))
    HahnSeries.toPowerSeries.symm.toRingHom

/-- PBW coefficient of the specified degree, as one finitely supported vector. -/
def seriesCoeff {ι : Type} (n : ℕ) (x : Series k ι) : ι →₀ k :=
  ((HahnModule.of k).symm x).coeff n

/-- Product topology on the sequence of discrete coefficient spaces. -/
instance seriesTopology (ι : Type) : TopologicalSpace (Series k ι) :=
  ⨅ n : ℕ, TopologicalSpace.induced (seriesCoeff k (ι := ι) n) ⊥

/-- The ordered PBW monomial at the single-algebra level. -/
def monomial (N : Level) (i : PBWIndex) : U k N :=
  TriangularPBW.orderedMonomial (truncated k N) i.1.1
    (∏ l : Root, (MvPolynomial.X l : TruncatedCartan k N) ^ i.1.2 l) i.2

/-- The monomial tensor family in each finite-level algebra. -/
def basisVector (p : TensorPower) (N : Level) : Index p → AtLevel k p N :=
  match p with
  | .single => monomial k N
  | .square => fun i => monomial k N i.1 ⊗ₜ[A k N] monomial k N i.2
  | .leftCube => fun i =>
      (monomial k N i.1.1 ⊗ₜ[A k N] monomial k N i.1.2) ⊗ₜ[A k N] monomial k N i.2
  | .rightCube => fun i =>
      monomial k N i.1 ⊗ₜ[A k N] (monomial k N i.2.1 ⊗ₜ[A k N] monomial k N i.2.2)

/-- The level reductions are the transition maps of an inverse system. -/
def TransitionLawsProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (p : TensorPower),
    (∀ N : Level, reduce (k := k) p (le_refl N) = RingHom.id (AtLevel k p N)) ∧
    ∀ (L M N : Level) (d : L ≤ M) (e : M ≤ N),
      (reduce (k := k) p d).comp (reduce (k := k) p e) = reduce (k := k) p (d.trans e)

/-- The bases have the indicated ordered monomials and commute with the level maps. -/
def CompatibleBasesProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (p : TensorPower),
    (∃ b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N),
      ∀ N i, b N i = basisVector k p N i) ∧
    ∀ (M N : Level) (e : M ≤ N) (i : Index p),
      reduce (k := k) p e (basisVector k p N i) = basisVector k p M i

/-- Topological freeness with the precise PBW coefficients of every finite projection. -/
def SeriesDescriptionProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (p : TensorPower),
    ∃ b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N),
      (∀ N i, b N i = basisVector k p N i) ∧
      ∃ c : Limit k p ≃ₗ[PowerSeries k] Series k (Index p),
        Continuous c ∧ Continuous c.symm ∧
        ∀ (N : Level) (n : Fin N) (x : Limit k p) (i : Index p),
          seriesCoeff k n (c x) i = Truncations.coeff n ((b N).repr (project k p N x) i)

/-- Scalar power series act by convolution of the coefficients. -/
def ScalarConvolutionProp : Prop :=
  ∀ (k : Type u) [Field k] (ι : Type) (f : PowerSeries k) (x : Series k ι) (n : ℕ),
    seriesCoeff k n (f • x) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff ab.1 f • seriesCoeff k ab.2 x

/-- The formal parameter acts injectively, the projections give the indicated
reductions, and the inverse-limit topology is the adic topology. -/
def ReductionProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (p : TensorPower),
    Function.Injective ((PowerSeries.X : PowerSeries k) • · : Limit k p → Limit k p) ∧
    (∀ (N : Level), Function.Surjective (project k p N) ∧
      ∀ x : Limit k p, project k p N x = 0 ↔
        ∃ y : Limit k p, (PowerSeries.X : PowerSeries k) ^ (N : ℕ) • y = x) ∧
    limitTopology k p =
      (Ideal.span {(PowerSeries.X : PowerSeries k)}).adicModuleTopology (Limit k p)

/-- Every sequence is allowed, with finiteness required separately at each degree. -/
def SeriesCoefficientsProp : Prop :=
  ∀ (k : Type u) [Field k] (ι : Type),
    Function.Bijective (fun x : Series k ι => fun n => seriesCoeff k n x)

/-- The scalar series ring carries its formal-parameter adic topology. -/
abbrev scalarTopology : TopologicalSpace (PowerSeries k) :=
  (Ideal.span {(PowerSeries.X : PowerSeries k)}).adicTopology

/-- The algebra and all the completed tensor powers are topological algebras. -/
def TopologicalAlgebrasProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (p : TensorPower),
    letI := scalarTopology k
    IsTopologicalRing (Limit k p) ∧ ContinuousSMul (PowerSeries k) (Limit k p)

/-- The completed Hopf operations and the tensor operations appearing in their axioms. -/
structure HopfMaps where
  comul : Uh k →ₐ[PowerSeries k] CompletedSquare k
  counit : Uh k →ₐ[PowerSeries k] PowerSeries k
  antipode : Uh k →ₐ[PowerSeries k] (Uh k)ᵐᵒᵖ
  comulLeft : CompletedSquare k →ₐ[PowerSeries k] CompletedLeftCube k
  comulRight : CompletedSquare k →ₐ[PowerSeries k] CompletedRightCube k
  associate : CompletedLeftCube k ≃ₐ[PowerSeries k] CompletedRightCube k
  counitLeft : CompletedSquare k →ₐ[PowerSeries k] Uh k
  counitRight : CompletedSquare k →ₐ[PowerSeries k] Uh k
  antipodeLeft : CompletedSquare k →ₗ[PowerSeries k] CompletedSquare k
  antipodeRight : CompletedSquare k →ₗ[PowerSeries k] CompletedSquare k
  multiply : CompletedSquare k →ₗ[PowerSeries k] Uh k

variable {k}

/-- The actual finite-level maps obtained by projecting each completed operation. -/
structure ProjectsTo (D : HopfMaps k)
    (d : ∀ N : Level, Coproduct.TruncatedData k N)
    (s : ∀ N : Level, Hopf.TruncatedData k N (d N)) : Prop where
  comul (N : Level) (x : Uh k) :
    project k .square N (D.comul x) = (d N).comul (project k .single N x)
  counit (N : Level) (x : Uh k) :
    Truncations.truncate N (D.counit x) = (d N).counit (project k .single N x)
  antipode (N : Level) (x : Uh k) :
    project k .single N (D.antipode x).unop =
      Hopf.antipodeLinear (s N).antipode (project k .single N x)
  comulLeft (N : Level) (x : CompletedSquare k) :
    project k .leftCube N (D.comulLeft x) =
      Algebra.TensorProduct.map (d N).comul (AlgHom.id (A k N) (U k N)) (project k .square N x)
  comulRight (N : Level) (x : CompletedSquare k) :
    project k .rightCube N (D.comulRight x) =
      Algebra.TensorProduct.map (AlgHom.id (A k N) (U k N)) (d N).comul (project k .square N x)
  associate (N : Level) (x : CompletedLeftCube k) :
    project k .rightCube N (D.associate x) = assocAt k N (project k .leftCube N x)
  counitLeft (N : Level) (x : CompletedSquare k) :
    project k .single N (D.counitLeft x) =
      lid (A k N) (U k N)
        (Algebra.TensorProduct.map (d N).counit (AlgHom.id (A k N) (U k N))
          (project k .square N x))
  counitRight (N : Level) (x : CompletedSquare k) :
    project k .single N (D.counitRight x) =
      rid (A k N) (A k N) (U k N)
        (Algebra.TensorProduct.map (AlgHom.id (A k N) (U k N)) (d N).counit
          (project k .square N x))
  antipodeLeft (N : Level) (x : CompletedSquare k) :
    project k .square N (D.antipodeLeft x) =
      (Hopf.antipodeLinear (s N).antipode).rTensor (U k N) (project k .square N x)
  antipodeRight (N : Level) (x : CompletedSquare k) :
    project k .square N (D.antipodeRight x) =
      (Hopf.antipodeLinear (s N).antipode).lTensor (U k N) (project k .square N x)
  multiply (N : Level) (x : CompletedSquare k) :
    project k .single N (D.multiply x) = LinearMap.mul' (A k N) (U k N) (project k .square N x)

/-- The associativity, counit and antipode identities on the completed tensor powers. -/
structure HopfIdentities (D : HopfMaps k) : Prop where
  coassoc (x : Uh k) : D.associate (D.comulLeft (D.comul x)) = D.comulRight (D.comul x)
  left_counit (x : Uh k) : D.counitLeft (D.comul x) = x
  right_counit (x : Uh k) : D.counitRight (D.comul x) = x
  left_antipode (x : Uh k) :
    D.multiply (D.antipodeLeft (D.comul x)) = algebraMap (PowerSeries k) (Uh k) (D.counit x)
  right_antipode (x : Uh k) :
    D.multiply (D.antipodeRight (D.comul x)) = algebraMap (PowerSeries k) (Uh k) (D.counit x)
  antipode_bijective : Function.Bijective (fun x : Uh k => (D.antipode x).unop)

/-- Continuity of the completed structure maps. -/
structure ContinuousHopfMaps (D : HopfMaps k) : Prop where
  comul : Continuous D.comul
  counit : @Continuous (Uh k) (PowerSeries k) (limitTopology k .single) (scalarTopology k) D.counit
  antipode : Continuous (fun x : Uh k => (D.antipode x).unop)
  comulLeft : Continuous D.comulLeft
  comulRight : Continuous D.comulRight
  associate : Continuous D.associate
  associate_inv : Continuous D.associate.symm
  counitLeft : Continuous D.counitLeft
  counitRight : Continuous D.counitRight
  antipodeLeft : Continuous D.antipodeLeft
  antipodeRight : Continuous D.antipodeRight
  multiply : Continuous D.multiply

/-- Existence of the completed Hopf structure on the actual compatible-tuple
algebra, with the prescribed finite Hopf operations and completed tensors. -/
def CompletedHopfProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (d : ∀ N : Level, Coproduct.TruncatedData k N)
      (s : ∀ N : Level, Hopf.TruncatedData k N (d N)) (D : HopfMaps k),
      ProjectsTo D d s ∧ HopfIdentities D ∧ ContinuousHopfMaps D

variable (k)

def UhType := type_of% (@Uh)
def CompletedSquareType := type_of% (@CompletedSquare)
def CompletedLeftCubeType := type_of% (@CompletedLeftCube)
def CompletedRightCubeType := type_of% (@CompletedRightCube)
def ProjectType := type_of% (@project)

end Specs.LieNotes.Quantum.Completion
