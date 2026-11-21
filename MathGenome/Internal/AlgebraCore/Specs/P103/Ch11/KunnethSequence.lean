import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsHomology
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethTotalConnector
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethOppositeInterchange

/-!
Independent interface for the nonsplit Künneth sequence, paper.tex
3050–3108 and 3166–3168. All modules, homology quotients, and the signed
coproduct tensor total are the existing canonical upstream objects.

The first-factor sequence is normalized by the positive total connector and
the canonical Tor kernel identification. Both orientations include naturality
in the two complex variables and all projective models for the Tor terms.
-/
namespace P103.Specs.Ch11.KunnethSequence
open CategoryTheory DirectSum
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.UniversalCoefficientsHomology
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {R : Type u} [Ring R]

abbrev RightComplex (R : Type u) [Ring R] := ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ
abbrev LeftComplex (R : Type u) [Ring R] := ChainComplex (ModuleCat.{w} R) ℕ

/-- The source's tensor diagonal, indexed without truncating subtraction. -/
abbrev Diagonal (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 = n}
/-- This index is empty at n=0 and is the (n-1)-diagonal at n>0. -/
abbrev TailDiagonal (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 + 1 = n}

abbrev TensorTerm (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (i : ℕ × ℕ) := Tensor R (Homology C i.1) (Homology D i.2)
abbrev TensorDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :=
  ⨁ i : Diagonal n, TensorTerm C D i.val

abbrev HomologyModels (C : RightComplex.{u,v} R) :=
  ∀ p, ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C p))

abbrev TorTerm (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (i : ℕ × ℕ) :=
  TorWith (P i.1).val (Homology D i.2) 1
abbrev TorDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ) :=
  ⨁ i : TailDiagonal n, TorTerm C D P i.val

/-- The prescribed functorial map on the tensor diagonal. -/
def tensorDiagonalMap {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    TensorDiagonal C D n →ₗ[ℤ] TensorDiagonal C' D' n :=
  DirectSum.lmap (fun i : Diagonal n =>
    tensorMap (homologyMap f i.val.1) (homologyMap g i.val.2))

/-- The prescribed map on the Tor diagonal permits every projective model. -/
def torDiagonalMap {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} R 1) (n : ℕ) :
    TorDiagonal C D P n →ₗ[ℤ] TorDiagonal C' D' P' n :=
  DirectSum.lmap (fun i : TailDiagonal n =>
    (T.map (P i.val.1) (P' i.val.1)
      (ModuleCat.ofHom (homologyMap f i.val.1))
      (ModuleCat.ofHom (homologyMap g i.val.2))).toAddMonoidHom.toIntLinearMap)

/-- The source's formula for α, specified on all actual cycle representatives.
Existence of the tensor cycle is a separate proved target below. -/
def AlphaFormula (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ)
    (α : TensorDiagonal C D n →ₗ[ℤ] Homology (ordinaryTotal C D) n) : Prop :=
  ∀ (i : Diagonal n) (c : cycles C i.val.1) (x : cycles D i.val.2)
    (z : cycles (ordinaryTotal C D) n),
    z.val = ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R c.val x.val) →
    α (DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i
      (tmul R (homologyClass C i.val.1 c) (homologyClass D i.val.2 x))) =
      homologyClass (ordinaryTotal C D) n z

/-- Short exact sequence data with the prescribed elementary class formula. -/
structure DegreeSequence (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ) where
  α : TensorDiagonal C D n →ₗ[ℤ] Homology (ordinaryTotal C D) n
  β : Homology (ordinaryTotal C D) n →ₗ[ℤ] TorDiagonal C D P n
  injective_α : Function.Injective α
  exact : Function.Exact α β
  surjective_β : Function.Surjective β
  α_formula : AlphaFormula C D n α

/-- Genuine flatness on the second side, with no commutativity assumption. -/
def LeftFlatTermsAndBoundaries (D : LeftComplex.{u,w} R) : Prop :=
  (∀ q, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (D.X q)) ∧
  (∀ q, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (boundaries D q))

/-- An elementary tensor of cycles is an actual cycle of the signed total.
This statement is independent of either flatness hypothesis. -/
def pure_tensor_cycleType : Prop :=
  ∀ (R : Type u) [Ring R] (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (p q n : ℕ) (h : p+q=n) (c : cycles C p) (x : cycles D q),
    ordinaryInclusion C D p q n h (tmul R c.val x.val) ∈ cycles (ordinaryTotal C D) n

/-- Naturality on actual representatives, before descending to homology. -/
def pure_tensor_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (C C' : RightComplex.{u,v} R)
    (D D' : LeftComplex.{u,w} R) (f : C ⟶ C') (g : D ⟶ D')
    (p q n : ℕ) (h : p+q=n) (c : cycles C p) (x : cycles D q),
    ((ordinaryTotalMap f g).f n).hom
      (ordinaryInclusion C D p q n h (tmul R c.val x.val)) =
    ordinaryInclusion C' D' p q n h
      (tmul R (cyclesMap f p c).val (cyclesMap g q x).val)

/-- The prescribed cycle formula forces simultaneous naturality of α,
without any flatness or exactness hypotheses. -/
def alpha_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (C C' : RightComplex.{u,v} R)
    (D D' : LeftComplex.{u,w} R) (f : C ⟶ C') (g : D ⟶ D') (n : ℕ)
    (α : TensorDiagonal C D n →ₗ[ℤ] Homology (ordinaryTotal C D) n)
    (α' : TensorDiagonal C' D' n →ₗ[ℤ] Homology (ordinaryTotal C' D') n),
    AlphaFormula C D n α → AlphaFormula C' D' n α' →
    ((homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap).comp α =
      α'.comp (tensorDiagonalMap f g n)

/-- The actual right Tor formula has a zero tail in degree zero, for every
projective model, including arbitrary sizes and the zero ring. -/
def tor_diagonal_zeroType : Prop :=
  ∀ (R : Type u) [Ring R] (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C), Subsingleton (TorDiagonal C D P 0)

/-- The source's cycle-flatness consequence, using the same test universe
as the left complex. This is reused from universal coefficients. -/
def cycles_flatType : Prop :=
  ∀ (R : Type u) [Ring R] (C : RightComplex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C →
    ∀ p, P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,w} R (cycles C p)


abbrev CycleDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :=
  P103.Specs.Ch11.KunnethFlatColumns.DiagonalTensor (cycleTerms C) D n

abbrev BoundaryDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :=
  ⨁ i : Diagonal n, Tensor R (boundaries C i.val.1) (Homology D i.val.2)

def jDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    BoundaryDiagonal C D n →ₗ[ℤ] CycleDiagonal C D n :=
  DirectSum.lmap (fun i : Diagonal n =>
    jTensor C (ModuleCat.of R (Homology D i.val.2)) i.val.1)

def qDiagonal (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (n : ℕ) :
    CycleDiagonal C D n →ₗ[ℤ] TensorDiagonal C D n :=
  DirectSum.lmap (fun i : Diagonal n =>
    tensorMap (homologyClass C i.val.1) (LinearMap.id : Homology D i.val.2 →ₗ[R] _))

abbrev ComponentKernel (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) (i : ℕ × ℕ) :=
  LinearMap.ker (jTensor C (ModuleCat.of R (Homology D i.2)) i.1)

/-- Insert the canonical Tor kernel in the actual shifted-boundary diagonal. -/
def torBoundaryMap (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ)
    (e : ∀ i : TailDiagonal n, TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val) :
    TorDiagonal C D P n →ₗ[ℤ]
      P103.Specs.Ch11.KunnethFlatColumns.DiagonalTensor (shiftedBoundaryTerms C) D n :=
  DirectSum.toModule ℤ _ _ (fun i : TailDiagonal n =>
    (DirectSum.lof ℤ _
      (fun j : Diagonal n => Tensor R (shiftedBoundaryTerms C j.val.1) (Homology D j.val.2))
      (⟨(i.val.1+1,i.val.2),by have := i.property; omega⟩ : Diagonal n)).comp
        (((ComponentKernel C D i.val).subtype.toAddMonoidHom.comp (e i).toAddMonoidHom).toIntLinearMap))

/-- Exactness together with the connector-normalized last arrow. -/
structure NormalizedDegreeSequence (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ) extends DegreeSequence C D P n where
  boundaryEquiv : P103.Specs.Ch11.KunnethFlatColumns.DiagonalTensor
      (shiftedBoundaryTerms C) D n ≃ₗ[ℤ]
        Homology (ordinaryTotal (shiftedBoundaryComplex C) D) n
  boundaryEquiv_formula : P103.Specs.Ch11.KunnethFlatColumns.DiagonalFormula
    (shiftedBoundaryTerms C) D n boundaryEquiv
  kernelIso : ∀ i : TailDiagonal n, TorTerm C D P i.val ≃ₗ[ℤ] ComponentKernel C D i.val
  kernelIso_canonical : ∀ i : TailDiagonal n,
    ∃ e : TorWith (P i.val.1).val (ModuleCat.of R (Homology D i.val.2)) 1 ≃ₗ[ℤ]
        LinearMap.ker (jTensor C (ModuleCat.of R (Homology D i.val.2)) i.val.1),
      TorKernelIdentification C (ModuleCat.of R (Homology D i.val.2)) i.val.1 (P i.val.1) e ∧
      ∀ x, kernelIso i x = e x
  β_formula : ∀ x, boundaryEquiv (torBoundaryMap C D P n kernelIso (β x)) =
    homologyMap (P103.Specs.Ch11.KunnethTotalConnector.projection C D) n x

def right_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R] (C : RightComplex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C → ∀ (D : LeftComplex.{u,w} R)
      (P : HomologyModels C) (n : ℕ), Nonempty (NormalizedDegreeSequence C D P n)

/-- Naturality for every normalized choice, including changes of Tor model. -/
def normalized_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (C C' : RightComplex.{u,v} R)
    (D D' : LeftComplex.{u,w} R) (f : C ⟶ C') (g : D ⟶ D')
    (P : HomologyModels C) (P' : HomologyModels C') (T : TorMaps.{u,v,w} R 1) (n : ℕ)
    (S : NormalizedDegreeSequence C D P n) (S' : NormalizedDegreeSequence C' D' P' n),
    ((homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap).comp S.α =
      S'.α.comp (tensorDiagonalMap f g n) ∧
    (torDiagonalMap f g P P' T n).comp S.β =
      S'.β.comp (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap

/-- Signed interchange on the tensor diagonal.  The scalar transport on
homology is the actual quotient-homology equivalence of the opposite-ring
interface, and the sign is the sign on the total complex itself. -/
def signedTensorInterchange (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (n : ℕ) :
    TensorDiagonal C D n →ₗ[ℤ]
      TensorDiagonal (P103.Specs.Ch11.KunnethOppositeInterchange.doubleOppositeComplex D) C n :=
  DirectSum.toModule ℤ _ _ (fun i : Diagonal n => by
    letI := P103.Specs.Ch02.FlatnessTests.doubleOppositeModule R (Homology D i.val.2)
    exact
      (DirectSum.lof ℤ _ _ (⟨(i.val.2,i.val.1),by have := i.property; omega⟩ : Diagonal n)).comp
        (((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
          (tensorMap
            (P103.Specs.Ch11.KunnethOppositeInterchange.homologyScalarEquiv D i.val.2).symm.toLinearMap
            (LinearMap.id : Homology C i.val.1 →ₗ[Rᵐᵒᵖ] _)).comp
          (P103.Specs.Ch11.KunnethOppositeInterchange.tensorFlip
            (Homology C i.val.1) (Homology D i.val.2)).toLinearMap))

/-- Tor interchange on one pair of homology degrees, including all projective
models on the two sides. The source is stated on the swapped Tor term itself. -/
def torInterchangeComponent (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C)
    (Q : HomologyModels
      (P103.Specs.Ch11.KunnethOppositeInterchange.doubleOppositeComplex D))
    (T : P103.Specs.Ch11.KunnethOppositeInterchange.AllModelTorTransport.{u,v,w} R)
    (p q : ℕ) :
    TorTerm (P103.Specs.Ch11.KunnethOppositeInterchange.doubleOppositeComplex D) C Q (q,p)
      ≃ₗ[ℤ] TorTerm C D P (p,q) := by
  letI := P103.Specs.Ch02.FlatnessTests.doubleOppositeModule R (Homology D q)
  exact T.equiv (ModuleCat.of Rᵐᵒᵖ (Homology C p)) (ModuleCat.of R (Homology D q))
    (P p).val (P p).property (Q q).val (Q q).property 1

/-- The second-factor sequence is the transport of the normalized first-factor
sequence over the opposite ring.  The total interchange carries its Koszul
sign, the tensor diagonal carries the same sign, and the Tor tail uses the
canonical all-model Tor interchange with `(-1)^(pq)`.  These equations fix the last arrow;
naturality alone would still permit a natural automorphism of every Tor term. -/
def LeftNormalization (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (n : ℕ) (S : DegreeSequence C D P n) : Prop :=
  ∃ (I : P103.Specs.Ch11.KunnethOppositeInterchange.SignedInterchange.{u,v,w} R)
    (T : P103.Specs.Ch11.KunnethOppositeInterchange.AllModelTorTransport.{u,v,w} R)
    (Q : HomologyModels
      (P103.Specs.Ch11.KunnethOppositeInterchange.doubleOppositeComplex D))
    (N : NormalizedDegreeSequence
      (P103.Specs.Ch11.KunnethOppositeInterchange.doubleOppositeComplex D) C Q n),
    (homologyMap (I.iso C D).hom n).toAddMonoidHom.toIntLinearMap.comp S.α =
      N.α.comp (signedTensorInterchange C D n) ∧
    ∀ (x : Homology (ordinaryTotal C D) n) (i : TailDiagonal n),
      (S.β x) i = ((i.val.1 : ℤ) * (i.val.2 : ℤ)).negOnePow •
        torInterchangeComponent C D P Q T i.val.1 i.val.2
          ((N.β (homologyMap (I.iso C D).hom n x))
            (⟨(i.val.2,i.val.1),by have := i.property; omega⟩ : TailDiagonal n))

/-- The second-factor version has the same right-left tensor and Tor terms. -/
def left_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R] (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
    LeftFlatTermsAndBoundaries.{u,v,w} D → ∀ (P : HomologyModels C) (n : ℕ),
      Nonempty (DegreeSequence C D P n)

/-- A simultaneous natural family for flatness in the second complex. -/
structure LeftSequenceFamily (R : Type u) [Ring R] where
  sequence : ∀ (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
    LeftFlatTermsAndBoundaries.{u,v,w} D → ∀ (P : HomologyModels C) (n : ℕ),
      DegreeSequence C D P n
  normalization : ∀ (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D) (P : HomologyModels C) (n : ℕ),
      LeftNormalization C D P n (sequence C D hD P n)
  naturality : ∀ (C C' : RightComplex.{u,v} R) (D D' : LeftComplex.{u,w} R)
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D)
    (hD' : LeftFlatTermsAndBoundaries.{u,v,w} D')
    (f : C ⟶ C') (g : D ⟶ D') (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} R 1) (n : ℕ),
    ((homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap).comp
        (sequence C D hD P n).α =
      (sequence C' D' hD' P' n).α.comp (tensorDiagonalMap f g n) ∧
    (torDiagonalMap f g P P' T n).comp (sequence C D hD P n).β =
      (sequence C' D' hD' P' n).β.comp
        (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap

def left_natural_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (LeftSequenceFamily.{u,v,w} R)


/-- Coefficient scalar multiplication on the tensor homology diagonal. -/
def tensorScalarDiagonal {K : Type u} [CommRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K) (n : ℕ) (r : K) :
    TensorDiagonal C D n →ₗ[ℤ] TensorDiagonal C D n :=
  DirectSum.lmap (fun i : Diagonal n => tensorMap
    (LinearMap.id : Homology C i.val.1 →ₗ[Kᵐᵒᵖ] _)
    (scalarMap (ModuleCat.of K (Homology D i.val.2)) r).hom)

/-- Scalar compatibility through the actual coefficient scalar endomorphism.
The representative formulas specify the natural actions on tensors and the
signed total, while the Tor summands use the established `torModule` action. -/
def ScalarCompatibility {K : Type u} [CommRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K) (P : HomologyModels C)
    (T : TorMaps.{u,v,w} K 1) (n : ℕ) (S : DegreeSequence C D P n) : Prop :=
  ∀ r : K, ∃ σ : D ⟶ D,
    (∀ q (x : D.X q), (σ.f q).hom x = r • x) ∧
    (∀ q (x : Homology D q), homologyMap σ q x = r • x) ∧
    (∀ (p q : ℕ) (h : p+q=n) (c : C.X p) (x : D.X q),
      ((ordinaryTotalMap (𝟙 C) σ).f n).hom
        (ordinaryInclusion C D p q n h (tmul K c x)) =
      ordinaryInclusion C D p q n h (tmul K c (r • x))) ∧
    (∀ (i : Diagonal n) (a : Homology C i.val.1) (b : Homology D i.val.2),
      tensorScalarDiagonal C D n r (DirectSum.lof ℤ _ _ i (tmul K a b)) =
        DirectSum.lof ℤ _ _ i (tmul K a (r • b))) ∧
    ((homologyMap (ordinaryTotalMap (𝟙 C) σ) n).toAddMonoidHom.toIntLinearMap).comp S.α =
      S.α.comp (tensorScalarDiagonal C D n r) ∧
    ∀ (x : Homology (ordinaryTotal C D) n) (i : TailDiagonal n),
      letI := torModule T (P i.val.1) (ModuleCat.of K (Homology D i.val.2))
      (S.β (homologyMap (ordinaryTotalMap (𝟙 C) σ) n x)) i = r • (S.β x) i

/-- Both coefficient sequences obey the chapter's commutative scalar convention. -/
def scalar_compatibilityType : Prop :=
  ∀ (K : Type u) [CommRing K],
    (∀ (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K) (P : HomologyModels C)
      (T : TorMaps.{u,v,w} K 1) (n : ℕ) (S : NormalizedDegreeSequence C D P n),
      ScalarCompatibility C D P T n S.toDegreeSequence) ∧
    ∀ (L : LeftSequenceFamily.{u,v,w} K) (C : RightComplex.{u,v} K)
      (D : LeftComplex.{u,w} K) (hD : LeftFlatTermsAndBoundaries.{u,v,w} D)
      (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ),
      ScalarCompatibility C D P T n (L.sequence C D hD P n)

end
end P103.Specs.Ch11.KunnethSequence
