import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.FrameParameters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntrinsicCubic

namespace LinearAlgebraicGroups.Albert.TrialitySpecification

open CliffordAlgebra Module _root_.LinearAlgebraicGroups.Composition
open Composition.ZornSpecification Composition.AdjointSpecification
open HermitianSpecification CubicSpecification FrameSpecification QuadraticOperatorSpecification

open scoped TensorProduct

universe u v w

abbrev OctonionLinearGroup (R : Type u) [CommRing R] := Zorn R ≃ₗ[R] Zorn R

abbrev Triple (R : Type u) [CommRing R] := Fin 3 → OctonionLinearGroup R

variable {R : Type u} [CommRing R]

/-- The three cyclic product identities in the cyclic Hermitian block convention. -/
def IsRelated (h : Triple R) : Prop :=
  (∀ i x, norm R (h i x) = norm R x) ∧
  ∀ i x y, h i (conjugate (norm R) (x * y)) =
    conjugate (norm R) (h (cyclicNext i) x * h (cyclicPrev i) y)

/-- The group of related triples, with componentwise composition. -/
def relatedTriples : Subgroup (Triple R) where
  carrier := {h | IsRelated h}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun i x => (hg.1 i (h i x)).trans (hh.1 i x), fun i x y =>
      (congrArg (g i) (hh.2 i x y)).trans (hg.2 i (h (cyclicNext i) x) (h (cyclicPrev i) y))⟩
  inv_mem' := by
    intro g hg
    constructor
    · intro i x
      simpa using (hg.1 i ((g i).symm x)).symm
    · intro i x y
      apply (g i).injective
      simpa using (hg.2 i ((g (cyclicNext i)).symm x) ((g (cyclicPrev i)).symm y)).symm

abbrev Model (R : Type u) [CommRing R] := Coordinates R (Zorn R)

abbrev modelOp : Model R → Model R → Model R := applyOperator (norm R) (fun _ => 1)

/-- Automorphisms of the split quadratic operator fixing the three diagonal idempotents. -/
def FixesFrame (g : Model R ≃ₗ[R] Model R) : Prop :=
  (∀ i, g (frameAxis i) = frameAxis i) ∧ ∀ x y, g (modelOp x y) = modelOp (g x) (g y)

def frameStabilizer : Subgroup (Model R ≃ₗ[R] Model R) where
  carrier := {g | FixesFrame g}
  one_mem' := ⟨fun _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun i => (congrArg g (hh.1 i)).trans (hg.1 i), fun x y =>
      (congrArg g (hh.2 x y)).trans (hg.2 (h x) (h y))⟩
  inv_mem' := by
    intro g hg
    constructor
    · intro i
      apply g.injective
      simpa using (hg.1 i).symm
    · intro x y
      apply g.injective
      simpa using (hg.2 (g.symm x) (g.symm y)).symm

def RelatedTriplesType :=
  ∀ (R : Type u) [CommRing R], Subgroup (Triple R)

def FrameStabilizerType :=
  ∀ (R : Type u) [CommRing R], Subgroup (Model R ≃ₗ[R] Model R)

abbrev CliffordUnits (R : Type u) [CommRing R] := (CliffordAlgebra (norm R))ˣ

/-- The reversion-norm-one even units in the actual Clifford algebra of the test ring. -/
def IsSpin (s : CliffordUnits R) : Prop :=
  (s : CliffordAlgebra (norm R)) ∈ evenOdd (norm R) 0 ∧ reverse (s : CliffordAlgebra (norm R)) * s = 1 ∧
    (fun x : CliffordAlgebra (norm R) => s * x * ↑s⁻¹) '' LinearMap.range (ι (norm R)) =
      LinearMap.range (ι (norm R))

/-- The canonical identification of a triple by the two diagonal Clifford blocks and
the action on the octonion vector module. -/
def Corresponds (e : CliffordAlgebra (norm R) →ₐ[R] Module.End R (Zorn R × Zorn R))
    (h : Triple R) (s : CliffordUnits R) : Prop :=
  (∀ x y, e s (x, y) = (conjugate (norm R) (h 0 (conjugate (norm R) x)), h 2 y)) ∧
  ∀ c, (s : CliffordAlgebra (norm R)) * ι (norm R) c = ι (norm R) (h 1 c) * s

/-- Every related triple has a unique spin lift, and every spin element gives a
unique related triple, through the specified Clifford action. -/
def CliffordTriality : Prop :=
  ∀ (R : Type u) [CommRing R]
    (e : CliffordAlgebra (norm R) ≃ₐ[R] Module.End R (Zorn R × Zorn R)),
    (∀ c, e (ι _ c) = CliffordSpecification.octonionOperator c) →
    (∀ a, a ∈ evenOdd (norm R) 0 ↔
      (∀ x, (e a (x, 0)).2 = 0) ∧ (∀ y, (e a (0, y)).1 = 0)) →
    (∀ a, LinearMap.IsAdjointPair CliffordSpecification.octonionPairing
      CliffordSpecification.octonionPairing (e a) (e (reverse a))) →
    (∀ h : relatedTriples (R := R), ∃! s : CliffordUnits R, IsSpin s ∧ Corresponds e h s) ∧
    ∀ s : CliffordUnits R, IsSpin s → ∃! h : relatedTriples (R := R), Corresponds e h s

/-- Identification of the related-triple action with the ordered frame stabilizer. -/
def FrameTriality : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : relatedTriples (R := R) ≃* frameStabilizer (R := R),
      ∀ (h : relatedTriples (R := R)) (x : Model R),
        (e h).val x = (x.1, fun i => h.val i (x.2 i))

/-- The actual quadratic Jordan law and the ground operator give the same
pointwise stabilizer in the split coordinates. -/
def FrameLaw : Prop :=
  ∀ (R : Type u) [CommRing R] (J : SplitSpecification.ParaQuadratic R (Model R)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∀ g : Model R ≃ₗ[R] Model R,
      FixesFrame g ↔ (∀ i, g (frameAxis i) = frameAxis i) ∧ J.IsIso J g


/-- A split Albert model with its intrinsic cubic norm. Its pointwise frame
stabilizer is the one obtained from the unit and the norm polynomial law. -/
def CubicFrameStabilizer : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (J : _root_.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan R (Model R))
      (F : IntrinsicCubicSpecification.Coefficients R (Model R)),
      let K := SplitSpecification.ParaQuadratic.ofJordan J
      J.unit = cubicUnit ∧ (∀ x y, J.groundOp x y = modelOp x y) ∧
      SplitSpecification.IsAlbert K ∧
      IntrinsicCubicSpecification.IsCharacteristic K F ∧
      IntrinsicCubicSpecification.AgreesOnCharts K F ∧
      ∀ g : Model R ≃ₗ[R] Model R, FixesFrame g ↔
        (∀ i, g (frameAxis i) = frameAxis i) ∧
        IntrinsicCubicSpecification.PreservesNorm K F g.toLinearMap

/-- Scalar maps on the three diagonal and three octonion coordinates. -/
def mapModel {S T : Type v} [CommRing S] [CommRing T] (f : S →+* T)
    (x : Model S) : Model T :=
  (fun i => f (x.1 i), fun i => mapCoordinates f (x.2 i))

/-- The base-change identification of the split Albert coordinates. -/
noncomputable def modelBaseChange (S T : Type v) [CommRing S] [CommRing T] [Algebra S T] :
    T ⊗[S] Model S ≃ₗ[T] Model T :=
  (coordinatesBaseChange T).trans
    ((LinearEquiv.refl T (Fin 3 → T)).prodCongr
      (LinearEquiv.piCongrRight fun _ : Fin 3 => ZornSpecification.baseChange S T))

/-- The extensions of the triple and frame actions under the canonical tensor identifications. -/
def ExtendsActions {S T : Type v} [CommRing S] [CommRing T] (f : S →+* T)
    (h : Triple S) (k : Triple T) (g : Model S ≃ₗ[S] Model S) (l : Model T ≃ₗ[T] Model T) : Prop :=
  letI : Algebra S T := f.toAlgebra
  (∀ i z, ZornSpecification.baseChange S T ((h i).toLinearMap.baseChange T z) =
      k i (ZornSpecification.baseChange S T z)) ∧
  ∀ z, modelBaseChange S T (g.toLinearMap.baseChange T z) = l (modelBaseChange S T z)

/-- The triality isomorphism on all scalar algebras, using the actual spin
point functor and preserving each of the three coordinate actions under scalar maps. -/
def ScalarTriality : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (G : ∀ (S : Type v) [CommRing S] [Algebra R S],
        Subgroup (SpinSpecification.ScalarClifford (norm R) S)ˣ)
      (c : ∀ (S : Type v) [CommRing S] [Algebra R S],
        SpinSpecification.ScalarClifford (norm R) S ≃ₐ[S] CliffordAlgebra (norm S))
      (a : ∀ (S : Type v) [CommRing S],
        CliffordAlgebra (norm S) ≃ₐ[S] Module.End S (Zorn S × Zorn S))
      (e : ∀ (S : Type v) [CommRing S] [Algebra R S],
        G S ≃* relatedTriples (R := S))
      (b : ∀ (S : Type v) [CommRing S] [Algebra R S],
        relatedTriples (R := S) ≃* frameStabilizer (R := S)),
      (∀ (S : Type v) [CommRing S] [Algebra R S], (↑(G S) : Set _) =
        SpinSpecification.spinUnits (norm R) S) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S] (x : S ⊗[R] Zorn R),
        c S (SpinSpecification.vectors (norm R) S x) = ι (norm S) (ZornSpecification.baseChange R S x)) ∧
      (∀ (S : Type v) [CommRing S] (x : Zorn S),
        a S (ι _ x) = CliffordSpecification.octonionOperator x) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S] (s : G S),
        Corresponds (a S) (e S s) (Units.map (c S).toMonoidHom s.val)) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S] (h : relatedTriples (R := S)) (x : Model S),
        (b S h).val x = (x.1, fun i => h.val i (x.2 i))) ∧
      ∀ (S T : Type v) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
        (f : S →ₐ[R] T) (s : G S), ∃ t : G T,
        t.val = Units.map (SpinSpecification.coefficientMap (norm R) S f).toMonoidHom s.val ∧
        (∀ i x, mapCoordinates f.toRingHom ((e S s).val i x) =
          (e T t).val i (mapCoordinates f.toRingHom x)) ∧
        (∀ x, mapModel f.toRingHom ((b S (e S s)).val x) =
          (b T (e T t)).val (mapModel f.toRingHom x)) ∧
        ExtendsActions f.toRingHom (e S s).val (e T t).val (b S (e S s)).val (b T (e T t)).val

section Geometry

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

/-- The integral spin scheme of the split octonion norm represents the ordered
frame stabilizer. It is smooth of relative dimension 28 with geometrically
connected fibers. Its action on the Peirce blocks is given by the related
triple of the Clifford point. -/
def IntegralFrameGeometry : Prop :=
  ∃ G : SpinSpecification.GroupScheme ℤ,
    SmoothOfRelativeDimension 28 G.X.hom ∧ GeometricallyConnected G.X.hom ∧
    ∃ (e : ∀ S : CommAlgCat ℤ, SpinSpecification.SchemePoints G S ≃* frameStabilizer (R := S))
      (ρ : ∀ S : CommAlgCat ℤ, SpinSpecification.SchemePoints G S →*
        (SpinSpecification.ScalarClifford (norm ℤ) S)ˣ)
      (h : ∀ S : CommAlgCat ℤ, SpinSpecification.SchemePoints G S ≃* relatedTriples (R := S))
      (c : ∀ S : CommAlgCat ℤ,
        SpinSpecification.ScalarClifford (norm ℤ) S ≃ₐ[S] CliffordAlgebra (norm S))
      (a : ∀ S : CommAlgCat ℤ, CliffordAlgebra (norm S) ≃ₐ[S] Module.End S (Zorn S × Zorn S)),
      SpinSpecification.IsSpinPointRepresentation (norm ℤ) G ρ ∧
      (∀ (S : CommAlgCat ℤ) x, c S (SpinSpecification.vectors (norm ℤ) S x) =
        CliffordAlgebra.ι (norm S) (ZornSpecification.baseChange ℤ S x)) ∧
      (∀ (S : CommAlgCat ℤ) (x : Zorn S),
        a S (CliffordAlgebra.ι _ x) = CliffordSpecification.octonionOperator x) ∧
      (∀ (S : CommAlgCat ℤ) (s : SpinSpecification.SchemePoints G S),
        Corresponds (a S) (h S s) (Units.map (c S).toMonoidHom (ρ S s))) ∧
      (∀ (S : CommAlgCat ℤ) (s : SpinSpecification.SchemePoints G S) (x : Model S),
        (e S s).val x = (x.1, fun i => (h S s).val i (x.2 i))) ∧
      ∀ {S T : CommAlgCat ℤ} (f : S ⟶ T) (a : SpinSpecification.SchemePoints G S) (x : Model S),
        mapModel f.hom.toRingHom ((e S a).val x) =
          (e T ((algSpec (CommRingCat.of ℤ)).map f.op ≫ a)).val (mapModel f.hom.toRingHom x)

end Geometry

/-- The even and odd exterior powers intertwine the two octonion blocks under
the rank-four hyperbolic identification. -/
def HalfSpinBlocks : Prop :=
  ∀ (R : Type u) [CommRing R]
    (a : CliffordAlgebra (norm R) ≃ₐ[R] Module.End R (Zorn R × Zorn R)),
    (∀ c, a (ι _ c) = CliffordSpecification.octonionOperator c) →
    let E := Option (Fin 3) → R
    let q := QuadraticForm.dualProd R E
    ∃ (d : (norm R).IsometryEquiv q)
      (b : CliffordAlgebra q ≃ₐ[R] Module.End R (ExteriorAlgebra R E))
      (F : ExteriorAlgebra R E ≃ₗ[R] (Zorn R × Zorn R)),
      (d.toLinearEquiv = Zorn.hyperbolicCoordinates R) ∧
      (∀ x, b (ι _ x) = CliffordSpecification.hyperbolicOperator x) ∧
      (∀ t x, F (b (equivOfIsometry d t) x) = a t (F x)) ∧
      (∀ x, x ∈ evenOdd (0 : QuadraticForm R E) 0 ↔ (F x).2 = 0) ∧
      (∀ x, x ∈ evenOdd (0 : QuadraticForm R E) 1 ↔ (F x).1 = 0) ∧
      ∀ (h : Triple R) (s : CliffordUnits R), Corresponds a h s →
        (∀ c, (s : CliffordAlgebra (norm R)) * ι (norm R) c * ↑s⁻¹ = ι (norm R) (h 1 c)) ∧
        ∀ x, F (b (equivOfIsometry d s) x) =
          (conjugate (norm R) (h 0 (conjugate (norm R) (F x).1)), h 2 (F x).2)

end LinearAlgebraicGroups.Albert.TrialitySpecification
