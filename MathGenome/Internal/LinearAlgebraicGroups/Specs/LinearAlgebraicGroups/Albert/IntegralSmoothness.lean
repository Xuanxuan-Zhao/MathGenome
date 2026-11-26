import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.ReductiveFibers

namespace LinearAlgebraicGroups.Albert.IntegralSmoothnessSpecification

open AlgebraicGeometry CategoryTheory Opposite
open TrialitySpecification (Model mapModel)
open IdempotentSpecification (IsSplitAutomorphism)
open ShortDirectionSpecification (IntegralPresentation)
open ReductiveFiberSpecification (traceZero scalarLine IsInvariant PointIrreducibility PointFaithfulness)
open scoped CategoryTheory.MonObj

def ScalarLineIntersectionType : Prop :=
  ∀ (k : Type) [Field k],
    ((3 : k) = 0 → scalarLine k ⊓ traceZero k = scalarLine k) ∧
    ((3 : k) ≠ 0 → scalarLine k ⊓ traceZero k = ⊥)

def TraceZeroInvariantType : Prop :=
  ∀ (k : Type) [Field k], IsInvariant (traceZero k)

def GeometricIrreducibilityType : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k], PointIrreducibility k

/-- Test for the point kernel, phrased in the ambient coordinates. The difference
of two lifts of a quotient vector belongs to the scalar line. -/
def GeometricPointKernelType : Prop :=
  ∀ (k : Type) [Field k], PointFaithfulness k

noncomputable abbrev coordinateScheme (P : IntegralPresentation) :=
  (algSpec (CommRingCat.of ℤ)).obj (op (CommAlgCat.of ℤ P.Coordinates))

/-- The integral scheme with its specified action on the split Albert algebra. -/
structure SplitGroup (P : IntegralPresentation) where
  group : SpinSpecification.GroupScheme ℤ
  coordinates : group.X ≅ coordinateScheme P
  affine : IsAffine group.X.left
  finitePresentation : LocallyOfFinitePresentation group.X.hom
  action : ∀ S : CommAlgCat ℤ, SpinSpecification.SchemePoints group S →*
    (Model S ≃ₗ[S] Model S)
  injective : ∀ S, Function.Injective (action S)
  image : ∀ S, Set.range (action S) = {g | IsSplitAutomorphism g}
  natural : ∀ {S T : CommAlgCat ℤ} (f : S ⟶ T)
    (g : SpinSpecification.SchemePoints group S) (x : Model S),
    mapModel f.hom.toRingHom (action S g x) =
      action T ((algSpec (CommRingCat.of ℤ)).map f.op ≫ g) (mapModel f.hom.toRingHom x)
  matrixCoordinates : ∀ (S : CommAlgCat ℤ) (g : SpinSpecification.SchemePoints group S),
    ∃ a : P.Coordinates →ₐ[ℤ] S,
      (algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom a).op = g ≫ coordinates.hom ∧
      ∃ m : Matrix.GeneralLinearGroup (Fin 27) S,
        (∀ i j, (m : Matrix (Fin 27) (Fin 27) S) i j =
          a (Ideal.Quotient.mk _
            (_root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.coordinateMatrix i j))) ∧
        ∀ x, action S g (TrialitySpecification.modelBaseChange ℤ S x) =
          TrialitySpecification.modelBaseChange ℤ S
            (_root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.matrixAction P.basis S m x)

def IntegralRepresentationType : Prop :=
  ∀ P : IntegralPresentation, Nonempty (SplitGroup P)

/-- The chosen smooth charts meet the identity of the same integral group
that realizes the presentation. -/
def IntegralIdentityChartsType : Prop :=
  ∃ (P : IntegralPresentation) (G : SplitGroup P) (e : P.Coordinates →ₐ[ℤ] ℤ),
    P.IsIdentity e ∧
    (algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom e).op =
      (1 : SpinSpecification.SchemePoints G.group (CommAlgCat.of ℤ ℤ)) ≫ G.coordinates.hom ∧
    ∀ (k : Type) [Field k], ∃ f : P.Coordinates,
      algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension 52 ℤ (Localization.Away f)

noncomputable abbrev geometricFiber {P : IntegralPresentation} (G : SplitGroup P)
    (k : Type) [Field k] : LinearAlgebraicGroups.Specs.GroupScheme k :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).mapGrp).obj G.group

/-- The same fiber, with the finiteness and affineness inherited from its presentation. -/
noncomputable def algebraicFiber {P : IntegralPresentation} (G : SplitGroup P)
    (k : Type) [Field k] : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup k := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
  have := G.affine
  have := G.finitePresentation
  refine ⟨geometricFiber G k, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsAffine (Limits.pullback G.group.X.hom f))
  · exact inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.group.X.hom f))
  · exact inferInstanceAs (QuasiCompact (Limits.pullback.snd G.group.X.hom f))

/-- Smoothness and geometric connectedness concern the same integral group whose
geometric fibers are reductive. -/
def IntegralGeometryType : Prop :=
  ∃ (P : IntegralPresentation) (G : SplitGroup P),
    SmoothOfRelativeDimension 52 G.group.X.hom ∧ GeometricallyConnected G.group.X.hom ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k],
      LinearAlgebraicGroups.Specs.GeometricRadicals.IsReductive (algebraicFiber G k)

end LinearAlgebraicGroups.Albert.IntegralSmoothnessSpecification
