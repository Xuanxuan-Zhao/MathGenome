import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

open CategoryTheory Filter
open scoped RatFunc TensorProduct

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace LinearAlgebraicGroups.Specs.FunctionFieldWeilAdelicPoints

open Arithmetic Arithmetic.AdelicGroups
open IntegralModels (MatrixRealization)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The usual separating parameter of the rational function field. -/
def rationalParameter (F : Type u) [Field F] : SeparatingParameter F F⟮X⟯ where
  element := RatFunc.X
  transcendental := RatFunc.transcendental_X
  finite := by
    rw [RatFunc.adjoin_X]
    exact Module.Finite.of_surjective (Algebra.linearMap _ _)
      (fun x => ⟨⟨x, IntermediateField.mem_top⟩, rfl⟩)
  separable := by
    rw [RatFunc.adjoin_X]
    exact ⟨fun x => isSeparable_algebraMap
      (K := F⟮X⟯) (⟨x, IntermediateField.mem_top⟩ : (⊤ : IntermediateField F F⟮X⟯))⟩

/-- The map from an extended test algebra induced by compatible maps from its factors. -/
def tensorSpecialization {k K R L : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra K L] (f : R →+* L)
    (hf : f.comp (algebraMap k R) = (algebraMap K L).comp (algebraMap k K)) :
    R ⊗[k] K →ₐ[K] L := by
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let g : R →ₐ[k] L := { f with commutes' := fun x => DFunLike.congr_fun hf x }
  exact (Algebra.TensorProduct.liftEquivRight k K R L g).comp
    (Algebra.TensorProduct.commRight k K R).symm.toAlgHom

@[simp]
theorem tensorSpecialization_tmul {k K R L : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra K L] (f : R →+* L)
    (hf : f.comp (algebraMap k R) = (algebraMap K L).comp (algebraMap k K))
    (r : R) (x : K) :
    tensorSpecialization f hf (r ⊗ₜ[k] x) = f r * algebraMap K L x := by
  simp [tensorSpecialization, Algebra.TensorProduct.liftEquivRight, mul_comm]

/-- Apply the given Weil point isomorphism and specialize to one factor of the test algebra. -/
def specializedPoint {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup k}
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    {R L : Type u} [CommRing R] [Algebra k R] [CommRing L] [Algebra K L]
    (f : R ⊗[k] K →ₐ[K] L) :
    ((groupPointsFunctor k).obj W.val).obj (CommAlgCat.of k R) →*
      ((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K L) :=
  (((groupPointsFunctor K).obj G.val).map (CommAlgCat.ofHom f)).hom.comp
    (ρ.hom.app (CommAlgCat.of k R)).hom

variable {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]

abbrev baseData (F : Type u) [Field F] [Finite F] : GlobalFieldData.{u, u} F⟮X⟯ :=
  GlobalFieldData.function F (rationalParameter F)

abbrev extensionData (t : SeparatingParameter F K) : GlobalFieldData.{u, u} K :=
  GlobalFieldData.function F t

/-- The full adelic topology from the fixed matrix realization. -/
abbrev fullAdelesTopology {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
    (D : GlobalFieldData.{u, u} k) (i : MatrixRealization H) :
    TopologicalSpace (Adeles D i ∅) :=
  inferInstance

abbrev localPointsTopology {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
    (D : GlobalFieldData.{u, u} k) (i : MatrixRealization H) (v : D.Place) :
    TopologicalSpace (LocalPoints D i v) :=
  inferInstance

/-- Index a function-field coordinate in the full restricted product. -/
def adelicIndex {k : Type u} [Field k] (D : GlobalFieldData.{u, u} k)
    (v : D.FinitePlace) : Outside D ∅ :=
  ⟨.inl v, Finset.notMem_empty _⟩

/-- The local comparison over every fiber and the induced full adelic comparison,
for the specified closed matrix realizations. -/
structure Comparison (t : SeparatingParameter F K)
    {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup F⟮X⟯}
    (i : MatrixRealization G) (j : MatrixRealization W)
    (ρ : letI := t.rationalAlgebra
      (groupPointsFunctor F⟮X⟯).obj W.val ≅
        WeilRestriction.extendScalars F⟮X⟯ K ⋙ (groupPointsFunctor K).obj G.val) where
  below : FunctionPlace K → FunctionPlace F⟮X⟯
  below_val : ∀ w, (below w).val = w.val.comap t.rationalMap.toRingHom
  finite_fiber : ∀ v, Finite {w // below w = v}
  completionMap : ∀ v (w : {w // below w = v}),
    letI := GlobalFieldData.instFieldCompletion (baseData F) (.inl v)
    letI := GlobalFieldData.instFieldCompletion (extensionData t) (.inl w.val)
    (baseData F).Completion (.inl v) →+* (extensionData t).Completion (.inl w.val)
  completionMap_continuous : ∀ v w,
    letI := GlobalFieldData.instTopologicalSpaceCompletion (baseData F) (.inl v)
    letI := GlobalFieldData.instTopologicalSpaceCompletion (extensionData t) (.inl w.val)
    Continuous (completionMap v w)
  completionMap_comp : ∀ v w,
    letI := GlobalFieldData.instFieldCompletion (baseData F) (.inl v)
    letI := GlobalFieldData.instFieldCompletion (extensionData t) (.inl w.val)
    (completionMap v w).comp ((baseData F).embedding (.inl v)) =
      ((extensionData t).embedding (.inl w.val)).comp t.rationalMap.toRingHom
  localEquiv : ∀ v,
    letI := localPointsTopology (baseData F) j (.inl v)
    letI (w : {w // below w = v}) := localPointsTopology (extensionData t) i (.inl w.val)
    LocalPoints (baseData F) j (.inl v) ≃ₜ*
    (∀ w : {w // below w = v}, LocalPoints (extensionData t) i (.inl w.val))
  localEquiv_apply : ∀ (v : FunctionPlace F⟮X⟯)
      (g : LocalPoints (baseData F) j (.inl v)) (w : {w // below w = v}),
    letI := t.rationalAlgebra
    letI : Field ((baseData F).Completion (.inl v)) :=
      GlobalFieldData.instFieldCompletion (baseData F) (.inl v)
    letI : Field ((extensionData t).Completion (.inl w.val)) :=
      GlobalFieldData.instFieldCompletion (extensionData t) (.inl w.val)
    letI := completionAlgebra (baseData F) (.inl v)
    letI := completionAlgebra (extensionData t) (.inl w.val)
    localEquiv v g w = specializedPoint (G := G) (W := W) ρ
      (R := (baseData F).Completion (.inl v)) (L := (extensionData t).Completion (.inl w.val))
      (tensorSpecialization (completionMap v w) (completionMap_comp v w)) g
  integral_iff : ∀ᶠ v in cofinite, ∀ g,
    g ∈ integralPoints (baseData F) j v ↔
      ∀ w, localEquiv v g w ∈ integralPoints (extensionData t) i w.val
  adelicEquiv :
    letI := fullAdelesTopology (baseData F) j
    letI := fullAdelesTopology (extensionData t) i
    Adeles (baseData F) j ∅ ≃ₜ* Adeles (extensionData t) i ∅
  adelicEquiv_apply : ∀ (g : Adeles (baseData F) j ∅) (w : FunctionPlace K),
    adelicEquiv g (adelicIndex (extensionData t) w) =
      localEquiv (below w) (g (adelicIndex (baseData F) (below w))) ⟨w, rfl⟩

/-- The natural Weil point comparison induces local and adelic topological
group isomorphisms and identifies the prescribed integral subgroups at
all but finitely many base places. -/
def WeilAdelicComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K)
    (G : AffineAlgebraicGroup K) (W : AffineAlgebraicGroup F⟮X⟯)
    (i : MatrixRealization G) (j : MatrixRealization W),
    letI := t.rationalAlgebra
    ∀ (ρ : (groupPointsFunctor F⟮X⟯).obj W.val ≅
      WeilRestriction.extendScalars F⟮X⟯ K ⋙ (groupPointsFunctor K).obj G.val),
      Nonempty (Comparison t i j ρ)

end LinearAlgebraicGroups.Specs.FunctionFieldWeilAdelicPoints
