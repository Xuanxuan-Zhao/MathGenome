import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.FaceOrientations
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The ordered simplex is the shared corner simplex, in coordinates 0,e₁,...,e_q.
Smoothness is tested in every target chart by a local ambient Euclidean extension.
The total `generate` operation sends a nonsmooth map to zero; the implementation
proves that every map used in a boundary or a smooth pushforward is smooth. Thus
this totalization never discards a face or a smooth image. -/
namespace SmoothManifolds.SmoothSingularData
open ModelData AtlasData MapData CornerData Set
open scoped Topology Classical
universe u v

abbrev Simplex := CornerData.Simplex

def faceAmbient {q : ℕ} (j : Fin (q+2)) (x : Euclidean q) : Euclidean (q+1) :=
  Fin.tail (j.insertNth 0 (simplexBarycentric x) : Euclidean (q+2))

/-- The affine ordered face map inserts the missing barycentric coordinate as zero. -/
def face {q : ℕ} (j : Fin (q+2)) (x : Simplex q) : Simplex (q+1) := by
  let b : Euclidean (q+2) := j.insertNth (0 : ℝ) (simplexBarycentric x.val)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    refine Fin.succAboveCases j (by simp [b]) (fun k => ?_) i
    simp only [b, Fin.insertNth_apply_succAbove]
    refine Fin.cases ?_ (fun k => ?_) k
    · exact sub_nonneg.mpr x.property.2
    · exact x.property.1 k
  have hs : ∑ i, b i = 1 := by
    change ∑ i, j.insertNth 0 (simplexBarycentric x.val) i = 1
    rw [Fin.sum_insertNth]
    simp [simplexBarycentric, Fin.sum_univ_succ]
  exact ⟨faceAmbient j x.val, fun i => hb i.succ,
    by have := hb 0; rw [Fin.sum_univ_succ] at hs; change ∑ i : Fin (q+1), b i.succ ≤ 1; linarith⟩

/-- Nonnegative barycentric coordinates of total mass one determine a simplex point. -/
def fromBarycentric {q : ℕ} (b : Euclidean (q+1))
    (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, b i = 1) : Simplex q :=
  ⟨Fin.tail b, fun i => hb i.succ, by
    rw [Fin.sum_univ_succ] at hs
    have hzero := hb 0
    change ∑ i : Fin q, b i.succ ≤ 1
    linarith⟩

/-- Ordered vertices v₀=0, v_{i+1}=e_{i+1}. -/
def vertex {q : ℕ} (i : Fin (q+1)) : Simplex q :=
  fromBarycentric (Pi.single i 1) (fun j => by simp [Pi.single_apply]; split <;> norm_num)
    (by simp [Pi.single_apply])

/-- A chart expression is required only near a point in that chart's source. -/
def SimplexSmooth {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : Simplex q → M) : Prop :=
  Continuous f ∧ ∀ x, ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
    LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val (fun y => (d (f y)).val) x

abbrev SingularSimplex {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ) := {f : Simplex q → M // SimplexSmooth S f}

abbrev Chains {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ) := SingularSimplex S q →₀ ℝ

noncomputable def generate {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : Simplex q → M) : Chains S q :=
  if h : SimplexSmooth S f then Finsupp.single ⟨f,h⟩ 1 else 0

noncomputable def boundary {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ) : Chains S (q+1) →ₗ[ℝ] Chains S q :=
  Finsupp.linearCombination ℝ (fun σ =>
    ∑ j : Fin (q+2), (-1 : ℝ)^j.val • generate S (σ.val ∘ face j))

/-- Degree-zero chains have zero boundary, into the zero vector space. -/
noncomputable def boundaryZero {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : Chains S 0 →ₗ[ℝ] (Fin 0 → ℝ) := 0

abbrev Cochains {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ) := Chains S q →ₗ[ℝ] ℝ

noncomputable def coboundary {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ) : Cochains S q →ₗ[ℝ] Cochains S (q+1) where
  toFun c := c.comp (boundary S q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def cocycles {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ) : Submodule ℝ (Cochains S q) :=
  LinearMap.ker (coboundary S q)

/-- There are no incoming coboundaries in degree zero. -/
noncomputable def previousCoboundary {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) :
    (q : ℕ) → Cochains S (q-1) →ₗ[ℝ] Cochains S q
  | 0 => 0
  | q+1 => coboundary S q

/-- The inverse image of the incoming range in cocycles. The square-zero theorem
shows that the entire incoming range consists of cocycles. -/
noncomputable def coboundaries {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (q : ℕ) :
    Submodule ℝ (cocycles S q) :=
  (LinearMap.range (previousCoboundary S q)).comap (cocycles S q).subtype

noncomputable abbrev Cohomology {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (q : ℕ) :=
  @HasQuotient.Quotient (cocycles S q) (Submodule ℝ (cocycles S q))
    (@Submodule.hasQuotient ℝ (cocycles S q) _ _ _) (coboundaries S q)

noncomputable def chainMap {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) (q : ℕ) :
    Chains S q →ₗ[ℝ] Chains T q :=
  Finsupp.linearCombination ℝ (fun σ => generate T (f ∘ σ.val))

noncomputable def cochainMap {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) (q : ℕ) :
    Cochains T q →ₗ[ℝ] Cochains S q where
  toFun c := c.comp (chainMap S T f q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SmoothManifolds.SmoothSingularData

namespace Specs.SmoothManifolds.Comparison.SmoothSingularComplex
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.CornerData _root_.SmoothManifolds.SmoothSingularData
open Set
universe u v w

def SimplexType := ℕ → Type
def SimplexValue : SimplexType := SmoothSingularData.Simplex

def faceAmbientType := {q : ℕ} → Fin (q+2) → Euclidean q → Euclidean (q+1)
def faceAmbientValue : faceAmbientType := @SmoothSingularData.faceAmbient

def faceType := {q : ℕ} → Fin (q+2) → SmoothSingularData.Simplex q → SmoothSingularData.Simplex (q+1)
def faceValue : faceType := @SmoothSingularData.face

def vertexType := {q : ℕ} → Fin (q+1) → SmoothSingularData.Simplex q
def vertexValue : vertexType := @SmoothSingularData.vertex

def SimplexSmoothType := {n q : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → (SmoothSingularData.Simplex q → M) → Prop
def SimplexSmoothValue : SimplexSmoothType := @SmoothSingularData.SimplexSmooth

def SingularSimplexType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → ℕ → Type u
def SingularSimplexValue : SingularSimplexType := @SmoothSingularData.SingularSimplex

def ChainsType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → ℕ → Type u
def ChainsValue : ChainsType := @SmoothSingularData.Chains

def generateType := {n q : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) →
    (SmoothSingularData.Simplex q → M) → Chains S q
noncomputable def generateValue : generateType := @SmoothSingularData.generate

def boundaryType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) →
    Chains S (q+1) →ₗ[ℝ] Chains S q
noncomputable def boundaryValue : boundaryType := @SmoothSingularData.boundary

def boundaryZeroType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) →
    Chains S 0 →ₗ[ℝ] (Fin 0 → ℝ)
noncomputable def boundaryZeroValue : boundaryZeroType := @SmoothSingularData.boundaryZero

def CochainsType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → ℕ → Type u
def CochainsValue : CochainsType := @SmoothSingularData.Cochains

def coboundaryType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) →
    Cochains S q →ₗ[ℝ] Cochains S (q+1)
noncomputable def coboundaryValue : coboundaryType := @SmoothSingularData.coboundary

def cocyclesType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) → Submodule ℝ (Cochains S q)
noncomputable def cocyclesValue : cocyclesType := @SmoothSingularData.cocycles

def previousCoboundaryType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) →
    Cochains S (q-1) →ₗ[ℝ] Cochains S q
noncomputable def previousCoboundaryValue : previousCoboundaryType := @SmoothSingularData.previousCoboundary

def coboundariesType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) → Submodule ℝ (cocycles S q)
noncomputable def coboundariesValue : coboundariesType := @SmoothSingularData.coboundaries

def CohomologyType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → ℕ → Type u
noncomputable def CohomologyValue : CohomologyType := @SmoothSingularData.Cohomology

def chainMapType := {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
  [TopologicalSpace M] → [TopologicalSpace N] → (S : SmoothManifold n a M) →
  (T : SmoothManifold m b N) → (M → N) → (q : ℕ) → Chains S q →ₗ[ℝ] Chains T q
noncomputable def chainMapValue : chainMapType := @SmoothSingularData.chainMap

def cochainMapType := {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
  [TopologicalSpace M] → [TopologicalSpace N] → (S : SmoothManifold n a M) →
  (T : SmoothManifold m b N) → (M → N) → (q : ℕ) → Cochains T q →ₗ[ℝ] Cochains S q
noncomputable def cochainMapValue : cochainMapType := @SmoothSingularData.cochainMap

def simplex_geometryType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.simplex_source_orientationType

def ordered_facesType : Prop :=
  (Nonempty (SmoothSingularData.Simplex 0) ∧ Subsingleton (SmoothSingularData.Simplex 0)) ∧
  (∀ q, (vertex (0 : Fin (q+1))).val = 0) ∧
  (∀ {q : ℕ} (i : Fin q), (vertex i.succ).val = Pi.single i 1) ∧
  (∀ {q : ℕ} (j : Fin (q+2)) (i : Fin (q+1)), face j (vertex i) = vertex (j.succAbove i)) ∧
  (∀ {q : ℕ} (j : Fin (q+2)) (r : ℝ) (x y : Euclidean q),
    faceAmbient j (r • x + (1-r) • y) = r • faceAmbient j x + (1-r) • faceAmbient j y) ∧
  (∀ {q : ℕ} (i : Fin (q+2)) (j : Fin (q+3)) (h : j.val ≤ i.val),
    face j ∘ face i = face i.succ ∘ face (Fin.castLT j (lt_of_le_of_lt h i.isLt))) ∧
  (∀ x : SmoothSingularData.Simplex 0,
    (face (0 : Fin 2) x).val 0 = 1 ∧ (face (1 : Fin 2) x).val 0 = 0)

def smooth_closureType : Prop :=
  ∀ {n m q : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N),
    (∀ (σ : SingularSimplex S (q+1)) (j : Fin (q+2)), SimplexSmooth S (σ.val ∘ face j)) ∧
    (∀ (f : M → N), IsSmoothMap S T f →
      ∀ σ : SingularSimplex S q, SimplexSmooth T (f ∘ σ.val))

def complex_identitiesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    (∀ q, (boundary S q).comp (boundary S (q+1)) = 0) ∧
    (boundaryZero S = 0) ∧
    (∀ q, (coboundary S (q+1)).comp (coboundary S q) = 0) ∧
    (∀ q, LinearMap.range (previousCoboundary S q) ≤ cocycles S q) ∧
    (coboundaries S 0 = ⊥) ∧
    (∀ q (σ : SingularSimplex S (q+1)),
      boundary S q (Finsupp.single σ 1) =
        ∑ j : Fin (q+2), (-1 : ℝ)^j.val • generate S (σ.val ∘ face j)) ∧
    (∀ q (d : Cochains S q) (z : Chains S (q+1)), coboundary S q d z = d (boundary S q z)) ∧
    (∀ σ : SingularSimplex S 1, boundary S 0 (Finsupp.single σ 1) =
      generate S (σ.val ∘ face (0 : Fin 2)) - generate S (σ.val ∘ face (1 : Fin 2)))

def naturalityType : Prop :=
  ∀ {n m l : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold l c P),
    (∀ q, chainMap S S id q = LinearMap.id) ∧
    (∀ q, cochainMap S S id q = LinearMap.id) ∧
    (∀ (f : M → N) (g : N → P), IsSmoothMap S T f → IsSmoothMap T U g → ∀ q,
      chainMap S U (g ∘ f) q = (chainMap T U g q).comp (chainMap S T f q) ∧
      cochainMap S U (g ∘ f) q = (cochainMap S T f q).comp (cochainMap T U g q)) ∧
    (∀ (f : M → N), IsSmoothMap S T f → ∀ q,
      (boundary T q).comp (chainMap S T f (q+1)) = (chainMap S T f q).comp (boundary S q) ∧
      (coboundary S q).comp (cochainMap S T f q) =
        (cochainMap S T f (q+1)).comp (coboundary T q)) ∧
    (∀ (f : M → N), IsSmoothMap S T f → ∀ q (σ : SingularSimplex S q),
      chainMap S T f q (Finsupp.single σ 1) = generate T (f ∘ σ.val))

def free_chainsType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {V : Type v} [AddCommGroup V] [Module ℝ V]
    (F : SingularSimplex S q → V),
    ∃! L : Chains S q →ₗ[ℝ] V, ∀ σ, L (Finsupp.single σ 1) = F σ

def extension_conventionType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (f : SmoothSingularData.Simplex q → M),
    SimplexSmooth S f ↔ Continuous f ∧
      ∀ x, ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
        ModelData.HasLocalContDiffExtensionAt (⊤ : ℕ∞) Subtype.val
          (fun y => (d (f y)).val) x

end Specs.SmoothManifolds.Comparison.SmoothSingularComplex
