import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

namespace RepTheorySurvey.Geometric.GrassmannianCoordinateInclusionSpecs

noncomputable section

open LatticeModelSpecs
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open Topology

section CoordinateMap

variable {ι κ : Type}

/-- Extend a coordinate vector by zero along the index embedding. -/
def extendCoordinates (f : ι ↪ κ) : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) := by
  classical
  exact LinearMap.pi fun j ↦
    if h : ∃ i, f i = j then LinearMap.proj (R := ℂ) h.choose else 0

theorem extendCoordinates_apply (f : ι ↪ κ) (x : ι → ℂ) (i : ι) :
    extendCoordinates f x (f i) = x i := by
  classical
  let h : ∃ k, f k = f i := ⟨i, rfl⟩
  change ((if h : ∃ k, f k = f i then LinearMap.proj (R := ℂ) h.choose else 0) :
    (ι → ℂ) →ₗ[ℂ] ℂ) x = x i
  rw [dite_eq_left h]
  exact congrArg x (f.injective h.choose_spec)

theorem extendCoordinates_apply_of_notMem_range (f : ι ↪ κ) (x : ι → ℂ) {j : κ}
    (hj : j ∉ Set.range f) : extendCoordinates f x j = 0 := by
  classical
  have h : ¬ ∃ k, f k = j := hj
  change ((if h : ∃ k, f k = j then LinearMap.proj (R := ℂ) h.choose else 0) :
    (ι → ℂ) →ₗ[ℂ] ℂ) x = 0
  simp only [dite_eq_right h, LinearMap.zero_apply]

end CoordinateMap

section Pivots

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {d : ℕ}

/-- The image set of pivot indices in the target basis. -/
def mappedPivot (f : ι ↪ κ) (I : Pivot ι d) : Pivot κ d :=
  ⟨I.val.map f, (Finset.card_map f).trans I.property⟩

/-- The bijection of pivot columns induced by the same index embedding. -/
def insideEquiv (f : ι ↪ κ) (I : Pivot ι d) : Inside I ≃ Inside (mappedPivot f I) :=
  Equiv.ofBijective
    (fun i ↦ ⟨f i.val, Finset.mem_map_of_mem f i.property⟩)
    ⟨fun _ _ h ↦ Subtype.ext (f.injective (congrArg Subtype.val h)), by
      intro j
      obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.property
      exact ⟨⟨i, hi⟩, Subtype.ext hij⟩⟩

/-- Embed the nonpivot indices into the nonpivot indices of the target chart. -/
def outsideEmbedding (f : ι ↪ κ) (I : Pivot ι d) : Outside I ↪ Outside (mappedPivot f I) where
  toFun i := ⟨f i.val, fun hi ↦ i.property ((Finset.mem_map' f).mp hi)⟩
  inj' _ _ h := Subtype.ext (f.injective (congrArg Subtype.val h))

/-- Insert zero rows and transport pivot columns along the induced bijection. -/
def extendChartMatrix (f : ι ↪ κ) (I : Pivot ι d)
    (A : Matrix (Outside I) (Inside I) ℂ) :
    Matrix (Outside (mappedPivot f I)) (Inside (mappedPivot f I)) ℂ :=
  Function.extend (outsideEmbedding f I) (fun i j ↦ A i ((insideEquiv f I).symm j))
    (fun _ _ ↦ 0)

/-- Retain the rows and columns coming from the source chart. -/
def extractChartMatrix (f : ι ↪ κ) (I : Pivot ι d)
    (A : Matrix (Outside (mappedPivot f I)) (Inside (mappedPivot f I)) ℂ) :
    Matrix (Outside I) (Inside I) ℂ :=
  fun i j ↦ A (outsideEmbedding f I i) (insideEquiv f I j)

end Pivots

section Grassmannians

variable {ι κ V W : Type} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- In basis coordinates this sends each coordinate to its indexed position and fills
the other positions with zero. -/
def coordinateInclusion (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ) :
    V →ₗ[ℂ] W :=
  b'.equivFun.symm.toLinearMap.comp ((extendCoordinates f).comp b.equivFun.toLinearMap)

theorem coordinateInclusion_injective (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W)
    (f : ι ↪ κ) : Function.Injective (coordinateInclusion b b' f) := by
  have h : Function.Injective (extendCoordinates f) := by
    intro x y hxy
    funext i
    simpa only [extendCoordinates_apply] using congrFun hxy (f i)
  exact b'.equivFun.symm.injective.comp (h.comp b.equivFun.injective)

/-- Every source plane dimension is also admissible in the target. -/
theorem targetDimension (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) : d ≤ Module.finrank ℂ W := by
  rw [Module.finrank_eq_card_basis b] at hd
  rw [Module.finrank_eq_card_basis b']
  exact hd.trans (Fintype.card_le_of_injective f f.injective)

variable [DecidableEq ι] [DecidableEq κ]
  (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
  {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W)

/-- The point represented by the linear image of the source plane. -/
def mapPoint (p : GrassmannianPoints b hd) : GrassmannianPoints b' hd' :=
  subspacePoint b' hd' ((grassmannianSubspace b hd p).map (coordinateInclusion b b' f))
    (((grassmannianSubspace b hd p).equivMapOfInjective _
      (coordinateInclusion_injective b b' f)).finrank_eq.symm.trans
      (grassmannianSubspace_finrank b hd p))

end Grassmannians

namespace Expected

def coordinateInclusionType := type_of% (@coordinateInclusion)
def mapPointType := type_of% (@mapPoint)

def MapPointSubspace : Prop :=
  ∀ {ι κ V W : Type} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W)
    (p : GrassmannianPoints b hd),
    grassmannianSubspace b' hd' (mapPoint b b' f hd hd' p) =
      (grassmannianSubspace b hd p).map (coordinateInclusion b b' f)

def MapPointRange : Prop :=
  ∀ {ι κ V W : Type} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W),
    Set.range (mapPoint b b' f hd hd') =
      {q | grassmannianSubspace b' hd' q ≤ (coordinateInclusion b b' f).range}

def MapPointClosedEmbedding : Prop :=
  ∀ {ι κ V W : Type} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W),
    @IsClosedEmbedding (GrassmannianPoints b hd) (GrassmannianPoints b' hd')
      (grassmannianAnalyticTopology b hd) (grassmannianAnalyticTopology b' hd')
      (mapPoint b b' f hd hd')

def MapPointChart : Prop :=
  ∀ {ι κ V W : Type} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W)
    (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ),
    mapPoint b b' f hd hd' (grassmannianChartPoint b hd I A) =
      grassmannianChartPoint b' hd' (mappedPivot f I) (extendChartMatrix f I A)

def MapPointImageChart : Prop :=
  ∀ {ι κ V W : Type} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W)
    (I : Pivot ι d) (S : Set (GrassmannianPoints b hd))
    (A : Matrix (Outside (mappedPivot f I)) (Inside (mappedPivot f I)) ℂ),
    grassmannianChartPoint b' hd' (mappedPivot f I) A ∈ mapPoint b b' f hd hd' '' S ↔
      (∀ (i : Outside (mappedPivot f I)), i.val ∉ Set.range f →
        ∀ j : Inside (mappedPivot f I), A i j = 0) ∧
      grassmannianChartPoint b hd I (extractChartMatrix f I A) ∈ S

def UnsupportedChart : Prop :=
  ∀ {ι κ V W : Type} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
    {d : ℕ} (hd' : d ≤ Module.finrank ℂ W)
    (J : Pivot κ d), (∃ j : Inside J, j.val ∉ Set.range f) →
    ∀ A : Matrix (Outside J) (Inside J) ℂ,
      ¬ grassmannianSubspace b' hd' (grassmannianChartPoint b' hd' J A) ≤
          (coordinateInclusion b b' f).range

def MappedPivotRange : Prop :=
  ∀ {ι κ : Type} (f : ι ↪ κ) {d : ℕ},
    Set.range (mappedPivot (d := d) f) =
      {J | ∀ j : Inside J, j.val ∈ Set.range f}

end Expected

end

end RepTheorySurvey.Geometric.GrassmannianCoordinateInclusionSpecs
