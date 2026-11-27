import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers
import Mathlib.Topology.Algebra.MulAction

/-! Continuous cochains with discrete coefficients descend to finite Galois layers. -/

namespace GaloisFormalization.GH.FiniteCochainDescent

open GaloisFormalization.GH.KrullLayers
open scoped Topology

universe u v w z

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
variable {X : Type w} {q : ℕ}

private noncomputable def restrictTuple (E : FiniteGaloisIntermediateField k L)
    (g : Fin q → Gal(L/k)) : Fin q → LayerGroup E :=
  fun j => restrict E (g j)

private theorem continuous_restrictTuple (E : FiniteGaloisIntermediateField k L) :
    Continuous (restrictTuple (q := q) E) :=
  continuous_pi fun j => (restrict E).continuous.comp (continuous_apply j)

private theorem restrictTuple_eq_of_le {E F : FiniteGaloisIntermediateField k L}
    (hle : E ≤ F) {g h : Fin q → Gal(L/k)} (heq : restrictTuple F g = restrictTuple F h) :
    restrictTuple E g = restrictTuple E h := by
  have hcomp (t : Fin q → Gal(L/k)) (j : Fin q) :
      restrictTuple E t j = transition hle (restrictTuple F t j) :=
    DFunLike.congr_fun (restrict_comp hle) (t j)
  funext j
  calc
    restrictTuple E g j = transition hle (restrictTuple F g j) := hcomp g j
    _ = transition hle (restrictTuple F h j) :=
      congrArg (fun σ : LayerGroup F => transition hle σ) (congrFun heq j)
    _ = restrictTuple E h j := (hcomp h j).symm

/-- Inflate a cochain by restriction in every coordinate and inclusion of fixed points. -/
noncomputable def inflate [MulAction Gal(L/k) X] (E : FiniteGaloisIntermediateField k L)
    (f : (Fin q → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X)
    (g : Fin q → Gal(L/k)) : X :=
  f (fun j => restrict E (g j))

theorem continuous_inflate [MulAction Gal(L/k) X] [TopologicalSpace X]
    (E : FiniteGaloisIntermediateField k L)
    (f : (Fin q → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X) :
    Continuous (inflate E f) :=
  (continuous_of_discreteTopology (f := fun t => (f t : X))).comp
    (continuous_restrictTuple E)

variable [IsGalois k L]

private theorem restrictTuple_surjective (E : FiniteGaloisIntermediateField k L) :
    Function.Surjective (restrictTuple (q := q) E) := by
  intro t
  choose g hg using fun j => restrict_surjective E (t j)
  exact ⟨g, funext hg⟩

theorem inflate_injective [MulAction Gal(L/k) X] (E : FiniteGaloisIntermediateField k L) :
    Function.Injective (inflate (X := X) (q := q) E) := by
  intro f h heq
  funext t
  obtain ⟨g, rfl⟩ := restrictTuple_surjective E t
  exact Subtype.ext (congrFun heq g)

variable [TopologicalSpace X] [DiscreteTopology X]

/-- A single finite restriction separates all pairs on which a continuous cochain differs. -/
private theorem exists_layer_constant_on_fibers (f : (Fin q → Gal(L/k)) → X)
    (hf : Continuous f) :
    ∃ E : FiniteGaloisIntermediateField k L,
      ∀ g h, restrictTuple E g = restrictTuple E h → f g = f h := by
  let D := Fin q → Gal(L/k)
  let bad : Set (D × D) := {p | f p.1 ≠ f p.2}
  let separated (E : FiniteGaloisIntermediateField k L) : Set (D × D) :=
    {p | restrictTuple E p.1 ≠ restrictTuple E p.2}
  have hcompact : IsCompact bad :=
    ((isClosed_discrete {p : X × X | p.1 ≠ p.2}).preimage
      ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))).isCompact
  have hopen (E : FiniteGaloisIntermediateField k L) : IsOpen (separated E) :=
    isOpen_ne_fun ((continuous_restrictTuple E).comp continuous_fst)
      ((continuous_restrictTuple E).comp continuous_snd)
  have hcover : bad ⊆ ⋃ E, separated E := by
    intro p hp
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (show p.1 ≠ p.2 from fun h => hp (congrArg f h))
    obtain ⟨x, hx⟩ := DFunLike.exists_ne hj
    obtain ⟨E, hxE⟩ := exists_layer_mem (k := k) x
    refine Set.mem_iUnion.mpr ⟨E, fun heq => hx ?_⟩
    simpa only [restrictTuple, restrict_apply] using
      congrArg (fun σ : LayerGroup E => (σ ⟨x, hxE⟩ : L)) (congrFun heq j)
  have hmono : Monotone separated := fun _ _ hle _ hp heq =>
    hp (restrictTuple_eq_of_le hle heq)
  obtain ⟨E, hE⟩ := hcompact.elim_directed_cover separated hopen hcover
    (fun E F => ⟨E ⊔ F, hmono le_sup_left, hmono le_sup_right⟩)
  refine ⟨E, fun g h heq => ?_⟩
  by_contra hne
  exact hE (show (g, h) ∈ bad from hne) heq

variable [MulAction Gal(L/k) X] [ContinuousSMul Gal(L/k) X]

/-- The intersection of the stabilizers of the finite image contains a layer kernel. -/
private theorem exists_layer_fixing_range (f : (Fin q → Gal(L/k)) → X) (hf : Continuous f) :
    ∃ E : FiniteGaloisIntermediateField k L,
      ∀ g, f g ∈ MulAction.fixedPoints (layerKernel E) X := by
  let : Finite (Set.range f) := (isCompact_range hf).finite_of_discrete
  let stabilizer (y : Set.range f) := (MulAction.stabilizer Gal(L/k) (y : X) : Set Gal(L/k))
  have hopen : IsOpen (⋂ y, stabilizer y) :=
    isOpen_iInter_of_finite fun y => stabilizer_isOpen Gal(L/k) (y : X)
  have hone : (1 : Gal(L/k)) ∈ ⋂ y, stabilizer y :=
    Set.mem_iInter.mpr fun y => (MulAction.stabilizer Gal(L/k) (y : X)).one_mem
  obtain ⟨E, _, hE⟩ := (layerKernels_basis k L).mem_iff.mp (hopen.mem_nhds hone)
  exact ⟨E, fun g σ => Set.mem_iInter.mp (hE σ.property) ⟨f g, Set.mem_range_self g⟩⟩

/-- Finitely many cochains, with possibly different arities, descend at one stage extending E₀. -/
theorem commonCochainFactorization (ι : Type z) [Finite ι] (q : ι → ℕ)
    (f : ∀ i, (Fin (q i) → Gal(L/k)) → X) (hf : ∀ i, Continuous (f i))
    (E₀ : FiniteGaloisIntermediateField k L) :
    ∃ E : FiniteGaloisIntermediateField k L, E₀ ≤ E ∧
      ∃ fE : ∀ i, (Fin (q i) → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X,
        ∀ i g, (fE i (fun j => restrict E (g j)) : X) = f i g := by
  classical
  let := Fintype.ofFinite ι
  choose A hA using fun i => exists_layer_constant_on_fibers (f i) (hf i)
  choose B hB using fun i => exists_layer_fixing_range (f i) (hf i)
  let stage (i : ι) := A i ⊔ B i
  let E := E₀ ⊔ Finset.univ.sup stage
  have hstage (i : ι) : stage i ≤ E :=
    (Finset.le_sup (f := stage) (Finset.mem_univ i)).trans le_sup_right
  have hfix (i : ι) (g : Fin (q i) → Gal(L/k)) : f i g ∈ MulAction.fixedPoints (layerKernel E) X :=
    fun σ => hB i g ⟨σ, layerKernel_le_iff.mpr (le_sup_right.trans (hstage i)) σ.property⟩
  choose lift hlift using fun i => (restrictTuple_surjective (q := q i) E).hasRightInverse
  refine ⟨E, le_sup_left, fun i t => ⟨f i (lift i t), hfix i (lift i t)⟩, ?_⟩
  intro i g
  change f i (lift i (restrictTuple E g)) = f i g
  exact hA i _ _ (restrictTuple_eq_of_le (le_sup_left.trans (hstage i))
    (hlift i (restrictTuple E g)))

/-- A continuous cochain descends along group restriction and fixed-coefficient inclusion. -/
theorem finiteCochainFactorization (f : (Fin q → Gal(L/k)) → X) (hf : Continuous f)
    (E₀ : FiniteGaloisIntermediateField k L) :
    ∃ E : FiniteGaloisIntermediateField k L, E₀ ≤ E ∧
      ∃ fE : (Fin q → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X,
        ∀ g, (fE (fun j => restrict E (g j)) : X) = f g := by
  obtain ⟨E, hE, fE, heq⟩ :=
    commonCochainFactorization Unit (fun _ => q) (fun _ => f) (fun _ => hf) E₀
  exact ⟨E, hE, fE (), heq ()⟩

end GaloisFormalization.GH.FiniteCochainDescent
