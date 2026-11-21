import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertScalarExtension
import MathGenome.Internal.AlgebraCore.P103.Ch06.NoetherNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.LinearGradedNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace P103.HilbertScalarExtension
open P103.Graded TensorProduct
open P103.Specs.Ch06.LinearGradedNormalization
universe u v w x

theorem base_change_dimension : Specs.P103.HilbertScalarExtension.dimensionType.{u,v,x} := by
  intro k K C _ _ _ _ _ _ _
  obtain ⟨d, g, hinj, hfin, hdim⟩ := P103.Ch06.NoetherNormalization.normalization_map k C
  let gK := Algebra.TensorProduct.lTensor (S := K) K g
  have hgKinj : Function.Injective gK := by
    change Function.Injective (g.toLinearMap.lTensor K)
    exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hinj
  have hgKfin : gK.Finite :=
    RingHom.Finite.tensorProductMap (AlgHom.Finite.id k K) hfin
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin d) k K
  let f := gK.comp e.symm.toAlgHom
  have hfinf : f.Finite := hgKfin.comp e.symm.toRingEquiv.finite
  have hinjf : Function.Injective f := hgKinj.comp e.symm.injective
  have hdimK := P103.Ch04.IntegralDimension.dimension_eq
    (MvPolynomial (Fin d) K) (TensorProduct k K C) f.toRingHom hfinf.to_isIntegral
  rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hinjf] at hdimK
  exact (hdimK.trans ((ringKrullDim_eq_of_ringEquiv
    (RingEquiv.quotientBot (MvPolynomial (Fin d) K))).trans
    (P103.Ch06.PolynomialDimension.polynomial_dimension K d))).trans hdim.symm


section Gradings
variable (k : Type u) (K : Type x) {C : Type v} {M : Type w}
  [Field k] [Field K] [Algebra k K] [CommRing C] [Algebra k C]
  [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

noncomputable def algebraPiece_decomposition (G : NonnegativeGrading C) (hzero : Connected k G) :
    DirectSum.Decomposition (algebraPiece k G hzero) :=
  { decompose' := DirectSum.decompose G.piece
    left_inv := (DirectSum.decomposeAddEquiv G.piece).left_inv
    right_inv := (DirectSum.decomposeAddEquiv G.piece).right_inv }

noncomputable def fieldPiece_decomposition (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) : DirectSum.Decomposition (fieldPiece k G U hzero) :=
  { decompose' := DirectSum.decompose U.piece
    left_inv := (DirectSum.decomposeAddEquiv U.piece).left_inv
    right_inv := (DirectSum.decomposeAddEquiv U.piece).right_inv }

lemma baseChange_mul_mem (G : NonnegativeGrading C) (hzero : Connected k G)
    {i j : ℤ} {a b : TensorProduct k K C}
    (ha : a ∈ (algebraPiece k G hzero i).baseChange K)
    (hb : b ∈ (algebraPiece k G hzero j).baseChange K) :
    a * b ∈ (algebraPiece k G hzero (i + j)).baseChange K := by
  obtain ⟨a, rfl⟩ := ha
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add, add_mul] using Submodule.add_mem _ ha hb
  | tmul a c =>
    obtain ⟨b, rfl⟩ := hb
    induction b using TensorProduct.inductionOn with
    | add b d hb hd => simpa only [map_add, mul_add] using Submodule.add_mem _ hb hd
    | tmul b d =>
      simp only [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ (SetLike.mul_mem_graded (A := G.piece) c.2 d.2)

noncomputable def algebraGrading (G : NonnegativeGrading C) (hzero : Connected k G) :
    NonnegativeGrading (TensorProduct k K C) where
  piece j := ((algebraPiece k G hzero j).baseChange K).toAddSubgroup
  grading := by
    letI := algebraPiece_decomposition k G hzero
    let D := DirectSum.Decomposition.baseChange (algebraPiece k G hzero) (S := K)
    exact
      { decompose' := D.decompose'
        left_inv := D.left_inv
        right_inv := D.right_inv
        one_mem := by
          change (1 : TensorProduct k K C) ∈ (algebraPiece k G hzero 0).baseChange K
          exact Submodule.tmul_mem_baseChange_of_mem 1 (SetLike.one_mem_graded G.piece)
        mul_mem := fun _ _ _ _ ha hb => baseChange_mul_mem k K G hzero ha hb }
  negative j hj := by
    have h : algebraPiece k G hzero j = ⊥ := by
      ext c
      change c ∈ G.piece j ↔ c = 0
      rw [G.negative j hj]
      rfl
    simp only [h, Submodule.baseChange_bot]
    rfl

lemma baseChange_smul_mem (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) {i j : ℤ} {a : TensorProduct k K C} {m : TensorProduct k K M}
    (ha : a ∈ (algebraPiece k G hzero i).baseChange K)
    (hm : m ∈ (fieldPiece k G U hzero j).baseChange K) :
    a • m ∈ (fieldPiece k G U hzero (i + j)).baseChange K := by
  obtain ⟨a, rfl⟩ := ha
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add, add_smul] using Submodule.add_mem _ ha hb
  | tmul a c =>
    obtain ⟨m, rfl⟩ := hm
    induction m using TensorProduct.inductionOn with
    | add m n hm hn => simpa only [map_add, smul_add] using Submodule.add_mem _ hm hn
    | tmul b m =>
      simp only [LinearMap.baseChange_tmul, tensor_smul]
      exact Submodule.tmul_mem_baseChange_of_mem _
        (SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) c.2 m.2)

noncomputable def moduleGrading (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) : ModuleGrading (algebraGrading k K G hzero) (TensorProduct k K M) where
  piece j := ((fieldPiece k G U hzero j).baseChange K).toAddSubgroup
  decomposition := by
    letI := fieldPiece_decomposition k G U hzero
    let D := DirectSum.Decomposition.baseChange (fieldPiece k G U hzero) (S := K)
    exact ⟨D.decompose', D.left_inv, D.right_inv⟩
  compatible := ⟨fun _ _ _ _ ha hm => baseChange_smul_mem k K G U hzero ha hm⟩

end Gradings

section FiniteFaithful
variable (k : Type u) (K : Type x) {C : Type v} {M : Type w}
  [Field k] [Field K] [Algebra k K] [CommRing C] [Algebra k C]
  [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

def generatorAction {n : ℕ} (m : Fin n → M) : C →ₗ[k] (Fin n → M) where
  toFun c i := c • m i
  map_add' c d := funext fun i => add_smul c d (m i)
  map_smul' a c := funext fun i => smul_assoc a c (m i)

lemma generatorAction_injective {n : ℕ} (m : Fin n → M)
    (hm : Submodule.span C (Set.range m) = ⊤) [FaithfulSMul C M] :
    Function.Injective (generatorAction k (C := C) m) := by
  intro c d h
  apply eq_of_smul_eq_smul (α := M)
  intro x
  have hx : x ∈ Submodule.span C (Set.range m) := by rw [hm]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact congrFun h i
  | zero => simp
  | add x y _ _ hx hy => simp only [smul_add, hx, hy]
  | smul a x _ hx => simpa only [smul_comm c a, smul_comm d a] using congrArg (a • ·) hx

/-- A finite generator test for faithfulness survives scalar extension. -/
theorem faithful_baseChange [Module.Finite C M] [FaithfulSMul C M] :
    FaithfulSMul (TensorProduct k K C) (TensorProduct k K M) := by
  classical
  obtain ⟨n, m, hm⟩ := Module.Finite.exists_fin (R := C) (M := M)
  let f := generatorAction k (C := C) m
  let e := TensorProduct.piRight k K K (fun _ : Fin n => M)
  let fK := e.toLinearMap.comp (f.baseChange K)
  have hinj : Function.Injective fK := by
    apply e.injective.comp
    change Function.Injective (f.lTensor K)
    exact Module.Flat.lTensor_preserves_injective_linearMap f (generatorAction_injective k (C := C) m hm)
  have heval (t : TensorProduct k K C) (i : Fin n) :
      fK t i = t • ((1 : K) ⊗ₜ[k] m i) := by
    induction t using TensorProduct.inductionOn with
    | tmul a c => simp [fK, e, f, generatorAction, tensor_smul, TensorProduct.piRight]
    | add t s ht hs => simp only [map_add, Pi.add_apply, add_smul, ht, hs]
  exact ⟨fun {a b} h => hinj (funext fun i => (heval a i).trans ((h _).trans (heval b i).symm))⟩

/-- Ordinary module finiteness survives extension to the tensor algebra. -/
theorem finite_baseChange [Module.Finite C M] :
    Module.Finite (TensorProduct k K C) (TensorProduct k K M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := C) (M := M)
  let t := s.image (fun m => (1 : K) ⊗ₜ[k] m)
  let P := Submodule.span (TensorProduct k K C) (t : Set (TensorProduct k K M))
  have hmem (m : M) : (1 : K) ⊗ₜ[k] m ∈ P := by
    have hm : m ∈ Submodule.span C (s : Set M) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    | zero => simpa using P.zero_mem
    | add m n _ _ hm hn => simpa only [tmul_add] using P.add_mem hm hn
    | smul c m _ hm =>
      simpa only [tensor_smul, one_mul] using P.smul_mem ((1 : K) ⊗ₜ[k] c) hm
  refine ⟨t, top_unique ?_⟩
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simpa only [tensor_smul, mul_one, one_smul] using P.smul_mem (a ⊗ₜ[k] (1 : C)) (hmem m)
  | add x y hx hy => exact P.add_mem hx hy

end FiniteFaithful

section ConnectedStandard
variable (k : Type u) (K : Type x) {C : Type v}
  [Field k] [Field K] [Algebra k K] [CommRing C] [Algebra k C]

/-- The extended degree-zero piece is exactly the larger structural field. -/
theorem connected_baseChange (G : NonnegativeGrading C) (hzero : Connected k G) :
    Connected K (algebraGrading k K G hzero) := by
  intro c
  constructor
  · intro hc
    obtain ⟨t, rfl⟩ := hc
    induction t using TensorProduct.inductionOn with
    | tmul a c =>
      obtain ⟨b, hb⟩ := (hzero (c : C)).mp c.2
      refine ⟨algebraMap k K b * a, ?_⟩
      change (algebraMap K (TensorProduct k K C)) _ = a ⊗ₜ[k] (c : C)
      rw [← hb]
      change (algebraMap k K b * a) ⊗ₜ[k] (1 : C) = a ⊗ₜ[k] algebraMap k C b
      have hb' : algebraMap k C b = b • (1 : C) := Algebra.algebraMap_eq_smul_one b
      rw [hb', ← TensorProduct.smul_tmul]
      simp only [Algebra.smul_def]
    | add t s ht hs =>
      obtain ⟨a, ha⟩ := ht
      obtain ⟨b, hb⟩ := hs
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  · rintro ⟨a, rfl⟩
    exact Submodule.tmul_mem_baseChange_of_mem a (SetLike.one_mem_graded G.piece)

lemma standard_of_field_generators (G : NonnegativeGrading C) (hzero : Connected k G)
    (s : Finset C) (hs : ∀ a ∈ s, a ∈ G.piece 1)
    (hgen : Algebra.adjoin k (s : Set C) = ⊤) : Specs.P103.Graded.standardValue G := by
  refine ⟨s, hs, top_unique ?_⟩
  intro c hc0
  clear hc0
  have hc : c ∈ Algebra.adjoin k (s : Set C) := by rw [hgen]; trivial
  induction hc using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap a =>
    exact (Algebra.adjoin (Base G) (s : Set C)).algebraMap_mem
      ⟨algebraMap k C a, (hzero _).mpr ⟨a, rfl⟩⟩
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

/-- The original finite set of degree-one generators extends to generators. -/
theorem standard_baseChange (G : NonnegativeGrading C) (hzero : Connected k G)
    (hstd : Specs.P103.Graded.standardValue G) :
    Specs.P103.Graded.standardValue (algebraGrading k K G hzero) := by
  classical
  obtain ⟨s, hs, hgen⟩ := P103.Ch06.LinearGradedNormalization.standard_generators G hzero hstd
  let t := s.image (fun c => (1 : K) ⊗ₜ[k] c)
  apply standard_of_field_generators K (algebraGrading k K G hzero)
    (connected_baseChange k K G hzero) t
  · intro a ha
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hs c hc)
  · simpa only [t, Finset.coe_image] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (R := k) (A := K) (s : Set C) hgen

end ConnectedStandard

section Components
variable (k : Type u) {C : Type v} {M : Type w}
  [Field k] [CommRing C] [Algebra k C]
  [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
open P103.HilbertSerreLength

/-- The structural field maps onto the actual degree-zero ring. -/
def baseScalarMap (G : NonnegativeGrading C) (hzero : Connected k G) : k →+* Base G where
  toFun a := ⟨algebraMap k C a, (hzero _).mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

lemma baseScalarMap_surjective (G : NonnegativeGrading C) (hzero : Connected k G) :
    Function.Surjective (baseScalarMap k G hzero) := by
  intro a
  obtain ⟨b, hb⟩ := (hzero a).mp a.2
  exact ⟨b, Subtype.ext hb⟩

/-- Finiteness and the bridge from lengths over C₀ to structural field dimensions. -/
theorem finite_components [Nontrivial C] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G)
    (hstd : Specs.P103.Graded.standardValue G) :
    (∀ j, Module.Finite k (fieldPiece k G U hzero j)) ∧
    (∀ j, hilbertFunction G U j = (Module.finrank k (fieldPiece k G U hzero j) : ℤ)) := by
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  have hsurj : Function.Surjective (algebraMap k (Base G)) := baseScalarMap_surjective k G hzero
  let : Module.Finite k (Base G) :=
    Module.Finite.of_surjective (Algebra.linearMap k (Base G)) hsurj
  let : IsScalarTower k (Base G) M :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change (algebraMap k C a) • m = a • m
      exact algebraMap_smul C a m
  let : Algebra.FiniteType k C :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hfin (j : ℤ) : Module.Finite k (fieldPiece k G U hzero j) := by
    letI : Module (Base G) (fieldPiece k G U hzero j) := (component G U j).module
    let : IsScalarTower k (Base G) (fieldPiece k G U hzero j) :=
      ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
    let : Module.Finite (Base G) (fieldPiece k G U hzero j) := component_finite_of_noetherian G U j
    exact Module.Finite.trans (Base G) (fieldPiece k G U hzero j)
  refine ⟨hfin, ?_⟩
  intro j
  letI : Module (Base G) (fieldPiece k G U hzero j) := (component G U j).module
  let : IsScalarTower k (Base G) (fieldPiece k G U hzero j) :=
    ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
  let := hfin j
  have hlength := Module.length_eq_of_surjective
    (R := Base G) (M := fieldPiece k G U hzero j) hsurj
  rw [Module.length_eq_finrank] at hlength
  change ((Module.length (Base G) (fieldPiece k G U hzero j)).toNat : ℤ) = _
  rw [← hlength]
  simp

variable (K : Type x) [Field K] [Algebra k K]

/-- The component isomorphism is induced by the canonical tensor inclusion. -/
noncomputable def componentEquiv (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) (j : ℤ) :
    TensorProduct k K (fieldPiece k G U hzero j) ≃ₗ[K]
      fieldPiece K (algebraGrading k K G hzero) (moduleGrading k K G U hzero)
        (connected_baseChange k K G hzero) j := by
  letI := fieldPiece_decomposition k G U hzero
  exact LinearEquiv.ofBijective ((fieldPiece k G U hzero j).toBaseChange K)
    (DirectSum.toBaseChange_bijective (fieldPiece k G U hzero) j)

@[simp] theorem componentEquiv_tmul (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) (j : ℤ) (a : K) (m : fieldPiece k G U hzero j) :
    (componentEquiv k K G U hzero j (a ⊗ₜ[k] m) : TensorProduct k K M) = a ⊗ₜ[k] (m : M) := rfl

theorem component_finrank (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) (j : ℤ) :
    Module.finrank K (fieldPiece K (algebraGrading k K G hzero) (moduleGrading k K G U hzero)
      (connected_baseChange k K G hzero) j) = Module.finrank k (fieldPiece k G U hzero j) := by
  rw [← (componentEquiv k K G U hzero j).finrank_eq]
  exact Module.finrank_baseChange

end Components

/-- Extension of scalars preserves all the structures and invariants needed in
Theorem 6.10, over arbitrary fields and with arbitrary integer module degrees. -/
theorem scalar_extension :
  ∀ (k : Type u) (K : Type x) {C : Type v} {M : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    [Nontrivial M] [FaithfulSMul C M] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G),
    Specs.P103.Graded.standardValue G → Specs.P103.HilbertScalarExtension.ExtensionResult k K G U hzero := by
  intro k K C M _ _ _ _ _ _ _ _ _ _ _ _ _ G U hzero hstd
  letI : Module.Finite (TensorProduct k K C) (TensorProduct k K M) := finite_baseChange k K
  letI : FaithfulSMul (TensorProduct k K C) (TensorProduct k K M) := faithful_baseChange k K
  letI : Algebra.FiniteType k C :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  let GK := algebraGrading k K G hzero
  let UK := moduleGrading k K G U hzero
  have hK : Connected K GK := connected_baseChange k K G hzero
  have hstdK : Specs.P103.Graded.standardValue GK := standard_baseChange k K G hzero hstd
  obtain ⟨hfin, hcoeff⟩ := finite_components k G U hzero hstd
  obtain ⟨hfinK, hcoeffK⟩ := finite_components K GK UK hK hstdK
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    base_change_dimension k K C, GK, UK, hK, hstdK,
    (fun _ => rfl), (fun _ => rfl), hfin, hfinK, ?_, ?_, hcoeff, hcoeffK, ?_⟩
  · intro j
    exact ⟨componentEquiv k K G U hzero j, componentEquiv_tmul k K G U hzero j⟩
  · exact component_finrank k K G U hzero
  · funext j
    rw [hcoeffK, hcoeff, component_finrank k K G U hzero]

/-- The rational function field is infinite even when the original field is finite. -/
instance ratFunc_infinite (k : Type u) [Field k] : Infinite (RatFunc k) :=
  Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k)) (IsFractionRing.injective _ _)

/-- The infinite-field reduction, with all comparison bridges retained. -/
theorem ratFunc_extension : Specs.P103.HilbertScalarExtension.ratFuncExtensionType.{u,v,w} := by
  intro k C M _ _ _ _ _ _ _ _ _ _ _ G U hzero hstd
  exact ⟨ratFunc_infinite k, scalar_extension k (RatFunc k) G U hzero hstd⟩

end P103.HilbertScalarExtension
