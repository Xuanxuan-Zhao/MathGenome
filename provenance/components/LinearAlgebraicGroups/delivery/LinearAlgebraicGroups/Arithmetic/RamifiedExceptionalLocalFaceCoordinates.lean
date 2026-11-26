import Batteries.Tactic.OpenPrivate
import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalOppositeWallLayer
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalRationalUnitTorus

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.RamifiedExceptionalLocalFaceCoordinates
open CategoryTheory WithZero
open scoped CategoryTheory.MonObj TensorProduct WithZero Pointwise Classical
open ExceptionalAffineRootSystems (ApartmentRoots threshold)
open ExceptionalAffineBruhat (FieldPoints LocalComparison ScalarComparison)
open ExceptionalAffineBuilding (Building parahoric standardWallSubgroup)
open ExceptionalMarkedRootDescent (wallMatrix rankOneMatrixWord)
open IntegralRootRelations (upper lower)
open ExceptionalIwahoriCongruence (cellValue integralRing)
open ExceptionalIwahoriImageComparison
  (markedBorelReduction residueReduction)
open ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open IntegralSemisimpleModel (Model integerAlgebra integralPointFunctor)
open Pinning (BasedRootDatum)

universe u v

section Chart

open AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory Opposite
open IntegralSemisimpleModel (IntegralAlgebra IntegralMarking Integers integralSpec
  additivePoint additiveScheme product torusPoint splitTorus cellMap)
open ExceptionalIwahoriCongruence (CellValues cellValuePoint rootValuePoint)
open OrderedRootProducts (Enumerates)

private theorem additivePoint_injective (R : IntegralAlgebra.{u}) :
    Function.Injective (additivePoint R) := by
  intro a b h
  have he := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).map_injective h
  have h' := Quiver.Hom.op_inj he
  have hv := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom h') Polynomial.X
  simpa [CommAlgCat.hom_ofHom] using hv

private theorem torusPoint_injective (D : BasedRootDatum.{u}) (R : IntegralAlgebra.{u}) :
    Function.Injective (torusPoint D R) := by
  intro a b hab
  have h := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).map_injective hab
  have h' := Quiver.Hom.op_inj h
  apply MonoidHom.ext
  intro m
  apply Units.ext
  have hval := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom h')
    (MonoidAlgebra.of Integers.{u} (Multiplicative D.X) m)
  rw [CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom,
    MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at hval
  exact hval

private theorem rootValuePoint_injective {I : Type u} (L : IntegralSemisimpleModel.AdditiveLine.{u})
    (R : IntegralAlgebra.{u}) (l : List I) :
    Function.Injective (rootValuePoint L R l) := by
  induction l with
  | nil =>
    intro x y _
    exact funext (fun i => Fin.elim0 i)
  | cons a l ih =>
    intro x y h
    have he : x 0 = y 0 := additivePoint_injective R (by
      simpa only [rootValuePoint, lift_fst] using
        congrArg (fun p => p ≫ fst L.group.X (product (fun _ : I => L.group.X) l)) h)
    have ht : Fin.tail x = Fin.tail y := ih (by
      simpa only [rootValuePoint, lift_snd] using
        congrArg (fun p => p ≫ snd L.group.X (product (fun _ : I => L.group.X) l)) h)
    exact funext (Fin.cases he (congrFun ht))

/-- The actual ordered integral cell has unique scalar coordinates. -/
theorem cellValue_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (hn : Enumerates negative {a | ¬ D.base.IsPos a})
    (hp : Enumerates positive {a | D.base.IsPos a}) :
    Function.Injective (cellValue M R negative positive) := by
  intro a b hab
  let c := cellMap M.line M.torus M.root negative positive
  have : IsOpenImmersion c.left := M.openCell negative positive hn hp
  have hv : cellValuePoint M.line R negative positive a =
      cellValuePoint M.line R negative positive b := by
    apply Over.OverMorphism.ext
    exact (cancel_mono c.left).mp (congrArg Over.Hom.left hab)
  have h₁ : a.1 = b.1 := rootValuePoint_injective _ _ _ (by
    simpa only [cellValuePoint, lift_fst] using congrArg (fun z => z ≫ fst _ _) hv)
  have hs := congrArg (fun z => z ≫ snd _ _) hv
  simp only [cellValuePoint, lift_snd] at hs
  have h₂ : a.2.1 = b.2.1 := torusPoint_injective D R (by
    simpa only [lift_fst] using congrArg (fun z => z ≫ fst _ _) hs)
  have h₃ : a.2.2 = b.2.2 := rootValuePoint_injective _ _ _ (by
    simpa only [lift_snd] using congrArg (fun z => z ≫ snd _ _) hs)
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

end Chart


section ChartScaling

open AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory Opposite
open IntegralSemisimpleModel (IntegralAlgebra IntegralMarking IntegralPoints Integers
  integralSpec additivePoint torusPoint TorusValues splitTorus cellMap rootProduct product)
open ExceptionalIwahoriCongruence (CellValues cellValuePoint rootValuePoint scaleCellValues
  mapCellValues changeRing)
open ExceptionalMarkedRootDescent (markedRootPoint)

private theorem changeRing_additivePoint {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (z : R) :
    changeRing f (additivePoint R z) = additivePoint S (f.hom z) := by
  unfold changeRing additivePoint
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact (Polynomial.aeval_algHom f.hom z).symm

private theorem changeRing_torusPoint {D : BasedRootDatum.{u}} {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (t : TorusValues D R) :
    changeRing f (torusPoint D R t) = torusPoint D S ((Units.map f.hom.toRingHom).comp t) := by
  unfold changeRing torusPoint
  erw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext
  · intro m
    change f.hom (MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
      ((Units.coeHom R).comp t) (MonoidAlgebra.of Integers.{u} (Multiplicative D.X) m)) =
      MonoidAlgebra.lift Integers.{u} S (Multiplicative D.X)
        ((Units.coeHom S).comp ((Units.map f.hom.toRingHom).comp t))
        (MonoidAlgebra.of Integers.{u} (Multiplicative D.X) m)
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]
    rfl
  · ext

private theorem changeRing_rootValuePoint {I : Type u} (L : IntegralSemisimpleModel.AdditiveLine.{u})
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List I) (z : Fin l.length → R) :
    changeRing f (rootValuePoint L R l z) = rootValuePoint L S l (fun i => f.hom (z i)) := by
  induction l with
  | nil =>
    unfold rootValuePoint
    exact comp_toUnit _
  | cons a l ih =>
    change integralSpec.map f.op ≫ lift (L.point R (z 0)) (rootValuePoint L R l (Fin.tail z)) =
      lift (L.point S (f.hom (z 0))) (rootValuePoint L S l (fun i => f.hom (Fin.tail z i)))
    rw [comp_lift]
    congr 1
    · exact changeRing_additivePoint f (z 0)
    · exact ih (Fin.tail z)

/-- The marked integral cell and its scalar coordinates commute with scalar
change, including reduction modulo the maximal ideal. -/
theorem changeRing_cellValue {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (negative positive : List D.I)
    (z : CellValues D R negative positive) :
    changeRing f (cellValue M R negative positive z) =
      cellValue M S negative positive (mapCellValues f z) := by
  change integralSpec.map f.op ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc]
  congr 1
  unfold cellValuePoint
  rw [comp_lift, comp_lift]
  change lift (changeRing f (rootValuePoint M.line R negative z.1))
    (lift (changeRing f (torusPoint D R z.2.1)) (changeRing f (rootValuePoint M.line R positive z.2.2))) = _
  rw [changeRing_rootValuePoint, changeRing_torusPoint, changeRing_rootValuePoint]
  rfl

private theorem cellValue_eq_product {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (z : CellValues D R negative positive) :
    cellValue M R negative positive z =
      (rootValuePoint M.line R negative z.1 ≫ rootProduct M.line M.root negative) *
      ((torusPoint D R z.2.1 ≫ M.torus.hom.hom) *
        (rootValuePoint M.line R positive z.2.2 ≫ rootProduct M.line M.root positive)) := by
  simp only [cellValue, cellValuePoint, cellMap, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]

private theorem rootValuePoint_cons_eval {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (l : List D.I) (z : Fin (a :: l).length → R) :
    rootValuePoint M.line R (a :: l) z ≫ rootProduct M.line M.root (a :: l) =
      (markedRootPoint M R a (z 0) : IntegralPoints M.group R) *
        (rootValuePoint M.line R l (Fin.tail z) ≫ rootProduct M.line M.root l) := by
  rw [rootValuePoint, rootProduct]
  erw [MonObj.comp_mul]
  congr 1
  · erw [← Category.assoc, lift_fst]
    rfl
  · erw [← Category.assoc, lift_snd]

private theorem conjugate_rootProduct {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (t : TorusValues D R) (l : List D.I)
    (z : Fin l.length → R) :
    let g : IntegralPoints M.group R := torusPoint D R t ≫ M.torus.hom.hom
    MulAut.conj g (rootValuePoint M.line R l z ≫ rootProduct M.line M.root l) =
      rootValuePoint M.line R l (fun i => (t (Multiplicative.ofAdd (D.datum.root l[i])) : R) * z i) ≫
        rootProduct M.line M.root l := by
  dsimp only
  induction l with
  | nil => simp [rootProduct, MonObj.comp_one]
  | cons a l ih =>
    rw [rootValuePoint_cons_eval, rootValuePoint_cons_eval, map_mul, ih, MulAut.conj_apply]
    simp only [markedRootPoint]
    rw [M.conjugation]
    rfl

/-- Conjugation by the marked torus scales each absolute root slot by its
character at the given torus point. -/
theorem changeRing_injective_of_affine {X : IntegralSemisimpleModel.IntegralScheme.{u}}
    (hX : IsAffine X.left) {R S : IntegralAlgebra.{u}} (f : R ⟶ S)
    (hf : Function.Injective f.hom) : Function.Injective (changeRing (X := X) f) := by
  intro x y hxy
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let ff := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let a := ff.preimage (x ≫ e.inv)
  let b := ff.preimage (y ≫ e.inv)
  have hab : a.unop ≫ f = b.unop ≫ f := by
    apply Quiver.Hom.op_inj
    apply ff.map_injective
    change integralSpec.map (f.op ≫ a) = integralSpec.map (f.op ≫ b)
    simpa only [Functor.map_comp, a, b, Functor.FullyFaithful.map_preimage, ← Category.assoc] using
      congrArg (· ≫ e.inv) hxy
  have hd : a.unop = b.unop := by
    ext c
    exact hf (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom hab) c)
  apply (cancel_mono e.inv).mp
  simpa only [a, b, Functor.FullyFaithful.map_preimage] using congrArg integralSpec.map
    (Quiver.Hom.unop_inj hd)


end ChartScaling

attribute [local instance] integerAlgebra

section Face

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- A point of the closed standard alcove permits every parameter in the
Iwahori chart at nonnegative scaled depth. -/
theorem iwahoriRootDepthsAtFace {C : LocalComparison (j := j) (Wf := Wf) A p} (q : ℕ) (hB : C.Bruhat q)
    (x : V) (hx : ∀ a : J × ℤ, A.positive p a → 0 ≤ A.wallValue a x)
    (g : C.I) :
    ∃ (z : C.chart.chart.torus × (∀ a, C.chart.parameter a)),
      cellValue M.toIntegralMarking (integralRing K) C.chart.negative C.chart.positive
        (C.chart.chart.coordinates z.1 z.2) = j g ∧
      (∀ χ, ExceptionalLocalRootCoordinates.normalizedValuation K (z.1.val χ : K) = 1) ∧
      ∀ a, C.chart.value a (z.2 a) = 0 ∨
        ∃ n : ℤ, C.chart.value a (z.2 a) = exp (-n) ∧ 0 ≤ A.root a x + (n : ℚ) := by
  obtain ⟨z, ⟨hz, ht, hd⟩, _⟩ := (hB.base_chart g).mp g.property
  refine ⟨z, hz, ht, fun a => ?_⟩
  let v := C.chart.value a (z.2 a)
  by_cases hv : v = 0
  · exact Or.inl hv
  right
  let n := -log v
  have hn : v = exp (-n) := by simpa [n] using (exp_log hv).symm
  refine ⟨n, hn, ?_⟩
  have hdepth : threshold (A.root a p) ≤ n := by
    have hd' : v ≤ exp (-threshold (A.root a p)) := hd a
    simpa only [hn, exp_le_exp, neg_le_neg_iff] using hd'
  have hpos : A.positive p (a, threshold (A.root a p)) := by
    change 0 < A.root a p + (threshold (A.root a p) : ℚ)
    have hh := Int.lt_floor_add_one (-(A.root a p))
    rw [threshold, Int.cast_add, Int.cast_one]
    linarith
  exact (hx _ hpos).trans (add_le_add_right (Int.cast_le.mpr hdepth) _)

variable (C : LocalComparison (j := j) (Wf := Wf) A p)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- No parameter is lost by passing to the absolute chart when each
relative direction occurs among its marked root slots. -/
theorem localRootChart_injective (C : ExceptionalAffineBruhat.LocalRootChart
    (M := M) (j := j) A p) (hsurj : Function.Surjective C.direction) :
    Function.Injective (fun b : C.chart.torus × (∀ i, C.parameter i) =>
      cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
        (C.chart.coordinates b.1 b.2)) := by
  intro a b hab
  obtain ⟨a₀, f⟩ := a
  obtain ⟨b₀, g⟩ := b
  have h := cellValue_injective M.toIntegralMarking _ C.negative C.positive
    C.negative_enumerates C.positive_enumerates hab
  refine Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) h)) (funext fun i => ?_)
  obtain ⟨r, rfl⟩ := hsurj i
  by_cases hr : D.base.IsPos r
  · obtain ⟨n, hn⟩ := List.mem_iff_getElem.mp ((C.positive_enumerates.2 r).mpr hr)
    have hx := congrFun (congrArg (fun z => z.2.2) h) ⟨n, hn.1⟩
    have hi : C.chart.pos ⟨n, hn.1⟩ = C.direction r := (C.pos_slots _).trans (congrArg C.direction hn.2)
    change algebraMap _ K (C.chart.posUnit ⟨n, hn.1⟩ : IntegralSemisimpleModel.Integers.{u}) *
        C.chart.posMap ⟨n, hn.1⟩ (f (C.chart.pos ⟨n, hn.1⟩)) =
      algebraMap _ K (C.chart.posUnit ⟨n, hn.1⟩ : IntegralSemisimpleModel.Integers.{u}) *
        C.chart.posMap ⟨n, hn.1⟩ (g (C.chart.pos ⟨n, hn.1⟩)) at hx
    rw [← hi]
    exact (C.chart.posMap _).injective (mul_left_cancel₀
      ((C.chart.posUnit ⟨n, hn.1⟩).isUnit.map (algebraMap _ K)).ne_zero hx)
  · obtain ⟨n, hn⟩ := List.mem_iff_getElem.mp ((C.negative_enumerates.2 r).mpr hr)
    have hx := congrFun (congrArg Prod.fst h) ⟨n, hn.1⟩
    have hi : C.chart.neg ⟨n, hn.1⟩ = C.direction r := (C.neg_slots _).trans (congrArg C.direction hn.2)
    change algebraMap _ K (C.chart.negUnit ⟨n, hn.1⟩ : IntegralSemisimpleModel.Integers.{u}) *
        C.chart.negMap ⟨n, hn.1⟩ (f (C.chart.neg ⟨n, hn.1⟩)) =
      algebraMap _ K (C.chart.negUnit ⟨n, hn.1⟩ : IntegralSemisimpleModel.Integers.{u}) *
        C.chart.negMap ⟨n, hn.1⟩ (g (C.chart.neg ⟨n, hn.1⟩)) at hx
    rw [← hi]
    exact (C.chart.negMap _).injective (mul_left_cancel₀
      ((C.chart.negUnit ⟨n, hn.1⟩).isUnit.map (algebraMap _ K)).ne_zero hx)

private theorem upper_mem_iwahori (q : ℕ) (hB : C.Bruhat q) (a : A.SimpleWall p)
    (r : Matrix.SpecialLinearGroup (Fin 2) (C.chart.parameter a.val.1) →* G)
    (c : (C.chart.parameter a.val.1)ˣ) (u₀ : C.chart.chart.torus)
    (hu : u₀.val = 1) (hc : C.chart.value a.val.1 (c : C.chart.parameter a.val.1) = 1)
    (hr : ∀ x : C.chart.parameter a.val.1, j (r (upper x)) =
      cellValue M.toIntegralMarking (integralRing K) C.chart.negative C.chart.positive
        (C.chart.chart.coordinates u₀
          (Function.update (fun _ => 0) a.val.1 ((c : C.chart.parameter a.val.1) * x))))
    (hcell : Function.Injective (fun b : C.chart.chart.torus × (∀ i, C.chart.parameter i) =>
      cellValue M.toIntegralMarking (integralRing K) C.chart.negative C.chart.positive
        (C.chart.chart.coordinates b.1 b.2)))
    (x : C.chart.parameter a.val.1) (hx : C.chart.value a.val.1 x ≤ exp (-a.val.2)) :
    r (upper x) ∈ C.I := by
  classical
  let z : C.chart.chart.torus × (∀ i, C.chart.parameter i) :=
    (u₀, Function.update (fun _ => 0) a.val.1 ((c : C.chart.parameter a.val.1) * x))
  have hb : ∀ i, C.chart.value i (z.2 i) ≤ exp (-threshold (A.root i p)) := by
    intro i
    by_cases hi : i = a.val.1
    · subst i
      simp only [z, Function.update_self, map_mul, hc, one_mul]
      rwa [← C.chart.signs.simple_index _ a.property]
    · simp only [z, Function.update_of_ne hi, map_zero, zero_le]
  have ht : ∀ χ, ExceptionalLocalRootCoordinates.normalizedValuation K (z.1.val χ : K) = 1 := by
    intro χ
    simp [z, hu]
  have hchart : ∃! b : C.chart.chart.torus × (∀ i, C.chart.parameter i),
      cellValue M.toIntegralMarking (integralRing K) C.chart.negative C.chart.positive
        (C.chart.chart.coordinates b.1 b.2) = j (r (upper x)) ∧
      (∀ χ, ExceptionalLocalRootCoordinates.normalizedValuation K (b.1.val χ : K) = 1) ∧
      ∀ i, C.chart.value i (b.2 i) ≤ exp (-threshold (A.root i p)) := by
    exact ⟨z, ⟨(hr x).symm, ht, hb⟩, fun b hb => hcell (hb.1.trans (hr x))⟩
  exact (hB.base_chart _).mpr hchart

private theorem wallMatrix_val {P : Type*} [Field P] (t : Pˣ) :
    (wallMatrix t).val = !![0, -(t : P); (↑t⁻¹ : P), 0] := by
  simp only [wallMatrix, rankOneMatrixWord, Matrix.SpecialLinearGroup.coe_mul]
  have ht : (t : P) ≠ 0 := Units.ne_zero t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two, ht]

private theorem wall_mul_upper {P : Type*} [Field P] (t : Pˣ) (x : P) :
    wallMatrix t * upper x = lower (-(↑t⁻¹ : P) ^ 2 * x) * wallMatrix t := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, wallMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two, inv_pow, mul_assoc, mul_left_comm]
  field_simp [Units.ne_zero t]

private theorem wallMatrixLayers (T : Set (A.SimpleWall p))
    (a : A.SimpleWall p) (ha : a ∈ T)
    (r : Matrix.SpecialLinearGroup (Fin 2) (C.chart.parameter a.val.1) →* G)
    (t : (C.chart.parameter a.val.1)ˣ)
    (ht : C.chart.value a.val.1 (t : C.chart.parameter a.val.1) = exp (-a.val.2))
    (hn : (C.lift (C.coxeter.coxeter.simple a) : G) = r (wallMatrix t))
    (hU : (fun z => r (upper z)) '' {z | C.chart.value a.val.1 z ≤ exp (-a.val.2)} ⊆ C.I) :
    let P := C.chart.parameter a.val.1
    let v := C.chart.value a.val.1
    let n := (C.lift (C.coxeter.coxeter.simple a) : G)
    let U := (fun x : P => r (upper x)) '' {x | v x ≤ exp (-a.val.2)}
    let V := (fun x : P => r (lower x)) '' {x | v x ≤ exp a.val.2}
    U ⊆ parahoric C T ∧ V ⊆ parahoric C T ∧
    (∀ x : P, n * r (upper x) * n⁻¹ = r (lower (-(↑t⁻¹ : P) ^ 2 * x))) ∧
    (fun g => n * g * n⁻¹) '' U = V ∧
    r (upper (-(t : P))) ∈ U ∧ r (lower (↑t⁻¹ : P)) ∈ V ∧
    n = r (upper (-(t : P))) * r (lower (↑t⁻¹ : P)) * r (upper (-(t : P))) := by
  let P := C.chart.parameter a.val.1
  let v := C.chart.value a.val.1
  let n := (C.lift (C.coxeter.coxeter.simple a) : G)
  let U := (fun x : P => r (upper x)) '' {x | v x ≤ exp (-a.val.2)}
  let V := (fun x : P => r (lower x)) '' {x | v x ≤ exp a.val.2}
  have hinv : v (↑t⁻¹ : P) = exp a.val.2 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht, ← exp_neg, neg_neg]
  let b : P := -(↑t⁻¹ : P) ^ 2
  have hb : v b = exp (a.val.2 + a.val.2) := by
    rw [Valuation.map_neg, map_pow, hinv, exp_add, pow_two]
  have hb0 : b ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (Units.ne_zero t⁻¹))
  have hdepth (x : P) : v (b * x) ≤ exp a.val.2 ↔ v x ≤ exp (-a.val.2) := by
    have he : exp (a.val.2 + a.val.2) * exp (-a.val.2) = exp a.val.2 := by
      rw [← exp_add]; congr 1; omega
    rw [map_mul, hb, ← he]
    exact mul_le_mul_iff_right₀ (by simp)
  have hconj (x : P) : n * r (upper x) * n⁻¹ = r (lower (b * x)) := by
    have hm := congrArg r (wall_mul_upper t x)
    rw [map_mul, map_mul, ← hn] at hm
    rw [hm, mul_assoc, mul_inv_cancel, mul_one]
  have hUV : (fun g => n * g * n⁻¹) '' U = V := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨b * x, (hdepth x).2 hx, (hconj x).symm⟩
    · rintro ⟨y, hy, rfl⟩
      let x := b⁻¹ * y
      have he : b * x = y := by
        change b * (b⁻¹ * y) = y
        rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
      exact ⟨r (upper x), ⟨x, (hdepth x).1 (he ▸ hy), rfl⟩,
        (hconj x).trans (congrArg (fun z => r (lower z)) he)⟩
  have hU' : U ⊆ parahoric C T := fun _ h => Subgroup.subset_closure (Or.inl (hU h))
  have hV : V ⊆ parahoric C T := by
    rw [← hUV]
    rintro g ⟨u, hu, rfl⟩
    have hn₀ : n ∈ parahoric C T := Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩)
    have hu₀ : u ∈ parahoric C T := Subgroup.subset_closure (Or.inl (hU hu))
    exact (parahoric C T).mul_mem ((parahoric C T).mul_mem hn₀ hu₀)
      ((parahoric C T).inv_mem hn₀)
  refine ⟨hU', hV, hconj, hUV, ⟨_, ?_, rfl⟩, ⟨_, hinv.le, rfl⟩, ?_⟩
  · change v (-(t : P)) ≤ exp (-a.val.2)
    rw [Valuation.map_neg, ht]
  · rw [hn]
    simp [wallMatrix, rankOneMatrixWord, Units.val_neg]

section Reduction

variable {H O : Type*} [Group H] [Group O]

/-- The scaling map lifts to the group of integral points once its Iwahori
and simple wall generators are integral. -/
theorem liftParahoricToIntegralPoints (T : Set (A.SimpleWall p)) (f : G →* H) (i : O →* H)
    (hi : Function.Injective i) (hI : C.I ≤ i.range.comap f)
    (hwall : ∀ a ∈ T, f (C.lift (C.coxeter.coxeter.simple a)) ∈ i.range) :
    ∃ r : parahoric C T →* O, i.comp r = f.comp (parahoric C T).subtype := by
  have hp : parahoric C T ≤ i.range.comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro g (hg | ⟨a, ha, rfl⟩)
    · exact hI hg
    · exact hwall a ha
  let m : parahoric C T →* i.range :=
    MonoidHom.codRestrict (f.comp (parahoric C T).subtype) _ (fun g => hp g.property)
  let e := MonoidHom.ofInjective hi
  refine ⟨e.symm.toMonoidHom.comp m, ?_⟩
  ext g
  exact congrArg Subtype.val (e.apply_symm_apply (m g))


end Reduction
end Face


open ValuativeRel WithZero
open ExceptionalLocalRootCoordinates (normalizedValuation normalizedValueGroupMap)

open scoped NNReal Topology Valued.integer

section Valuations

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

theorem normalizedValuation_surjective (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (normalizedValuation K) := by
  change Function.Surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) ∘ valuation K)
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
    (valuation_surjective (K := K))

theorem normalizedValuation_le_one {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (a : K) :
    normalizedValuation K a ≤ 1 ↔ valuation K a ≤ 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K a) ≤ 1 ↔ _
  have ho : e 1 = 1 := e.map_one
  rw [← ho, e.strictMono.le_iff_le]

theorem normalizedValuation_lt_one {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (a : K) :
    normalizedValuation K a < 1 ↔ valuation K a < 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K a) < 1 ↔ _
  have ho : e 1 = 1 := e.map_one
  rw [← ho, e.strictMono.lt_iff_lt]

theorem normalizedValueGroupMap_apply (a : K) :
    normalizedValueGroupMap K E (normalizedValuation K a) =
      normalizedValuation E (algebraMap K E a) := by
  unfold normalizedValueGroupMap normalizedValuation
  simp [MonoidWithZeroHom.comp_apply, Valuation.map_apply]

theorem normalizedValuation_of_uniformizerRoot
    (π : K) (hπ : normalizedValuation K π = exp (-1)) (ξ : E) (d : ℕ)
    (hξ : ξ ^ d = algebraMap K E π) (a : K) (ha : a ≠ 0) :
    normalizedValuation E (algebraMap K E a) =
      (normalizedValuation E ξ) ^ ((d : ℤ) * (-log (normalizedValuation K a))) := by
  let b := -log (normalizedValuation K a)
  have hb : normalizedValuation K a = exp (-1 : ℤ) ^ b := by
    rw [← exp_zsmul]
    simpa [b] using (exp_log ((map_ne_zero (normalizedValuation K)).2 ha)).symm
  change _ = _ ^ ((d : ℤ) * b)
  rw [← normalizedValueGroupMap_apply, hb, map_zpow₀, ← hπ, normalizedValueGroupMap_apply,
    ← hξ, map_pow, ← zpow_natCast, ← zpow_mul]


end Valuations
section IntegralCells

open AlgebraicGeometry Opposite
open IntegralSemisimpleModel (IntegralAlgebra IntegralMarking IntegralPoints Integers
  integralSpec torusPoint TorusValues cocharacter)
open ExceptionalIwahoriCongruence (CellValues scaleCellValues integralRingMap
  mapCellValues changeRing changeRingHom)

private def restrictUnit {K : Type u} [Field K] [ValuativeRel K] (a : Kˣ)
    (ha : valuation K (a : K) = 1) : ((valuation K).valuationSubring)ˣ where
  val := ⟨(a : K), ha.le⟩
  inv := ⟨(↑a⁻¹ : K), by
    change valuation K (↑a⁻¹ : K) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]⟩
  val_inv := Subtype.ext a.val_inv
  inv_val := Subtype.ext a.inv_val

/-- An ordered cell with integral root coefficients and unit torus
coefficients is the base change of the same ordered integral cell. -/
theorem liftMarkedCellToIntegers {D : BasedRootDatum.{u}}
    (K : Type u) [Field K] [ValuativeRel K] (negative positive : List D.I)
    (z : CellValues D (integralRing K) negative positive)
    (hn : ∀ i, valuation K (z.1 i) ≤ 1)
    (hp : ∀ i, valuation K (z.2.2 i) ≤ 1)
    (ht : ∀ χ, valuation K (z.2.1 χ : K) = 1) :
    ∃ z₀ : CellValues D (integralRing (valuation K).valuationSubring) negative positive,
      mapCellValues (valuationRingInclusion K) z₀ = z := by
  let t : TorusValues D (integralRing (valuation K).valuationSubring) := {
    toFun χ := restrictUnit (z.2.1 χ) (ht χ)
    map_one' := Units.ext (Subtype.ext (congrArg Units.val (map_one z.2.1)))
    map_mul' χ ψ := Units.ext (Subtype.ext (congrArg Units.val (map_mul z.2.1 χ ψ))) }
  refine ⟨(fun i => ⟨z.1 i, hn i⟩, t, fun i => ⟨z.2.2 i, hp i⟩), ?_⟩
  change (_, (Units.map _).comp t, _) = z
  rfl

/-- Pointwise integrality of the scaled marked cell follows from its scaled
root coefficients and the unchanged torus units. The formula also identifies
its reduction with the marked cell on the reduced tuple. -/
theorem scaledCellReduction {D : BasedRootDatum.{u}} (M : Model D) {K E : Type u}
    [Field K] [Field E] [ValuativeRel E] (f : K →+* E)
    (negative positive : List D.I) (t : TorusValues D (integralRing E))
    (z : CellValues D (integralRing K) negative positive)
    (hN : ∀ i, valuation E ((t (Multiplicative.ofAdd (D.datum.root negative[i])) : E) *
      f (z.1 i)) ≤ 1)
    (hP : ∀ i, valuation E ((t (Multiplicative.ofAdd (D.datum.root positive[i])) : E) *
      f (z.2.2 i)) ≤ 1)
    (hT : ∀ χ, valuation E (f (z.2.1 χ : K)) = 1) :
    ∃ (z₀ : CellValues D (integralRing (valuation E).valuationSubring) negative positive)
      (p : IntegralPoints M.group (integralRing (valuation E).valuationSubring)),
      mapCellValues (valuationRingInclusion E) z₀ = scaleCellValues t (mapCellValues (integralRingMap f) z) ∧
      changeRing (valuationRingInclusion E) p =
        MulAut.conj (torusPoint D (integralRing E) t ≫ M.torus.hom.hom)
          (changeRing (integralRingMap f) (cellValue M.toIntegralMarking _ negative positive z)) ∧
      changeRing (residueReduction E) p =
        cellValue M.toIntegralMarking _ negative positive (mapCellValues (residueReduction E) z₀) := by
  let w := scaleCellValues t (mapCellValues (integralRingMap f) z)
  obtain ⟨z₀, hz₀⟩ := liftMarkedCellToIntegers E negative positive w hN hP hT
  let p := cellValue M.toIntegralMarking (integralRing (valuation E).valuationSubring) negative positive z₀
  refine ⟨z₀, p, hz₀, ?_, changeRing_cellValue M.toIntegralMarking _ _ _ _⟩
  change changeRing _ (cellValue M.toIntegralMarking _ _ _ z₀) = _
  rw [changeRing_cellValue, hz₀, changeRing_cellValue,
    ExceptionalIwahoriCongruence.scaleMarkedChart M.toIntegralMarking (integralRing E) negative positive t]

end IntegralCells

section ValuedAutomorphisms

open Filter

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]

private theorem normalizedValueGroupMap_strictMono :
    StrictMono (normalizedValueGroupMap K E) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E).strictMono.comp
    ((ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := E)).comp
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm.strictMono)

/-- The image of the normalized value group of a local field is cofinal
towards zero in the value group of a valued extension which is also local. -/
theorem localAlgebraMap_continuous : Continuous (algebraMap K E) := by
  apply continuous_of_continuousAt_zero (algebraMap K E)
  change Tendsto (algebraMap K E) (𝓝 0) (𝓝 ((algebraMap K E) 0))
  rw [map_zero, (IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro a ha
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let eE := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  let b := normalizedValueGroupMap K E
  have hmono := normalizedValueGroupMap_strictMono (K := K) (E := E)
  let r := b (exp (-1))
  have hr0 : r ≠ 0 := by
    apply ne_of_gt
    simpa only [map_zero] using hmono (show (0 : ℤᵐ⁰) < exp (-1) by simp)
  have hr : r < 1 := by
    simpa only [map_one] using hmono (show exp (-1 : ℤ) < (1 : ℤᵐ⁰) by simp)
  have hc : log r ≤ -1 := by
    have : log r < 0 := by rwa [← exp_lt_one_iff, exp_log hr0]
    omega
  have ha' : eE a ≠ 0 := by
    intro he
    exact ha (eE.injective (he.trans (map_zero eE.toMonoidWithZeroHom).symm))
  let m : ℤ := |log (eE a)| + 1
  have hm : 0 ≤ m := (abs_nonneg _).trans (le_add_of_nonneg_right (by omega : (0 : ℤ) ≤ 1))
  have hm' : -m < log (eE a) := by
    have := neg_abs_le (log (eE a))
    dsimp [m]
    omega
  have hb : b (exp (-m)) < eE a := by
    have he : exp (-m) = exp (-1 : ℤ) ^ m := by rw [← exp_zsmul]; congr 1; simp
    rw [he, map_zpow₀, show b (exp (-1)) = r from rfl, ← exp_log hr0, ← exp_zsmul,
      ← exp_log ha', exp_lt_exp]
    have hc' := mul_le_mul_of_nonneg_left hc hm
    simpa [zsmul_eq_mul] using hc'.trans_lt (by simpa using hm')
  refine (IsValuativeTopology.hasBasis_nhds_zero' K).eventually_iff.mpr
    ⟨eK.symm (exp (-m)), ?_, ?_⟩
  · intro h
    exact exp_ne_zero (eK.symm.injective (h.trans (map_zero eK.symm.toMonoidWithZeroHom).symm))
  · intro x hx
    change valuation E (algebraMap K E x) < a
    apply eE.strictMono.lt_iff_lt.mp
    change normalizedValuation E (algebraMap K E x) < eE a
    rw [← normalizedValueGroupMap_apply]
    apply lt_trans _ hb
    apply hmono
    change eK (valuation K x) < exp (-m)
    simpa only [eK.apply_symm_apply] using eK.strictMono hx

private theorem valuation_lt_one_iff_powers_tendsto {E : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (x : E) :
    valuation E x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : Valued E (ValueGroupWithZero E) := inferInstance
  have : (Valued.v (R := E)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := E).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NormedField E := Valued.toNormedField E (ValueGroupWithZero E)
  exact ((tendsto_pow_atTop_nhds_zero_iff_norm_lt_one (x := x)).trans
    (Valued.toNormedField.norm_lt_one_iff (x := x))).symm

private theorem valuation_lt_one_algEquiv [FiniteDimensional K E]
    (s : E ≃ₐ[K] E) (x : E) : valuation E (s x) < 1 ↔ valuation E x < 1 := by
  have : ContinuousSMul K E := continuousSMul_of_algebraMap K E localAlgebraMap_continuous
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : Valued K (ValueGroupWithZero K) := inferInstance
  have : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  have : CompleteSpace K := inferInstance
  have h (s : E ≃ₐ[K] E) (x : E) (hx : valuation E x < 1) : valuation E (s x) < 1 := by
    have hs : Continuous s.toLinearEquiv.toLinearMap :=
      s.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
    apply (valuation_lt_one_iff_powers_tendsto _).2
    simpa only [Function.comp_def, AlgEquiv.toLinearEquiv_apply, LinearEquiv.coe_coe,
      map_pow, map_zero] using (hs.tendsto 0).comp ((valuation_lt_one_iff_powers_tendsto x).1 hx)
  exact ⟨fun hx => by simpa only [AlgEquiv.symm_apply_apply] using h s.symm (s x) hx, h s x⟩

theorem valuationRing_mem_algEquiv [FiniteDimensional K E]
    (s : E ≃ₐ[K] E) (x : E) :
    valuation E (s x) ≤ 1 ↔ valuation E x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have hne : s x ≠ 0 := (map_ne_zero s).2 hx
  have h₀ : 0 < valuation E (s x) := bot_lt_iff_ne_bot.mpr ((map_ne_zero (valuation E)).2 hne)
  have h₁ : 0 < valuation E x := bot_lt_iff_ne_bot.mpr ((map_ne_zero (valuation E)).2 hx)
  have h := valuation_lt_one_algEquiv s x⁻¹
  rw [map_inv₀ s, map_inv₀ (valuation E), map_inv₀ (valuation E), inv_lt_one₀ h₀, inv_lt_one₀ h₁] at h
  simpa only [not_lt] using not_congr h


private theorem normalizedValuation_maxBelowOne {E : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {z : E} (hz : normalizedValuation E z < 1) : normalizedValuation E z ≤ exp (-1) := by
  let v := normalizedValuation E
  by_cases h : v z = 0
  · change v z ≤ _
    rw [h]
    exact zero_le
  rw [← exp_log h, exp_le_exp]
  change v z < 1 at hz
  rw [← exp_log h, exp_lt_one_iff] at hz
  omega

/-- An automorphism of a finite extension of local fields preserves the
normalized integer valuation on the extension. -/
theorem normalizedValuation_algEquiv [FiniteDimensional K E]
    (s : E ≃ₐ[K] E) (x : E) : normalizedValuation E (s x) = normalizedValuation E x := by
  let v := normalizedValuation E
  have horder (a b : E) : v (s a) ≤ v (s b) ↔ v a ≤ v b := by
    by_cases hb : b = 0
    · simp [hb]
    have hs : s b ≠ 0 := (map_ne_zero s).2 hb
    have h := valuationRing_mem_algEquiv s (a / b)
    rw [← normalizedValuation_le_one, ← normalizedValuation_le_one, map_div₀ s] at h
    change v (s a / s b) ≤ 1 ↔ v (a / b) ≤ 1 at h
    rw [map_div₀, map_div₀,
      div_le_one₀ (bot_lt_iff_ne_bot.mpr ((map_ne_zero v).2 hs)),
      div_le_one₀ (bot_lt_iff_ne_bot.mpr ((map_ne_zero v).2 hb))] at h
    exact h
  obtain ⟨π, hπ⟩ := normalizedValuation_surjective E (exp (-1))
  change v π = _ at hπ
  have hlt (z : E) : v (s z) < 1 ↔ v z < 1 := by
    simpa only [map_one, not_le] using not_congr (horder 1 z)
  have hπs : v (s π) = exp (-1) := by
    have hltπ : v π < 1 := by rw [hπ]; simp
    apply le_antisymm (normalizedValuation_maxBelowOne ((hlt π).2 hltπ))
    have hb : v (s.symm π) < 1 := (hlt (s.symm π)).1 (by simpa using hltπ)
    have hle : v (s.symm π) ≤ v π := hπ ▸ normalizedValuation_maxBelowOne hb
    simpa only [AlgEquiv.apply_symm_apply, hπ] using (horder (s.symm π) π).2 hle
  by_cases hx : x = 0
  · simp [hx]
  let n := -log (v x)
  have heq : v (π ^ n) = v x := by
    rw [map_zpow₀, hπ, ← exp_zsmul]
    simpa [n] using (exp_log ((map_ne_zero v).2 hx))
  have heq' : v (s (π ^ n)) = v (s x) :=
    le_antisymm ((horder _ _).2 heq.le) ((horder _ _).2 heq.ge)
  rw [← heq', map_zpow₀ s, map_zpow₀ v, hπs, ← hπ, ← map_zpow₀, heq]

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

/-- The induced automorphism of the ring of integers over the coefficient
ring. Its reduction is functorial under compatible scalar maps. -/
def valuationRingAlgEquiv [FiniteDimensional K E] (s : E ≃ₐ[K] E) :
    (valuation E).valuationSubring ≃ₐ[(valuation K).valuationSubring] (valuation E).valuationSubring where
  toFun a := ⟨s a, (valuationRing_mem_algEquiv s a).2 a.property⟩
  invFun a := ⟨s.symm a, (valuationRing_mem_algEquiv s.symm a).2 a.property⟩
  left_inv a := Subtype.ext (s.symm_apply_apply a)
  right_inv a := Subtype.ext (s.apply_symm_apply a)
  map_mul' a b := Subtype.ext (s.map_mul a b)
  map_add' a b := Subtype.ext (s.map_add a b)
  commutes' a := Subtype.ext (s.commutes (a : K))

end ValuedAutomorphisms


open IsLocalRing

section LeadingCoefficients

variable {k K E : Type*} [Field k] [Field K] [Field E] [Algebra k K] [Algebra K E]
  [ValuativeRel k] [ValuativeRel K] [ValuativeRel E] [ValuativeExtension k K] [ValuativeExtension K E]

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

local notation "𝒪" L => Valuation.integer (valuation L)

/-- A residue-trivial extension forces the induced integral automorphism
over the base valuation ring to act trivially on residues. -/
theorem residueFixedByIntegralAutomorphism [Finite (ResidueField (𝒪 k))]
    [Finite (ResidueField (𝒪 K))]
    (hκ : Nat.card (ResidueField (𝒪 k)) = Nat.card (ResidueField (𝒪 K)))
    (t : (𝒪 K) ≃ₐ[(𝒪 k)] (𝒪 K)) :
    ∀ b, residue (𝒪 K) (t b) = residue (𝒪 K) b := by
  let f := ResidueField.map (algebraMap (𝒪 k) (𝒪 K))
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨f.injective, hκ⟩).2
  intro b
  obtain ⟨v, hv⟩ := hsurj (residue (𝒪 K) b)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v
  change residue (𝒪 K) (algebraMap (𝒪 k) (𝒪 K) c) = _ at hv
  have : IsLocalHom t.toRingHom := IsLocalHom.of_surjective _ t.surjective
  have hfix := congrArg (ResidueField.map t.toRingHom) hv
  change residue (𝒪 K) (t (algebraMap (𝒪 k) (𝒪 K) c)) = residue (𝒪 K) (t b) at hfix
  rw [AlgEquiv.commutes, hv] at hfix
  exact hfix.symm

/-- An automorphism of the valuation ring sends a uniformizer to the same
uniformizer multiplied by an integral unit. -/
theorem uniformizerRatio
    (t : (𝒪 K) ≃+* (𝒪 K)) (π : 𝒪 K)
    (hπ : maximalIdeal (𝒪 K) = Ideal.span {π}) :
    ∃ ε : (𝒪 K)ˣ, t π = (ε : 𝒪 K) * π := by
  have hid : Ideal.span {t π} = Ideal.span {π} := by
    calc
      Ideal.span {t π} = (Ideal.span {π}).map t.toRingHom := by
        rw [Ideal.map_span, Set.image_singleton]
        rfl
      _ = Ideal.span {π} := by
        rw [← hπ]
        exact IsLocalRing.map_ringEquiv_maximalIdeal t
  obtain ⟨ε, he⟩ := Ideal.span_singleton_eq_span_singleton.mp hid.symm
  exact ⟨ε, by simpa only [mul_comm] using he.symm⟩

/-- After the common auxiliary uniformizer power is factored out, the
two residue entries come from one leading coefficient multiplied by the
marking units and, in the second entry, the conjugate-uniformizer ratio. -/
theorem scaledPairedRootCoefficients
    (τ : K ≃+* K) (τ₀ : (𝒪 K) ≃+* (𝒪 K))
    (hτ₀ : ∀ b : 𝒪 K, (τ₀ b : K) = τ (b : K))
    (hτ : ∀ b, residue (𝒪 K) (τ₀ b) = residue (𝒪 K) b)
    (π : Kˣ) (ξ : Eˣ) (d : ℕ) (hξ : (ξ : E) ^ d = algebraMap K E (π : K))
    (ε : (𝒪 K)ˣ) (hε : τ (π : K) = ((ε : 𝒪 K) : K) * (π : K))
    (c₁ c₂ : (𝒪 E)ˣ) (s m : ℤ) (b : 𝒪 K) :
    ∃ z₁ z₂ : 𝒪 E,
      (ξ : E) ^ s * (c₁ : 𝒪 E) * algebraMap K E ((π : K) ^ m * (b : K)) =
        (ξ : E) ^ (s + (d : ℤ) * m) * (z₁ : E) ∧
      (ξ : E) ^ s * (c₂ : 𝒪 E) * algebraMap K E (τ ((π : K) ^ m * (b : K))) =
        (ξ : E) ^ (s + (d : ℤ) * m) * (z₂ : E) ∧
      let red := residue (𝒪 E)
      let f := algebraMap (𝒪 K) (𝒪 E)
      red z₁ = red c₁ * red (f b) ∧
      red z₂ = (red c₂ * red (f ((ε ^ m : (𝒪 K)ˣ) : 𝒪 K))) * red (f b) := by
  let f := algebraMap (𝒪 K) (𝒪 E)
  let z₁ : 𝒪 E := (c₁ : 𝒪 E) * f b
  let z₂ : 𝒪 E := (c₂ : 𝒪 E) * f ((ε ^ m : (𝒪 K)ˣ) : 𝒪 K) * f (τ₀ b)
  have fcoe (z : 𝒪 K) : (f z : E) = algebraMap K E (z : K) := rfl
  have mulcoe (z w : 𝒪 E) : ((z * w : 𝒪 E) : E) = (z : E) * (w : E) := rfl
  have unitcoe : (((ε ^ m : (𝒪 K)ˣ) : 𝒪 K) : K) = (((ε : 𝒪 K) : K) ^ m) := by
    let i := (valuation K).valuationSubring.subtype.toMonoidHom
    change ((Units.map i (ε ^ m) : Kˣ) : K) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hpow : (ξ : E) ^ (s + (d : ℤ) * m) = (ξ : E) ^ s * (algebraMap K E (π : K)) ^ m := by
    rw [zpow_add₀ (Units.ne_zero ξ), zpow_mul, zpow_natCast, hξ]
  refine ⟨z₁, z₂, ?_, ?_, ?_⟩
  · rw [hpow, map_mul, map_zpow₀]
    simp only [z₁, mulcoe, fcoe]
    ac_rfl
  · rw [hpow, map_mul τ, map_zpow₀, hε, mul_zpow, map_mul, map_mul, map_zpow₀, map_zpow₀]
    simp only [z₂, mulcoe, fcoe, unitcoe, hτ₀, map_zpow₀]
    ring
  · let red := residue (𝒪 E)
    have hb : red (f (τ₀ b)) = red (f b) := by
      simpa only [ResidueField.map_residue] using congrArg (ResidueField.map f) (hτ b)
    change red z₁ = red c₁ * red (f b) ∧
      red z₂ = (red c₂ * red (f ((ε ^ m : (𝒪 K)ˣ) : 𝒪 K))) * red (f b)
    exact ⟨map_mul red _ _, by simp only [z₂, map_mul, hb]⟩

end LeadingCoefficients
open ExceptionalAffineBruhat (FoldedApartment FoldedLevel RamifiedReference)
open ExceptionalAffineRootSystems (FoldedRootDirection IsLongF4Doubled foldedDepthDenominator)
open ExceptionalValuedTorusNormalizer (invariantApartment)
open IntegralSemisimpleModel (Integers)

private def foldedStep (i : FoldedRootDirection) : ℕ :=
  if IsLongF4Doubled i.val then 2 else 1

/-- The absolute character of the integral scaling cocharacter has an
exponent measured in the same units as the folded parameter depth. -/
theorem foldedRootScalingExponent {D : BasedRootDatum.{u}} {τ : Pinning.BasedIso D D}
    (A : FoldedApartment τ) (x : invariantApartment D τ) (y : D.Y) (d : ℕ)
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y) (i : D.I) :
    (D.datum.toLinearMap (D.datum.root i) y : ℚ) =
      ((d : ℚ) * (foldedStep (A.direction i) : ℚ)) * A.roots.root (A.direction i) x := by
  let l := (ApartmentRoots.split D.datum ℚ).root i
  have hl : (D.datum.toLinearMap (D.datum.root i) y : ℚ) = l ((1 : ℚ) ⊗ₜ[ℤ] y) :=
    (RootData.extendFunctional_one_tmul ℚ (D.datum.toLinearMap (D.datum.root i)) y).symm
  rw [hl, ← hy, map_smul, smul_eq_mul, A.root_value]
  change (2 * (d : ℚ)) * l x.val = _ * (_ * l x.val)
  by_cases h : IsLongF4Doubled (A.direction i).val
  · rw [foldedStep, foldedDepthDenominator, ite_eq_left h, ite_eq_left h, Nat.cast_one, one_mul]
    push_cast
    ring
  · rw [foldedStep, foldedDepthDenominator, ite_eq_right h, ite_eq_right h, Nat.cast_one, mul_one]
    push_cast
    ring

section Slots

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional k K] [ValuativeExtension k K]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {σK : Gal(K/k)} {f : L →ₐ[F] K} {A : FoldedApartment (R.diagram σ)}
  (X : FoldedLevel R σ σK f A)

/-- The ring embedding in a marked slot multiplies normalized depths by
two for a fixed root and by one for either member of a paired root. -/
theorem foldedRootSlotEmbedding (i : D.I) :
    let C := X.comparison.chart
    let a := A.direction i
    ∃ e : C.parameter a →+* K, C.UsesSlot i a e ∧
      ∀ z, normalizedValuation K (e z) = C.value a z ^ foldedStep a := by
  dsimp only
  by_cases hlong : IsLongF4Doubled (A.direction i).val
  · obtain ⟨e, hslot, hv⟩ := X.singleton i ((A.long i).1 hlong)
    refine ⟨(algebraMap k K).comp e.toRingHom, hslot, fun z => ?_⟩
    change normalizedValuation K (algebraMap k K (e z)) = _
    rw [X.ramification, hv, foldedStep, ite_eq_left hlong]
  · obtain ⟨j, hj, e, h₁, h₂, he⟩ := X.pair (A.direction i) hlong
    rcases (A.orbits j i).mp hj with h | h
    · subst i
      refine ⟨e.toRingHom, h₁, ?_⟩
      intro z
      change normalizedValuation K (e z) = _
      rw [foldedStep, ite_eq_right hlong, pow_one, he]
    · subst i
      refine ⟨σK.toRingHom.comp e.toRingHom, h₂, ?_⟩
      intro z
      change normalizedValuation K (σK (e z)) = _
      rw [normalizedValuation_algEquiv, he, foldedStep, ite_eq_right hlong, pow_one]


private theorem normalizedIntegerUnit {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (c : Integers.{u}ˣ) :
    normalizedValuation K (algebraMap Integers.{u} K (c : Integers.{u})) = 1 := by
  let v := valuation K
  let c₀ := Units.map (algebraMap Integers.{u} v.integer).toMonoidHom c
  have hunit := (Valuation.integer.integers v).valuation_unit c₀
  change v (algebraMap Integers.{u} K (c : Integers.{u})) = 1 at hunit
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (v _) = 1
  rw [hunit]
  exact e.map_one

private theorem castParameter_valuation {J : Type*} {P : J → Type*} [∀ j, Field (P j)]
    (v : ∀ j, Valuation (P j) ℤᵐ⁰) {a b : J} (h : a = b) (x : P a) :
    v b (h ▸ x) = v a x := by
  cases h
  rfl

private theorem castParameter_cancel {J : Type*} {P : J → Type*}
    {a b : J} (h : a = b) (x : P a) : h.symm ▸ (h ▸ x : P b) = x := by
  cases h
  rfl

theorem foldedNegativeSlotValuation
    (t : X.comparison.chart.chart.torus) (z : ∀ a, X.comparison.chart.parameter a)
    (l : Fin X.comparison.chart.negative.length) :
    let C := X.comparison.chart
    normalizedValuation K ((C.chart.coordinates t z).1 l) =
      C.value (C.chart.neg l) (z (C.chart.neg l)) ^ foldedStep (A.direction C.negative[l]) := by
  let C := X.comparison.chart
  let i := C.negative[l]
  obtain ⟨e, huse, hval⟩ := foldedRootSlotEmbedding X i
  have h : C.chart.neg l = A.direction i :=
    (C.neg_slots l).trans (congrFun X.directions i)
  let w : C.parameter (A.direction i) := h ▸ z (C.chart.neg l)
  have hw : h.symm ▸ w = z (C.chart.neg l) := castParameter_cancel h _
  have hcoord := huse.2.1 l h w rfl
  rw [hw] at hcoord
  change normalizedValuation K ((algebraMap Integers.{u} K (C.chart.negUnit l : Integers.{u})) *
    C.chart.negMap l (z (C.chart.neg l))) = _
  rw [map_mul, normalizedIntegerUnit, one_mul, hcoord, hval, castParameter_valuation C.value h]

theorem foldedPositiveSlotValuation
    (t : X.comparison.chart.chart.torus) (z : ∀ a, X.comparison.chart.parameter a)
    (l : Fin X.comparison.chart.positive.length) :
    let C := X.comparison.chart
    normalizedValuation K ((C.chart.coordinates t z).2.2 l) =
      C.value (C.chart.pos l) (z (C.chart.pos l)) ^ foldedStep (A.direction C.positive[l]) := by
  let C := X.comparison.chart
  let i := C.positive[l]
  obtain ⟨e, huse, hval⟩ := foldedRootSlotEmbedding X i
  have h : C.chart.pos l = A.direction i :=
    (C.pos_slots l).trans (congrFun X.directions i)
  let w : C.parameter (A.direction i) := h ▸ z (C.chart.pos l)
  have hw : h.symm ▸ w = z (C.chart.pos l) := castParameter_cancel h _
  have hcoord := huse.2.2 l h w rfl
  rw [hw] at hcoord
  change normalizedValuation K ((algebraMap Integers.{u} K (C.chart.posUnit l : Integers.{u})) *
    C.chart.posMap l (z (C.chart.pos l))) = _
  rw [map_mul, normalizedIntegerUnit, one_mul, hcoord, hval, castParameter_valuation C.value h]

end Slots


section IwahoriScaling

open CategoryTheory
open scoped CategoryTheory.MonObj
open ExceptionalAffineBruhat (FieldPoints scalarPoints)
open ExceptionalLocalRootCoordinates (normalizedValueGroupMap)
open ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open ExceptionalIwahoriCongruence (CellValues cellValue integralRing integralRingMap
  changeRing changeRingHom mapCellValues)
open IntegralSemisimpleModel (IntegralPoints TorusValues torusPoint cocharacter integralPointFunctor)

variable {F L k K E : Type u} [Field F] [Field L] [Field k] [Field K] [Field E]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K] [Algebra K E]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [FiniteDimensional k K] [ValuativeExtension k K] [ValuativeExtension K E]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {σK : Gal(K/k)} {f : L →ₐ[F] K} {A : FoldedApartment (R.diagram σ)}
  (X : FoldedLevel R σ σK f A)

omit [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [FiniteDimensional k K] [ValuativeExtension k K] in
private theorem scaledParameterValuation_le_one
    (π : K) (hπ : normalizedValuation K π = exp (-1))
    (d : ℕ) (ξ : Eˣ) (hξ : (ξ : E) ^ d = algebraMap K E π)
    (s m : ℤ) (a : K) (ha : normalizedValuation K a = exp (-m))
    (hm : 0 ≤ s + (d : ℤ) * m) :
    valuation E ((ξ : E) ^ s * algebraMap K E a) ≤ 1 := by
  apply (normalizedValuation_le_one _).1
  let v := normalizedValuation E
  have hne : v (ξ : E) ≠ 0 := (map_ne_zero v).2 (Units.ne_zero ξ)
  have ha₀ : a ≠ 0 := (map_ne_zero (normalizedValuation K)).1 (by rw [ha]; simp)
  have hπlt : normalizedValuation K π < 1 := by rw [hπ]; simp
  have hπlt' : normalizedValuation E (algebraMap K E π) < 1 := by
    apply (normalizedValuation_lt_one _).2
    rw [← map_one (valuation E), ← map_one (algebraMap K E), ← (valuation E).vlt_iff_lt,
      ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt, map_one]
    exact (normalizedValuation_lt_one _).1 hπlt
  have hξlt : v (ξ : E) < 1 := by
    by_contra! h
    apply hπlt'.not_ge
    rw [← hξ, map_pow]
    exact one_le_pow₀ h
  change v _ ≤ 1
  rw [map_mul, map_zpow₀, normalizedValuation_of_uniformizerRoot π hπ (ξ : E) d hξ a ha₀,
    ha, log_exp, neg_neg, ← zpow_add₀ hne]
  exact zpow_le_one₀ (bot_lt_iff_ne_bot.mpr hne) hξlt.le hm

omit [Algebra F K] in
private theorem integralScaledSlot
    (x : invariantApartment D (R.diagram σ))
    (π : K) (hπ : normalizedValuation K π = exp (-1))
    (d : ℕ) (ξ : Eˣ) (hξ : (ξ : E) ^ d = algebraMap K E π)
    (y : D.Y) (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (i : D.I) (v : ℤᵐ⁰) (z : K)
    (hz : normalizedValuation K z = v ^ foldedStep (A.direction i))
    (hdepth : v = 0 ∨ ∃ n : ℤ, v = exp (-n) ∧ 0 ≤ A.roots.root (A.direction i) x + (n : ℚ)) :
    valuation E ((ξ : E) ^ D.datum.toLinearMap (D.datum.root i) y * algebraMap K E z) ≤ 1 := by
  let b := foldedStep (A.direction i)
  have hb : 0 < b := by
    unfold b foldedStep
    split <;> omega
  rcases hdepth with he | ⟨n, hv, hn⟩
  · have hzero : z = 0 := (normalizedValuation K).zero_iff.mp (by
      rw [hz, he]
      exact zero_pow hb.ne')
    simp [hzero]
  · let m : ℤ := (b : ℤ) * n
    have hm : normalizedValuation K z = exp (-m) := by
      rw [hz, hv]
      change exp (-n) ^ b = exp (-m)
      rw [← exp_nsmul]
      congr 1
      simp [m]
    apply scaledParameterValuation_le_one π hπ d ξ hξ _ m z hm
    have hR : (0 : ℚ) ≤ (D.datum.toLinearMap (D.datum.root i) y : ℚ) +
        (d : ℚ) * ((b : ℚ) * (n : ℚ)) := by
      rw [foldedRootScalingExponent A x y d hy i]
      change 0 ≤ ((d : ℚ) * (b : ℚ)) * A.roots.root (A.direction i) x + (d : ℚ) * ((b : ℚ) * (n : ℚ))
      rw [← mul_assoc, ← mul_add]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hn
    exact_mod_cast hR

set_option maxHeartbeats 800000 in
/-- Nonnegative scaled depths on the marked chart produce an integral
point of the very same chart. -/
theorem scaledFoldedChartIntegral
    (x : invariantApartment D (R.diagram σ))
    (π : K) (hπ : normalizedValuation K π = exp (-1))
    (d : ℕ) (ξ : Eˣ) (hξ : (ξ : E) ^ d = algebraMap K E π)
    (y : D.Y) (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (z : X.comparison.chart.chart.torus × (∀ a, X.comparison.chart.parameter a))
    (hT : ∀ χ, normalizedValuation K (z.1.val χ : K) = 1)
    (hdepth : ∀ a, X.comparison.chart.value a (z.2 a) = 0 ∨ ∃ n : ℤ,
      X.comparison.chart.value a (z.2 a) = exp (-n) ∧ 0 ≤ A.roots.root a x + (n : ℚ)) :
    let C := X.comparison.chart
    let t := cocharacter D y (integralRing E) ξ
    let p : FieldPoints M E := torusPoint D (integralRing E) t ≫ M.torus.hom.hom
    MulAut.conj p (scalarPoints M (algebraMap K E) (cellValue M.toIntegralMarking (integralRing K)
      C.negative C.positive (C.chart.coordinates z.1 z.2))) ∈
      ((integralPointFunctor M.group).map (valuationRingInclusion E)).hom.range := by
  let C := X.comparison.chart
  let t := cocharacter D y (integralRing E) ξ
  let w := C.chart.coordinates z.1 z.2
  have ht (χ) : valuation E (algebraMap K E (w.2.1 χ : K)) = 1 := by
    have h := normalizedValueGroupMap_apply (E := E) (w.2.1 χ : K)
    have hK : normalizedValuation K (w.2.1 χ : K) = 1 := hT χ
    rw [hK, map_one] at h
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
    apply e.injective
    exact h.symm.trans e.map_one.symm
  have hN (l : Fin C.negative.length) :
      valuation E ((t (Multiplicative.ofAdd (D.datum.root C.negative[l])) : E) *
        algebraMap K E (w.1 l)) ≤ 1 := by
    have he : C.chart.neg l = A.direction C.negative[l] :=
      (C.neg_slots l).trans (congrFun X.directions _)
    change valuation E ((↑(ξ ^ D.datum.toLinearMap (D.datum.root C.negative[l]) y) : E) *
      algebraMap K E (w.1 l)) ≤ 1
    rw [Units.val_zpow_eq_zpow_val]
    exact integralScaledSlot (A := A) x π hπ d ξ hξ y hy C.negative[l]
        (C.value (C.chart.neg l) (z.2 (C.chart.neg l))) (w.1 l)
        (foldedNegativeSlotValuation X _ _ l) (by
          obtain h | ⟨n, hv, hn⟩ := hdepth (C.chart.neg l)
          · exact Or.inl h
          · exact Or.inr ⟨n, hv, he ▸ hn⟩)
  have hP (l : Fin C.positive.length) :
      valuation E ((t (Multiplicative.ofAdd (D.datum.root C.positive[l])) : E) *
        algebraMap K E (w.2.2 l)) ≤ 1 := by
    have he : C.chart.pos l = A.direction C.positive[l] :=
      (C.pos_slots l).trans (congrFun X.directions _)
    change valuation E ((↑(ξ ^ D.datum.toLinearMap (D.datum.root C.positive[l]) y) : E) *
      algebraMap K E (w.2.2 l)) ≤ 1
    rw [Units.val_zpow_eq_zpow_val]
    exact integralScaledSlot (A := A) x π hπ d ξ hξ y hy C.positive[l]
        (C.value (C.chart.pos l) (z.2 (C.chart.pos l))) (w.2.2 l)
        (foldedPositiveSlotValuation X _ _ l) (by
          obtain h | ⟨n, hv, hn⟩ := hdepth (C.chart.pos l)
          · exact Or.inl h
          · exact Or.inr ⟨n, hv, he ▸ hn⟩)
  obtain ⟨_, p, _, hp, _⟩ := scaledCellReduction M (algebraMap K E) C.negative C.positive t w hN hP ht
  exact ⟨p, hp⟩


set_option maxHeartbeats 800000 in
/-- At a point of the closed standard alcove, conjugating the actual
folded Iwahori points by the scaling cocharacter gives integral marked
points. The integral representative is the same ordered marked cell. -/
theorem scaledFoldedIwahoriPointIntegral
    (x : invariantApartment D (R.diagram σ))
    (hx : ∀ a : FoldedRootDirection × ℤ, A.roots.positive A.basepoint a → 0 ≤ A.roots.wallValue a x)
    (π : K) (hπ : normalizedValuation K π = exp (-1))
    (d : ℕ) (ξ : Eˣ) (hξ : (ξ : E) ^ d = algebraMap K E π)
    (y : D.Y) (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y) (g : X.comparison.I) :
    let t := cocharacter D y (integralRing E) ξ
    let p : FieldPoints M E := torusPoint D (integralRing E) t ≫ M.torus.hom.hom
    MulAut.conj p (scalarPoints M (algebraMap K E) (X.points g)) ∈
      ((integralPointFunctor M.group).map (valuationRingInclusion E)).hom.range := by
  obtain ⟨z, hz, hT, hdepth⟩ := iwahoriRootDepthsAtFace _ X.bruhat x hx g
  rw [← hz]
  exact scaledFoldedChartIntegral X x π hπ d ξ hξ y hy z hT hdepth

end IwahoriScaling
section SingleLevel

open CategoryTheory
open ExceptionalAffineBruhat (DiagramCompositum FieldPoints scalarPoints)
open ExceptionalAffineBuilding (Weights rationalPoint simplexPoint realWallValue)
open ExceptionalIwahoriCongruence (integralRing)
open IntegralSemisimpleModel (IntegralPoints torusPoint cocharacter)

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

private theorem rationalClosedAlcove
    {K G Wf V : Type u} {J : Type v} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {D : BasedRootDatum.{u}} {M : Model D} {j : G →* FieldPoints M K}
    {A : ApartmentRoots ℚ V J} {p : V}
    {C : LocalComparison (j := j) (Wf := Wf) A p} (B : Building C)
    (t : Weights (A.SimpleWall p)) (x : V)
    (hx : rationalPoint B.realization.coordinates x =
      simplexPoint B.realization.coordinates B.realization.vertex t) :
    ∀ a : J × ℤ, A.positive p a → 0 ≤ A.wallValue a x := by
  have hm : rationalPoint B.realization.coordinates x ∈
      Set.range (simplexPoint B.realization.coordinates B.realization.vertex) :=
    ⟨t, hx.symm⟩
  rw [B.realization.closed_alcove] at hm
  intro a ha
  have h := hm a ha
  have he : realWallValue A B.realization.coordinates a (rationalPoint B.realization.coordinates x) =
      ((A.root a.1 x : ℚ) : ℝ) + (a.2 : ℝ) := by
    simp [ExceptionalRealAlcove.realWallValue, ExceptionalRealAlcove.rationalPoint, Algebra.smul_def]
  rw [he] at h
  change (0 : ℚ) ≤ A.root a.1 x + (a.2 : ℚ)
  exact_mod_cast h

/-- A simple wall contains the simplex point exactly when its opposite
vertex has zero weight. -/
theorem rationalFaceCotype
    {K G Wf V : Type u} {J : Type v} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {D : BasedRootDatum.{u}} {M : Model D} {j : G →* FieldPoints M K}
    {A : ApartmentRoots ℚ V J} {p : V}
    {C : LocalComparison (j := j) (Wf := Wf) A p} (B : Building C)
    (t : Weights (A.SimpleWall p)) (x : V)
    (hx : rationalPoint B.realization.coordinates x =
      simplexPoint B.realization.coordinates B.realization.vertex t) :
    ExceptionalAffineBuilding.cotype t = {a | A.wallValue a.val x = 0} := by
  classical
  letI : Finite (A.SimpleWall p) := B.realization.finite_types
  letI := Fintype.ofFinite (A.SimpleWall p)
  let r := B.realization.coordinates
  let vertex := B.realization.vertex
  ext a
  change (t.val a = 0) ↔ A.wallValue a.val x = 0
  have hwt : ∑ i, t.val i = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using t.property.2
  let L : ExceptionalAffineBuilding.EuclideanApartment V →ₗ[ℝ] ℝ :=
    (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).toLinearMap.comp
      (((A.root a.val.1).baseChange ℝ).comp r.symm.toLinearMap)
  have hr (z : V) : L (rationalPoint r z) = (A.root a.val.1 z : ℝ) := by
    simp [L, ExceptionalRealAlcove.rationalPoint, Algebra.smul_def]
  have hx' : rationalPoint r x = ∑ i, t.val i • rationalPoint r (vertex i) := by
    simpa only [ExceptionalRealAlcove.simplexPoint, finsum_eq_sum_of_fintype] using hx
  have hw : (A.wallValue a.val x : ℝ) =
      ∑ i, t.val i * (A.wallValue a.val (vertex i) : ℝ) := by
    have h := congrArg L hx'
    rw [hr, map_sum] at h
    simp only [map_smul, hr, smul_eq_mul] at h
    change ((A.root a.val.1 x + (a.val.2 : ℚ) : ℚ) : ℝ) =
      ∑ i, t.val i * ((A.root a.val.1 (vertex i) + (a.val.2 : ℚ) : ℚ) : ℝ)
    push_cast
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hwt, one_mul, h]
  have hsingle : (∑ i, t.val i * (A.wallValue a.val (vertex i) : ℝ)) =
      t.val a * (A.wallValue a.val (vertex a) : ℝ) := by
    apply Finset.sum_eq_single a
    · intro b _ hb
      have hzero := ((B.realization.vertex_marked b).2 a).2 (Ne.symm hb)
      simp [vertex, hzero]
    · simp
  have hne : A.wallValue a.val (vertex a) ≠ 0 := by
    intro h
    exact (B.realization.vertex_marked a).2 a |>.mp h |>.elim rfl
  rw [hsingle] at hw
  constructor
  · intro ht
    have h := hw.trans (by rw [ht, zero_mul])
    exact_mod_cast h
  · intro hz
    have h : (A.wallValue a.val x : ℝ) = 0 := by exact_mod_cast hz
    rw [hw, mul_eq_zero] at h
    exact h.resolve_right (by exact_mod_cast hne)


end SingleLevel

local notation "Oᵥ[" K "]" => Valuation.valuationSubring (valuation K)
local notation "kᵥ[" K "]" => ExceptionalAffineBruhat.residue K

section NormalizeDepth

variable {K : Type u} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem normalizedUniformizer_zpow (w : Kˣ)
    (hw : normalizedValuation K (w : K) = exp (-1)) (m : ℤ) :
    normalizedValuation K ((w : K) ^ m) = exp (-m) := by
  rw [map_zpow₀, hw, ← exp_zsmul]
  congr 1
  simp

/-- Dividing a parameter at or above the stated depth by the corresponding
uniformizer power identifies its entire layer with the valuation ring. -/
private def normalizeParameter (w : Kˣ) (hw : normalizedValuation K (w : K) = exp (-1))
    (m : ℤ) (z : K) (hz : normalizedValuation K z ≤ exp (-m)) : Oᵥ[K] :=
  ⟨((w : K) ^ m)⁻¹ * z, (normalizedValuation_le_one _).mp (by
    rw [map_mul, map_inv₀, normalizedUniformizer_zpow w hw m]
    calc
      (exp (-m))⁻¹ * normalizedValuation K z ≤ (exp (-m))⁻¹ * exp (-m) :=
        mul_le_mul_of_nonneg_left hz zero_le
      _ = 1 := inv_mul_cancel₀ exp_ne_zero)⟩

private theorem normalizeParameter_eq (w : Kˣ) (hw : normalizedValuation K (w : K) = exp (-1))
    (m : ℤ) (z : K) (hz : normalizedValuation K z ≤ exp (-m)) :
    z = (w : K) ^ m * (normalizeParameter w hw m z hz : K) := by
  change z = (w : K) ^ m * (((w : K) ^ m)⁻¹ * z)
  rw [← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ w.ne_zero), one_mul]

private theorem normalizeParameter_surjective {P : Type u} [Field P]
    (v : Valuation P ℤᵐ⁰) (e : P ≃+* K)
    (he : ∀ z, v z = normalizedValuation K (e z))
    (w : Kˣ) (hw : normalizedValuation K (w : K) = exp (-1)) (m : ℤ) :
    Function.Surjective (fun z : {z : P // v z ≤ exp (-m)} =>
      normalizeParameter w hw m (e z) (he z ▸ z.property)) := by
  intro b
  let z := e.symm ((w : K) ^ m * (b : K))
  have hz : v z ≤ exp (-m) := by
    rw [he]
    change normalizedValuation K (e (e.symm _)) ≤ _
    rw [e.apply_symm_apply, map_mul, normalizedUniformizer_zpow w hw m]
    exact mul_le_of_le_one_right' ((normalizedValuation_le_one _).2 b.property)
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  change ((w : K) ^ m)⁻¹ * e (e.symm _) = _
  rw [e.apply_symm_apply, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ w.ne_zero), one_mul]

private theorem sameValuation_ratio (a b : Kˣ)
    (h : normalizedValuation K (a : K) = normalizedValuation K (b : K)) :
    ∃ c : Oᵥ[K]ˣ, (a : K) = ((c : Oᵥ[K]) : K) * (b : K) := by
  let x := a * b⁻¹
  have hxval : (x : K) = (a : K) * (b : K)⁻¹ := by
    simp only [x, Units.val_mul, Units.val_inv_eq_inv_val]
  have hx : normalizedValuation K (x : K) = 1 := by
    rw [hxval, map_mul, map_inv₀, h]
    exact mul_inv_cancel₀ ((map_ne_zero (normalizedValuation K)).2 b.ne_zero)
  have hval : valuation K (x : K) = 1 := by
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    apply e.injective
    exact hx.trans e.map_one.symm
  refine ⟨restrictUnit x hval, ?_⟩
  change (a : K) = (x : K) * (b : K)
  rw [hxval, mul_assoc, inv_mul_cancel₀ b.ne_zero, mul_one]

end NormalizeDepth

section ConstructLeading

open ExceptionalLocalRootCoordinates (residueMap ramificationIndex)
open IntegralSemisimpleModel (IntegralPoints Integers TorusValues)
open scoped Classical

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeExtension F L] [FiniteDimensional F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}

set_option maxHeartbeats 800000 in
/-- The independent residue coefficient in each marked direction is obtained
by dividing by the threshold power in its actual parameter field. -/
theorem existsLeadingCoefficients (X : MarkedLevel R σ A k)
    (hdeg : Module.finrank F L = 2) (hram : 1 < ramificationIndex F L)
    (hk : ExceptionalAffineBruhat.IsUnramifiedLocalExtension F k)
    (ϖ : Fˣ) (hϖ : normalizedValuation F (ϖ : F) = exp (-1))
    (π : Lˣ) (hπ : normalizedValuation L (π : L) = exp (-1))
    (a : FoldedRootDirection × ℤ) : Nonempty (LeadingCoefficients X ϖ π a) := by
  let T := X.compositum
  let K := T.field
  let C := X.folded.comparison.chart
  let P := C.parameter a.1
  let v := C.value a.1
  let w := Units.map (algebraMap F k).toMonoidHom ϖ
  let p := Units.map (algebraMap L K).toMonoidHom π
  have hw : normalizedValuation k (w : k) = exp (-1) := (hk _).trans hϖ
  have hp : normalizedValuation K (p : K) = exp (-1) := (T.unramified _).trans hπ
  let redL := (residueMap L K).comp (residue (Oᵥ[L]))
  let redk := residueMap k K
  letI : Finite kᵥ[K] := inferInstanceAs (Finite (𝓀[X.compositum.field]))
  have hredk : Function.Surjective redk := by
    have hcard : Nat.card kᵥ[k] = Nat.card kᵥ[K] := X.folded.same_residue.symm
    exact ((Nat.bijective_iff_injective_and_card redk).mpr ⟨redk.injective, hcard⟩).2
  by_cases hl : IsLongF4Doubled a.1.val
  · obtain ⟨i, hi⟩ := A.surjective a.1
    have hfix : (R.diagram σ).val.indexEquiv i = i := (A.long i).mp (hi ▸ hl)
    obtain ⟨e, he, hev⟩ := X.folded.singleton i hfix
    change A.direction i = a.1 at hi
    revert e he hev
    rw [hi]
    intro e he hev
    obtain ⟨ratio, hratio⟩ := sameValuation_ratio
      (Units.map (algebraMap F L).toMonoidHom ϖ) (π ^ 2) (by
        change normalizedValuation L (algebraMap F L (ϖ : F)) =
          normalizedValuation L ((π : L) ^ (2 : ℕ))
        rw [(ExceptionalLocalRootCoordinates.ramifiedQuadratic F L hdeg hram).2.1, map_pow, hϖ, hπ])
    let b (z : X.ParametersAtDepth a) := normalizeParameter w hw a.2 (e z.val) (hev z.val ▸ z.property)
    have hb : Function.Surjective b := normalizeParameter_surjective v e hev w hw a.2
    let c := (Units.map redL.toMonoidHom ratio) ^ a.2
    refine ⟨⟨fun z => redk (residue Oᵥ[k] (b z)),
      hredk.comp ((Ideal.Quotient.mk_surjective (I := maximalIdeal Oᵥ[k])).comp hb),
      fun _ => c, ?_⟩⟩
    change (if IsLongF4Doubled a.1.val then _ else _)
    rw [ite_eq_left hl]
    exact ⟨i, e, ratio, hi, he, hratio, rfl, fun z =>
      ⟨b z, normalizeParameter_eq w hw a.2 (e z.val) _, rfl⟩⟩
  · obtain ⟨i, hi, e, he, he', hev⟩ := X.folded.pair a.1 hl
    have hne : (R.diagram σ).val.indexEquiv i ≠ i := by
      intro h
      exact hl (hi ▸ (A.long i).mpr h)
    obtain ⟨ε, hε⟩ := sameValuation_ratio
      (Units.map σ.toRingHom.toMonoidHom π) π (normalizedValuation_algEquiv σ (π : L))
    let b (z : X.ParametersAtDepth a) := normalizeParameter p hp a.2 (e z.val) (hev z.val ▸ z.property)
    have hb : Function.Surjective b := normalizeParameter_surjective v e hev p hp a.2
    let c := (Units.map redL.toMonoidHom ε) ^ a.2
    let f : D.I → kᵥ[K]ˣ := fun j =>
      if j = (R.diagram σ).val.indexEquiv i then c else 1
    refine ⟨⟨fun z => residue Oᵥ[K] (b z),
      (Ideal.Quotient.mk_surjective (I := maximalIdeal Oᵥ[K])).comp hb, f, ?_⟩⟩
    change (if IsLongF4Doubled a.1.val then _ else _)
    rw [ite_eq_right hl]
    exact ⟨i, e, ε, hi, he, he', hε, ite_eq_right hne.symm, ite_eq_left rfl, fun z =>
      ⟨b z, normalizeParameter_eq p hp a.2 (e z.val) _, rfl⟩⟩

end ConstructLeading

section Equivariance

open ExceptionalAffineBruhat (coefficientPoints scalarPoints)
open AdjointRepresentation (GroupPoints)
open ExceptionalIwahoriCongruence (changeRing changeRingHom integralRingMap)
open IntegralSemisimpleModel (IntegralAlgebra IntegralGroup integralSpec TorusValues
  torusPoint cocharacter IntegralPoints)

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

private theorem changeRing_comp_apply (G : IntegralGroup.{u})
    {R S T : IntegralAlgebra.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (z : IntegralPoints G R) :
    changeRingHom G g (changeRingHom G f z) = changeRingHom G (f ≫ g) z := by
  change changeRing g (changeRing f z) = changeRing (f ≫ g) z
  unfold changeRing
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]

private theorem composeIntegralRingMaps
    {K E H : Type u} [CommRing K] [CommRing E] [CommRing H]
    (f : K →+* E) (g : E →+* H) :
    integralRingMap f ≫ integralRingMap g = integralRingMap (g.comp f) := by
  ext z
  rfl

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} (X : MarkedLevel R σ A k)

private theorem coefficientPreservesParahoric (J : Set (A.roots.SimpleWall A.basepoint))
    (s : Gal(k/F)) (g : X.parahoric J) :
    coefficientPoints R.descent.group.val s.toAlgHom g.val ∈ X.parahoric J := by
  let C := X.folded.comparison
  let G := GroupPoints R.descent.group.val (CommAlgCat.of F k)
  obtain ⟨a, hcoeff, _, hA⟩ := X.coefficients
  rw [← hcoeff]
  have hi : C.T₀ ≤ C.I := by
    change (ExceptionalIwahoriImageComparison.integralUnitTorus M).comap X.folded.points ≤ _
    rw [← C.localIwahori.intersection]
    exact inf_le_left
  have hpreserve : X.parahoric J ≤ (X.parahoric J).comap (a s).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro u (hu | ⟨b, hb, rfl⟩)
    · have hm : a s u ∈ C.I.map (a s).toMonoidHom := ⟨u, hu, rfl⟩
      rw [(hA s).1.1] at hm
      exact Subgroup.subset_closure (Or.inl hm)
    · let w := C.coxeter.coxeter.simple b
      obtain ⟨w', hw, hunit⟩ := (hA s).1.2.2.2.2.2.2.2 w
      have he : w' = w := Subtype.ext (by simpa using hw)
      subst w'
      have h₁ : a s (C.lift w) * (C.lift w : G)⁻¹ ∈ X.parahoric J :=
        Subgroup.subset_closure (Or.inl (hi hunit))
      have h₂ : (C.lift w : G) ∈ X.parahoric J := Subgroup.subset_closure (Or.inr ⟨b, hb, rfl⟩)
      change a s (C.lift w : G) ∈ X.parahoric J
      simpa only [inv_mul_cancel_right] using (X.parahoric J).mul_mem h₁ h₂
  exact hpreserve g.property

set_option maxHeartbeats 1000000 in
/-- The lift from the actual parahoric is determined on the generic fibre.
Compatibility of scalar maps then implies its coefficient equivariance. -/
theorem scaledParahoricOfIntegralGenerators
    (J : Set (A.roots.SimpleWall A.basepoint)) (π : Lˣ) (d : ℕ) (y : D.Y)
    (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L)))
    (hI : X.folded.comparison.I ≤ (integralPointsInField M U.field).range.comap
      (scalingConjugation X π d y U))
    (hW : ∀ a ∈ J, scalingConjugation X π d y U (X.wallLift a) ∈
      (integralPointsInField M U.field).range) :
    Nonempty (ScaledParahoric X J π d y U) := by
  let K := X.compositum.field
  let E := U.field
  let i := integralPointsInField M E
  let f := scalingConjugation X π d y U
  have hi : Function.Injective i := changeRing_injective_of_affine M.affine _ Subtype.val_injective
  obtain ⟨m, hm⟩ := liftParahoricToIntegralPoints X.folded.comparison J f i hi hI hW
  have hm' (g : X.parahoric J) : i (m g) = f g.val := DFunLike.congr_fun hm g
  refine ⟨⟨m, hm, ?_, coefficientPreservesParahoric X J, ?_⟩⟩
  · intro n hn
    apply MonoidHom.ext
    intro g
    exact hi ((DFunLike.congr_fun hn g).trans (hm' g).symm)
  · intro s b b₀ hb hξ g
    let g' : X.parahoric J :=
      ⟨coefficientPoints R.descent.group.val s.toAlgHom g.val, coefficientPreservesParahoric X J s g⟩
    change m g' = changeRingHom M.group (integralRingMap b₀.integers) (m g) ∧ _
    let inc := valuationRingInclusion E
    let red := residueReduction E
    have hinc : integralRingMap b₀.integers ≫ inc = inc ≫ integralRingMap b.toRingHom := by
      ext z
      exact b₀.field_eq z
    have hred : integralRingMap b₀.integers ≫ red = red ≫ integralRingMap b₀.residue := by
      ext z
      exact (ResidueField.map_residue b₀.integers z).symm
    have hcoeff : X.folded.points g'.val =
        scalarPoints M (X.compositum.coefficient s).toRingHom (X.folded.points g.val) := by
      obtain ⟨act, hact, hpoints, _⟩ := X.coefficients
      exact (congrArg X.folded.points (hact s g.val).symm).trans (hpoints s g.val)
    have hscalar : (algebraMap K E).comp (X.compositum.coefficient s).toRingHom =
        b.toRingHom.comp (algebraMap K E) := RingHom.ext (fun z => (hb z).symm)
    let t := cocharacter D y (integralRing E) U.root
    let p : FieldPoints M E := torusPoint D (integralRing E) t ≫ M.torus.hom.hom
    have hp : scalarPoints M b.toRingHom p = p := by
      change changeRing (integralRingMap b.toRingHom) (torusPoint D _ t ≫ _) = _
      unfold changeRing
      rw [← Category.assoc]
      change changeRing (integralRingMap b.toRingHom) (torusPoint D _ t) ≫ _ = _
      rw [changeRing_torusPoint]
      congr 2
      apply MonoidHom.ext
      intro z
      apply Units.ext
      let n := D.datum.toLinearMap (Multiplicative.toAdd z) y
      change b ((U.root ^ n : Eˣ) : E) = ((U.root ^ n : Eˣ) : E)
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hξ]
    have hEq : m g' = changeRingHom M.group (integralRingMap b₀.integers) (m g) := by
      apply hi
      change i (m g') = changeRingHom M.group inc (changeRingHom M.group _ (m g))
      rw [hm', changeRing_comp_apply, hinc, ← changeRing_comp_apply, ← show
        i (m g) = changeRingHom M.group inc (m g) from rfl, hm']
      change MulAut.conj p (scalarPoints M (algebraMap K E) (X.folded.points g'.val)) =
        scalarPoints M b.toRingHom
          (MulAut.conj p (scalarPoints M (algebraMap K E) (X.folded.points g.val)))
      simp only [MulAut.conj_apply, map_mul, map_inv, hp]
      rw [hcoeff]
      congr 2
      change changeRingHom M.group (integralRingMap (algebraMap K E))
          (changeRingHom M.group (integralRingMap (X.compositum.coefficient s).toRingHom) _) =
        changeRingHom M.group (integralRingMap b.toRingHom)
          (changeRingHom M.group (integralRingMap (algebraMap K E)) _)
      rw [changeRing_comp_apply, changeRing_comp_apply, composeIntegralRingMaps,
        composeIntegralRingMaps, hscalar]
    refine ⟨hEq, ?_⟩
    change changeRingHom M.group red (m g') =
      changeRingHom M.group (integralRingMap b₀.residue) (changeRingHom M.group red (m g))
    rw [hEq, changeRing_comp_apply, changeRing_comp_apply, hred]

end Equivariance

section ReduceSlot

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]

/-- After extracting the threshold powers, a remaining positive uniformizer
power kills the coefficient on reduction. At zero depth the whole
leading coefficient survives. -/
theorem residueOfScaledPower (ξ : Eˣ) (hξ : valuation E (ξ : E) < 1)
    (n : ℤ) (hn : 0 ≤ n) (a : Oᵥ[E]) :
    ∃ z : Oᵥ[E], (z : E) = (ξ : E) ^ n * (a : E) ∧
      IsLocalRing.residue Oᵥ[E] z = if n = 0 then IsLocalRing.residue Oᵥ[E] a else 0 := by
  have hle : valuation E ((ξ : E) ^ n) ≤ 1 := by
    rw [map_zpow₀]
    exact zpow_le_one₀ (bot_lt_iff_ne_bot.mpr ((map_ne_zero (valuation E)).mpr ξ.ne_zero))
      hξ.le hn
  let t : Oᵥ[E] := ⟨(ξ : E) ^ n, hle⟩
  refine ⟨t * a, rfl, ?_⟩
  split
  · next h =>
      subst n
      have ht : t = 1 := Subtype.ext (zpow_zero _)
      simp [ht]
  · next h =>
      have ht : IsLocalRing.residue Oᵥ[E] t = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, (valuation E).mem_maximalIdeal_iff]
        change valuation E ((ξ : E) ^ n) < 1
        rw [map_zpow₀]
        exact zpow_lt_one₀ (bot_lt_iff_ne_bot.mpr ((map_ne_zero (valuation E)).mpr ξ.ne_zero))
          hξ (lt_of_le_of_ne hn (Ne.symm h))
      rw [map_mul, ht, zero_mul]

end ReduceSlot

section MarkedWall

open ExceptionalAffineBruhat (coefficientPoints scalarPoints)
open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBuilding (cotype)

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} (X : MarkedLevel R σ A k)

private theorem markedUpperLayer
    (a : FoldedRootDirection × ℤ)
    (r : Matrix.SpecialLinearGroup (Fin 2) (X.folded.comparison.chart.parameter a.1) →*
      GroupPoints R.descent.group.val (CommAlgCat.of F k))
    (c : (X.folded.comparison.chart.parameter a.1)ˣ)
    (u₀ : X.folded.comparison.chart.chart.torus)
    (hu : u₀.val = 1)
    (hc : X.folded.comparison.chart.value a.1 (c : X.folded.comparison.chart.parameter a.1) = 1)
    (hr : ∀ z : X.folded.comparison.chart.parameter a.1,
      X.folded.points (r (upper z)) = cellValue M.toIntegralMarking
        (integralRing X.compositum.field) X.folded.comparison.chart.negative
        X.folded.comparison.chart.positive (X.folded.comparison.chart.chart.coordinates u₀
          (Function.update (fun _ => 0) a.1 ((c : X.folded.comparison.chart.parameter a.1) * z)))) :
    X.rootLayer a = (fun z => r (upper z)) '' {z | X.folded.comparison.chart.value a.1 z ≤ exp (-a.2)} := by
  let C := X.folded.comparison.chart
  let P := C.parameter a.1
  let v := C.value a.1
  ext g
  constructor
  · rintro ⟨t, z, ht, hz, hg⟩
    let w : P := (↑c⁻¹ : P) * z
    have hw : (c : P) * w = z := by
      change (c : P) * ((↑c⁻¹ : P) * z) = z
      rw [← mul_assoc, c.mul_inv, one_mul]
    have hv : v w ≤ exp (-a.2) := by
      change v ((↑c⁻¹ : P) * z) ≤ _
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_one, one_mul]
      exact hz
    refine ⟨w, hv, X.folded.comparison.point_injective ?_⟩
    rw [show t = u₀ from Subtype.ext (ht.trans hu.symm)] at hg
    rw [hr, hw]
    exact hg.symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨u₀, (c : P) * z, hu, ?_, hr z⟩
    change v ((c : P) * z) ≤ _
    rwa [map_mul, hc, one_mul]

/-- The upper layer of the marked rank-one map is exactly the positive
simple-wall layer in the given folded chart. -/
theorem wallUpperLayer (a : A.roots.SimpleWall A.basepoint) :
    let C := X.folded.comparison.chart
    ∃ (r : Matrix.SpecialLinearGroup (Fin 2) (C.parameter a.val.1) →*
        GroupPoints R.descent.group.val (CommAlgCat.of F k))
      (t : (C.parameter a.val.1)ˣ),
      C.value a.val.1 t = exp (-a.val.2) ∧ X.wallLift a = r (wallMatrix t) ∧
      X.rootLayer a.val = (fun z => r (upper z)) '' {z | C.value a.val.1 z ≤ exp (-a.val.2)} ∧
      X.rootLayer a.val ⊆ X.folded.comparison.I := by
  obtain ⟨_, _, r, t, c, u₀, _, _, _, _, _, hu, hc, hr, ht, hn⟩ := X.folded.bruhat.rank_one a
  have hd : (fun a b : FoldedRootDirection => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq FoldedRootDirection) := Subsingleton.elim _ _
  have hr' := hr
  rw [hd] at hr'
  have h := markedUpperLayer X a.val r c u₀ hu hc hr'
  refine ⟨r, t, ht, hn, h, ?_⟩
  rw [h]
  rintro g ⟨z, hz, rfl⟩
  have hs : Function.Surjective X.folded.comparison.chart.direction := X.folded.directions ▸ A.surjective
  exact upper_mem_iwahori X.folded.comparison _ X.folded.bruhat a r c u₀ hu hc hr
    (localRootChart_injective X.folded.comparison.chart hs) z hz

include X in
/-- The opposite equation has the same zero set as a marked simple wall,
with the negated integral threshold. -/
theorem simpleWallOppositeValue (a : A.roots.SimpleWall A.basepoint)
    (x : invariantApartment D (R.diagram σ)) :
    A.roots.wallValue (A.roots.opposite a.val) x = -A.roots.wallValue a.val x := by
  let C := X.folded.comparison.coxeter
  letI := C.action
  have h := C.walls.simple_opposite a
  rw [C.simple_wall, C.opposite_eq] at h
  rw [← h, C.equation, C.simple_eq]
  change A.roots.wallValue a.val ((A.roots.reflection a.val).symm x) = _
  change A.roots.wallValue a.val ((A.roots.reflection a.val)⁻¹ x) = _
  rw [AffineArrangement.reflection_inv]
  exact AffineArrangement.value_reflection_self A.roots a.val x

section Ramified

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeExtension F L] [ValuativeExtension F k]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F k]

open ExceptionalAffineBruhat (ExceptionalNumbering IsUnramifiedLocalExtension)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalLocalRootCoordinates (ramificationIndex)
open LinearAlgebraicGroups.RamifiedExceptionalOppositeWallLayer (oppositeWallLayer)

set_option maxHeartbeats 1000000 in
/-- Identify both actual chart layers using the witness of the same marked
simple lift, including the exact parameters of its three-term expression. -/
theorem markedSignedWallLayers
    (hdeg : Module.finrank F L = 2) (hσ : σ ≠ 1) (hram : 1 < ramificationIndex F L)
    (hk : IsUnramifiedLocalExtension F k) (numbering : Fin 6 ≃ D.base.support)
    (hnum : ExceptionalNumbering D 6 numbering) (had : D.datum.rootSpan ℤ = ⊤)
    (hτ : ∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i))
    (J : Set (A.roots.SimpleWall A.basepoint)) (a : A.roots.SimpleWall A.basepoint) (ha : a ∈ J) :
    ∃ r t, SignedWallLayers X J a r t := by
  let C := X.folded.comparison
  obtain ⟨word, orbit, r, t, c, u₀, hw, hlen, hnodup, hlabels, hrank, hu, hc, hr, ht, hn⟩ :=
    X.folded.bruhat.rank_one a
  have hd : (fun a b : FoldedRootDirection => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq FoldedRootDirection) := Subsingleton.elim _ _
  have hr' := hr
  rw [hd] at hr'
  have hplus := markedUpperLayer X a.val r c u₀ hu hc hr'
  have hsurj : Function.Surjective C.chart.direction := X.folded.directions ▸ A.surjective
  have hI : X.rootLayer a.val ⊆ C.I := by
    rw [hplus]
    rintro g ⟨z, hz, rfl⟩
    exact upper_mem_iwahori C _ X.folded.bruhat a r c u₀ hu hc hr
      (localRootChart_injective C.chart hsurj) z hz
  obtain ⟨⟨e, he⟩, hneg⟩ := oppositeWallLayer (F := F) (L := L) (k := k)
    σ hdeg hσ hram hk R numbering hnum had hτ A X.compositum X.folded
    a word orbit r t c u₀ hw hlen hnodup hlabels hrank hu hc hr ht hn
  have hminus : X.rootLayer (A.roots.opposite a.val) =
      (fun z => r (lower z)) '' {z | C.chart.value a.val.1 z ≤ exp a.val.2} := hneg.symm
  have hU : (fun z => r (upper z)) '' {z | C.chart.value a.val.1 z ≤ exp (-a.val.2)} ⊆ C.I :=
    hplus ▸ hI
  obtain ⟨hp, hm, hconj, hset, htpos, htneg, hword⟩ :=
    wallMatrixLayers C J a ha r t ht hn hU
  have hmark : IsMarkedWallRankOne X a r :=
    ⟨word, orbit, hw, hnodup, hlabels, hrank⟩
  refine ⟨r, t, hmark, ht, hn, hplus, hminus, hI, hplus.symm ▸ hp, hminus.symm ▸ hm,
    hconj, ?_, hplus.symm ▸ htpos, hminus.symm ▸ htneg, hword, ?_, ?_⟩
  · rw [hplus, hminus]
    exact hset
  · refine ⟨u₀, (c : C.chart.parameter a.val.1) * -(t : C.chart.parameter a.val.1),
      hu, ?_, hr' _⟩
    rw [map_mul, hc, Valuation.map_neg, ht, one_mul]
  · let z : C.chart.parameter a.val.1 := ↑t⁻¹
    refine ⟨u₀, e z, hu, ?_, (he z).2⟩
    rw [(he z).1]
    change C.chart.value a.val.1 (↑t⁻¹ : C.chart.parameter a.val.1) = exp (-(-a.val.2))
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht, ← exp_neg]

end Ramified

end MarkedWall

section LeadingSlots

open ExceptionalLocalRootCoordinates (residueMap)
attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

private theorem valuationRing_unit_zpow_coe {K : Type u} [Field K] [ValuativeRel K]
    (b : Oᵥ[K]ˣ) (m : ℤ) :
    (((b ^ m : Oᵥ[K]ˣ) : Oᵥ[K]) : K) = (((b : Oᵥ[K]) : K) ^ m) := by
  let i := (valuation K).valuationSubring.subtype.toMonoidHom
  change ((Units.map i (b ^ m) : Kˣ) : K) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

private theorem residue_unit_power {L K : Type u} [Field L] [Field K] [Algebra L K]
    [ValuativeRel L] [ValuativeRel K] [ValuativeExtension L K] (b : Oᵥ[L]ˣ) (m : ℤ) :
    IsLocalRing.residue Oᵥ[K] (algebraMap Oᵥ[L] Oᵥ[K] ((b ^ m : Oᵥ[L]ˣ) : Oᵥ[L])) =
      (((Units.map ((residueMap L K).comp (IsLocalRing.residue Oᵥ[L])).toMonoidHom b) ^
        m : kᵥ[K]ˣ) : kᵥ[K]) := by
  rw [← map_zpow]
  exact (ResidueField.map_residue (algebraMap Oᵥ[L] Oᵥ[K]) _).symm

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} (X : MarkedLevel R σ A k)

set_option maxHeartbeats 1000000 in
/-- In every absolute slot above a given relative direction, extraction of
the uniformizer power gives the common leading coefficient times the
slot's residue unit. -/
theorem rootSlotLeadingCoefficient (ϖ : Fˣ) (π : Lˣ)
    (a : FoldedRootDirection × ℤ) (B : LeadingCoefficients X ϖ π a)
    (i : D.I) (hi : A.direction i = a.1) (z : X.ParametersAtDepth a) :
    let K := X.compositum.field
    ∃ (e : X.folded.comparison.chart.parameter a.1 →+* K) (b : Oᵥ[K]),
      X.folded.comparison.chart.UsesSlot i a.1 e ∧
      e z.val = (algebraMap L K (π : L)) ^ ((foldedStep a.1 : ℤ) * a.2) * (b : K) ∧
      IsLocalRing.residue Oᵥ[K] b = (B.factor i : kᵥ[K]) * B.leading z := by
  let T := X.compositum
  let K := T.field
  let πK := algebraMap L K (π : L)
  let fL := algebraMap Oᵥ[L] Oᵥ[K]
  let fk := algebraMap Oᵥ[k] Oᵥ[K]
  have fLval (q : Oᵥ[L]) : (fL q : K) = algebraMap L K (q : L) := rfl
  have fkval (q : Oᵥ[k]) : (fk q : K) = algebraMap k K (q : k) := rfl
  have h := B.normalized
  by_cases hl : IsLongF4Doubled a.1.val
  · rw [ite_eq_left hl] at h
    obtain ⟨j, e, b, hj, he, hb, hfactor, hparam⟩ := h
    have hj' : i = j := by
      rcases (A.orbits j i).mp (hj.trans hi.symm) with h | h
      · exact h
      · exact h.trans ((A.long j).mp (hj ▸ hl))
    subst i
    obtain ⟨q, hq, hqred⟩ := hparam z
    refine ⟨(algebraMap k K).comp e.toRingHom,
      fL ((b ^ a.2 : Oᵥ[L]ˣ) : Oᵥ[L]) * fk q, he, ?_, ?_⟩
    · change algebraMap k K (e z.val) =
        πK ^ ((foldedStep a.1 : ℤ) * a.2) *
          ((fL ((b ^ a.2 : Oᵥ[L]ˣ) : Oᵥ[L]) : K) * (fk q : K))
      have hbase : algebraMap k K (algebraMap F k (ϖ : F)) =
          algebraMap L K (((b : Oᵥ[L]) : L) * (π : L) ^ 2) := by
        rw [← IsScalarTower.algebraMap_apply F k K, IsScalarTower.algebraMap_apply F L K, hb]
      rw [hq, map_mul, map_zpow₀, hbase, map_mul, map_pow, fLval, fkval,
        valuationRing_unit_zpow_coe, map_zpow₀, mul_zpow, ← zpow_natCast, ← zpow_mul,
        foldedStep, ite_eq_left hl]
      dsimp only [πK]
      ring
    · rw [map_mul, residue_unit_power, hfactor, hqred]
      rw [← ResidueField.map_residue (algebraMap Oᵥ[k] Oᵥ[K])]
      rfl
  · rw [ite_eq_right hl] at h
    obtain ⟨j, e, ε, hj, hslot, hslot', hε, hf, hf', hparam⟩ := h
    obtain ⟨q, hq, hqred⟩ := hparam z
    rcases (A.orbits j i).mp (hj.trans hi.symm) with h | h
    · subst i
      refine ⟨e.toRingHom, q, hslot, ?_, ?_⟩
      · change e z.val = _
        simpa only [foldedStep, ite_eq_right hl, Nat.cast_one, one_mul] using hq
      · rw [hf, hqred]
        simp
    · subst i
      let bar := valuationRingAlgEquiv T.diagram
      let q' : Oᵥ[K] := bar q
      refine ⟨T.diagram.toRingHom.comp e.toRingHom,
        fL ((ε ^ a.2 : Oᵥ[L]ˣ) : Oᵥ[L]) * q', hslot', ?_, ?_⟩
      · change T.diagram (e z.val) = πK ^ ((foldedStep a.1 : ℤ) * a.2) *
          ((fL ((ε ^ a.2 : Oᵥ[L]ˣ) : Oᵥ[L]) : K) * T.diagram (q : K))
        have hπ' : T.diagram πK = (fL (ε : Oᵥ[L]) : K) * πK := by
          change T.diagram (algebraMap L K (π : L)) = _
          rw [T.diagram_extends, hε, map_mul, fLval]
        rw [hq, map_mul, map_zpow₀, hπ', mul_zpow, fLval, fLval,
          valuationRing_unit_zpow_coe, map_zpow₀, foldedStep, ite_eq_right hl,
          Nat.cast_one, one_mul]
        ac_rfl
      · letI : Finite kᵥ[K] := inferInstanceAs (Finite (𝓀[X.compositum.field]))
        have hq' : IsLocalRing.residue Oᵥ[K] q' = IsLocalRing.residue Oᵥ[K] q :=
          residueFixedByIntegralAutomorphism X.folded.same_residue.symm bar q
        rw [map_mul, residue_unit_power, hq', hf', hqred]

end LeadingSlots

section IntegralFace

open CategoryTheory
open ExceptionalAffineBruhat (scalarPoints)
open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBuilding (Weights cotype rationalPoint simplexPoint)
open IntegralSemisimpleModel (torusPoint cocharacter integralPointFunctor)

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} (X : MarkedLevel R σ A k)

set_option maxHeartbeats 800000 in
/-- Either signed marked root layer through the scaling point has integral
image in the split model. -/
theorem scaledRootLayerIntegral (π : Lˣ)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (d : ℕ) (y : D.Y)
    (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L)))
    (x : invariantApartment D (R.diagram σ))
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (a : FoldedRootDirection × ℤ) (ha : A.roots.wallValue a x = 0)
    {g : GroupPoints R.descent.group.val (CommAlgCat.of F k)} (hg : g ∈ X.rootLayer a) :
    scalingConjugation X π d y U g ∈ (integralPointsInField M U.field).range := by
  let K := X.compositum.field
  let C := X.folded.comparison.chart
  obtain ⟨t, z, ht, hz, he⟩ := hg
  let p := Function.update (fun _ => 0) a.1 z
  have ht₀ (χ) : normalizedValuation K (t.val χ : K) = 1 := by simp [ht]
  have hdepth (i : FoldedRootDirection) : C.value i (p i) = 0 ∨
      ∃ n : ℤ, C.value i (p i) = exp (-n) ∧ 0 ≤ A.roots.root i x + (n : ℚ) := by
    by_cases h : i = a.1
    · subst i
      simp only [p, Function.update_self]
      by_cases h₀ : C.value a.1 z = 0
      · exact Or.inl h₀
      let n := -log (C.value a.1 z)
      have hn : C.value a.1 z = exp (-n) := by simpa [n] using (exp_log h₀).symm
      have hj : a.2 ≤ n := by
        change C.value a.1 z ≤ exp (-a.2) at hz
        simpa only [hn, exp_le_exp, neg_le_neg_iff] using hz
      have : 0 ≤ A.roots.root a.1 x + (n : ℚ) := by
        change A.roots.root a.1 x + (a.2 : ℚ) = 0 at ha
        linarith only [ha, (show (a.2 : ℚ) ≤ (n : ℚ) from Int.cast_le.mpr hj)]
      exact Or.inr ⟨n, hn, this⟩
    · exact Or.inl (by simp [p, Function.update_of_ne h])
  have hπK : normalizedValuation K (algebraMap L K (π : L)) = exp (-1) :=
    (X.compositum.unramified _).trans hπ
  change MulAut.conj _ (scalarPoints M (algebraMap K U.field) (X.folded.points g)) ∈ _
  rw [he]
  exact scaledFoldedChartIntegral X.folded x (algebraMap L K (π : L)) hπK d U.root U.power y hy
    ⟨t, p⟩ ht₀ hdepth

set_option maxHeartbeats 1100000 in
/-- Given the signed layer identifications, all marked face generators
have integral scaled images, giving the single equivariant map. -/
theorem scaledParahoricFromSignedLayers
    (t : Weights (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ))
    (hx : rationalPoint X.building.realization.coordinates x =
      simplexPoint X.building.realization.coordinates X.building.realization.vertex t)
    (π : Lˣ) (hπ : normalizedValuation L (π : L) = exp (-1)) (d : ℕ) (y : D.Y)
    (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L)))
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hS : ∀ a ∈ cotype t, ∃ r z, SignedWallLayers X (cotype t) a r z) :
    Nonempty (ScaledParahoric X (cotype t) π d y U) := by
  let K := X.compositum.field
  have hπK : normalizedValuation K (algebraMap L K (π : L)) = exp (-1) :=
    (X.compositum.unramified _).trans hπ
  have hclosed := rationalClosedAlcove X.building t x hx
  have hcotype := rationalFaceCotype X.building t x hx
  apply scaledParahoricOfIntegralGenerators X _ π d y U
  · intro g hg
    exact scaledFoldedIwahoriPointIntegral X.folded x hclosed (algebraMap L K (π : L)) hπK
      d U.root U.power y hy ⟨g, hg⟩
  · intro a ha
    have ha₀ : A.roots.wallValue a.val x = 0 := by rw [hcotype] at ha; exact ha
    have ha₁ : A.roots.wallValue (A.roots.opposite a.val) x = 0 := by
      rw [simpleWallOppositeValue X, ha₀, neg_zero]
    obtain ⟨r, u, _, _, _, _, _, _, _, _, _, _, hp, hq, hword, _, _⟩ := hS a ha
    have h₁ := scaledRootLayerIntegral X π hπ d y U x hy a.val ha₀ hp
    have h₂ := scaledRootLayerIntegral X π hπ d y U x hy (A.roots.opposite a.val) ha₁ hq
    rw [hword, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) h₁

end IntegralFace



section ReduceWallWord

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} {X : MarkedLevel R σ A k}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  {U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L))}

/-- Once the two signed layers have been identified, the integral
homomorphism reduces the marked word in its actual face subgroup. -/
theorem reducesWallWordOfSignedLayers (P : ScaledParahoric X J π d y U)
    (a : A.roots.SimpleWall A.basepoint)
    (r : X.WallRankOneMap a) (t : (X.folded.comparison.chart.parameter a.val.1)ˣ)
    (h : SignedWallLayers X J a r t) : P.ReducesWallWord a r t := by
  obtain ⟨_, _, hn, _, _, _, hpos, hneg, _, _, hp, hq, hw, _, _⟩ := h
  let p : X.parahoric J := ⟨_, hpos hp⟩
  let q : X.parahoric J := ⟨_, hneg hq⟩
  refine ⟨p, q, rfl, rfl, hp, hq, p * q * p, hw.symm, hw.symm.trans hn, ?_⟩
  rw [map_mul, map_mul]

end ReduceWallWord

section ResidueCoordinates

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

open AdjointRepresentation (GroupPoints)
open ExceptionalIwahoriCongruence (CellValues mapCellValues scaleCellValues integralRingMap changeRing)
open ExceptionalLocalRootCoordinates (residueMap)
open IntegralSemisimpleModel (IntegralPoints Integers TorusValues torusPoint cocharacter)

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} (X : MarkedLevel R σ A k)
  (ϖ : Fˣ) (π : Lˣ) (d : ℕ) (y : D.Y)
  (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L)))
  (x : invariantApartment D (R.diagram σ))
  (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)

include hy in
set_option maxHeartbeats 800000 in
/-- Reducing a normalized absolute slot uses its leading coefficient only
when the corresponding relative wall has value zero at the scaling point. -/
theorem reduceNormalizedSlot
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (a : FoldedRootDirection × ℤ) (ha : 0 ≤ A.roots.wallValue a x)
    (B : LeadingCoefficients X ϖ π a) (z : X.ParametersAtDepth a)
    (i : D.I) (hi : A.direction i = a.1) (c : Integers.{u}ˣ)
    (e : X.folded.comparison.chart.parameter a.1 →+* X.compositum.field)
    (he : X.folded.comparison.chart.UsesSlot i a.1 e) :
    let K := X.compositum.field
    let E := U.field
    ∃ q : Oᵥ[E],
      (q : E) = (U.root : E) ^ D.datum.toLinearMap (D.datum.root i) y *
        algebraMap K E (algebraMap Integers.{u} K (c : Integers.{u}) * e z.val) ∧
      IsLocalRing.residue Oᵥ[E] q =
        if A.roots.wallValue a x = 0 then
          algebraMap Integers.{u} kᵥ[E] (c : Integers.{u}) *
            residueMap K E (B.factor i : kᵥ[K]) * residueMap K E (B.leading z)
        else 0 := by
  let K := X.compositum.field
  let E := U.field
  let C := X.folded.comparison.chart
  obtain ⟨e', b, he', hb, hr⟩ := rootSlotLeadingCoefficient X ϖ π a B i hi z
  have hsame : e z.val = e' z.val := by
    by_cases hp : D.base.IsPos i
    · obtain ⟨n, hn⟩ := List.mem_iff_get.mp ((C.positive_enumerates.2 i).mpr hp)
      change C.positive[n] = i at hn
      have hdir : C.chart.pos n = a.1 := by rw [C.pos_slots n, hn, he.1]
      exact (he.2.2 n hdir z.val hn).symm.trans (he'.2.2 n hdir z.val hn)
    · obtain ⟨n, hn⟩ := List.mem_iff_get.mp ((C.negative_enumerates.2 i).mpr hp)
      change C.negative[n] = i at hn
      have hdir : C.chart.neg n = a.1 := by rw [C.neg_slots n, hn, he.1]
      exact (he.2.1 n hdir z.val hn).symm.trans (he'.2.1 n hdir z.val hn)
  let πK := algebraMap L K (π : L)
  let m : ℤ := (foldedStep a.1 : ℤ) * a.2
  let s := D.datum.toLinearMap (D.datum.root i) y
  let n : ℤ := s + (d : ℤ) * m
  have hn : (n : ℚ) = ((d : ℚ) * (foldedStep a.1 : ℚ)) * A.roots.wallValue a x := by
    simp only [n, s, m, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [foldedRootScalingExponent A x y d hy i, hi]
    change _ = _ * (A.roots.root a.1 x + (a.2 : ℚ))
    ring
  have hpos : (0 : ℚ) < (d : ℚ) * (foldedStep a.1 : ℚ) := by
    apply mul_pos (by exact_mod_cast hd)
    unfold foldedStep
    split <;> norm_num
  have hn₀ : 0 ≤ n := by exact_mod_cast (hn ▸ mul_nonneg hpos.le ha : (0 : ℚ) ≤ n)
  have hn_eq : n = 0 ↔ A.roots.wallValue a x = 0 := by
    rw [← Int.cast_eq_zero (α := ℚ), hn, mul_eq_zero]
    exact or_iff_right hpos.ne'
  have hπK : normalizedValuation K πK = exp (-1) := (X.compositum.unramified _).trans hπ
  have hξlt : valuation E (U.root : E) < 1 := by
    have hlt : valuation K πK < 1 :=
      (normalizedValuation_lt_one _).1 (by rw [hπK]; simp)
    have hlt' : valuation E (algebraMap K E πK) < 1 := by
      rw [← map_one (valuation E), ← map_one (algebraMap K E), ← (valuation E).vlt_iff_lt,
        ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt, map_one]
      exact hlt
    by_contra! h
    apply hlt'.not_ge
    rw [← U.power, map_pow]
    exact one_le_pow₀ h
  let w : Oᵥ[E] := algebraMap Integers.{u} Oᵥ[E] (c : Integers.{u}) * algebraMap Oᵥ[K] Oᵥ[E] b
  have hw : (w : E) = algebraMap Integers.{u} E (c : Integers.{u}) * algebraMap K E (b : K) := by
    change (Oᵥ[E]).subtype (algebraMap Integers.{u} Oᵥ[E] (c : Integers.{u})) *
      algebraMap K E (b : K) = _
    rfl
  obtain ⟨q, hq, hred⟩ := residueOfScaledPower U.root hξlt n hn₀ w
  refine ⟨q, ?_, ?_⟩
  · change (q : E) = (U.root : E) ^ s * algebraMap K E
      (algebraMap Integers.{u} K (c : Integers.{u}) * e z.val)
    rw [hq, hw, hsame, hb, map_mul, map_mul, map_zpow₀,
      ← U.power, ← zpow_natCast, ← zpow_mul]
    change (U.root : E) ^ (s + (d : ℤ) * m) * _ = _
    rw [zpow_add₀ U.root.ne_zero]
    have hc : algebraMap K E (algebraMap Integers.{u} K (c : Integers.{u})) =
        algebraMap Integers.{u} E (c : Integers.{u}) := map_intCast _ _
    rw [hc]
    change ((U.root : E) ^ s * (U.root : E) ^ ((d : ℤ) * m)) *
        (algebraMap Integers.{u} E (c : Integers.{u}) * algebraMap K E (b : K)) =
      (U.root : E) ^ s * (algebraMap Integers.{u} E (c : Integers.{u}) *
        ((U.root : E) ^ ((d : ℤ) * m) * algebraMap K E (b : K)))
    rw [mul_mul_mul_comm, mul_assoc]
  · rw [hred, ite_congr (propext hn_eq) (fun _ => rfl) (fun _ => rfl)]
    congr 1
    change IsLocalRing.residue Oᵥ[E] (algebraMap Integers.{u} Oᵥ[E] (c : Integers.{u}) *
      algebraMap Oᵥ[K] Oᵥ[E] b) = _
    rw [map_mul, ← ResidueField.map_residue (algebraMap Oᵥ[K] Oᵥ[E])]
    change _ * residueMap K E (IsLocalRing.residue Oᵥ[K] b) = _
    rw [hr, map_mul, mul_assoc]
    congr 1


variable {J : Set (A.roots.SimpleWall A.basepoint)}
  (P : ScaledParahoric X J π d y U)

/-- The reduced value of a scaled chart point is determined by the
reductions of any integral lifts of its scaled coordinates. -/
theorem reduceMarkedCell
    (g : X.parahoric J)
    (z : CellValues D (integralRing X.compositum.field)
      X.folded.comparison.chart.negative X.folded.comparison.chart.positive)
    (hg : X.folded.points g.val = cellValue M.toIntegralMarking _ _ _ z)
    (w : CellValues D (integralRing Oᵥ[U.field])
      X.folded.comparison.chart.negative X.folded.comparison.chart.positive)
    (hw : mapCellValues (valuationRingInclusion U.field) w =
      scaleCellValues (cocharacter D y (integralRing U.field) U.root)
        (mapCellValues (integralRingMap (algebraMap X.compositum.field U.field)) z)) :
    P.reduction g = cellValue M.toIntegralMarking _ _ _
      (mapCellValues (residueReduction U.field) w) := by
  let C := X.folded.comparison.chart
  let f := integralRingMap (algebraMap X.compositum.field U.field)
  let p := cellValue M.toIntegralMarking (integralRing Oᵥ[U.field]) C.negative C.positive w
  have hp : P.integral g = p := by
    apply changeRing_injective_of_affine M.affine (valuationRingInclusion U.field)
      Subtype.val_injective
    change integralPointsInField M U.field (P.integral g) = changeRing _ p
    have h := DFunLike.congr_fun P.conjugation g
    change integralPointsInField M U.field (P.integral g) = scalingConjugation X π d y U g.val at h
    rw [h]
    change MulAut.conj _ (changeRing f (X.folded.points g.val)) = changeRing _ p
    rw [hg, changeRing_cellValue, show changeRing (valuationRingInclusion U.field) p =
      cellValue M.toIntegralMarking _ _ _ (mapCellValues (valuationRingInclusion U.field) w)
      from changeRing_cellValue M.toIntegralMarking _ _ _ _, hw,
      ExceptionalIwahoriCongruence.scaleMarkedChart M.toIntegralMarking (integralRing U.field)]
  change changeRing (residueReduction U.field) (P.integral g) = _
  rw [hp, show changeRing (residueReduction U.field) p = _ from
    changeRing_cellValue M.toIntegralMarking _ _ _ _]

include hy in
set_option maxHeartbeats 900000 in
/-- On a signed depth-zero wall the entire image is the line with its
specified coefficient in every absolute slot of that direction. -/
theorem reduceRootLayerPoint
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (a : FoldedRootDirection × ℤ) (ha : A.roots.wallValue a x = 0)
    (B : LeadingCoefficients X ϖ π a)
    (g : X.parahoric J)
    (t : X.folded.comparison.chart.chart.torus) (ht : t.val = 1)
    (z : X.ParametersAtDepth a)
    (hg : X.folded.points g.val = cellValue M.toIntegralMarking _ _ _
      (X.folded.comparison.chart.chart.coordinates t (Function.update (fun _ => 0) a.1 z.val))) :
    P.reduction g = rootResiduePoint X ϖ π a B (residueMap X.compositum.field U.field)
      (residueMap X.compositum.field U.field (B.leading z)) := by
  let K := X.compositum.field
  let E := U.field
  let C := X.folded.comparison.chart
  let v := Function.update (fun _ => 0) a.1 z.val
  let rel := fun (i : D.I) (c : Integers.{u}ˣ) =>
    if A.direction i = a.1 then algebraMap Integers.{u} kᵥ[E] (c : Integers.{u}) *
      residueMap K E (B.factor i : kᵥ[K]) * residueMap K E (B.leading z) else 0
  have slot (i : D.I) (c : Integers.{u}ˣ) (j : FoldedRootDirection) (hj : j = A.direction i)
      (f : C.parameter j →+* K)
      (hf : ∀ e : C.parameter a.1 →+* K, C.UsesSlot i a.1 e →
        ∀ h : j = a.1, f (h.symm ▸ z.val) = e z.val) :
      ∃ q : Oᵥ[E], (q : E) = (U.root : E) ^ D.datum.toLinearMap (D.datum.root i) y *
          algebraMap K E (algebraMap Integers.{u} K (c : Integers.{u}) * f (v j)) ∧
        IsLocalRing.residue Oᵥ[E] q = rel i c := by
    by_cases hi : A.direction i = a.1
    · obtain ⟨e, _, he, _, _⟩ := rootSlotLeadingCoefficient X ϖ π a B i hi z
      have hj' : j = a.1 := hj.trans hi
      have update_eq (j' : FoldedRootDirection) (h : j' = a.1) :
          v j' = (h.symm ▸ z.val : C.parameter j') := by
        subst j'
        exact Function.update_self _ _ _
      obtain ⟨q, hq, hr⟩ := reduceNormalizedSlot X ϖ π d y U x hy hπ hd a ha.ge B z i hi c e he
      exact ⟨q, by rw [hq, update_eq j hj', hf e he hj'], by simpa [ha, rel, hi] using hr⟩
    · have hv : v j = 0 := Function.update_of_ne (hj.trans_ne hi) _ _
      exact ⟨0, by simp [hv], by simp [rel, hi]⟩
  choose qn hqn hrn using fun l : Fin C.negative.length =>
    slot C.negative[l] (C.chart.negUnit l) (C.chart.neg l)
      ((C.neg_slots l).trans (congrFun X.folded.directions _)) (C.chart.negMap l)
      (fun e he h => he.2.1 l h z.val rfl)
  choose qp hqp hrp using fun l : Fin C.positive.length =>
    slot C.positive[l] (C.chart.posUnit l) (C.chart.pos l)
      ((C.pos_slots l).trans (congrFun X.folded.directions _)) (C.chart.posMap l)
      (fun e he h => he.2.2 l h z.val rfl)
  let w : CellValues D (integralRing Oᵥ[E]) C.negative C.positive := (qn, 1, qp)
  rw [reduceMarkedCell X π d y U P g _ hg w]
  · congr 1
    refine Prod.ext (funext hrn) (Prod.ext ?_ (funext hrp))
    ext χ
    simp [mapCellValues, w]
  · apply Prod.ext
    · funext l
      change (qn l : E) = (↑(U.root ^ D.datum.toLinearMap (D.datum.root C.negative[l]) y) : E) * _
      rw [Units.val_zpow_eq_zpow_val]
      exact hqn l
    · apply Prod.ext
      · change (Units.map _).comp 1 = (Units.map _).comp t.val
        rw [ht]
        ext χ
        simp
      · funext l
        change (qp l : E) = (↑(U.root ^ D.datum.toLinearMap (D.datum.root C.positive[l]) y) : E) * _
        rw [Units.val_zpow_eq_zpow_val]
        exact hqp l

include hy in
set_option maxHeartbeats 800000 in
theorem rootLayerReductionImage
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (a : FoldedRootDirection × ℤ) (ha : A.roots.wallValue a x = 0)
    (B : LeadingCoefficients X ϖ π a) (hmem : X.rootLayer a ⊆ X.parahoric J)
    (t : X.folded.comparison.chart.chart.torus) (ht : t.val = 1) :
    P.image (X.rootLayer a) = Set.range (rootResiduePoint X ϖ π a B
      (residueMap X.compositum.field U.field)) := by
  let C := X.folded.comparison.chart
  ext w
  constructor
  · rintro ⟨g, ⟨t', z, ht', hz, hgz⟩, rfl⟩
    exact ⟨_, (reduceRootLayerPoint X ϖ π d y U x hy P hπ hd a ha B g t' ht' ⟨z, hz⟩ hgz).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := U.residue_bijective.2 c
    obtain ⟨z, rfl⟩ := B.surjective b
    let v := C.chart.coordinates t (Function.update (fun _ => 0) a.1 z.val)
    obtain ⟨g, hg⟩ := (C.rational v).2 ⟨_, _, rfl⟩
    have hs : g ∈ X.rootLayer a := ⟨t, z.val, ht, z.property, hg⟩
    let g' : X.parahoric J := ⟨g, hmem hs⟩
    exact ⟨g', hs, reduceRootLayerPoint X ϖ π d y U x hy P hπ hd a ha B g' t ht z hg⟩

end ResidueCoordinates





section ExactIwahoriImage

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat (scalarPoints)
open ExceptionalIwahoriCongruence (CellValues mapCellValues scaleCellValues integralRingMap changeRing)
open ExceptionalIwahoriImageComparison (integralUnitTorus)
open ExceptionalLocalRootCoordinates (residueMap)
open IntegralSemisimpleModel (IntegralPoints Integers TorusValues torusPoint cocharacter)
open LinearAlgebraicGroups.Specs.RamifiedExceptionalRationalUnitTorus
  (genericTorusValues markedTorusPoint reduceTorusValues)
open LinearAlgebraicGroups.RamifiedExceptionalRationalUnitTorus (rationalUnitTorusComparison)

open private cellValue_torus from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)} (X : MarkedLevel R σ A k)
  {J : Set (A.roots.SimpleWall A.basepoint)}
  (π : Lˣ) (d : ℕ) (y : D.Y)
  (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L)))
  (P : ScaledParahoric X J π d y U)

private theorem unitTorus_le_iwahori : X.folded.comparison.T₀ ≤ X.folded.comparison.I := by
  change (integralUnitTorus M).comap X.folded.points ≤ _
  rw [← X.folded.comparison.localIwahori.intersection]
  exact inf_le_left

private theorem iwahori_le_parahoric : X.folded.comparison.I ≤ X.parahoric J :=
  fun _ h => Subgroup.subset_closure (Or.inl h)

private theorem valuation_torusLift (q : TorusValues D (integralRing Oᵥ[X.compositum.field]))
    (χ : Multiplicative D.X) :
    normalizedValuation X.compositum.field ((genericTorusValues q) χ : X.compositum.field) = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt X.compositum.field
  change e (valuation X.compositum.field ((q χ : Oᵥ[X.compositum.field]) : X.compositum.field)) = 1
  have h := (Valuation.integer.integers (valuation X.compositum.field)).valuation_unit (q χ)
  change valuation X.compositum.field ((q χ : Oᵥ[X.compositum.field]) : X.compositum.field) = 1 at h
  rw [h]
  exact map_one e

private theorem existsValuationTorus (q : TorusValues D (integralRing X.compositum.field))
    (hq : ∀ χ, normalizedValuation X.compositum.field (q χ : X.compositum.field) = 1) :
    ∃ q₀ : TorusValues D (integralRing Oᵥ[X.compositum.field]),
      genericTorusValues q₀ = q := by
  let K := X.compositum.field
  have hq' (χ) : valuation K (q χ : K) = 1 :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
      ((hq χ).trans (map_one _).symm)
  obtain ⟨b, hb⟩ := liftMarkedCellToIntegers K ([] : List D.I) []
    (fun i => Fin.elim0 i, q, fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hq'
  exact ⟨b.2.1, congrArg (fun z => z.2.1) hb⟩

private abbrev mapTorusValues {D : BasedRootDatum.{u}} {K E : Type u} [CommRing K] [CommRing E]
    (f : K →+* E) (q : TorusValues D (integralRing K)) :
    TorusValues D (integralRing E) :=
  (Units.map f.toMonoidHom).comp q

private def mapInvariantTorus {τ : Pinning.BasedIso D D} {K E : Type u} [Field K] [Field E]
    (f : K →+* E) (t : InvariantTorusValues τ K) : InvariantTorusValues τ E :=
  ⟨mapTorusValues f t.val, fun χ => congrArg (fun z : Kˣ => Units.map f.toMonoidHom z)
    (t.property χ)⟩

private theorem scalarPoints_torus {K E : Type u} [Field K] [Field E] (f : K →+* E)
    (t : TorusValues D (integralRing K)) :
    scalarPoints M f (markedTorusPoint M t) = markedTorusPoint M (mapTorusValues f t) := by
  change changeRing (integralRingMap f) (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) = _
  change _ ≫ (_ ≫ M.torus.hom.hom) = _
  rw [← Category.assoc]
  exact congrArg (· ≫ M.torus.hom.hom) (changeRing_torusPoint (integralRingMap f) t)

private theorem residue_torus_extension (q : TorusValues D (integralRing Oᵥ[X.compositum.field])) :
    let K := X.compositum.field
    let E := U.field
    let qE := mapTorusValues (algebraMap Oᵥ[K] Oᵥ[E]) q
    reduceTorusValues qE = mapTorusValues (residueMap K E) (reduceTorusValues q) := by
  dsimp only
  apply MonoidHom.ext
  intro χ
  apply Units.ext
  exact (ResidueField.map_residue (algebraMap Oᵥ[X.compositum.field] Oᵥ[U.field]) _).symm

private theorem reduceMarkedTorusPoint (g : X.parahoric J)
    (q : TorusValues D (integralRing Oᵥ[X.compositum.field]))
    (hg : X.folded.points g.val = markedTorusPoint M (genericTorusValues q)) :
    P.reduction g = scalarPoints M (residueMap X.compositum.field U.field)
      (markedTorusPoint M (reduceTorusValues q)) := by
  let K := X.compositum.field
  let E := U.field
  let C := X.folded.comparison.chart
  let qE := mapTorusValues (algebraMap Oᵥ[K] Oᵥ[E]) q
  let qK := genericTorusValues q
  let z : CellValues D (integralRing K) C.negative C.positive := (fun _ => 0, qK, fun _ => 0)
  let w : CellValues D (integralRing Oᵥ[E]) C.negative C.positive := (fun _ => 0, qE, fun _ => 0)
  have hgz : X.folded.points g.val = cellValue M.toIntegralMarking _ _ _ z :=
    hg.trans (cellValue_torus M.toIntegralMarking _ C.negative C.positive qK).symm
  rw [reduceMarkedCell X π d y U P g z hgz w]
  · rw [scalarPoints_torus]
    have he : mapCellValues (residueReduction E) w =
        (0, mapTorusValues (residueMap K E) (reduceTorusValues q), 0) := by
      apply Prod.ext
      · funext l
        exact map_zero _
      · exact Prod.ext (residue_torus_extension X π d U q) (funext fun _ => map_zero _)
    rw [he, cellValue_torus]
  · apply Prod.ext
    · funext l
      change (0 : E) = _ * (algebraMap K E) 0
      simp
    · refine Prod.ext ?_ (funext fun l => ?_)
      · apply MonoidHom.ext
        intro χ
        exact Units.ext rfl
      · change (0 : E) = _ * (algebraMap K E) 0
        simp

set_option maxHeartbeats 900000 in
theorem unitTorusReductionImage (had : D.datum.rootSpan ℤ = ⊤) :
    P.image (X.folded.comparison.T₀ : Set _) =
      Set.range (fun t : InvariantTorusValues (R.diagram σ) kᵥ[X.compositum.field] =>
        scalarPoints M (residueMap X.compositum.field U.field)
          (torusPoint D (integralRing kᵥ[X.compositum.field]) t.val ≫ M.torus.hom.hom)) := by
  have hT := rationalUnitTorusComparison X.compositum X.folded
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨q, hq⟩ := (hT.integral g.val).1 hg
    have hr : markedTorusPoint M (genericTorusValues q) ∈ X.folded.points.range := ⟨g.val, hq⟩
    exact ⟨⟨reduceTorusValues q, hT.reduction q hr⟩,
      (reduceMarkedTorusPoint X π d y U P g q hq).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨q, hq, g, hg⟩ := hT.lift had t.val t.property
    have hg₀ : g ∈ X.folded.comparison.T₀ := (hT.integral g).2 ⟨q, hg⟩
    let g' : X.parahoric J := ⟨g, iwahori_le_parahoric X (unitTorus_le_iwahori X hg₀)⟩
    refine ⟨g', hg₀, ?_⟩
    change P.reduction g' = scalarPoints M _ (markedTorusPoint M t.val)
    rw [reduceMarkedTorusPoint X π d y U P g' q hg, hq]

variable (ϖ : Fˣ) (x : invariantApartment D (R.diagram σ))
  (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
  (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
  (hclosed : ∀ a : FoldedRootDirection × ℤ, A.roots.positive A.basepoint a →
      0 ≤ A.roots.wallValue a x)
  (B : ∀ a, LeadingCoefficients X ϖ π a)

include hy hπ hd hclosed in
set_option maxHeartbeats 1100000 in
private theorem reduceIwahoriCell (g : X.parahoric J)
    (t : X.folded.comparison.chart.chart.torus)
    (q : TorusValues D (integralRing Oᵥ[X.compositum.field]))
    (hq : genericTorusValues q = t.val)
    (tres : InvariantTorusValues (R.diagram σ) kᵥ[U.field])
    (htres : mapTorusValues (residueMap X.compositum.field U.field) (reduceTorusValues q) = tres.val)
    (z : ∀ i, X.ParametersAtDepth (X.iwahoriDepth i))
    (hg : X.folded.points g.val = cellValue M.toIntegralMarking _ _ _
      (X.folded.comparison.chart.chart.coordinates t (fun i => (z i).val))) :
    P.reduction g = iwahoriResidueCell X ϖ π x B (residueMap X.compositum.field U.field)
      tres
      (fun i => residueMap X.compositum.field U.field ((B (X.iwahoriDepth i)).leading (z i))) := by
  let K := X.compositum.field
  let E := U.field
  let C := X.folded.comparison.chart
  let f := residueMap K E
  let qE := mapTorusValues (algebraMap Oᵥ[K] Oᵥ[E]) q
  let v := fun (i : D.I) (c : Integers.{u}ˣ) =>
    let a := X.iwahoriDepth (A.direction i)
    if A.roots.wallValue a x = 0 then algebraMap Integers.{u} kᵥ[E] (c : Integers.{u}) *
      f ((B a).factor i) * f ((B a).leading (z a.1)) else 0
  have slot (i : D.I) (c : Integers.{u}ˣ)
      (j : FoldedRootDirection) (hj : j = A.direction i) (e : C.parameter j →+* K)
      (he : ∀ e' : C.parameter (A.direction i) →+* K,
        C.UsesSlot i (A.direction i) e' → e (hj.symm ▸ (z (A.direction i)).val) =
          e' (z (A.direction i)).val) :
      ∃ b : Oᵥ[E], (b : E) = (U.root : E) ^ D.datum.toLinearMap (D.datum.root i) y *
          algebraMap K E (algebraMap Integers.{u} K (c : Integers.{u}) * e (z j).val) ∧
        IsLocalRing.residue Oᵥ[E] b = v i c := by
    let a := X.iwahoriDepth (A.direction i)
    have ha : A.roots.positive A.basepoint a := by
      change 0 < A.roots.root (A.direction i) A.basepoint + (a.2 : ℚ)
      have hp := Int.lt_floor_add_one (-A.roots.root (A.direction i) A.basepoint)
      change 0 < A.roots.root (A.direction i) A.basepoint +
        (threshold (A.roots.root (A.direction i) A.basepoint) : ℚ)
      rw [threshold, Int.cast_add, Int.cast_one]
      linarith
    obtain ⟨e', he', _⟩ := foldedRootSlotEmbedding X.folded i
    obtain ⟨b, hb, hr⟩ := reduceNormalizedSlot X ϖ π d y U x hy hπ hd a (hclosed a ha)
      (B a) (z a.1) i rfl c e' he'
    have hz (j' : FoldedRootDirection) (h : j' = A.direction i) :
        (z j').val = (h.symm ▸ (z (A.direction i)).val : C.parameter j') := by
      subst j'
      rfl
    exact ⟨b, by rw [hb, hz j hj, he e' he'], hr⟩
  choose qn hqn hrn using fun l : Fin C.negative.length =>
    slot C.negative[l] (C.chart.negUnit l) (C.chart.neg l)
      ((C.neg_slots l).trans (congrFun X.folded.directions _)) (C.chart.negMap l)
      (fun e h => h.2.1 l ((C.neg_slots l).trans (congrFun X.folded.directions _)) _ rfl)
  choose qp hqp hrp using fun l : Fin C.positive.length =>
    slot C.positive[l] (C.chart.posUnit l) (C.chart.pos l)
      ((C.pos_slots l).trans (congrFun X.folded.directions _)) (C.chart.posMap l)
      (fun e h => h.2.2 l ((C.pos_slots l).trans (congrFun X.folded.directions _)) _ rfl)
  let w : CellValues D (integralRing Oᵥ[E]) C.negative C.positive := (qn, qE, qp)
  rw [reduceMarkedCell X π d y U P g _ hg w]
  · congr 1
    exact Prod.ext (funext hrn) (Prod.ext ((residue_torus_extension X π d U q).trans htres) (funext hrp))
  · apply Prod.ext
    · funext l
      change (qn l : E) = (↑(U.root ^ D.datum.toLinearMap (D.datum.root C.negative[l]) y) : E) * _
      rw [Units.val_zpow_eq_zpow_val]
      exact hqn l
    · apply Prod.ext
      · change (Units.map _).comp qE = (Units.map _).comp t.val
        rw [← hq]
        exact MonoidHom.ext (fun _ => Units.ext rfl)
      · funext l
        change (qp l : E) = (↑(U.root ^ D.datum.toLinearMap (D.datum.root C.positive[l]) y) : E) * _
        rw [Units.val_zpow_eq_zpow_val]
        exact hqp l

include hy hπ hd hclosed in
set_option maxHeartbeats 1800000 in
theorem iwahoriReductionImage (had : D.datum.rootSpan ℤ = ⊤) :
    P.image (X.folded.comparison.I : Set _) =
      Set.range (fun b : InvariantTorusValues (R.diagram σ) kᵥ[U.field] ×
        (FoldedRootDirection → kᵥ[U.field]) =>
          iwahoriResidueCell X ϖ π x B (residueMap X.compositum.field U.field) b.1 b.2) := by
  let K := X.compositum.field
  let E := U.field
  let C := X.folded.comparison.chart
  let f := residueMap K E
  have hT := rationalUnitTorusComparison X.compositum X.folded
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨⟨t, v⟩, ⟨hgv, ht, hv⟩, _⟩ := (X.folded.bruhat.base_chart g.val).1 hg
    obtain ⟨q, hq⟩ := existsValuationTorus X t.val ht
    have hrat : markedTorusPoint M (genericTorusValues q) ∈ X.folded.points.range :=
      hq.symm ▸ (hT.chart t.val).1 t.property
    let t₀ : InvariantTorusValues (R.diagram σ) kᵥ[K] :=
      ⟨reduceTorusValues q, hT.reduction q hrat⟩
    let tE := mapInvariantTorus f t₀
    let z : ∀ i, X.ParametersAtDepth (X.iwahoriDepth i) := fun i => ⟨v i, hv i⟩
    refine ⟨(tE, fun i => f ((B (X.iwahoriDepth i)).leading (z i))), ?_⟩
    exact (reduceIwahoriCell X π d y U P ϖ x hy hπ hd hclosed B g t q hq tE rfl z hgv.symm).symm
  · rintro ⟨⟨t, v⟩, rfl⟩
    let e : kᵥ[K] ≃+* kᵥ[E] := RingEquiv.ofBijective f U.residue_bijective
    let t₀ := mapInvariantTorus e.symm.toRingHom t
    obtain ⟨q, hq, hrat⟩ := hT.lift had t₀.val t₀.property
    let qK := genericTorusValues q
    let tK : C.chart.torus := ⟨qK, (hT.chart qK).2 hrat⟩
    choose z hz using fun i => (B (X.iwahoriDepth i)).surjective (e.symm (v i))
    let w := C.chart.coordinates tK (fun i => (z i).val)
    obtain ⟨g, hg⟩ := (C.rational w).2 ⟨tK, _, rfl⟩
    have hI : g ∈ X.folded.comparison.I := by
      apply (X.folded.bruhat.base_chart g).2
      refine ⟨(tK, fun i => (z i).val), ⟨hg.symm, valuation_torusLift X q, fun i => (z i).property⟩, ?_⟩
      intro b hb
      apply localRootChart_injective C (X.folded.directions ▸ A.surjective)
      exact hb.1.trans hg
    let g' : X.parahoric J := ⟨g, iwahori_le_parahoric X hI⟩
    have ht : mapTorusValues f (reduceTorusValues q) = t.val := by
      rw [hq]
      apply MonoidHom.ext
      intro χ
      exact Units.ext (e.apply_symm_apply _)
    refine ⟨g', hI, (reduceIwahoriCell X π d y U P ϖ x hy hπ hd hclosed B g' tK q rfl t ht z hg).trans ?_⟩
    congr 1
    funext i
    change f ((B (X.iwahoriDepth i)).leading (z i)) = v i
    rw [hz]
    exact e.apply_symm_apply _

end ExactIwahoriImage

open ExceptionalAffineBuilding (Weights cotype)
open LinearAlgebraicGroups.RamifiedExceptionalRationalUnitTorus (rationalUnitTorusComparison)

set_option maxHeartbeats 1100000 in
/-- The parahoric at the marked face has an equivariant integral scaling
with exact residue coordinates at the given coefficient level. -/
theorem ramifiedLocalFaceCoordinates : RamifiedLocalFaceCoordinates.{u} := by
  intro F L k _ _ _ _ _
    _ _ _
    _ _ _ _
    _ _ _ _
    _ _ _
    σ hdeg hσ hram hk D M R numbering hnum had hτ A X t x _ hx ϖ π hϖ hπ d y hd hy U
  have hcotype := rationalFaceCotype X.building t x hx
  have hclosed := rationalClosedAlcove X.building t x hx
  have hs : ∀ a ∈ cotype t, ∃ r z, SignedWallLayers X (cotype t) a r z :=
    fun a ha => markedSignedWallLayers X hdeg hσ hram hk numbering hnum had hτ (cotype t) a ha
  obtain ⟨P⟩ := scaledParahoricFromSignedLayers X t x hx π hπ d y U hy hs
  let leading : ∀ a, LeadingCoefficients X ϖ π a :=
    fun a => Classical.choice (existsLeadingCoefficients X hdeg hram hk ϖ hϖ π hπ a)
  have hT := rationalUnitTorusComparison X.compositum X.folded
  have hone : 1 ∈ X.folded.comparison.chart.chart.torus := by
    apply (hT.chart 1).2
    apply (hT.rational 1).2
    intro χ
    simp
  let unit : X.folded.comparison.chart.chart.torus := ⟨1, hone⟩
  refine ⟨hcotype, P, ⟨{
    leading := leading
    iwahori := iwahoriReductionImage X π d y U P ϖ x hy hπ hd hclosed leading had
    torus := unitTorusReductionImage X π d y U P had
    wall := ?_ }⟩⟩
  intro a ha
  have ha₀ : A.roots.wallValue a.val x = 0 := by
    rw [hcotype] at ha
    exact ha
  have ha₁ : A.roots.wallValue (A.roots.opposite a.val) x = 0 := by
    rw [simpleWallOppositeValue X, ha₀, neg_zero]
  obtain ⟨r, z, h⟩ := hs a ha
  refine ⟨r, z, h, reducesWallWordOfSignedLayers P a r z h, ?_⟩
  obtain ⟨_, _, _, _, _, _, hplus, hminus, _⟩ := h
  intro b hb
  rcases Set.mem_insert_iff.mp hb with hb | hb
  · subst b
    exact ⟨ha₀, rootLayerReductionImage X ϖ π d y U x hy P hπ hd a.val ha₀
      (leading a.val) hplus unit rfl⟩
  · have hb' := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨ha₁, rootLayerReductionImage X ϖ π d y U x hy P hπ hd (A.roots.opposite a.val) ha₁
      (leading (A.roots.opposite a.val)) hminus unit rfl⟩

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
