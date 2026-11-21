import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Naturality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SurjectiveTarget

/-! The surjective-target theorem, with arbitrary change of base (KD-10). -/
namespace AdvCommAlg.Differentials

universe u v u' v'
noncomputable section

theorem surjective_target_map :
    Specs.AdvCommAlg.Differentials.surjectiveTargetMap.{u,v,u',v'} := by
  intro A B A' B' _ _ _ _ _ _ g f h hf
  let : Algebra A A' := g.toAlgebra
  let : Algebra B B' := f.toAlgebra
  let : Algebra A B' := (f.comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' h
  exact KaehlerDifferential.map_surjective_of_surjective A A' B B' hf

theorem surjective_target_kernel :
    Specs.AdvCommAlg.Differentials.surjectiveTargetKernel.{u,v,u',v'} := by
  intro A B A' B' _ _ _ _ _ _ g f h hf
  let : Algebra B B' := f.toAlgebra
  let F : KaehlerDifferential A B →ₗ[B] KaehlerDifferential A' B' :=
    algebraDifferentialMap g f h
  let L : Submodule B (KaehlerDifferential A B) :=
    Submodule.span B {x | ∃ b : B, f b ∈ Set.range (algebraMap A' B') ∧
      x = KaehlerDifferential.D A B b}
  change LinearMap.ker F = L
  have hgen (b : B) (hb : f b ∈ Set.range (algebraMap A' B')) :
      KaehlerDifferential.D A B b ∈ L :=
    Submodule.subset_span ⟨b, hb, rfl⟩
  have hL : L ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro x ⟨b, ⟨a, ha⟩, rfl⟩
    change algebraDifferentialMap g f h (KaehlerDifferential.D A B b) = 0
    rw [show algebraDifferentialMap g f h (KaehlerDifferential.D A B b) =
      KaehlerDifferential.D A' B' (f b) from algebraDifferentialMap_apply g f h b, ← ha]
    exact (KaehlerDifferential.D A' B').map_algebraMap a
  -- In the quotient, the differential of every element over the new base is zero.
  let Q := (KaehlerDifferential A B) ⧸ L
  let q : KaehlerDifferential A B →ₗ[B] Q := L.mkQ
  let D : Derivation A B Q := q.compDer (KaehlerDifferential.D A B)
  have hD (b : B) (hb : f b ∈ Set.range (algebraMap A' B')) : D b = 0 := by
    exact (Submodule.Quotient.mk_eq_zero L).mpr (hgen b hb)
  have hDker (b : B) (hb : f b = 0) : D b = 0 :=
    hD b ⟨0, by simpa using hb.symm⟩
  -- Leibniz makes ker(f) annihilate all differential generators, hence Q.
  have hkill (i : B) (hi : f i = 0) (z : Q) : i • z = 0 := by
    obtain ⟨x, rfl⟩ := L.mkQ_surjective z
    have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      change i • D b = 0
      have hib := hDker (i * b) (by rw [map_mul, hi, zero_mul])
      rw [D.leibniz, hDker i hi, smul_zero, add_zero] at hib
      exact hib
    | zero => simp
    | add x y hx hy ex ey => simp only [map_add, smul_add, ex, ey, add_zero]
    | smul b x hx ex =>
      rw [map_smul, smul_comm i b, ex, smul_zero]
  -- Transport the scalar action across f. The action is independent of lifts.
  let s : B' → B := Function.surjInv hf
  have hs (b' : B') : f (s b') = b' := Function.rightInverse_surjInv hf b'
  let : SMul B' Q := ⟨fun b' z => s b' • z⟩
  have hsmul (b : B) (z : Q) : f b • z = b • z := by
    change s (f b) • z = b • z
    apply sub_eq_zero.mp
    rw [← sub_smul]
    exact hkill _ (by rw [map_sub, hs, sub_self]) z
  let : Module B' Q := hf.moduleLeft f hsmul
  let : Module A' Q := Module.compHom Q (algebraMap A' B')
  let : IsScalarTower A' B' Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- Descend the additive derivation; equality of lifts follows from hDker.
  have hDeq (x y : B) (hxy : f x = f y) : D x = D y := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hDker _ (by rw [map_sub, hxy, sub_self])
  let δ : B' → Q := fun b' => D (s b')
  have hδ (b : B) : δ (f b) = D b := hDeq _ _ (hs _)
  have hadd (x y : B') : δ (x + y) = δ x + δ y := by
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← map_add, hδ, hδ, hδ, map_add]
  have hmul (x y : B') : δ (x * y) = x • δ y + y • δ x := by
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← map_mul, hδ, hδ, hδ, hsmul, hsmul, D.leibniz]
  have hbase (a : A') : δ (algebraMap A' B' a) = 0 :=
    hD _ ⟨a, (hs _).symm⟩
  obtain ⟨δ', hδ', _⟩ := (additive_characterization δ).mpr ⟨hadd, hmul, hbase⟩
  let H : KaehlerDifferential A' B' →ₗ[B'] Q := δ'.liftKaehlerDifferential
  have hH (b : B) : H (F (KaehlerDifferential.D A B b)) = D b := by
    rw [show F (KaehlerDifferential.D A B b) = KaehlerDifferential.D A' B' (f b)
      from algebraDifferentialMap_apply g f h b]
    change δ'.liftKaehlerDifferential (KaehlerDifferential.D A' B' (f b)) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact (congrFun hδ' (f b)).trans (hδ b)
  have hinverse (x : KaehlerDifferential A B) : H (F x) = q x := by
    have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact hH b
    | zero => simp
    | add x y hx hy ex ey => simp only [map_add, ex, ey]
    | smul b x hx ex =>
      rw [show F (b • x) = f b • F x from algebraDifferentialMap_smul g f h b x,
        map_smul, hsmul, ex, map_smul]
  apply le_antisymm ?_ hL
  intro x hx
  have hz : q x = 0 := by rw [← hinverse, LinearMap.mem_ker.mp hx, map_zero]
  exact (Submodule.Quotient.mk_eq_zero L).mp hz

end
end AdvCommAlg.Differentials
