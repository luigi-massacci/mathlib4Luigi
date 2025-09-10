/-
Copyright (c) 2025 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci
-/

import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!

# Space of Test Functions

We define the space of test functions `𝓓^{n}(E, F)` as the space of `n`-times continuously
differentiable with compact support.

-/

open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable {n : ℕ∞}

structure TestFunction (n : ℕ∞) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected compact_supp' : HasCompactSupport toFun

scoped[Distributions] notation "𝓓^{" n "}(" E ", " F ")" =>
  TestFunction E F n

open Distributions

class TestFunctionClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  compact_supp (f : B) : HasCompactSupport f

open TestFunctionClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    rcases (map_continuous f).bounded_above_of_compact_support (compact_supp f) with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)


namespace TestFunction

instance toTestFunctionClass :
    TestFunctionClass 𝓓^{n}(E, F) E F n where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  compact_supp f := f.compact_supp'

variable {E F}

protected theorem contDiff (f : 𝓓^{n}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem compact_supp (f : 𝓓^{n}(E, F)) : HasCompactSupport f := compact_supp f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓^{n}(E, F)) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections TestFunction (toFun → apply)

@[ext]
theorem ext {f g : 𝓓^{n}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  compact_supp' := h.symm ▸ f.compact_supp

@[simp]
theorem coe_copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h


@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓓^{n}(E, F)) (x : E) :
   (f : BoundedContinuousFunction E F) x  = (f x) := rfl


section AddCommGroup

instance : Zero 𝓓^{n}(E, F) where
  zero := TestFunction.mk 0 contDiff_zero_fun HasCompactSupport.zero

@[simp]
lemma coe_zero : (0 : 𝓓^{n}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}(E, F)) x = 0 :=
  rfl

instance : Add 𝓓^{n}(E, F) where
  add f g := TestFunction.mk (f + g) (f.contDiff.add g.contDiff) (f.compact_supp.add g.compact_supp)

@[simp]
lemma coe_add (f g : 𝓓^{n}(E, F)) : (f + g : 𝓓^{n}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

instance : Neg 𝓓^{n}(E, F) where
  neg f := TestFunction.mk (-f) (f.contDiff.neg) (f.compact_supp.neg)

instance instSub : Sub 𝓓^{n}(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.contDiff').sub (g.contDiff'),
    sub_eq_add_neg (f : E → F) g ▸ f.compact_supp.add g.compact_supp.neg
    ⟩
  ⟩

instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}(E, F) :=
  ⟨fun c f ↦
    TestFunction.mk (c • (f : E → F)) (f.contDiff.const_smul c)  f.compact_supp.smul_left
  ⟩

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) : (c • f : 𝓓^{n}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl

instance instNSMul : SMul ℕ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance instZSMul : SMul ℤ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance : AddCommGroup 𝓓^{n}(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F K n)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓓^{n}(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F n : 𝓓^{n}(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F n) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module


instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(E, F) :=
  (coeHom_injective n).module R (coeHom E F n) fun _ _ => rfl

end Module

variable (n : ℕ∞) (F)

def ContDiffMapSupportedIn.toTestFunction (K : Compacts E) : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}(E, F)
    where
  toFun f := TestFunction.mk f (f.contDiff) (f.hasCompactSupport)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ContDiffMapSupportedIn.toTestFunction_apply {K : Compacts E} (f : 𝓓^{n}_{K}(E, F)) (x : E) :
  (toTestFunction 𝕜 F n K f) x = f x := rfl


open ContDiffMapSupportedIn

noncomputable def originalTop : TopologicalSpace 𝓓^{n}(E, F) :=
  ⨆ (K : Compacts E), coinduced (toTestFunction 𝕜 F n K) (inferInstance)

variable (E)
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(E, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(E, F)
       | originalTop ℝ F n ≤ t ∧ @LocallyConvexSpace ℝ 𝓓^{n}(E, F) _ _ _ _ t}

noncomputable instance : LocallyConvexSpace ℝ 𝓓^{n}(E, F) := by
  apply LocallyConvexSpace.sInf
  simp only [mem_setOf_eq, and_imp, imp_self, implies_true]

theorem continuous_toTestFunction (K : Compacts E) :
    Continuous (toTestFunction 𝕜 F n K) := by
  apply continuous_iff_coinduced_le.2
  have : originalTop 𝕜 F n ≤ TestFunction.topologicalSpace E F n := by
    exact le_sInf (by aesop)
  exact le_trans (le_sSup (by aesop)) this

variable {n E F}


protected theorem continuous_iff {V : Type*} [AddCommMonoid V] [Module ℝ V]
  [t : TopologicalSpace V] [LocallyConvexSpace ℝ V] (f : 𝓓^{n}(E, F) →ₗ[ℝ] V) :
    Continuous f ↔
  ∀ K : Compacts E, Continuous (f ∘ toTestFunction 𝕜 F n K) := by
  rw [continuous_iff_le_induced]
  have : TestFunction.topologicalSpace E F n ≤ induced f t
        ↔ originalTop ℝ F n ≤ induced f t := by
      constructor <;> refine fun h ↦ ?_
      · refine le_trans (le_sInf (fun _ _ ↦ ?_)) h
        simp_all only [mem_setOf_eq]
      · refine sInf_le ?_
        simp only [mem_setOf_eq, LocallyConvexSpace.induced f, and_true, h]
  rw [this, originalTop, iSup_le_iff]
  simp_rw [← @coinduced_le_iff_le_induced _ _ f _ t, coinduced_compose]
  simp_rw [← continuous_iff_coinduced_le]
  rfl

variable (E F n)

@[simps]
noncomputable def toBoundedContinuousFunctionₗ : 𝓓^{n}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma to_bcf_comp_eq (K : Compacts E) :
  (toBoundedContinuousFunctionₗ 𝕜 E F n) ∘ (ContDiffMapSupportedIn.toTestFunction 𝕜 F n K)  =
    ContDiffMapSupportedIn.toBoundedContinuousFunctionₗ 𝕜 := by
    congr 0

@[simps!]
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}(E, F) →L[𝕜] E →ᵇ F  :=
  { toLinearMap := toBoundedContinuousFunctionₗ 𝕜 E F n
    cont := show Continuous (toBoundedContinuousFunctionₗ ℝ E F n)
      by
        (
          rw [TestFunction.continuous_iff ℝ (toBoundedContinuousFunctionₗ ℝ E F n)]
          intro K
          rw [to_bcf_comp_eq _ _]
          exact (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous
        )
  }

theorem injective_toBoundedContinuousFunctionCLM :
    Function.Injective (toBoundedContinuousFunctionCLM 𝕜 E F n) := by
  intro f g
  simp [toBoundedContinuousFunctionCLM, toBoundedContinuousFunctionₗ]

theorem T25Space_TestFunction : T25Space 𝓓^{n}(E, F) :=
  T25Space.of_injective_continuous
    (injective_toBoundedContinuousFunctionCLM ℝ E F n)
    (toBoundedContinuousFunctionCLM ℝ E F n).continuous

variable {G 𝕜' : Type*} [NontriviallyNormedField 𝕜']
variable {σ : 𝕜 →+* 𝕜'}
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]

variable {E F n}
variable (𝕜')

def toTestFunction_comp
  (f : 𝓓^{n}(E, F) → 𝓓^{n}(E, G)) : Prop :=
  ∀ K : Compacts E, ∃ g : 𝓓^{n}_{K}(E, F) → 𝓓^{n}_{K}(E, G), Continuous g
        ∧ f ∘ toTestFunction 𝕜 F n K = toTestFunction 𝕜' G n K ∘ g

open ContDiffMapSupportedIn in
theorem continuous_of_commute_toTestFunction
  (f : 𝓓^{n}(E, F) →ₗ[ℝ] 𝓓^{n}(E, G))
  (hc : toTestFunction_comp 𝕜 𝕜' f) :
    Continuous f := by
  refine (TestFunction.continuous_iff ℝ f).mpr (fun K ↦ ?_)
  obtain ⟨g, hg, hfg⟩ := hc K
  exact hfg ▸ (continuous_toTestFunction ℝ E G n K).comp hg

variable (n)


section FromMeasure

open MeasureTheory Module

variable [MeasurableSpace E]
variable (μ : Measure E)


noncomputable def ofMeasure : 𝓓^{n}(E, F) → F := (∫ x, · x ∂μ)

@[simp]
lemma ofMeasure_apply (f : 𝓓^{n}(E, F)) : ofMeasure n μ f = (∫ x, f x ∂μ) := by
  rfl

variable [BorelSpace E] [IsFiniteMeasureOnCompacts μ]

lemma map_integrable (f : 𝓓^{n}(E, F)) : Integrable f μ  := by
  apply Continuous.integrable_of_hasCompactSupport (map_continuous f) (compact_supp f)

variable {K : Compacts E}


lemma map_integrable' (f : 𝓓^{n}_{K}(E, F)) : Integrable f μ  := by
  apply Continuous.integrable_of_hasCompactSupport (map_continuous f) (f.hasCompactSupport)


variable [SecondCountableTopology E] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

noncomputable def ofMeasureₗ : 𝓓^{n}(E, F) →ₗ[𝕜] F :=
  { toFun := ofMeasure n μ
    map_add' := fun f g ↦ integral_add (f.map_integrable n μ) (g.map_integrable n μ)
    map_smul' := fun c f ↦ integral_smul c f}

variable [CompleteSpace F]

noncomputable def _root_.integralFiniteMeasure (𝕜 E F : Type*) [NormedField 𝕜]
  [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [IsFiniteMeasure μ] : (E →ᵇ F) →L[𝕜] F :=
  LinearMap.mkContinuous
  ({
    toFun := (∫ x, · x ∂μ)
    map_add' := fun f g ↦ integral_add (f.integrable μ) (g.integrable μ)
    map_smul' := fun c f ↦ integral_smul c f
  })
  (measureUnivNNReal μ) (fun f ↦ le_trans (f.norm_integral_le_mul_norm _) le_rfl)


@[simps! apply]
noncomputable def ofMeasureL : 𝓓^{n}(E, F) →L[𝕜] F where
  toLinearMap := (ofMeasureₗ 𝕜 n μ : 𝓓^{n}(E, F) →ₗ[𝕜] F)
  cont := show Continuous (ofMeasureₗ ℝ n μ) by
    (
      rw [TestFunction.continuous_iff ℝ (ofMeasureₗ ℝ n μ)]
      intro K
      have fin_μ : IsFiniteMeasure (μ.restrict K) := by
        have : Fact (μ K < ⊤) := fact_iff.mpr <| K.isCompact.measure_lt_top
        apply MeasureTheory.Restrict.isFiniteMeasure
      have : ofMeasureₗ ℝ n μ ∘ (toTestFunction ℝ F n K)
          = ((∫ x, · x ∂(μ.restrict K)) : (E →ᵇ F) → F)  ∘
            (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜) := by
        ext f
        simp [ofMeasureₗ]
        have hK : MeasurableSet (K : Set E) := K.isCompact.measurableSet
        have : ∫ (x : E) in (K : Set E)ᶜ, f x ∂μ = 0 := by
          refine setIntegral_eq_zero_of_forall_eq_zero f.zero_on_compl
        rw [← add_zero (∫ (x : E) in ↑K, f x ∂μ), ← this,
          MeasureTheory.integral_add_compl hK (map_integrable' n μ f)]
        congr
      rw [this]
      apply (integralFiniteMeasure 𝕜 E F (μ.restrict K)).continuous.comp
          (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous
    )


end FromMeasure


section FromLocallyIntegrable


open MeasureTheory Module

variable [MeasurableSpace E]
variable (μ : Measure E)

variable [NormedSpace ℝ 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [ContinuousConstSMul 𝕜 F]


variable [Module 𝕜 F] [SMulCommClass ℝ 𝕜 F] [ContinuousConstSMul 𝕜 F] [IsScalarTower ℝ 𝕜 F]

noncomputable def ofLocallyIntegrable (f : E → F) :
    𝓓^{n}(E, 𝕜) → F := fun φ : 𝓓^{n}(E, 𝕜) ↦ (∫ x, (φ x) • (f x) ∂μ)

@[simp]
lemma ofLocallyIntegrable_apply (f : E → F) (φ : 𝓓^{n}(E, 𝕜)) :
    ofLocallyIntegrable 𝕜 n μ f φ = (∫ x, (φ x) • (f x) ∂μ) := by
  rfl

variable [OpensMeasurableSpace E] [IsBoundedSMul 𝕜 F]
variable {𝕜}

lemma ofLocallyIntegrable_integrable {f : E → F} (hf : LocallyIntegrable f μ) (φ : 𝓓^{n}(E, 𝕜)) :
    Integrable (fun x ↦ (φ x) • (f x)) μ := by
  apply MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hf
          (map_continuous φ) (compact_supp φ)

-- TODO: This fails to synthetize Module 𝕜 𝓓^{n}(E, 𝕜), so fixing map to be ℝ-linear.
noncomputable def ofLocallyIntegrableₗ {f : E → F} (hf : LocallyIntegrable f μ) :
    𝓓^{n}(E, 𝕜) →ₗ[ℝ] F :=
  { toFun := ofLocallyIntegrable 𝕜 n μ f
    map_add' := fun φ Φ  ↦ by
      simp only [ofLocallyIntegrable_apply, add_apply]
      simp_rw [add_smul]
      apply integral_add (ofLocallyIntegrable_integrable n μ hf φ)
        (ofLocallyIntegrable_integrable n μ hf Φ)
    map_smul' := fun c φ ↦ by
      simp only [ofLocallyIntegrable_apply, smul_apply, RingHom.id_apply]
      simp_rw [smul_assoc, integral_smul c (fun x ↦  φ x • f x)]
  }

variable [IsFiniteMeasureOnCompacts μ] [SecondCountableTopology E] [NormSMulClass 𝕜 F]

open LocallyIntegrableOn Integrable MeasureTheory

variable (𝕜)
theorem isLinear_integral {f : E → F} (hf : LocallyIntegrable f μ) (K : Compacts E) :
  IsLinearMap 𝕜 fun φ : (E →ᵇ 𝕜) ↦ ∫ (x : E), φ x • (K : Set E).indicator f x ∂μ := by
  constructor
  · intro φ Φ
    have h: ∀ φ : (E →ᵇ 𝕜), Integrable (fun x ↦ (φ x) • ((K : Set E).indicator f x)) μ := by
      intro φ
      have : support (fun x ↦ (φ x) • ((K : Set E).indicator f x)) ⊆ K := by
        aesop
      rw [← integrableOn_iff_integrable_of_support_subset this]
      apply MeasureTheory.IntegrableOn.continuousOn_smul
      · refine IntegrableOn.integrable_indicator ?_ (K.isCompact.measurableSet)
        refine integrableOn_isCompact (?_) K.isCompact
        rw [MeasureTheory.locallyIntegrableOn_iff_locallyIntegrable_restrict]
        rw [MeasureTheory.Measure.restrict_restrict]
        simp
        rw [← MeasureTheory.locallyIntegrableOn_iff_locallyIntegrable_restrict]
        apply MeasureTheory.LocallyIntegrable.locallyIntegrableOn (hf) K
        · exact K.isCompact.isClosed
        · exact K.isCompact.measurableSet
        · exact K.isCompact.isClosed
      · exact φ.continuous.continuousOn
      · exact K.isCompact
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    simp_rw [add_smul, integral_add (h φ) (h Φ)]
  · refine fun c φ ↦ by
      simp only [BoundedContinuousFunction.coe_smul]
      rw [← integral_smul c (fun (x : E) ↦  φ x • (K : Set E).indicator f x)]
      simp_rw [smul_assoc]




-- theorem  isBDL_integral {f : E → F} (hf : LocallyIntegrable f μ) (K : Compacts E):
--     IsBoundedLinearMap 𝕜 (fun φ : (E →ᵇ 𝕜) ↦ ∫ x, (φ x) • ((K : Set E).indicator f x) ∂μ) := by
--   constructor
--   · -- exact isLinear_integral 𝕜 μ hf K bleach
--     sorry
--   · set M := ∫ x, ‖(K : Set E).indicator f x‖∂μ
--     use M + 1
--     constructor
--     · refine add_pos_of_nonneg_of_pos ?_ (Real.zero_lt_one)
--       · refine le_trans ?_ (MeasureTheory.norm_integral_le_integral_norm _)
--         exact norm_nonneg _
--     · intro φ
--       set g : E → ℝ := fun x ↦ ‖φ‖ * ‖(K : Set E).indicator f x‖
--       have hg : Integrable g μ := by
--         apply Integrable.const_mul (Integrable.norm ?_)
--         refine IntegrableOn.integrable_indicator ?_ (K.isCompact.measurableSet)
--         refine integrableOn_isCompact (hf.locallyIntegrableOn K) K.isCompact
--       have hgf : ∀ᵐ (x : E) ∂μ, ‖(fun a ↦ (φ a) • (K : Set E).indicator f a) x‖ ≤ g x := by
--         apply ae_of_all
--         intro x
--         simp only [g, norm_smul]
--         gcongr
--         exact BoundedContinuousFunction.norm_coe_le_norm φ x
--       apply le_trans (MeasureTheory.norm_integral_le_of_norm_le hg hgf)
--       simp only [g]
--       rw [integral_const_mul_of_integrable]
--       · rw [mul_comm]
--         gcongr
--         simp only [le_add_iff_nonneg_right, zero_le_one, M]
--       · apply Integrable.norm ?_
--         refine IntegrableOn.integrable_indicator ?_ (K.isCompact.measurableSet)
--         refine integrableOn_isCompact (hf.locallyIntegrableOn K) K.isCompact



@[simps! apply]
noncomputable def ofLocallyIntegrableL {f : E → F} (hf : LocallyIntegrable f μ) :
    𝓓^{n}(E, 𝕜) →L[ℝ] F where
  toLinearMap := (ofLocallyIntegrableₗ n μ hf : 𝓓^{n}(E, 𝕜) →ₗ[ℝ] F)
  cont := show Continuous (ofLocallyIntegrableₗ n μ hf) by
    (
        rw [TestFunction.continuous_iff ℝ (ofLocallyIntegrableₗ n μ hf)]
        intro K
        set int' : (E →ᵇ 𝕜) →ₗ[ℝ] F := {
            toFun := fun φ ↦ ∫ x, (φ x) • ((K : Set E).indicator f x) ∂μ
            map_add' := by
              intro φ Φ
              have h: ∀ φ : (E →ᵇ 𝕜), Integrable (fun x ↦ (φ x) • ((K : Set E).indicator f x)) μ :=
                by
                intro φ
                have : support (fun x ↦ (φ x) • ((K : Set E).indicator f x)) ⊆ K := by
                  aesop
                rw [← integrableOn_iff_integrable_of_support_subset this]
                apply MeasureTheory.IntegrableOn.continuousOn_smul
                · refine IntegrableOn.integrable_indicator ?_ (K.isCompact.measurableSet)
                  refine integrableOn_isCompact (?_) K.isCompact
                  rw [MeasureTheory.locallyIntegrableOn_iff_locallyIntegrable_restrict]
                  rw [MeasureTheory.Measure.restrict_restrict]
                  simp
                  rw [← MeasureTheory.locallyIntegrableOn_iff_locallyIntegrable_restrict]
                  apply MeasureTheory.LocallyIntegrable.locallyIntegrableOn (hf) K
                  · exact K.isCompact.isClosed
                  · exact K.isCompact.measurableSet
                  · exact K.isCompact.isClosed
                · exact φ.continuous.continuousOn
                · exact K.isCompact
              simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
              simp_rw [add_smul, integral_add (h φ) (h Φ)]
            map_smul' :=  fun c φ ↦ by
              simp only [BoundedContinuousFunction.coe_smul, RingHom.id_apply]
              rw [← integral_smul c (fun (x : E) ↦  φ x • (K : Set E).indicator f x)]
              simp_rw [smul_assoc]
        }
        have : IsBoundedLinearMap ℝ int' := by
          constructor
          · exact LinearMap.isLinear int'
          · set M := ∫ x, ‖(K : Set E).indicator f x‖∂μ
            use M + 1
            constructor
            · refine add_pos_of_nonneg_of_pos ?_ (Real.zero_lt_one)
              · refine le_trans ?_ (MeasureTheory.norm_integral_le_integral_norm _)
                exact norm_nonneg _
            · intro φ
              simp [int']
              set g : E → ℝ := fun x ↦ ‖φ‖ * ‖(K : Set E).indicator f x‖
              have hg : Integrable g μ := by
                apply Integrable.const_mul (Integrable.norm ?_)
                refine IntegrableOn.integrable_indicator ?_ (K.isCompact.measurableSet)
                refine integrableOn_isCompact (hf.locallyIntegrableOn K) K.isCompact
              have hgf : ∀ᵐ (x : E) ∂μ, ‖(fun a ↦ (φ a) • (K : Set E).indicator f a) x‖ ≤ g x := by
                apply ae_of_all
                intro x
                simp only [g, norm_smul]
                gcongr
                exact BoundedContinuousFunction.norm_coe_le_norm φ x
              apply le_trans (MeasureTheory.norm_integral_le_of_norm_le hg hgf)
              simp only [g]
              rw [integral_const_mul_of_integrable]
              · rw [mul_comm]
                gcongr
                simp only [le_add_iff_nonneg_right, zero_le_one, M]
              · apply Integrable.norm ?_
                refine IntegrableOn.integrable_indicator ?_ (K.isCompact.measurableSet)
                refine integrableOn_isCompact (hf.locallyIntegrableOn K) K.isCompact
        set int : (E →ᵇ 𝕜) →L[ℝ] F :=
          { toLinearMap := int'
            cont := by
              apply IsBoundedLinearMap.continuous this  }
        have : ofLocallyIntegrableₗ n μ hf ∘ (toTestFunction ℝ 𝕜 n K)
          = (fun φ ↦ ∫ x, (φ x) • ((K : Set E).indicator f x) ∂μ) ∘
              ((ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ)):= by
            ext φ
            simp [ofLocallyIntegrableₗ]
            congr
            ext x
            simp [toTestFunction_apply]
            by_cases h : x ∈ K
            · simp [h]
            · simp [h, φ.zero_on_compl h]
        rw [this]
        exact int.continuous.comp
          ((ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ)).continuous
    )

end FromLocallyIntegrable


section DiracDelta

variable (F)

noncomputable def delta (x : E) : 𝓓^{n}(E, F) →L[𝕜] F :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp (toBoundedContinuousFunctionCLM 𝕜 E F n)

@[simp]
theorem delta_apply (x₀ : E) (f : 𝓓^{n}(E, F)) : delta 𝕜 F n x₀ f = f x₀ :=
  rfl

open MeasureTheory Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
variable [CompleteSpace F]

/-- Integrating against the Dirac measure is equal to the delta distribution. -/
@[simp]
theorem integralCLM_dirac_eq_delta (x : E) : ofMeasureL 𝕜 n (dirac x) = delta 𝕜 F n x := by
  aesop

end DiracDelta

end TestFunction

namespace Distribution

open TestFunction

variable [RCLike 𝕜] [Module ℝ F]

end Distribution
