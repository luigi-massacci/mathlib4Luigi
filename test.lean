import Mathlib

noncomputable def t : NormedSpace ℝ ℂ := by infer_instance

noncomputable def t' : MeasurableSpace E  := by infer_instance

variable (μ : Measure E)

#min_imports
