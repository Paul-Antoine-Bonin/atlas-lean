/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverLocalDegree

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]

example : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) :=
  finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg v w

example (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  rw [finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg v w, he, hf,
    mul_one]

end HeightOneSpectrum

end IsDedekindDomain
