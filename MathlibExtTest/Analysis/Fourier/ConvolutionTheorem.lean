module

import MathlibExt.Analysis.Fourier.ConvolutionTheorem

open MeasureTheory
open scoped Convolution

namespace MetaMathlibExt

-- The abstract result recovers the standard Fourier convolution theorem on `ℝ`.
example {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    Fourier.fourierIntegral Real.fourierChar volume
        (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g) w =
      Fourier.fourierIntegral Real.fourierChar volume f w *
        Fourier.fourierIntegral Real.fourierChar volume g w := by
  exact convolution_theorem Real.continuous_fourierChar
    (fun a => measurePreserving_add_left volume a) hf hg w

end MetaMathlibExt
