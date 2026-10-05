module

public import MathlibExt.NumberTheory.Harmonic.Floor

@[expose] public section

open Asymptotics Filter Real Topology

example :
    (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ) - Real.log x -
      eulerMascheroniConstant) =O[Filter.atTop] fun x : ℝ => x⁻¹ :=
  Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant

theorem tendsto_centered_floor_harmonic_error_atTop :
    Filter.Tendsto
      (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ) - Real.log x -
        eulerMascheroniConstant) Filter.atTop (nhds 0) :=
  Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant.trans_tendsto
    tendsto_inv_atTop_zero

end
