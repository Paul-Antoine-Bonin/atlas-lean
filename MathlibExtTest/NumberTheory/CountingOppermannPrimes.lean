/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingOppermannPrimes

namespace MetaMathlibExt

example : oppermannLowerPrimeCount 2 = 2 := by decide
example : oppermannUpperPrimeCount 2 = 1 := by decide

#print axioms oppermannLowerPrimeCount
#print axioms oppermannUpperPrimeCount
#print axioms oppermannAsymptotic

end MetaMathlibExt
