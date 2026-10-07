/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BAryMultinomialCoefficient

open MetaMathlibExt

example : bAryDigit 2 6 0 = 0 := by decide
example : bAryDigit 2 6 1 = 1 := by decide
example : bAryDigit 2 6 2 = 1 := by decide
example : bAryDigit 2 6 3 = 0 := by decide
example : ordinaryMultinomialFactor 5 [2, 3] = 10 := by decide
example : ordinaryMultinomialFactor 5 [2, 2] = 0 := by decide
example : ordinaryMultinomialFactor 0 [1] = 0 := by decide
example : bAryMultinomial 10 5 [2, 3] (by decide) = 10 := by decide
example : bAryMultinomial 10 5 [2, 2] (by decide) = 0 := by decide
example : bAryMultinomial 2 1 [1] (by decide) = 1 := by decide
example : bAryMultinomial 2 2 [2] (by decide) = 1 := by decide
example : bAryMultinomial 2 3 [1, 2] (by decide) = 1 := by decide
example : bAryMultinomial 2 2 [1, 1] (by decide) = 0 := by decide
example : bAryMultinomial 2 0 [] (by decide) = 1 := by decide
example : bAryMultinomial 2 0 [0] (by decide) = 1 := by decide
example : bAryMultinomial 2 0 [1] (by decide) = 0 := by decide
