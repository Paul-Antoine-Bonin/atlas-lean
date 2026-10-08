/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.OrderedSetPartition
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : IsOrderedSetPartition ({0, 1} : Finset ℕ)
    [({0} : Finset ℕ), ({1} : Finset ℕ)] := by
  norm_num [IsOrderedSetPartition]; decide

example : ¬ IsOrderedSetPartition ({0, 1} : Finset ℕ)
    [({0} : Finset ℕ), ({0, 1} : Finset ℕ)] := by
  norm_num [IsOrderedSetPartition]

end MetaMathlibExt
