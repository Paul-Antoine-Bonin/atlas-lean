/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.PartitionPolynomial

namespace MetaMathlibExt

private def samplePartition : Nat.Partition 10 :=
  Nat.Partition.ofMultiset {1, 2, 2, 5}

example : partitionPolynomial (Nat.Partition.indiscrete 0) = 0 := by
  simp [partitionPolynomial]

example : (partitionPolynomial samplePartition).coeff 2 = 2 := by
  rw [coeff_partitionPolynomial]
  decide

example : (partitionPolynomial samplePartition).coeff 3 = 0 := by
  rw [coeff_partitionPolynomial]
  decide

example : (partitionPolynomial samplePartition).eval 1 = 4 := by
  rw [eval_partitionPolynomial_at_one]
  decide

#print axioms partitionPolynomial
#print axioms coeff_partitionPolynomial
#print axioms eval_partitionPolynomial_at_one

end MetaMathlibExt
