/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.NumberTheory.CommaSequence

open MetaMathlibExt

#check MetaMathlibExt.commaMsd
#check MetaMathlibExt.IsCommaCandidate
#check MetaMathlibExt.IsCommaSucc
#check MetaMathlibExt.IsCommaTerminal
#check MetaMathlibExt.IsInfiniteCommaSeq
#check MetaMathlibExt.IsCommaTerminating

example : IsCommaSucc 10 1 12 := by
  unfold IsCommaSucc IsCommaCandidate commaMsd
  decide

example : IsCommaSucc 10 12 35 := by
  unfold IsCommaSucc IsCommaCandidate commaMsd
  decide

example : IsCommaTerminal 10 36 := by
  unfold IsCommaTerminal IsCommaCandidate commaMsd
  decide

example (b v : Nat) (a : Nat → Nat) (h : IsInfiniteCommaSeq b v a) : a 1 = v := by
  unfold IsInfiniteCommaSeq at h
  exact h.2.2.1
