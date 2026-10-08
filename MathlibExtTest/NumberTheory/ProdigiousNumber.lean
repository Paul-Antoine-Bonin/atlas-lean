/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ProdigiousNumber

example : ¬ MetaMathlibExt.IsProdigious 0 12 := by decide

example : ¬ MetaMathlibExt.IsProdigious 1 12 := by decide

example : ¬ MetaMathlibExt.IsProdigious 10 0 := by decide

example : MetaMathlibExt.IsProdigious 2 5 := by decide

example : MetaMathlibExt.IsProdigious 10 12 := by decide

example : ¬ MetaMathlibExt.IsProdigious 10 13 := by decide
