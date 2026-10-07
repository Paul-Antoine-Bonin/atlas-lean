/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.IntegerPolynomialMap

@[expose] public section

namespace MetaMathlibExt

noncomputable example {n m : ℕ} (F : IntegerPolynomialMap n m) (x : Fin n → ℤ) :
    Fin m → ℤ :=
  F.toFun x

noncomputable example {n m p : ℕ} (F : IntegerPolynomialMap n m) (x : Fin n → ZMod p) :
    Fin m → ZMod p :=
  F.toFunReduce p x

noncomputable example {n : ℕ} (F : IntegerPolynomialMap n n) (x : Fin n → ℤ) :
    F.iterate 0 x = x := rfl

noncomputable example {n p : ℕ} (F : IntegerPolynomialMap n n) (x : Fin n → ZMod p) :
    F.iterateReduce p 0 x = x := rfl

#print axioms MetaMathlibExt.IntegerPolynomialMap
#print axioms MetaMathlibExt.IntegerPolynomialMap.toFun
#print axioms MetaMathlibExt.IntegerPolynomialMap.toFunReduce
#print axioms MetaMathlibExt.IntegerPolynomialMap.iterate
#print axioms MetaMathlibExt.IntegerPolynomialMap.iterateReduce

end MetaMathlibExt

end
