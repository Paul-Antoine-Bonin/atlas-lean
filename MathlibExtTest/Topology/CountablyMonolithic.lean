/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CountablyMonolithic
import Mathlib.Topology.Metrizable.Basic

/-- Every second-countable space is countably monolithic. -/
example (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    CountablyMonolithicSpace X where
  hasCountableNetwork_closure_of_countable _ _ :=
    hasCountableNetwork_of_secondCountable _

/-- Every metrizable space is countably monolithic. -/
example (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    CountablyMonolithicSpace X where
  hasCountableNetwork_closure_of_countable {s} hs := by
    letI : SecondCountableTopology ↥(closure s) :=
      (hs.isSeparable.closure).secondCountableTopology
    exact hasCountableNetwork_of_secondCountable _
