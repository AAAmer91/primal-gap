import CutBitReconstruction
import Mathlib.Util.AssertNoSorry

assert_no_sorry CutBit.reconstruct_cutBit
assert_no_sorry CutBit.cutBit_eq_of_intervals
assert_no_sorry CutBit.thirdCutBit_not_determined

example : CutBit.cutSize {0, 2} [(0, 1), (0, 2), (2, 3)] = 2 := by
  decide

example : CutBit.cutBit [(0, 1), (0, 2), (2, 3)] {0, 2} = 1 := by
  decide

example : CutBit.mixedDifference (CutBit.cutBit [(0, 1), (0, 2), (2, 3)]) 0 2 = 1 := by
  decide
