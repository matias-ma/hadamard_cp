import HadamardAppendix

-- Expect only propext, Classical.choice, and Quot.sound.
-- The cited literature is an explicit hypothesis visible in #check,
-- not a project-specific axiom and not part of FourStage.
#print axioms HadamardAppendix.sixth_pivot
#print axioms HadamardAppendix.sixth_pivot_any_order
#print axioms HadamardAppendix.sixth_pivot_exclusions
#print axioms HadamardAppendix.fourStage_of_completePivoting
#print axioms HadamardAppendix.hadamard_of_abs_det_four
#print axioms HadamardAppendix.eliminate_four_eq_schur

#check HadamardAppendix.sixth_pivot
#check HadamardAppendix.sixth_pivot_any_order
#print HadamardAppendix.CitedPivotFacts
#print HadamardAppendix.CompletelyPivoted
#print HadamardAppendix.pivotMagnitude
#print HadamardAppendix.eliminate
