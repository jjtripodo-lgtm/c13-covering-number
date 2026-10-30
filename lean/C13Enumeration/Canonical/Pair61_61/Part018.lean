import C13Enumeration.Canonical.Pair61_61.Part019
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound607 : ∀ f ∈ assignSearch step finish [11] [7] table607, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table607 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound608

theorem bound606 : ∀ f ∈ assignSearch step finish [10,11] [0,7] table606, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,7] [0] table606 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound607

theorem bound605 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,7] table605, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,7] [2] table605 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound606

theorem bound604 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,3,7] table604, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,3,7] [3] table604 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound605

theorem bound603 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,7,11] table603, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,7,11] [11] table603 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound604

theorem bound602 : ∀ f ∈ assignSearch step finish [] [] table602, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound601 : ∀ f ∈ assignSearch step finish [11] [3] table601, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table601 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound602

theorem bound600 : ∀ f ∈ assignSearch step finish [10,11] [3,11] table600, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,11] [11] table600 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound601

theorem bound599 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,11] table599, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,11] [9] table599 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound600

theorem bound598 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,7,9,11] table598, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,7,9,11] [7] table598 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound599

theorem bound597 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,7,9,11] table597, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,7,9,11] [0] table597 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound598

theorem bound596 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,7,9,11] table596, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,7,9,11] [2,9] table596 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound597
    · exact bound603

theorem bound595 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,7,9,10,11] table595, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,7,9,10,11] [10] table595 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound596

theorem bound594 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,7,9,10,11] table594, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,7,9,10,11] [1] table594 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound595

theorem bound593 : ∀ f ∈ assignSearch step finish [] [] table593, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound592 : ∀ f ∈ assignSearch step finish [11] [6] table592, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table592 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound593

theorem bound591 : ∀ f ∈ assignSearch step finish [10,11] [1,6] table591, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,6] [1] table591 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound592

theorem bound590 : ∀ f ∈ assignSearch step finish [9,10,11] [1,6,9] table590, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,6,9] [9] table590 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound591

theorem bound589 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,6,7,9] table589, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,6,7,9] [7] table589 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound590

theorem bound588 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,7,9] table588, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,7,9] [0] table588 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound589

theorem bound587 : ∀ f ∈ assignSearch step finish [] [] table587, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound586 : ∀ f ∈ assignSearch step finish [11] [7] table586, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table586 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound587

theorem bound585 : ∀ f ∈ assignSearch step finish [10,11] [0,7] table585, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,7] [0] table585 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound586

theorem bound584 : ∀ f ∈ assignSearch step finish [9,10,11] [0,7,10] table584, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,7,10] [10] table584 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound585

theorem bound583 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,6,7,10] table583, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,6,7,10] [6] table583 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound584

theorem bound582 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,7,10] table582, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,7,10] [1] table582 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound583

theorem bound581 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,6,7,9,10] table581, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,6,7,9,10] [9,10] table581 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound582
    · exact bound588

theorem bound580 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,7,9,10] table580, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,7,9,10] [2] table580 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound581

theorem bound579 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,9,10,11] table579, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,9,10,11] [11] table579 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound580

theorem bound578 : ∀ f ∈ assignSearch step finish [] [] table578, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound577 : ∀ f ∈ assignSearch step finish [11] [0] table577, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table577 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound578

theorem bound576 : ∀ f ∈ assignSearch step finish [10,11] [0,7] table576, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,7] [7] table576 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound577
end C13.Enumeration.Canonical.Pair61_61
