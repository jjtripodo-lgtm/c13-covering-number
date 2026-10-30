import C13Enumeration.Template6.Part037
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound591 : ∀ f ∈ assignSearch step finish [11] [2] table591, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table591 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound592

theorem bound590 : ∀ f ∈ assignSearch step finish [9,11] [2,11] table590, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,11] [11] table590 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound591

theorem bound589 : ∀ f ∈ assignSearch step finish [8,9,11] [2,3,11] table589, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,3,11] [3] table589 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound590

theorem bound588 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,3,4,11] table588, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,3,4,11] [4] table588 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound589

theorem bound587 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,3,4,7,11] table587, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,3,4,7,11] [7] table587 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound588

theorem bound586 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,3,4,5,7,11] table586, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,3,4,5,7,11] [5] table586 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound587

theorem bound585 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,3,4,5,7,11] table585, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,3,4,5,7,11] [1,11] table585 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound586
    · exact bound593

theorem bound584 : ∀ f ∈ assignSearch step finish [] [] table584, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound583 : ∀ f ∈ assignSearch step finish [11] [2] table583, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table583 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound584

theorem bound582 : ∀ f ∈ assignSearch step finish [9,11] [1,2] table582, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,2] [1] table582 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound583

theorem bound581 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table581, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [9] table581 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound582

theorem bound580 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,4,9] table580, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,4,9] [4] table580 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound581

theorem bound579 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,4,7,9] table579, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,4,7,9] [7] table579 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound580

theorem bound578 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table578, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [5] table578 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound579

theorem bound577 : ∀ f ∈ assignSearch step finish [] [] table577, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound576 : ∀ f ∈ assignSearch step finish [11] [2] table576, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table576 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound577
end C13.Enumeration.Template6
