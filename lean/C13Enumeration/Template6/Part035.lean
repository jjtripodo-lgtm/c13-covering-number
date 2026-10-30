import C13Enumeration.Template6.Part036
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound575 : ∀ f ∈ assignSearch step finish [9,11] [2,11] table575, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,11] [11] table575 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound576

theorem bound574 : ∀ f ∈ assignSearch step finish [8,9,11] [2,9,11] table574, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,9,11] [9] table574 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound575

theorem bound573 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,4,9,11] table573, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,4,9,11] [4] table573 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound574

theorem bound572 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,4,7,9,11] table572, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,4,7,9,11] [7] table572 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound573

theorem bound571 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,4,5,7,9,11] table571, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,4,5,7,9,11] [5] table571 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound572

theorem bound570 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,4,5,7,9,11] table570, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,4,5,7,9,11] [1,11] table570 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound571
    · exact bound578

theorem bound569 : ∀ f ∈ assignSearch step finish [] [] table569, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound568 : ∀ f ∈ assignSearch step finish [11] [2] table568, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table568 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound569

theorem bound567 : ∀ f ∈ assignSearch step finish [9,11] [2,3] table567, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,3] [3] table567 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound568

theorem bound566 : ∀ f ∈ assignSearch step finish [8,9,11] [2,3,11] table566, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,3,11] [11] table566 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound567

theorem bound565 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,3,4,11] table565, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,3,4,11] [4] table565 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound566

theorem bound564 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,3,4,5,11] table564, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,3,4,5,11] [5] table564 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound565

theorem bound563 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,3,4,5,7,11] table563, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,3,4,5,7,11] [7] table563 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound564

theorem bound562 : ∀ f ∈ assignSearch step finish [] [] table562, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound561 : ∀ f ∈ assignSearch step finish [11] [2] table561, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table561 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound562

theorem bound560 : ∀ f ∈ assignSearch step finish [9,11] [2,9] table560, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,9] [9] table560 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound561
end C13.Enumeration.Template6
