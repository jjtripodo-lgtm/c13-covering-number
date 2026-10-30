import C13Enumeration.Canonical.Pair61_61.Part004
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound127 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,7,9,11] table127, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,7,9,11] [11] table127 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound128

theorem bound126 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,7,9,11] table126, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,7,9,11] [3,7] table126 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound127
    · exact bound133

theorem bound125 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,7,9,10,11] table125, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,7,9,10,11] [10] table125 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound126

theorem bound124 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,7,8,9,10,11] table124, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,7,8,9,10,11] [8] table124 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound125

theorem bound123 : ∀ f ∈ assignSearch step finish [] [] table123, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound122 : ∀ f ∈ assignSearch step finish [11] [6] table122, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table122 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound123

theorem bound121 : ∀ f ∈ assignSearch step finish [10,11] [6,8] table121, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,8] [8] table121 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound122

theorem bound120 : ∀ f ∈ assignSearch step finish [9,10,11] [6,7,8] table120, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [6,7,8] [7] table120 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound121

theorem bound119 : ∀ f ∈ assignSearch step finish [8,9,10,11] [6,7,8,9] table119, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [6,7,8,9] [9] table119 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound120

theorem bound118 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,7,8,9,11] table118, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,7,8,9,11] [11] table118 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound119

theorem bound117 : ∀ f ∈ assignSearch step finish [] [] table117, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound116 : ∀ f ∈ assignSearch step finish [11] [9] table116, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table116 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound117

theorem bound115 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table115, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [11] table115 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound116

theorem bound114 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table114, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table114 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound115

theorem bound113 : ∀ f ∈ assignSearch step finish [8,9,10,11] [6,9,10,11] table113, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [6,9,10,11] [6] table113 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound114

theorem bound112 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table112, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,8,9,10,11] [8] table112 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound113

theorem bound111 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table111, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [7,10] table111 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound112
    · exact bound118

theorem bound110 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [3,6,7,8,9,10,11] table110, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [3,6,7,8,9,10,11] [3] table110 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound111

theorem bound109 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,3,6,7,8,9,10,11] table109, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,3,6,7,8,9,10,11] [0] table109 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound110

theorem bound108 : ∀ f ∈ assignSearch step finish [] [] table108, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound107 : ∀ f ∈ assignSearch step finish [11] [8] table107, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table107 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound108

theorem bound106 : ∀ f ∈ assignSearch step finish [10,11] [6,8] table106, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,8] [6] table106 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound107

theorem bound105 : ∀ f ∈ assignSearch step finish [9,10,11] [6,7,8] table105, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [6,7,8] [7] table105 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound106

theorem bound104 : ∀ f ∈ assignSearch step finish [8,9,10,11] [6,7,8,11] table104, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [6,7,8,11] [11] table104 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound105

theorem bound103 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,7,8,9,11] table103, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,7,8,9,11] [9] table103 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound104

theorem bound102 : ∀ f ∈ assignSearch step finish [] [] table102, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound101 : ∀ f ∈ assignSearch step finish [11] [11] table101, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table101 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound102

theorem bound100 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table100, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [9] table100 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound101

theorem bound99 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table99, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table99 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound100

theorem bound98 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table98, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [8] table98 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound99

theorem bound97 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table97, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table97 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound98

theorem bound96 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table96, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [7,10] table96 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound97
    · exact bound103
end C13.Enumeration.Canonical.Pair61_61
