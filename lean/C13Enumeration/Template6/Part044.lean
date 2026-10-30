import C13Enumeration.Template6.Part045
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound719 : ∀ f ∈ assignSearch step finish [9,11] [1,3] table719, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,3] [3] table719 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound720

theorem bound718 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,3] table718, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,3] [2] table718 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound719

theorem bound717 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,3,7] table717, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,3,7] [7] table717 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound718

theorem bound716 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,3,5,7] table716, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,3,5,7] [5] table716 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound717

theorem bound715 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,3,4,5,7] table715, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,3,4,5,7] [4] table715 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound716

theorem bound714 : ∀ f ∈ assignSearch step finish [] [] table714, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound713 : ∀ f ∈ assignSearch step finish [11] [1] table713, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table713 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound714

theorem bound712 : ∀ f ∈ assignSearch step finish [9,11] [1,9] table712, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,9] [9] table712 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound713

theorem bound711 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table711, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [2] table711 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound712

theorem bound710 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,7,9] table710, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,7,9] [7] table710 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound711

theorem bound709 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,5,7,9] table709, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,5,7,9] [5] table709 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound710

theorem bound708 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table708, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [4] table708 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound709

theorem bound707 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,3,4,5,7,9] table707, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,3,4,5,7,9] [3,9] table707 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound708
    · exact bound715

theorem bound706 : ∀ f ∈ assignSearch step finish [] [] table706, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound705 : ∀ f ∈ assignSearch step finish [11] [1] table705, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table705 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound706

theorem bound704 : ∀ f ∈ assignSearch step finish [9,11] [1,2] table704, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,2] [2] table704 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound705
end C13.Enumeration.Template6
