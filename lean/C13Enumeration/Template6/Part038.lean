import C13Enumeration.Template6.Part039
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound623 : ∀ f ∈ assignSearch step finish [] [] table623, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound622 : ∀ f ∈ assignSearch step finish [11] [3] table622, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table622 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound623

theorem bound621 : ∀ f ∈ assignSearch step finish [9,11] [3,8] table621, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,8] [8] table621 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound622

theorem bound620 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table620, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [11] table620 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound621

theorem bound619 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,5,8,11] table619, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,5,8,11] [5] table619 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound620

theorem bound618 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,4,5,8,11] table618, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,4,5,8,11] [4] table618 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound619

theorem bound617 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table617, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [7] table617 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound618

theorem bound616 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [2,3,4,5,7,8,11] table616, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [2,3,4,5,7,8,11] [2,8] table616 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound617
    · exact bound624

theorem bound615 : ∀ f ∈ assignSearch step finish [2,3,4,5,7,8,9,11] [1,2,3,4,5,7,8,11] table615, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7,8,9,11] [1,2,3,4,5,7,8,11] [1,2,8,11] table615 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound616
    · exact bound631
    · exact bound646
    · exact bound661

theorem bound614 : ∀ f ∈ assignSearch step finish [] [] table614, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound613 : ∀ f ∈ assignSearch step finish [11] [2] table613, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table613 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound614

theorem bound612 : ∀ f ∈ assignSearch step finish [9,11] [2,3] table612, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,3] [3] table612 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound613

theorem bound611 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,3] table611, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,3] [1] table611 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound612

theorem bound610 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,3,4] table610, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,3,4] [4] table610 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound611

theorem bound609 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,3,4,5] table609, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,3,4,5] [5] table609 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound610

theorem bound608 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,3,4,5,7] table608, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,3,4,5,7] [7] table608 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound609
end C13.Enumeration.Template6
