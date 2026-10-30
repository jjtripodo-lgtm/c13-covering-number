import C13Enumeration.Canonical.Pair61_61.Part020
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound639 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,10,11] table639, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,10,11] [1,2,3,6,10,11] table639 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound640
    · exact bound655
    · exact bound670
    · exact bound685
    · exact bound700
    · exact bound715

theorem bound638 : ∀ f ∈ assignSearch step finish [] [] table638, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound637 : ∀ f ∈ assignSearch step finish [11] [1] table637, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table637 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound638

theorem bound636 : ∀ f ∈ assignSearch step finish [10,11] [1,6] table636, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,6] [6] table636 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound637

theorem bound635 : ∀ f ∈ assignSearch step finish [9,10,11] [1,6,9] table635, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,6,9] [9] table635 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound636

theorem bound634 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,6,9] table634, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,6,9] [0] table634 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound635

theorem bound633 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,7,9] table633, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,7,9] [7] table633 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound634

theorem bound632 : ∀ f ∈ assignSearch step finish [] [] table632, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound631 : ∀ f ∈ assignSearch step finish [11] [0] table631, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table631 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound632

theorem bound630 : ∀ f ∈ assignSearch step finish [10,11] [0,7] table630, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,7] [7] table630 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound631

theorem bound629 : ∀ f ∈ assignSearch step finish [9,10,11] [0,7,10] table629, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,7,10] [10] table629 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound630

theorem bound628 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,7,10] table628, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,7,10] [1] table628 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound629

theorem bound627 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,7,10] table627, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,7,10] [6] table627 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound628

theorem bound626 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,6,7,9,10] table626, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,6,7,9,10] [9,10] table626 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound627
    · exact bound633

theorem bound625 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,7,9,10] table625, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,7,9,10] [2] table625 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound626

theorem bound624 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,9,10] table624, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,7,9,10] [3] table624 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound625

theorem bound623 : ∀ f ∈ assignSearch step finish [] [] table623, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound622 : ∀ f ∈ assignSearch step finish [11] [6] table622, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table622 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound623

theorem bound621 : ∀ f ∈ assignSearch step finish [10,11] [1,6] table621, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,6] [1] table621 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound622

theorem bound620 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,6] table620, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,6] [2] table620 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound621

theorem bound619 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,3,6] table619, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,3,6] [3] table619 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound620

theorem bound618 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,6,11] table618, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,6,11] [11] table618 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound619

theorem bound617 : ∀ f ∈ assignSearch step finish [] [] table617, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound616 : ∀ f ∈ assignSearch step finish [11] [3] table616, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table616 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound617

theorem bound615 : ∀ f ∈ assignSearch step finish [10,11] [3,11] table615, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,11] [11] table615 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound616

theorem bound614 : ∀ f ∈ assignSearch step finish [9,10,11] [3,10,11] table614, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,10,11] [10] table614 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound615

theorem bound613 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,6,10,11] table613, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,6,10,11] [6] table613 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound614

theorem bound612 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,6,10,11] table612, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,6,10,11] [1] table612 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound613

theorem bound611 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,6,10,11] table611, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,6,10,11] [2,10] table611 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound612
    · exact bound618

theorem bound610 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,9,10,11] table610, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,9,10,11] [9] table610 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound611

theorem bound609 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,9,10,11] table609, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,9,10,11] [0] table609 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound610

theorem bound608 : ∀ f ∈ assignSearch step finish [] [] table608, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Canonical.Pair61_61
