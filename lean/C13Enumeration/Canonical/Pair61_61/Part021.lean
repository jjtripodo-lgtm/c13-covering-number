import C13Enumeration.Canonical.Pair61_61.Part022
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound703 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,6,7,11] table703, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,6,7,11] [1] table703 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound704

theorem bound702 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,6,7,11] table702, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,6,7,11] [0,7] table702 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound703
    · exact bound709

theorem bound701 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,6,7,8,11] table701, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,6,7,8,11] [8] table701 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound702

theorem bound700 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,11] table700, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,7,8,11] [2] table700 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound701

theorem bound699 : ∀ f ∈ assignSearch step finish [] [] table699, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound698 : ∀ f ∈ assignSearch step finish [11] [2] table698, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table698 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound699

theorem bound697 : ∀ f ∈ assignSearch step finish [10,11] [2,10] table697, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,10] [10] table697 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound698

theorem bound696 : ∀ f ∈ assignSearch step finish [9,10,11] [2,7,10] table696, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,7,10] [7] table696 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound697

theorem bound695 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,7,10] table695, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,7,10] [1] table695 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound696

theorem bound694 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,7,10,11] table694, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,7,10,11] [11] table694 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound695

theorem bound693 : ∀ f ∈ assignSearch step finish [] [] table693, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound692 : ∀ f ∈ assignSearch step finish [11] [1] table692, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table692 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound693

theorem bound691 : ∀ f ∈ assignSearch step finish [10,11] [1,11] table691, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,11] [11] table691 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound692

theorem bound690 : ∀ f ∈ assignSearch step finish [9,10,11] [1,8,11] table690, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,8,11] [8] table690 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound691

theorem bound689 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,8,11] table689, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,8,11] [2] table689 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound690

theorem bound688 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,8,10,11] table688, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,8,10,11] [10] table688 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound689

theorem bound687 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,7,8,10,11] table687, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,7,8,10,11] [7,8] table687 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound688
    · exact bound694

theorem bound686 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,7,8,10,11] table686, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,7,8,10,11] [0] table686 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound687

theorem bound685 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,7,8,10,11] table685, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,7,8,10,11] [3] table685 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound686

theorem bound684 : ∀ f ∈ assignSearch step finish [] [] table684, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound683 : ∀ f ∈ assignSearch step finish [11] [10] table683, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table683 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound684

theorem bound682 : ∀ f ∈ assignSearch step finish [10,11] [2,10] table682, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,10] [2] table682 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound683

theorem bound681 : ∀ f ∈ assignSearch step finish [9,10,11] [2,7,10] table681, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,7,10] [7] table681 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound682

theorem bound680 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,7,10,11] table680, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,7,10,11] [11] table680 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound681

theorem bound679 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,7,10,11] table679, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,7,10,11] [1] table679 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound680

theorem bound678 : ∀ f ∈ assignSearch step finish [] [] table678, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound677 : ∀ f ∈ assignSearch step finish [11] [11] table677, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table677 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound678

theorem bound676 : ∀ f ∈ assignSearch step finish [10,11] [1,11] table676, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,11] [1] table676 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound677

theorem bound675 : ∀ f ∈ assignSearch step finish [9,10,11] [1,8,11] table675, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,8,11] [8] table675 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound676

theorem bound674 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,8,10,11] table674, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,8,10,11] [10] table674 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound675

theorem bound673 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,8,10,11] table673, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,8,10,11] [2] table673 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound674

theorem bound672 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,7,8,10,11] table672, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,7,8,10,11] [7,8] table672 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound673
    · exact bound679
end C13.Enumeration.Canonical.Pair61_61
