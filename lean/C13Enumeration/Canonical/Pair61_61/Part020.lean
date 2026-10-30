import C13Enumeration.Canonical.Pair61_61.Part021
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound671 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,7,8,10,11] table671, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,7,8,10,11] [0] table671 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound672

theorem bound670 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,10,11] table670, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,8,10,11] [6] table670 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound671

theorem bound669 : ∀ f ∈ assignSearch step finish [] [] table669, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound668 : ∀ f ∈ assignSearch step finish [11] [1] table668, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table668 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound669

theorem bound667 : ∀ f ∈ assignSearch step finish [10,11] [1,11] table667, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,11] [11] table667 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound668

theorem bound666 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,11] table666, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,11] [0] table666 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound667

theorem bound665 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,6,11] table665, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,6,11] [6] table665 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound666

theorem bound664 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,6,11] table664, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,6,11] [3] table664 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound665

theorem bound663 : ∀ f ∈ assignSearch step finish [] [] table663, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound662 : ∀ f ∈ assignSearch step finish [11] [6] table662, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table662 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound663

theorem bound661 : ∀ f ∈ assignSearch step finish [10,11] [3,6] table661, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,6] [3] table661 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound662

theorem bound660 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,7] table660, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,7] [7] table660 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound661

theorem bound659 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,6,7] table659, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,6,7] [1] table659 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound660

theorem bound658 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,6,7,11] table658, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,6,7,11] [11] table658 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound659

theorem bound657 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,6,7,11] table657, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,6,7,11] [0,7] table657 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound658
    · exact bound664

theorem bound656 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,6,7,8,11] table656, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,6,7,8,11] [8] table656 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound657

theorem bound655 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,6,7,8,10,11] table655, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,6,7,8,10,11] [10] table655 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound656

theorem bound654 : ∀ f ∈ assignSearch step finish [] [] table654, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound653 : ∀ f ∈ assignSearch step finish [11] [2] table653, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table653 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound654

theorem bound652 : ∀ f ∈ assignSearch step finish [10,11] [2,10] table652, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,10] [10] table652 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound653

theorem bound651 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,10] table651, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,10] [0] table651 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound652

theorem bound650 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,6,10] table650, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,6,10] [6] table650 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound651

theorem bound649 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,6,10] table649, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,6,10] [3] table649 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound650

theorem bound648 : ∀ f ∈ assignSearch step finish [] [] table648, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound647 : ∀ f ∈ assignSearch step finish [11] [6] table647, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table647 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound648

theorem bound646 : ∀ f ∈ assignSearch step finish [10,11] [3,6] table646, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,6] [3] table646 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound647

theorem bound645 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,8] table645, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,8] [8] table645 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound646

theorem bound644 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,6,8] table644, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,6,8] [2] table644 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound645

theorem bound643 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,6,8,10] table643, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,6,8,10] [10] table643 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound644

theorem bound642 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,6,8,10] table642, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,6,8,10] [0,8] table642 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound643
    · exact bound649

theorem bound641 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,6,7,8,10] table641, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,6,7,8,10] [7] table641 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound642

theorem bound640 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,6,7,8,10,11] table640, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,6,7,8,10,11] [11] table640 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound641
end C13.Enumeration.Canonical.Pair61_61
