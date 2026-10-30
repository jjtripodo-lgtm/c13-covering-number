import C13Enumeration.DegreeEightPilot.Data
namespace C13.Enumeration.DegreeEightPilot.Source38Center00
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def valuesA : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,1,1,2,2,1,1,1,1,1,1,0,0,1,3,1,2,2,1,1,1,1,1,1,0,0,1,1,3,2,2,1,1,1,1,1,1,0,0,2,2,2,5,3,2,2,4,1,1,1,0,0,2,2,2,3,5,2,2,2,3,1,1,0,0,1,1,1,2,2,4,2,2,1,3,1,0,0,1,1,1,2,2,2,4,2,1,1,3,0,0,1,1,1,4,2,2,2,4,1,1,1,0,0,1,1,1,1,3,1,1,1,3,1,1,0,0,1,1,1,1,1,3,1,1,1,3,1,0,0,1,1,1,1,1,1,3,1,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrixA (a b : Point) : Nat := valuesA.getD (13*a.val+b.val) 0
theorem matrixA_checked : ∀ a b, matrixA a b = coDegree (link link38 0) a b := by decide +kernel

def maps : List (Point → Point) := []
def step := starStep (link link38 0) (link link01 4) matrixA matrix
def finish := crossMapFinish link38 link01 hole 0 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 4 0
def table2 : Point → Point := put table1 5 1
def table3 : Point → Point := put table2 6 2
def table4 : Point → Point := put table3 7 3
def table5 : Point → Point := put table2 6 3
def table6 : Point → Point := put table5 7 2
def table7 : Point → Point := put table0 4 1
def table8 : Point → Point := put table7 5 0
def table9 : Point → Point := put table8 6 2
def table10 : Point → Point := put table9 7 3
def table11 : Point → Point := put table8 6 3
def table12 : Point → Point := put table11 7 2

theorem bound12 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [5,6,7,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [5,6,7,8,9,10,11] [] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound11 : ∀ f ∈ assignSearch step finish [7,8,1,2,3,9,10,11] [2,5,6,7,8,9,10,11] table11, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,1,2,3,9,10,11] [2,5,6,7,8,9,10,11] [2] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound12

theorem bound10 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [5,6,7,8,9,10,11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [5,6,7,8,9,10,11] [] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound9 : ∀ f ∈ assignSearch step finish [7,8,1,2,3,9,10,11] [3,5,6,7,8,9,10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,1,2,3,9,10,11] [3,5,6,7,8,9,10,11] [3] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [6,7,8,1,2,3,9,10,11] [2,3,5,6,7,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,1,2,3,9,10,11] [2,3,5,6,7,8,9,10,11] [2,3] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound9
    · exact bound11

theorem bound7 : ∀ f ∈ assignSearch step finish [5,6,7,8,1,2,3,9,10,11] [0,2,3,5,6,7,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,1,2,3,9,10,11] [0,2,3,5,6,7,8,9,10,11] [0] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [5,6,7,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [5,6,7,8,9,10,11] [] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound5 : ∀ f ∈ assignSearch step finish [7,8,1,2,3,9,10,11] [2,5,6,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,1,2,3,9,10,11] [2,5,6,7,8,9,10,11] [2] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [8,1,2,3,9,10,11] [5,6,7,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,9,10,11] [5,6,7,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ f ∈ assignSearch step finish [7,8,1,2,3,9,10,11] [3,5,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,1,2,3,9,10,11] [3,5,6,7,8,9,10,11] [3] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ f ∈ assignSearch step finish [6,7,8,1,2,3,9,10,11] [2,3,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,1,2,3,9,10,11] [2,3,5,6,7,8,9,10,11] [2,3] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound5

theorem bound1 : ∀ f ∈ assignSearch step finish [5,6,7,8,1,2,3,9,10,11] [1,2,3,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,1,2,3,9,10,11] [1,2,3,5,6,7,8,9,10,11] [1] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [4,5,6,7,8,1,2,3,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,8,1,2,3,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] [0,1] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound7

theorem complete_maps (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (0 : Point) = hole)
    (hs : transport e (link link38 0) = link link01 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link38 link01 hole 0 4 [4,5,6,7,8,1,2,3,9,10,11]
    (by decide +kernel) (by decide +kernel) matrixA matrix matrixA_checked matrix_checked maps bound0 e he hc hs

def pick : Fin maps.length → table.Index := fun i => Fin.elim0 (show Fin 0 from i)

theorem rows_checked : ∀ i : Fin maps.length,
    (codedDomain.pencil (table.row (pick i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes38 0 4 (fun x => maps.get i ((Equiv.refl Point) x))).toFinset := by
  decide +kernel

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (0 : Point) = hole)
    (hs : transport e (link link38 0) = link link01 4) :
    ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p (emitPencil link38 0 4 e) := by
  exact mapsRepresented_of_code_checks codedDomain table RawClass9.CatalogCodes.codes38
    link38 RawClass9.CatalogCodes.checked38 0 4 (Equiv.refl Point) maps pick rows_checked
    e (complete_maps e he hc hs)
end C13.Enumeration.DegreeEightPilot.Source38Center00
