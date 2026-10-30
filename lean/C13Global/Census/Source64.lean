import C13Global.Relative.Source64
import C13Global.Bindings.Source64
namespace C13.Global.Source64
open Finset C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_foursets (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link64 Q :=
  Relative.Source64.all_foursets alphabet_complete Q hQ
end C13.Global.Source64
