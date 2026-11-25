/-
The two premises `HeckeContinuation` and `FunctionalEquation5` of
`elliotglazer/diophantine-z-q`, proved from this library.

Not part of the `HeckeCM` library. To check it: build `HeckeCM` with Lean 4.35.0
(see `README.md` in this folder), add that repository as a Lake dependency and
run `lake env lean` on this file.
-/
import ZInQKernel.Hypotheses.CR3Literature
import HeckeCM.Bridge
import HeckeCM.FunctionalEqStrip

namespace ZInQ.Contrib

theorem heckeContinuation : ZInQ.Literature.HeckeContinuation :=
  fun _ hd => CMPoints.entire_lseries_curveD_of_ne_zero hd

theorem functionalEquation5 : ZInQ.Literature.FunctionalEquation5 := by
  intro d h5 hsq F hF s h0 h2
  have h := CMPoints.functional_equation_strip_five h5 hsq F hF s h0 h2
  simpa [ZInQ.Literature.completedL] using h

end ZInQ.Contrib

#check (ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation)
#check (ZInQ.Contrib.functionalEquation5 : ZInQ.Literature.FunctionalEquation5)
#print axioms ZInQ.Contrib.heckeContinuation
#print axioms ZInQ.Contrib.functionalEquation5
