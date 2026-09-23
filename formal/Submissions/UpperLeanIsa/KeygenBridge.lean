import Submissions.UpperLeanIsa.Stages

-- TEMPORARY CI STUB (never submitted): lets Security.lean elaborate while the real bridge is fixed.
open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem E_run_keygen (g' : (PublicKey × Words) × Cache → ℝ≥0∞) :
    E (run keygen ∅) g' = ∑ ξ : Record, w * g' ((ξ.publicKey, ξ.1), ξ.cache) := by
  sorry

end OptimalOTS.LeanIsaBaseline
