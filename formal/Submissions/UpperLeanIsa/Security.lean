import Submissions.UpperLeanIsa.Budget
import Submissions.UpperLeanIsa.KeygenBridge
import Submissions.UpperLeanIsa.StageA

/-!
# Strong unforgeability of the leanISA Winternitz candidate

For every adversary `A` whose experiment costs at most `B` compressions on every path,

```
probTrue (experiment scheme A) ≤ κ B = B / 2 ^ 128 < B / 2 ^ 127,
```

where the strict inequality uses `2 ≤ B` (the first chain query of key generation).

The proof: key generation is a uniform record (`E_run_keygen`); the first attacker stage is
coupled to a run in which only the exposed part of the keygen cache is present (`stageA_iub`);
records are regrouped by their public data before signing (`regroup`); each group is bounded by
`stageA_master`; the group weights sum to one (`sum_sumW_fiber₀`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

attribute [local irreducible] hashBits blockBits msgBits securityBits maxSignatureBits
attribute [local irreducible] keygenBudget signBudget verifyBudget
attribute [local irreducible] CostAtMost OracleAlgorithm.experiment rest rest₂ stB
attribute [local irreducible] keygen sign verify

local instance instDecEqRecordSecurity : DecidableEq Record := Classical.decEq Record

local instance instDecEqPublicDataSecurity : DecidableEq PublicData := Classical.decEq PublicData

variable (A : OracleAlgorithm.Adversary)

/-! ## Budget after key generation -/

/-- Every record is a possible outcome of key generation. -/
theorem mem_support_run_keygen (ξ : Record) :
    ((ξ.publicKey, ξ.1), ξ.cache) ∈ support (run keygen ∅) := by
  by_contra hns
  have h0 : E (run keygen ∅) (fun p => ind (p = ((ξ.publicKey, ξ.1), ξ.cache))) = 0 := by
    refine le_antisymm (expectedValue_le_of_support fun p hp => ?_) zero_le
    have hne : p ≠ ((ξ.publicKey, ξ.1), ξ.cache) := by
      intro he
      apply hns
      rw [← he]
      exact hp
    exact le_of_eq (ind_not hne)
  rw [E_run_keygen] at h0
  have hle : w * ind (((ξ.publicKey, ξ.1), ξ.cache) = ((ξ.publicKey, ξ.1), ξ.cache)) ≤
      ∑ ζ : Record, w * ind (((ζ.publicKey, ζ.1), ζ.cache) = ((ξ.publicKey, ξ.1), ξ.cache)) :=
    Finset.single_le_sum (f := fun ζ : Record =>
      w * ind (((ζ.publicKey, ζ.1), ζ.cache) = ((ξ.publicKey, ξ.1), ξ.cache)))
      (fun _ _ => zero_le) (Finset.mem_univ ξ)
  have h1 : ind (((ξ.publicKey, ξ.1), ξ.cache) = ((ξ.publicKey, ξ.1), ξ.cache)) = 1 :=
    ind_of rfl
  rw [h0, h1, mul_one] at hle
  exact w_ne_zero_stg (le_antisymm hle zero_le)

/-- The budget of the experiment is a budget of the continuation after key generation, at every
record. -/
theorem costAtMost_rest {B : ℕ} (h : CostAtMost (OracleAlgorithm.experiment scheme A) B) :
    ∀ ξ : Record, CostAtMost (rest A (ξ.publicKey, ξ.1)) B := by
  intro ξ
  rw [experiment_eq] at h
  exact costAtMost_bind_run_support keygen (rest A) h ∅ _ (mem_support_run_keygen ξ)

/-! ## Stage A: identical until a hidden keygen point is queried -/

theorem stageA_iub (ξ : Record) :
    E (run (rest A (ξ.publicKey, ξ.1)) ξ.cache) g ≤
      E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (fun p =>
        if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
          E (run (rest₂ A ξ.publicKey ξ.1 p.1)
            (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g) := by
  unfold rest
  rw [run_bind, E_bind, ← exposure_partition beforeSigning ξ]
  exact iub (A.choose ξ.publicKey) (hiddenCache beforeSigning ξ)
    (fun p => E (run (rest₂ A ξ.publicKey ξ.1 p.1) p.2) g) (fun _ => E_le_one _ g_le_one)
    (exposedCache beforeSigning ξ) (exposure_disjoint beforeSigning ξ)

/-- The experiment as a uniform average over records of the continuation after key
generation. -/
theorem E_run_experiment (g' : Bool × Cache → ℝ≥0∞) :
    E (run (OracleAlgorithm.experiment scheme A) ∅) g' =
      ∑ ξ : Record, w * E (run (rest A (ξ.publicKey, ξ.1)) ξ.cache) g' := by
  rw [experiment_eq, run_bind keygen (rest A) ∅, E_bind]
  exact E_run_keygen _

/-! ## Regrouping by public data before signing -/

theorem mem_fiber₀_sec (v : PublicData) (ξ : Record) :
    ξ ∈ fiber₀ v ↔ publicData beforeSigning ξ = v := by
  unfold fiber₀
  exact mem_publicFiber beforeSigning v ξ

theorem fiber₀_eq_filter_sec (v : PublicData) :
    (Finset.univ.filter fun ξ : Record => publicData beforeSigning ξ = v) = fiber₀ v := by
  ext ξ
  rw [Finset.mem_filter, mem_fiber₀_sec]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ ξ, h⟩⟩

/-- A representative of the records with public data `v` (any record if there is none). -/
def rep (v : PublicData) : Record :=
  @dite Record (∃ ξ, ξ ∈ fiber₀ v) (Classical.propDecidable _)
    (fun h => Classical.choose h) (fun _ => ((fun _ => 0), (fun _ => 0)))

theorem rep_mem {v : PublicData} (hv : v ∈ Finset.univ.image (publicData beforeSigning)) :
    rep v ∈ fiber₀ v := by
  have hex : ∃ ξ, ξ ∈ fiber₀ v := by
    obtain ⟨ξ, -, hξ⟩ := Finset.mem_image.1 hv
    exact ⟨ξ, (mem_fiber₀_sec v ξ).2 hξ⟩
  unfold rep
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem regroup (G : Record → (Message × A.State) × Cache → ℝ≥0∞) :
    ∑ ξ : Record, w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) =
      ∑ v ∈ Finset.univ.image (publicData beforeSigning),
        E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
          (fun p => ∑ ξ ∈ fiber₀ v, w * G ξ p) := by
  symm
  calc ∑ v ∈ Finset.univ.image (publicData beforeSigning),
        E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
          (fun p => ∑ ξ ∈ fiber₀ v, w * G ξ p)
      = ∑ v ∈ Finset.univ.image (publicData beforeSigning), ∑ ξ ∈ fiber₀ v,
          w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [E_weighted_sum]
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        have hd : publicData beforeSigning ξ = publicData beforeSigning (rep v) :=
          ((mem_fiber₀_sec v ξ).1 hξ).trans ((mem_fiber₀_sec v (rep v)).1 (rep_mem hv)).symm
        rw [publicKey_data_eq beforeSigning ξ (rep v) hd,
          exposedCache_data_eq beforeSigning ξ (rep v) hd]
    _ = ∑ v ∈ Finset.univ.image (publicData beforeSigning),
          ∑ ξ ∈ Finset.univ.filter (fun ξ : Record => publicData beforeSigning ξ = v),
            w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [fiber₀_eq_filter_sec]
    _ = ∑ ξ : Record, w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
          (t := Finset.univ.image (publicData beforeSigning)) (g := publicData beforeSigning)
          (fun ξ _ => Finset.mem_image_of_mem _ (Finset.mem_univ ξ)) _

theorem sum_sumW_fiber₀ :
    ∑ v ∈ Finset.univ.image (publicData beforeSigning), sumW (fiber₀ v) = 1 := by
  calc ∑ v ∈ Finset.univ.image (publicData beforeSigning), sumW (fiber₀ v)
      = ∑ v ∈ Finset.univ.image (publicData beforeSigning),
          ∑ _ξ ∈ Finset.univ.filter (fun ξ : Record => publicData beforeSigning ξ = v), w := by
        refine Finset.sum_congr rfl fun v _ => ?_
        unfold sumW
        rw [fiber₀_eq_filter_sec]
    _ = ∑ _ξ : Record, w :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
          (t := Finset.univ.image (publicData beforeSigning)) (g := publicData beforeSigning)
          (fun ξ _ => Finset.mem_image_of_mem _ (Finset.mem_univ ξ)) _
    _ = 1 := sum_w

/-! ## The bound -/

theorem main_bound {B : ℕ} (hB : CostAtMost (OracleAlgorithm.experiment scheme A) B) :
    probTrue (OracleAlgorithm.experiment scheme A) ≤ κ * B := by
  have hrest : ∀ ξ : Record,
      CostAtMost (A.choose ξ.publicKey >>= rest₂ A ξ.publicKey ξ.1) B := by
    intro ξ
    have h := costAtMost_rest A hB ξ
    unfold rest at h
    exact h
  rw [probTrue_eq_E_run, E_run_experiment]
  calc ∑ ξ : Record, w * E (run (rest A (ξ.publicKey, ξ.1)) ξ.cache) g
      ≤ ∑ ξ : Record, w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ))
          (fun p => if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
            E (run (rest₂ A ξ.publicKey ξ.1 p.1)
              (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (stageA_iub A ξ)
    _ = ∑ v ∈ Finset.univ.image (publicData beforeSigning),
          E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
            (fun p => ∑ ξ ∈ fiber₀ v, w *
              (if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
                E (run (rest₂ A ξ.publicKey ξ.1 p.1)
                  (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g)) :=
        regroup A (fun ξ p => if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
          E (run (rest₂ A ξ.publicKey ξ.1 p.1)
            (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g)
    _ = ∑ v ∈ Finset.univ.image (publicData beforeSigning),
          E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
            (fun p => FA A v p.1 p.2) := rfl
    _ ≤ ∑ v ∈ Finset.univ.image (publicData beforeSigning), κ * sumW (fiber₀ v) * B :=
        Finset.sum_le_sum fun v hv =>
          stageA_master A v (rep v) (rep_mem hv) B (fun ξ _ => hrest ξ)
    _ = κ * B := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_sumW_fiber₀, mul_one]

theorem κ_mul_lt {B : ℕ} (h2 : 2 ≤ B) : κ * (B : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hsec : securityBits = 127 := by
    unfold securityBits
    rfl
  rw [κ_eq, hsec, ENNReal.div_eq_inv_mul]
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    have hB : B ≠ 0 := by omega
    exact_mod_cast hB
  have hlt : (2 : ℝ≥0∞) ^ 127 < 2 ^ 128 := by
    first
    | exact_mod_cast (show (2 : ℕ) ^ 127 < 2 ^ 128 by norm_num)
    | (have h := ENNReal.mul_lt_mul_right (a := (2 : ℝ≥0∞) ^ 127) (b := 1) (c := 2)
          (by simp) (by simp) ENNReal.one_lt_two
       rwa [mul_one, ← pow_succ] at h)
  exact ENNReal.mul_lt_mul_left hB0 (ENNReal.natCast_ne_top B) (ENNReal.inv_lt_inv.2 hlt)

/-- **Strong unforgeability** of the leanISA Winternitz candidate. -/
theorem secure : scheme.Secure := by
  intro A B hB
  exact (main_bound A hB).trans_lt (κ_mul_lt (two_le_of_costAtMost_experiment A hB))

end OptimalOTS.LeanIsaBaseline

end
