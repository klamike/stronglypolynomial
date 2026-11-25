# Width change `paperWidth N = (7*N^2+8)*N+1`: repair report

Build directory: `/Users/mike/Git/stronglypolynomial/upstream-build` (Lean v4.34.1, pins unchanged).

## Result

- All 769 modules listed in `closure-full.txt` build (the list has 768 newline-terminated
  lines plus a last line `OAI.Optimization.LinearProgramming.Specification` without a trailing
  newline; that source file was missing when the first pass started and appeared in the build
  directory during it -- not created by this repair -- so two passes were needed).
- All 31 upstream files mentioning `paperWidth` build (table below).
- Beyond the closure: the closure is a *downward* import closure, so it does not contain
  modules that import the changed files without naming `paperWidth`. Upstream has 23 such
  reverse dependents of `AdaptiveRequests`/`BitBudget` outside the closure. The four that
  name width-dependent quantities or import a changed file directly, plus the final theorem
  module `ServiceTheorem`, were added together with their 16 missing imports (21 pristine
  files copied from `src/lean`, listed in `extra-modules.txt`) and build:
  `Compression.ServiceTheorem` (Theorem 1.4, `onlineMinorCompression`),
  `Compression.NumericMinorROM`, `Geometry.DimensionBounds`, `BitRAM.AddressHorner`,
  `BitRAM.NativePriceEpoch`. `NumericMinorROM` needed one repair (it used the old closed form
  by `change` without naming `paperWidth`), so the predicted closure was not sufficient.
- No `sorry`, `axiom`, `native_decide`; no theorem deleted; no warnings in any log.

Final build command and summary line (a no-op re-run confirming every trace is current;
log `build-final.log`):

    lake build OAI.WidthAll OAI.WidthExtra
    Build completed successfully (10021 jobs).

`OAI/WidthAll.lean` imports the 769 closure modules, `OAI/WidthExtra.lean` the five downstream
targets. Both are aggregates only and are not part of `width.patch`.
Logs: `build-full.pass1.log` (first pass, stopped only by the missing `Specification.lean`),
`build-full.log` (second pass, 77 remaining modules), `build-extra.log`, `build-final.log`.

## Not verified (outside the build directory)

18 further upstream reverse dependents were not built; they need 762 more modules:
`Feasibility`, `Optimization`, `PrimalDual.CallCount`, `Geometry.{SealedSignRecovery,
SubspaceDecision,WireEpoch}`, `NormalSubspace.{Joined,Main,Unconditional}`,
`Recovery.{EpochHandles,EpochSetup,PhysicalEpoch,PhysicalRestart,PriceTransfer,SubspaceAccess,
SubspaceBounds,SubspaceKernel,WireGeometry}` (all under `OAI.Optimization.LinearProgramming`).
None of them names `paperWidth`, `onlineMinorBit*`, `manuscriptProxyFuel`, `RoundingBudgets`,
a literal `(·+1)^6`, or imports a changed file directly, so breakage is unlikely, but
`NumericMinorROM` shows that such a prediction can be wrong.

## Edits

Pre-applied by `apply-width.py` (not by this repair): the definition of `paperWidth`
(AdaptiveRequests), `onlineMinorBitFormula` and the statement of
`fiber_manuscript_value_height` (BitBudget), the proof of the width bound (MinorAssignments).

Repairs (15 files, 20 declarations: 2 new lemmas, 1 private definition body, 17 proofs).
Every proof repair replaces a use of the definitional equality `paperWidth N = (N+1)^6`
(`change`, `unfold ...; omega`, `simp [paperWidth]`, `show ... from`, or implicit unification)
by the new lemma `paperWidth_le_pow`. No theorem statement was changed by the repairs.
Most sites were repaired from inspection before the first pass reached them, so only the
`NumericMinorROM` failure was observed in a log; the others fail necessarily, because the
replaced step asks for a definitional equality that no longer holds.

| File (Compression/) | Declaration | Change |
|---|---|---|
| AdaptiveRequests | `paperWidth_le_pow` (new) | `paperWidth N ≤ (N+1)^6`, by expansion and `omega` |
| ProxyFuelQueries | `fiberProjectionBudget_mono_width` (new, private) | the budget is a sum over `range (width+1)`, monotone in the width |
| ProxyFuelQueries | `manuscript_commit_fuel` | width hypothesis via `paperWidth_le_pow`; the budget at the new width is bounded by the budget at `(N+1)^6` (monotonicity, `Nat.size_le_size`) before applying `manuscript_commit_inputWidth` |
| ProxyFuelQueries | `manuscript_request_fuel`, `manuscript_grid_query_l1` | `unfold paperWidth at hj` replaced by `hj.trans (paperWidth_le_pow N)` |
| RoundingBudgets | `width` (private def) | the bit-stack procedure now computes `(7*n^2+8)*n+1` (`uadd (umul (uadd (umul 7 (upow n 2)) 8) n) 1`) instead of `upow (n+1) 6`; its type `U e (fun x => paperWidth (a x))` is unchanged and forces this |
| RoundingBudgets | `run_under_width` | `change g ≤ (n+1)^6` replaced by the lemma; `widthInputBound`/`budgetBound` keep `(X+1)^6` |
| InnerParameterSize | `parameterSizes` | `hg` weakened to `(N+1)^6` once; `paperWidth` removed from three `simp` sets |
| NumericROMBounds | `arity_le`, `window_le` | lemma instead of `simpa [paperWidth]` / `change` |
| ProxyNumericComplexity | `numericProxyCacheSteps_le` | `hw : g ≤ (N+1)^6` now from the lemma |
| RequestGraphInputSize | `paper_graph_input_length_for` | same |
| ProxyHomogeneousFuel | `manuscript_homogeneous_grid_fuel` | `change d ≤ w+1 at hd` replaced by the lemma |
| SignWireInitialResidentBound | `initialResidentClock_le_polynomial` | `show g≤(N+1)^6 from width` replaced by the lemma |
| SignWireNumericFootprint | `numericCacheSeed_footprint` | same |
| ServiceParameters | `live_le` | `change` replaced by the lemma |
| ServiceResources | `time_le` | same |
| ServiceBudget | `magnitudeInput_le` | lemma inserted before `Nat.pow_le_pow_left` |
| ServiceImplementation | `assembly` (private) | `hg6 : J.card ≤ (n+1)^6` passed to `inspectHeight_bound` and `inspectAndGather_native` |
| NumericMinorROM (extension) | `NumericROM.numericalPrefix_correct` | `change g≤(n+1)^6 at width` replaced by the lemma |

`width.patch` (17 files, 25 hunks) contains these repairs and the three pre-applied files; it
was checked by applying it with `patch -p0` to pristine copies and comparing byte for byte.

## Old-width over-estimates deliberately kept

Still stated with `(N+1)^6` and still valid, because the new width is smaller:
`manuscriptProxyFuelFormula` and `manuscript_*_inputWidth`/`manuscript_rounding_fuel`
(ProxyFuel; note this fuel is the cutoff exponent the algorithm actually uses, not only a
bound), `cacheInputPolynomial`/`numericCacheClockPolynomial` (ProxyNumericComplexity),
`paperInputFormula` (RequestGraphInputSize), `basePolynomial` (InnerParameterSize),
`widthInputBound` (RoundingBudgets), `cacheSeedPolynomial` (SignWireNumericFootprint),
`initialResidentClockPolynomial` (SignWireInitialResidentBound), `arity`/`window`
(NumericROMBounds), `setupTime` (NumericMinorROM), `timePolynomial`/`heightPolynomial`
(ServiceResources), `live_le` (ServiceParameters), the hypotheses `J.card ≤ (n+1)^6` of
ServiceInspect{Bounds,Native,Gather,Program}, and the counting/offline cutoffs in Bound,
MinorIndex, Offline, OfflineBudget. `onlineMinorBitPolynomial` is used downstream only through
`eval` and a generic `natDegree`, so its lower degree needed no repair.

## The 31 `paperWidth` files

All build. Edited: AdaptiveRequests, InnerParameterSize, MinorAssignments, NumericROMBounds,
ProxyFuelQueries, ProxyHomogeneousFuel, ProxyNumericComplexity, RequestGraphInputSize,
RoundingBudgets, ServiceBudget, ServiceImplementation, ServiceParameters, ServiceResources,
SignWireInitialResidentBound, SignWireNumericFootprint.
Unchanged: InnerClock, InnerControl, InnerNative, InnerNativeSemantics, InnerNativeWords,
InnerRAMAdapter, MinorNative, NativeCache, NumericROMCore, NumericROMLogic, NumericROMScatter,
NumericROMSetup, RequestGraphPaper, ServiceDecision, ServiceNumericSpec, ServicePrepare.

## Modules left failing

None.

## Axioms

`lake env lean WidthAxioms.lean` (output saved in `width-axioms.out`):

```
def OAI.Optimization.LinearProgramming.Compression.paperWidth : ℕ → ℕ :=
fun N => (7 * N ^ 2 + 8) * N + 1
paperWidth_le_pow : ∀ (N : ℕ), paperWidth N ≤ (N + 1) ^ 6
'OAI.Optimization.LinearProgramming.Compression.minor_transcript_guarantees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Compression.minorProxy_independent_bound_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Compression.NumericROM.solver_of_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Compression.onlineMinorLogCompression_of_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Compression.numericMinorROM_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Compression.onlineMinorCompression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
onlineMinorCompression : OAI.Optimization.LinearProgramming.OracleSpec.OnlineMinorLogCompression
RoundingBudgets.run_under_width : ∀ (n g : ℕ),
  g ≤ paperWidth n →
    ∃ c ≤ Polynomial.eval n RoundingBudgets.budgetBound,
      OAI.ExactQuantumFactoring.BitStackProgram.Runs RoundingBudgets.both.program
          (OAI.ExactQuantumFactoring.BitStackProgram.singletonStore RoundingBudgets.both.input
            (RoundingBudgets.inputsCode (n, g)))
          (OAI.ExactQuantumFactoring.BitStackProgram.singletonStore RoundingBudgets.both.output
            (OAI.ExactQuantumFactoring.BitStackProgram.prodCode Nat.bits Nat.bits (RoundingBudgets.values n g)))
          c ∧
        (RoundingBudgets.values n g).1.bits.length + (RoundingBudgets.values n g).2.bits.length ≤
          Polynomial.eval n RoundingBudgets.budgetBound
```

## Modules added beyond the closure (`extra-modules.txt`)

```
OAI.Optimization.LinearProgramming.BitRAM.AddressHorner
OAI.Optimization.LinearProgramming.BitRAM.Boot
OAI.Optimization.LinearProgramming.BitRAM.ConfiguredEntry
OAI.Optimization.LinearProgramming.BitRAM.NativeInstall
OAI.Optimization.LinearProgramming.BitRAM.NativeMetadataEffect
OAI.Optimization.LinearProgramming.BitRAM.NativePriceEpoch
OAI.Optimization.LinearProgramming.BitRAM.NativePriceFields
OAI.Optimization.LinearProgramming.BitRAM.NativePriceRange
OAI.Optimization.LinearProgramming.BitRAM.ReceiveInput
OAI.Optimization.LinearProgramming.Compression.InnerNativeInput
OAI.Optimization.LinearProgramming.Compression.MetadataDivide
OAI.Optimization.LinearProgramming.Compression.MetadataFinish
OAI.Optimization.LinearProgramming.Compression.MetadataInput
OAI.Optimization.LinearProgramming.Compression.MetadataNat
OAI.Optimization.LinearProgramming.Compression.MetadataPacket
OAI.Optimization.LinearProgramming.Compression.MetadataRepeat
OAI.Optimization.LinearProgramming.Compression.MetadataStart
OAI.Optimization.LinearProgramming.Compression.NumericMinorROM
OAI.Optimization.LinearProgramming.Compression.ServiceTheorem
OAI.Optimization.LinearProgramming.Contraction.DyadicRange
OAI.Optimization.LinearProgramming.Geometry.DimensionBounds
```
