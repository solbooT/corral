# Corral Boogie 3.5.5 Migration Status

## Current Situation

**Errors: ~218** (down from 355 initially)

## Main Blocking Issues

### 1. **Immutable VCGenOptions** (Highest Priority) ⛔
- **Problem**: Cannot assign to read-only properties (InlineDepth, TimeLimit, etc.)
- **Files**: VerificationPasses.cs, CompilerPass.cs, BoogieVerify.cs
- **Root Cause**: Boogie 3.5.5 made options immutable
- **Solution Needed**: Create new VCGenOptions instances instead of modifying existing ones
- **Status**: Helper class created (`OptionsHelper.cs`) but needs Boogie 3.5.5 API knowledge to implement

### 2. **StratifiedInlining Internal Fields** ⛔
- **Problem**: Cannot access `prover`, `implName2StratifiedInliningInfo`, `program` (private/protected)
- **Files**: StratifiedInlining.cs, HoudiniLite.cs
- **Solution Needed**: Refactor to use public APIs or make fields accessible
- **Count**: ~50+ errors

### 3. **BoogieUtil.DoModSetAnalysis Missing** ⛔
- **Problem**: Method removed/moved in Boogie 3.5.5
- **Files**: Multiple (CBAPasses, CompilerPass, SdvUtils, VerificationPasses, Instrumentation, VariableSlice, Refinement)
- **Solution Needed**: Find replacement API or implement locally
- **Count**: ~10 errors

### 4. **API Signature Changes**
- ProverInterface.CreateProver() - needs more/different parameters
- ProverInterface.Check() - signature changed
- VerificationConditionGenerator constructor - changed
- Houdini constructor - needs Program parameter
- Various other constructors

## What Works ✅

- QKeyValue.FindBoolAttribute → BoogieApiHelpers wrapper
- CommandLineOptions.RecursionBound → placeholder (999)
- VCGen → VerificationConditionGenerator
- Most CommandLineOptions static → ExecutionEngineOptions.Options
- List extension methods fixed

## Next Steps (Priority Order)

1. **Research Boogie 3.5.5 VCGenOptions API**
   - How to create new instances with modified values?
   - Constructor? Builder? With methods?
   - This blocks ~50+ errors

2. **Fix StratifiedInlining architecture**
   - Either expose needed fields as protected/public
   - Or refactor to use existing public APIs
   - This blocks ~50+ errors

3. **Find DoModSetAnalysis replacement**
   - Check Boogie 3.5.5 for equivalent
   - Or copy old implementation to Corral
   - Blocks ~10 errors

4. **Fix remaining API signatures**
   - Update all constructor/method calls to match Boogie 3.5.5
   - Blocks ~100+ errors

## Temporary Workarounds Applied

- Commented problematic code with TODO markers
- Created placeholder helpers
- These allow identifying real issues but don't fix them

## Recommendations

### Short Term (Make it Compile)
1. Use reflection to bypass read-only options (HACK, not recommended for production)
2. Or: Document that options must be set at startup and cannot change dynamically
3. Stub out DoModSetAnalysis calls

### Long Term (Proper Fix)
1. Study Boogie 3.5.5 source code/documentation
2. Refactor Corral architecture to match new Boogie patterns
3. May need significant code changes in StratifiedInlining
4. Consider if some Corral features need to be deprecated

## Help Needed

To complete this migration, we need:
1. Access to Boogie 3.5.5 API documentation
2. Understanding of how to properly create/use VCGenOptions
3. Knowledge of ModSet analysis alternatives
4. Possibly Boogie developer input on architectural changes

