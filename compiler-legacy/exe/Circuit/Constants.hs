{- | Constants for Circuit IR and Interaction Net runtime.

This module defines named constants for magic numbers used throughout
the Circuit IR pipeline and LLVM code generation. Using named constants
instead of magic numbers improves code readability and maintainability.
-}
module Circuit.Constants where

-- ============================================================================
-- Node Tag Constants (stored in heap objects)
-- ============================================================================

-- | Tag for closure nodes (stored in first byte of heap object)
nodeTagClosure :: Int
nodeTagClosure = 1

-- | Base tag for SUP nodes (values 128-131 indicate SUP with different states)
supTagBase :: Int
supTagBase = 128

-- | SUP state: not yet accessed
supTagFresh :: Int
supTagFresh = 128

-- | SUP state: proj0 accessed first
supTagProj0 :: Int
supTagProj0 = 129

-- | SUP state: proj1 accessed first
supTagProj1 :: Int
supTagProj1 = 130

-- | SUP state: both projections accessed
supTagBoth :: Int
supTagBoth = 131

-- ============================================================================
-- Memory Layout Constants
-- ============================================================================

-- | Size of SUP node in bytes (aligned)
supNodeSize :: Int
supNodeSize = 40

-- | Size of closure header in bytes (tag, arity, env_size, padding, func_ptr)
closureHeaderSize :: Int
closureHeaderSize = 16

-- | Size of each environment slot in bytes
envSlotSize :: Int
envSlotSize = 8

-- ============================================================================
-- Memory Pool Constants
-- ============================================================================

-- | Size of each memory pool block in bytes
poolBlockSize :: Int
poolBlockSize = 64 * 1024 -- 64KB

-- | Size class for small closures (0-3 env slots)
poolClosureSmall :: Int
poolClosureSmall = 48

-- | Size class for medium closures (4-11 env slots)
poolClosureMedium :: Int
poolClosureMedium = 112

-- ============================================================================
-- Parallel Runtime Constants
-- ============================================================================

-- | Minimum estimated work to consider parallel reduction
parallelWorkThreshold :: Int
parallelWorkThreshold = 200

-- | Maximum number of worker threads
maxParallelWorkers :: Int
maxParallelWorkers = 64

-- | Per-worker task queue capacity
taskQueueSize :: Int
taskQueueSize = 4096

-- | Maximum pending tasks before saturation
maxPendingTasks :: Int
maxPendingTasks = 1024

-- ============================================================================
-- Tagged Pointer Constants
-- ============================================================================

-- | Number of low bits used for type tags
tagBits :: Int
tagBits = 3

-- | Mask for extracting tag bits
tagMask :: Int
tagMask = 0x7

-- | Tag value for heap pointers
tagPtr :: Int
tagPtr = 0

-- | Tag value for small integers
tagInt :: Int
tagInt = 1

-- | Tag value for booleans/unit
tagBool :: Int
tagBool = 2

-- | Tag value for characters
tagChar :: Int
tagChar = 3

-- ============================================================================
-- GEP Index Constants (for LLVM struct access)
-- ============================================================================

-- | SUP node field indices
supFieldTag, supFieldLabel, supFieldValue, supFieldProj0, supFieldProj1 :: Int
supFieldTag = 0
supFieldLabel = 1
supFieldValue = 2
supFieldProj0 = 3
supFieldProj1 = 4

-- | Closure header field indices
closureFieldTag, closureFieldArity, closureFieldEnvSize, closureFieldFuncPtr :: Int
closureFieldTag = 0
closureFieldArity = 1
closureFieldEnvSize = 2
closureFieldFuncPtr = 3
