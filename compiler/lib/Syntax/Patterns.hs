{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Patterns (
    PatternPhase (..),

    Pattern (..),
    ParsedPattern,
    ResolvedPattern,

    Literal (..),

    patternSpan,
) where

import Lexing.Position (Span)
import Project.Name (Name)

-- | Literal values in patterns
data Literal
    = LitInt Int
    | LitString String
    | LitBool Bool
    deriving (Show, Eq, Ord)

-- | Pattern phases - before and after name resolution
data PatternPhase = Parsed | Resolved

-- | Type family mapping phase to the name type used
type family PatternName (p :: PatternPhase) where
    PatternName 'Parsed = String
    PatternName 'Resolved = Name

-- | Pattern type parameterized by phase
data Pattern (p :: PatternPhase)
    = PVar (PatternName p) Span
    | PWildcard Span
    | PLit Literal Span
    | PConstructor (PatternName p) [Pattern p] Span
    | PTuple [Pattern p] Span
    | PArray [Pattern p] Span
    | PAs (PatternName p) (Pattern p) Span

-- | Type aliases for convenience
type ParsedPattern = Pattern 'Parsed
type ResolvedPattern = Pattern 'Resolved

-- Deriving instances for ParsedPattern (String-based)
deriving instance Show ParsedPattern
deriving instance Eq ParsedPattern
deriving instance Ord ParsedPattern

-- Deriving instances for ResolvedPattern (Name-based)
deriving instance Show ResolvedPattern
deriving instance Eq ResolvedPattern
deriving instance Ord ResolvedPattern

-- | Get the span from any pattern
patternSpan :: Pattern p -> Span
patternSpan (PVar _ s) = s
patternSpan (PWildcard s) = s
patternSpan (PLit _ s) = s
patternSpan (PConstructor _ _ s) = s
patternSpan (PTuple _ s) = s
patternSpan (PArray _ s) = s
patternSpan (PAs _ _ s) = s
