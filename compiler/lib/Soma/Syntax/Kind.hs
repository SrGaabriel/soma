module Soma.Syntax.Kind where

import Maple.Green (RawKind)

tRoot, tEof, tNumber, tStar, tUnknown :: RawKind
tRoot = -1
tEof = 0
tNumber = 1
tStar = 2
tUnknown = 3
