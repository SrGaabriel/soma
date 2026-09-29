module Soma.Syntax.Kind where

import Maple.Green (RawKind)

tEof, tNumber, tStar, tUnknown :: RawKind
tEof = 0
tNumber = 1
tStar = 2
tUnknown = 3
