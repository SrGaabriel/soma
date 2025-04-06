module Logging.Reporting where

import Lexing.Lexer (Token (..))

data ReportingMethod
    = TokenReporting Token
