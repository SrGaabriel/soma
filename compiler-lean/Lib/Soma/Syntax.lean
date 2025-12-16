-- Soma Compiler - Syntax Module
-- This module re-exports all syntax-related components

-- Foundation
import Soma.Syntax.Source
import Soma.Syntax.Diagnostic

-- Green/Red Trees (rust-analyzer style CST)
import Soma.Syntax.SyntaxKind
import Soma.Syntax.GreenTree
import Soma.Syntax.RedTree

-- Lexer
import Soma.Syntax.Lexer

-- AST (Abstract Syntax Tree)
import Soma.Syntax.Ast

-- Parser
import Soma.Syntax.Parser
import Soma.Syntax.Parse.Pattern
import Soma.Syntax.Parse.Type
import Soma.Syntax.Parse.Expr
import Soma.Syntax.Parse.Decl

-- CST → AST Lowering
import Soma.Syntax.Lower
