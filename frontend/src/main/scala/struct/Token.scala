package me.gabriel.seren.frontend
package struct

case class Token(value: String, kind: TokenKind)

enum TokenKind:
  case BOF
  case NumberLiteral
  case Plus
  case Minus
  case StringLiteral
  case Let
  case SemiColon
  case Function
  case Identifier
  case Return
  case Multiply
  case Divide
  case Comma
  case Exponentiation
  case LeftBrace
  case TypeDeclaration
  case VoidType
  case StringType
  case Int8Type
  case Int16Type
  case Int32Type
  case Int64Type
  case UInt8Type
  case UInt16Type
  case UInt32Type
  case UInt64Type
  case Float32Type
  case Float64Type
  case RightBrace
  case LeftParenthesis
  case RightParenthesis
  case EOF
