package me.gabriel.seren
package lexer

import error.LexicalError
import struct.{Token, TokenKind}

class DefaultLexer extends Lexer {
  def lex(input: String): Either[LexicalError, List[Token]] = {
    val tokens = collection.mutable.ListBuffer(Token("", TokenKind.BOF))
    var position = 0

    while (position < input.length) {
      val currentChar = input(position)

      currentChar match {
        case ' ' | '\t' | '\n' => {
          position += 1
        }
        case '+' => {
          tokens += Token("+", TokenKind.Plus)
          position += 1
        }
        case '-' => {
          tokens += Token("-", TokenKind.Minus)
          position += 1
        }
        case '*' => {
          tokens += Token("*", TokenKind.Multiply)
          position += 1
        }
        case '/' => {
          tokens += Token("/", TokenKind.Divide)
          position += 1
        }
        case '(' => {
          tokens += Token("(", TokenKind.LeftParenthesis)
          position += 1
        }
        case ')' => {
          tokens += Token(")", TokenKind.RightParenthesis)
          position += 1
        }
        case '^' => {
          tokens += Token("^", TokenKind.Exponentiation)
          position += 1
        }
        case '"' => {
          val string = input.drop(position + 1).takeWhile(_ != '"')
          if (string.isEmpty) {
            return Left(LexicalError.UnterminatedString(position))
          }
          tokens += Token(string, TokenKind.String)
          position += string.length + 2
        }
        case _ if currentChar.isDigit => {
          val number = currentChar.toString + input.drop(position + 1).takeWhile(_.isDigit)
          tokens += Token(number, TokenKind.Number)
          position += number.length
        }
        case _ => {
          return Left(LexicalError.UnexpectedCharacterError(currentChar, position))
        }
      }
    }

    tokens += Token("", TokenKind.EOF)
    Right(tokens.toList)
  }
}
