module Parser (parse) where

import Text.ParserCombinators.Parsec hiding (parse, try, Line, State)
import qualified Text.ParserCombinators.Parsec          as PP
import qualified Text.ParserCombinators.Parsec.Token    as P
import qualified Text.ParserCombinators.Parsec.Language as Language
import Text.ParserCombinators.Parsec.Expr 

import Datatypes

-- Parser für Ausdrücke des Kalküls
-- Entspricht ziemlich genau den simplen Beispielparsern für arithmetische Ausdrücke

lexer      = P.makeTokenParser (Language.haskellStyle { P.reservedOpNames = ["¬", "!", "∧", "^", "∨", "v", "⊃", "->", "≣", "<->"] })
whiteSpace = P.whiteSpace lexer
lexeme     = P.lexeme     lexer
parens     = P.parens     lexer
identifier = P.identifier lexer
reservedOp = P.reservedOp lexer

runLex p input = PP.parse (do whiteSpace
                              x <- p
                              eof
                              return x
                          ) ""  input

expr    = buildExpressionParser table term
          <?> "expression"
term    = parens expr 
          <|> propConst 
          <?> "expression or propositional constant"
table   = [ [prefix "¬" Neg, prefix "!" Neg]
          , [binary "∧" And, binary "^" And, binary "∨" Or, binary "v" Or]
          , [binary "⊃" If, binary "->" If, binary "≣" Iff, binary "<->" Iff]
          ]
propConst = do s <- identifier 
               return (Const s) 

binary  name fun = Infix (do{ reservedOp name; return fun }) AssocNone
prefix  name fun = Prefix (do{ reservedOp name; return fun })

--parse :: String -> Either Proposition
parse s = runLex expr s
