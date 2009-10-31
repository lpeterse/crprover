module Main where

import List
import Maybe
import Codec.Binary.UTF8.String 
import Data.Char

import System.Console.Readline
import System.Exit

import Text.ParserCombinators.Parsec hiding (Line)
import qualified Text.ParserCombinators.Parsec.Token as P
import qualified Text.ParserCombinators.Parsec.Language as Language
import Text.ParserCombinators.Parsec.Expr

license = 
    "------------------------------------------------------------------------------\n"
  ++" \"THE BEER-WARE LICENSE\" (Revision 42):                                     \n"
  ++" <lpeterse@uos.de> wrote this file. As long as you retain this notice you     \n"
  ++" can do whatever you want with this stuff. If we meet some day, and you think \n"
  ++" this stuff is worth it, you can buy me a beer in return. Lars Petersen       \n"
  ++"------------------------------------------------------------------------------\n"

manual =  "\nBeweiser für die Aussagenlogik im CR-Kalkül\n"
        ++"===========================================\n\n"
        ++"Befehle:\n"
        ++"  ls       - listet den Annahmenspeicher\n"
        ++"  clear    - leert den Annahmenspeicher\n"
        ++"  A [expr] - fügt dem Annahmenspeicher eine weitere Aussage hinzu\n"
        ++"  [expr]   - beweise Aussage\n\n"
        ++"  demo     - zeigt die Beweise einiger ausgewählter Sätze\n"
        ++"  help     - zeigt diese Hilfe\n"
        ++"  license  - zeigt Lizenz und Autor\n"
        ++"  exit     - beendet das Programm\n\n"
        ++"Syntax:\n"
        ++"  Das Programm unterstützt die Verwendung von Unicodezeichen. Jedoch\n"
        ++"  gibt es für jedes Zeichen auch eine ASCII-Alternative.\n"
        ++"                (ASCII)  (Unicode)\n"
        ++"  Negation:      !       ¬ \n"
        ++"  Conjunction:   ^       ∧ (u+2227)\n"
        ++"  Disjunction:   v       ∨ (u+2228)\n"
        ++"  Conditional:   ->      ⊃ (u+2283)\n"
        ++"  Biconditional: <->     ≣ (u+2263)\n\n"
        ++"  Die Operatoren sind nach Bindungsstärke geordnet. Die Verwendung von\n"
        ++"  Klammern ist zulässig. Die Operatoren sind darüber hinaus nicht assoziativ.\n\n"
        ++"Sonstiges:\n"
        ++"  Fragen und Verbesserungsvorschläge bitte an info@lars-petersen.net.\n"

-------------------------------------------------------------------------------------------------------------------------------
-- Parser für Ausdrücke des Kalküls
-- Entspricht ziemlich genau den simplen Beispielparsern für arithmetische Ausdrücke

lexer = P.makeTokenParser (Language.haskellStyle { P.reservedOpNames = ["¬", "!", "∧", "^", "∨", "v", "⊃", "->", "≣", "<->"] })
whiteSpace = P.whiteSpace lexer
lexeme     = P.lexeme     lexer
parens     = P.parens     lexer
identifier = P.identifier lexer
reservedOp = P.reservedOp lexer

runLex p input = parse (do whiteSpace
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

-------------------------------------------------------------------------------------------------------------------------------
-- Userinterface und Hauptschleife
main = (putUtf8Ln manual) >> readEvalPrintLoop []

readEvalPrintLoop :: [Proof] -> IO ()
readEvalPrintLoop ps = do
  maybeLine <- readline ">> "
  case maybeLine of 
       Nothing     -> exitWith (ExitSuccess) -- EOF / control-d
       Just "exit" -> exitWith (ExitSuccess) 
       Just "clear"-> (addHistory "clear")>> readEvalPrintLoop []
       Just "ls"   -> (addHistory "ls")   >> (putStr $ unlines $ map (encodeString.show) $ map fromProof ps) >> (readEvalPrintLoop ps)
       Just "demo" -> (addHistory "demo") >> demo >> (readEvalPrintLoop ps)
       Just "help" -> (addHistory "help") >> (putUtf8Ln manual) >> (readEvalPrintLoop ps)
       Just "license" -> (addHistory "license") >> (putUtf8Ln license) >> (readEvalPrintLoop ps)
       Just line -> do addHistory line
                       case line of
                        'A':' ':line' -> case runLex expr (decodeString line') of
                                           Left err -> do{ putStr "parse error at "; print err}
                                           Right x  -> readEvalPrintLoop (ps `union` [A x])
                        _             -> case runLex expr (decodeString line) of
                                           Left err -> do{ putStr "parse error at "; print err}
                                           Right x  -> catch (prove x ps) (const $ readEvalPrintLoop ps) 
                       readEvalPrintLoop ps

--einige String-Formatierungsfunktionen
putUtf8Ln   = putStrLn . encodeString
underline x = x ++ '\n':( map (const '-') x)

-------------------------------------------------------------------------------------------------------------------------------
-- Demobeweise. Dies stellt gleichzeitig einen Unit-Test dar. Wenn diese nicht beweisbar sind, stimmt was nicht.
demo = do
         prove (If (Const "p") (Const "p")) [] 
--     Teste Reductio Ad Absurdum
         prove (Neg (Const "p")) [A (If (Const "p") (Neg (Const "q"))), A (Const "q")] 
--     Teste OrElimination
         prove (Const "p") [A (Neg (Const "q")), A (Or (Const "p") (Const "q"))]
         prove (Const "p") [A (Neg (Const "q")), A (Or (Const "q") (Const "p"))]
--     Teste AndIntroduction
         prove (And (Const "p") (Const "q")) [A (Const "p"), A (Const "q")]
--     Teste AndElimination
         prove (Const "p") [A (And (Const "p") (Const "q"))]
         prove (Const "q") [A (And (Const "p") (Const "q"))]
         prove (Const "q") [A (And (And (Const "q") (Const "p")) (Const "r"))]
--     Kompliziertere Sätze aus dem Skript von Achim Stephan und Sven Walter
         prove (If (Or (Const "r") (Neg (Const "q"))) (If (Const "p") (Const "r"))) [A (If (Const "p") (Const "q"))]
         prove (And (And (Const "r1") (Const "r")) (Neg (Const "p1"))) [A (If (Neg (Const "p")) (And (Const "q") (Const "r"))), A (If (Or (Neg (Const "p")) (Const "q1")) (Neg (Const "p1"))), A (And (Const "r1") (Neg (Const "p")))]
         prove (If (And (Const "p") (Const "q")) (Const "r")) [A (If (Const "p") (If (Const "q") (Const "r")))]
         prove (If (If (Const "p") (Const "q")) (If (If (Const "p") (Neg (Const "q"))) (Neg (Const "p")))) []


-------------------------------------------------------------------------------------------------------------------------------
-- Beweisfunktionen: Iterative Vertiefung mit und ohne Begrenzung. Aktion innerhalb der IO-Monade
prove p as = do putUtf8Ln $ underline ("Beweis von "++(init $ tail $ show (map fromProof as))++" ⊦ "++(show p)++":")
                prove'' 7 p as

prove'        :: Proposition -> [Proof] -> IO ()
prove' p as    = putUtf8Ln $ unlines $ map show $ proof2Lines $ idsProve' p as

prove'' 0 p as = putUtf8Ln "Beweis nicht möglich. Aus Sicherheitsgründen ist die Beweistiefe auf diesem System begrenzt.\n"
prove'' n p as | (idsProve n p as ) == Unprovable = prove'' (n-1) p as
               | otherwise        = putUtf8Ln $ unlines $ map show $ proof2Lines $ idsProve n p as


-------------------------------------------------------------------------------------------------------------------------------
-- Datentypen

-- Aussage mit den Junktoren "und", "oder", "dann", "gdw", "nicht"
data Proposition = Const { constant:: String }                                  -- propositionale Konstante
                 | And   { fstConj :: Proposition, sndConj :: Proposition }
                 | Or    { fstDisj :: Proposition, sndDisj :: Proposition } 
                 | If    { premise :: Proposition, consequence :: Proposition } -- Implikation
                 | Iff   { first   :: Proposition, second :: Proposition }      -- logische Äquivalenz
                 | Neg   { neg     :: Proposition }                             -- Negation
                   deriving (Eq) -- Vergleich bezieht sich auf Syntax

-- Funktionen zum Testen auf die verschiedenen Konstruktoren
isConst (Const _) = True
isConst _         = False
isAnd   (And _ _) = True
isAnd   _         = False
isOr    (Or  _ _) = True
isOr    _         = False
isIf    (If  _ _) = True
isIf    _         = False
isIff   (Iff _ _) = True
isIff   _         = False
isNeg   (Neg _)   = True
isNeg   _         = False

-- Instanz der Show-Klasse. Verwendung von Unicode-Zeichen.
instance Show Proposition where
  show (Const x) = x
  show (And x y) = "(" ++ (show x) ++ " ∧ "   ++ (show y) ++ ")"
  show (Or  x y) = "(" ++ (show x) ++ " ∨ "   ++ (show y) ++ ")"
  show (If  x y) = "(" ++ (show x) ++ " ⊃ "  ++ (show y) ++ ")"
  show (Iff x y) = "(" ++ (show x) ++ " ≣ " ++ (show y) ++ ")"
  show (Neg x)   = "¬" ++ (show x)

-- Datentyp, mit dem ein Beweis dargestellt werden kann. Ein Beweis ist,
-- wie unschwer zu erkennen, ein Baum. Der Datentyp macht keine expliziten
-- Angaben über die Annahmen, von denen das Ergebnis abhängig ist. Dies
-- bedarf einer externen Interpretation.
data Proof        = Unprovable
                  | A        Proposition
                  | IfInt    Proof       Proof 
                  | IfElim   Proof       Proof
                  | IffInt   Proof       Proof
                  | IffElim1 Proof
                  | IffElim2 Proof
                  | OrInt1   Proof       Proof
                  | OrInt2   Proof       Proof
                  | OrElim1  Proof       Proof
                  | OrElim2  Proof       Proof
                  | AndInt   Proof       Proof
                  | AndElim1 Proof  
                  | AndElim2 Proof 
                  | RAA      Proof       Proof       Proof
                  deriving (Eq, Show)

-- Wandelt einen Beweis wieder in eine Aussage um. Es geht hierbei natürlich
-- Information verloren darüber, wie diese Aussage entstanden ist.
fromProof                 :: Proof -> Proposition
fromProof Unprovable       = Const "Unprovable"
fromProof (A        a)     = a
fromProof (IfInt    a b)   = If (fromProof a) (fromProof b)
fromProof (IfElim   _ b)   = consequence (fromProof b)
fromProof (IffInt   a b)   = Iff (premise (fromProof a)) (consequence (fromProof a))
fromProof (IffElim1 a)     = If (first $ fromProof a) (second $ fromProof a) 
fromProof (IffElim2 a)     = If (second $ fromProof a) (first $ fromProof a)
fromProof (OrInt1   a b)   = Or (fromProof a) (fromProof b)
fromProof (OrInt2   a b)   = Or (fromProof b) (fromProof a)
fromProof (OrElim1  a _)   = fstDisj (fromProof a)
fromProof (OrElim2  a _)   = sndDisj (fromProof a)
fromProof (AndInt   a b)   = And (fromProof a) (fromProof b)
fromProof (AndElim1 a)     = fstConj (fromProof a)
fromProof (AndElim2 a)     = sndConj (fromProof a)
fromProof (RAA      _ _ c) = neg (fromProof c)

-- einige Typaliase, insbesondere für Funktionen
type Depth          = Int
type Assumptions    = [Proof]
type Prover         = Proposition -> Assumptions -> Proof
type Transformation = Proposition -> Assumptions -> Prover -> Proof

-- Prüft ob linke Seite beweisbar ist und setzt Beweis in rechte Funktion ein.
-- Wenn nicht beweisbar, breche ab, indem Unprovable zurückgegeben wird.
-- Rechte Funktion kann auch Konstruktorfunktion sein, das sollte nicht verwirren ;-)
(->>)                       :: Proof -> (Proof -> Proof) -> Proof
Unprovable ->> _             = Unprovable
a          ->> f             = f a

-- p: zu beweisende Aussage
-- State:    Annahmen, die zulässig sind
-- Funktion: Funktion, die Aussage unter Berücksichtigung des States beweisen kann

-- StateMonade

-- Liste mit Transformationsfunktionen (siehe unten), die an jedem Knoten des
-- iterativen Baumes evaluiert werden. Eine Transformationsfunktion liefert einen Beweis
-- zurück (evtl. Unprovable) den es mithilfe des ihr übergebenen Provers ermittelt hat.
transformations = [tryAssumption, tryIfInt, tryIfElim, tryIffInt, tryIffElim, tryFoobar, tryOrInt, tryOrElim1, tryOrElim2, tryAndInt, tryAndElim, tryRAA] 

-- Implementierung einer iterativen Tiefensuche.
-- Die Funktion ruft alle Transformationsfunktionen mit dem zu beweisenden Ausdruck auf.
-- Außerem wird den Transformationsfunktionen als Beweisfunktion die Funktion selbst übergeben,
-- wobei hier eine partielle Funktionsanwendung mit der reduzierten Tiefe stattfindet.
-- Auf diese Weise ist es möglich die Transformationsfunktionen von einer speziellen Art
-- der Suche zu abstrahieren. Da sie nur eine Beweisfunktion nehmen, könnte man leicht z.B.
-- auf Breitensuche wechseln.
idsProve       :: Depth -> Prover
idsProve 0 _ _  = Unprovable 
idsProve d p as = fromMaybe Unprovable (find (/=Unprovable) proofs)
                    where
                      np     = idsProve (d-1)
                      proofs = map (\f -> f p as np) transformations

-- Erhöht die Tiefe schrittweise. Wir finden so meist den kürzestmöglichen Beweis,
-- da unsere Suche vollständig ist.
idsProve' p as         = fromMaybe Unprovable $ find (/=Unprovable) [idsProve d p as | d <- [1..30]]

-------------------------------------------------------------------------------
-- Teste, ob zu beweisender Satz im Set of Assumptions steht.
-- Hier wird die Rekursion beendet und ein Teilzweig gilt eventuell als bewiesen.
tryAssumption              :: Transformation
tryAssumption p    as _     = fromMaybe Unprovable $ find ((==p).fromProof) as

-- Teste, ob Aussage durch Konditionalisierung entstanden sein kann.
tryIfInt                   :: Transformation
tryIfInt  (If p q) as pr    = pr q as' ->> \x-> IfInt (A p) x 
                              where
                                as' = as `union` [A p]
tryIfInt  _        _  _     = Unprovable

-- Versuche Konditionale im SoA aufzulösen und dann erneut den Satz zu beweisen.
tryIfElim                  :: Transformation
tryIfElim q       as pr     = pr q as'
                              where
                                pas = map fromProof as
                                f x = isIf (fromProof x) && (k x) /= Unprovable 
                                k x = pr (premise (fromProof x)) as
                                ls = filter f as
                                as' = as++(map (\x-> IfElim (k x) x) ls)

-- Versuche im SoA gespiegelte Konditionale zu finden 
tryIffInt                  :: Transformation
tryIffInt q       as pr     = pr q as'
                              where
                                ls  = filter (isIf.fromProof) as
                                mirrored a b = premise a == consequence b && consequence a == premise b 
                                as' = as `union` [IffInt a b | a <- ls, b <- ls, (fromProof a) `mirrored` (fromProof b)]

tryIffElim                 :: Transformation
tryIffElim q      as pr     = pr q as'
                              where
                                ls  = filter (isIff.fromProof) as
                                as' = as `union` (map IffElim1 ls) `union` (map IffElim2 ls)

tryFoobar (Iff p q) as pr   = pr (If p q) as ->> \x->
                              pr (If q p) as ->> \y-> IffInt x y
tryFoobar _         _  _    = Unprovable
                              
                                  
-- Teste, ob die Aussage durch OrIntroduction zustande gekommen sein kann.
tryOrInt                   :: Transformation
tryOrInt (Or p q)  as pr    | pr p as /= Unprovable = pr p as ->> \x-> OrInt1 x (A q)
                            | otherwise             = pr q as ->> \x-> OrInt2 x (A p)
tryOrInt  _        _  _     = Unprovable

-- Wende Or-Eliminatino auf alle möglichen Elemte im SoA an. Versuche jeweils,
-- das negierte Element zu beweisen. Wenn dies möglich ist, erweitere das SoA.
tryOrElim              :: (Proposition -> Proposition) -> Transformation
tryOrElim dj p as pr    = pr p as'
                          where
                            pas = map fromProof as
                            f x = isOr (fromProof x) && (k x) /= Unprovable 
                            k x = pr (Neg (dj (fromProof x))) as
                            ls  = filter f as
                            as' = as `union` (map (\x-> OrElim1 x (k x)) ls) 

tryOrElim1              = tryOrElim sndDisj
tryOrElim2              = tryOrElim fstDisj

-- Teste, ob Aussage durch And-Introduction zustande gekommen sein kann.
-- Wenn dies der Fall ist, müssen beide Conjuncte einzeln beweisbar sein.
tryAndInt                  :: Transformation
tryAndInt (And p q) as pr   = pr p as ->> \x->
                              pr q as ->> \y-> AndInt x y
tryAndInt _         _  _    = Unprovable

-- Versuche, im SoA Ands zu elminieren. Die einzelnen Conjuncte werden dem SoA
-- hinzugefügt.
tryAndElim                 :: Transformation
tryAndElim  p       as pr   = pr p $ as `union` (map AndElim1 ls) `union` (map AndElim2 ls)
                              where
                                ls = filter (\x->isAnd (fromProof x)) as

-- Teste, ob Aussage durch ReductioAdAdsurdum zustande gekommen sein kann.
-- Hierbei wird zunächst das SoA um die Annahme der negierten Aussage erweitert.
-- Danach wird versucht, im SoA ein Element zu finden, von dem auch das Gegenteil
-- beweisbar ist.
tryRAA                     :: Transformation
tryRAA    p        as pr    | null ks   = Unprovable
                            | otherwise = RAA (head ks) (pr (Neg $ fromProof $ head $ ks) as') (A (Neg p))
                              where
                                as' = as `union` [A (Neg p)]
                                ks  = filter ((/=Unprovable).(\x-> pr (Neg x) as').fromProof) as'

-------------------------------------------------------------------------------

-- Datentyp, der eine Beweiszeile in Cr-Darstellung repräsentiert.
-- Es gibt eine Menge von Zahlen (soa), die sich auf andere Zeilen beziehen,
-- von denen die aktuelle abhängig ist. Außerdem gibt es einen Zeilenindex und
-- eine Menge von Zahlen (dfl), die angibt, wovon diese Zeile abgeleitet wurde.
data Line = Line { soa :: [Int], index :: Int, proof :: Proof, dfl :: [Int]}
            deriving (Eq)

-- Wir nutzen eine eigene, eingängige Darstellung um unsere Zeilen anzuzeigen.
-- Dabei machen wir uns die automatische Dastellung von Listen zu nutze.
instance Show Line where
  show (Line as n p ls) = (fl as' 9)++(fl (show n) 4)++(fl (delbrace (show (fromProof p))) 40)++(fl (lastStep p) 9)++ls'
                         where
                           fl s n | n > length s = s ++ concat (replicate (n-length s) " ")
                                  | otherwise    = s
                           as' = "{" ++ tail (init (show (unique as))) ++ "}"
                           ls' | null ls = ""
                               | otherwise = "(" ++ tail (init (show ls)) ++ ")"
                           unique []     = []
                           unique (x:xs) = x:(unique (filter (/=x) xs))
                           delbrace xs = if (head xs)=='(' && (last xs)==')' then init (tail xs) else xs

-- dient der Ersetzung eines bestimmten Wertes a durch einen anderen b.
replace       :: Eq a => a -> a -> (a -> a)
replace a b    = \x-> if x==a then b else x

-- Bildet Zeile auf Zeile ab, wobei auf alle Zahlen in der Zeile Funktion f angewendet wurde.
mapIntInLine    :: (Int -> Int) -> Line -> Line
mapIntInLine f l = l { soa = (map f (soa l)), index = f (index l), dfl = (map f (dfl l)) }

-- Legt fest, wie die angewendete Regel im Beweis dargestellt werden soll.
lastStep             :: Proof -> String
lastStep (Unprovable) = ""
lastStep (A _)        = "A"
lastStep (IfInt  _ _) = "⊃-Int" 
lastStep (IfElim _ _) = "⊃-Elim" 
lastStep (IffInt  _ _)= "≣-Int" 
lastStep (IffElim1 _) = "≣-Elim" 
lastStep (IffElim2 _) = "≣-Elim" 
lastStep (AndInt _ _) = "∧-Int" 
lastStep (AndElim1 _) = "∧-Elim" 
lastStep (AndElim2 _) = "∧-Elim" 
lastStep (OrInt1 _ _) = "∨-Int" 
lastStep (OrInt2 _ _) = "∨-Int" 
lastStep (OrElim1 _ _)= "∨-Elim" 
lastStep (OrElim2 _ _)= "∨-Elim" 
lastStep (RAA _ _ _)  = "RAA"

-- bildet einen baumartigen `Proof` auf eine Liste von `Line` ab.
-- Hierbei werden auch gleich noch, Anpassungen der Zahlen vorgenommen
-- und überflüssige Zeilen entfernt.
proof2Lines                    :: Proof -> [Line]
proof2Lines                     = zipGaps . consolid . lineifyProof 1

-- bildet den Beweis auf Liste von Line ab.
-- n gibt hierbei an, welchen Index die erste Zeile erhalten soll. Dies ist nicht
-- notwendigerweise 1, da Rekursion im Spiel ist.
-- Bei IfInt und RAA, darf im Assumptionset der Zeilenindex einer Zeile weggelasssen werden.
-- Dies war nicht ganz einfach umzusetzen und verunstaltet außerdem die Mengen (siehe `freed`).
lineifyProof                   :: Int -> Proof -> [Line]
lineifyProof n p@(Unprovable)   = [Line [] n (A (Const "Kein Beweis gefunden.")) []]
lineifyProof n p@(A _)          = [Line [n] n p []]
lineifyProof n p@(IfInt a b)    = as++bs++[Line set (n+las+lbs) p [(n+las+lbs-1), (n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last bs)  \\ freed 
                                    freed = map index (filter ((== proof (head as)).proof) bs)
lineifyProof n p@(IfElim a b)   = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]]
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(IffInt a b)   = as++bs++[Line set (n+las+lbs) p [(n+las+lbs-1), (n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs) 
lineifyProof n p@(IffElim1 a)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(IffElim2 a)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(AndInt   a b) = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(AndElim1 a)   = as++[Line set (n+las) p [(n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(AndElim2 a)   = as++[Line set (n+las) p [(n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(OrInt1 a b)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(OrInt2 a b)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(OrElim1 a b)  = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    bs = lineifyProof  (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(OrElim2 a b)  = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    bs = lineifyProof  (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(RAA a b c)    = as++bs++cs++[Line set (n+las+lbs+lcs) p [(n+las-1), (n+las+lbs-1), (n+las+lbs+lcs-1)]]
                                  where
                                    as = lineifyProof  n           a
                                    bs = lineifyProof  (n+las)     b
                                    cs = lineifyProof  (n+las+lbs) c
                                    las = length as
                                    lbs = length bs
                                    lcs = length cs
                                    set = (soa (last as) `union` soa (last bs)) \\ freed 
                                    freed = map index (filter ((== proof (head cs)).proof) (as++bs))

-- Konsolidierung meint hier: Wir suchen gleiche Zeilen, die Annahmen sind, 
-- löschen alle doppelten und müssen dann natürlich die Referenzen in den 
-- anderen Zeilen anpassen. Dies ist nicht der Schönheit geduldet, sondern notwendig,
-- damit wir "die Annahmen wieder loswerden".
consolid                          :: [Line] -> [Line]
consolid []                        = []
consolid (x@(Line _ _ (A _) _):xs) = x:(consolid xs'')
                                     where
                                       doublets  = filter (\k-> proof x == proof k) xs
                                       replace d = \k-> if k==(index d) then (index x) else k
                                       xs'       = xs \\ doublets
                                       xs''      = foldr (\j-> map (mapIntInLine (replace j))) xs' doublets
consolid (x:xs)                    = x:(consolid xs)

-- Durch die Funktion `consolid` entstehen Lücken, die wir schließen, indem wir alle 
-- Zahlen in den nachfolgenden Zeilen anpassen.
-- Hierzu reicht es nicht die Zahlen nur zu erniedrigen - sie müssen gezielt ersetzt werden.
-- Man darf sich bitte selbst denken, warum ich das hier so explizit schreibe.
zipGaps                           :: [Line] -> [Line]
zipGaps []                         = []
zipGaps (x:xs)                     = x:(zipGaps(map (mapIntInLine (\k->if k==(index (head xs)) then k-offset+1 else k)) xs))
                                     where offset = (index (head xs)) - (index x)



