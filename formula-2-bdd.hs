import Data.List.Split
import Debug.Trace
import System.Environment
import System.Exit
import System.IO

type Result a = Either String a

data ProgramAction = PrintFormula | PrintThruthTable | PrintBdd | PrintRbdd deriving (Show,Eq,Ord,Enum)
data ProgramOptions = ProgramOptions {
	input :: Maybe FilePath,
	action :: ProgramAction
} deriving Show

type Variable = Char
data Literal = Literal {
	var :: Variable,
	val :: Bool
} deriving Eq
instance Show Literal where
	show (Literal var val) =
		if val
			then [var]
			else '-':[var]

data Clause = Clause {
	literals :: [Literal]
}
instance Show Clause where
	show (Clause (lit:[])) = show lit
	show (Clause (lit:lits)) = (show lit) ++ (',':(show (Clause lits)))


data Formula = Formula {
	vars :: [Variable],
	clauses :: [Clause]
}
instance Show Formula where
	show (Formula vars (cl:[])) = show cl
	show (Formula vars (cl:clauses)) = (show cl) ++ ('\n':(show (Formula vars clauses)))

data TruthTableRow = TruthTableRow {
	ttclause :: Clause,
	ttval :: Bool
}

data TruthTable = TruthTable {
	ttvars :: [Variable],
	ttrows :: [TruthTableRow]
}
instance Show TruthTable where
	show (TruthTable vars rows) = showVars vars ++ showRows rows
		where
			showVars (var:[]) = [var,'\n']
			showVars (var:vars) = var:' ':(showVars vars)

			showRows (row:[]) = showRow row
			showRows (row:rows) = (showRow row) ++ ['\n'] ++ (showRows rows)

			showRow (TruthTableRow clause val) =
				if val
					then showTruthValues (literals clause) ++ ['1']
					else showTruthValues (literals clause) ++ ['0']

			showTruthValues (lit:[]) =
				if (val lit)
					then ['1', ' ']
					else ['0', ' ']
			showTruthValues (lit:lits) =
				if (val lit)
					then ['1', ' '] ++ (showTruthValues lits)
					else ['0', ' '] ++ (showTruthValues lits)

----------------------------------------------------------
--                  Utility functions                   --
----------------------------------------------------------

isLowcaseAlpha :: Char -> Bool
isLowcaseAlpha c = c `elem` ['a'..'z']

openFileOrStdin :: Maybe FilePath -> IO Handle
openFileOrStdin path = do
	case path of
		Nothing -> return stdin
		Just path' -> openFile path' ReadMode

readLines :: Handle -> [String] -> IO [String]
readLines inputHandle lines = do
	eof <- hIsEOF inputHandle
	if eof
		then return lines
		else do
			line <- hGetLine inputHandle
			readLines inputHandle (lines ++ [line])

errorAndFail :: String -> IO ExitCode
errorAndFail msg = do
	hPutStrLn stderr msg
	return (ExitFailure 1)

isSublistOf :: (Eq a) => [a] -> [a] -> Bool
isSublistOf [] y = True
isSublistOf (x:xs) y =
	if x `elem` y
		then xs `isSublistOf` y
		else False

----------------------------------------------------------
--                 Truth table functions                --
----------------------------------------------------------

literalsOfVariable :: Variable -> [Literal]
literalsOfVariable var = [(Literal var val) | val <- [False, True]]

literalsOfVariables :: [Variable] -> [[Literal]]
literalsOfVariables [] = [[]]
literalsOfVariables (var:vars) = [(lit:lits) | lit <- literalsOfVariable var, lits <- literalsOfVariables vars]

clausesFromLiterals :: [[Literal]] -> [Clause]
clausesFromLiterals llits = [(Clause lits) | lits <- llits]

varCombinations :: [Variable] -> [Clause]
varCombinations vars = clausesFromLiterals $ literalsOfVariables vars

truthValueOf :: Clause -> [Clause] -> Bool
truthValueOf cl [] = False
truthValueOf cl (clause:rest) =
	if (literals clause) `isSublistOf` (literals cl)
		then True
		else truthValueOf cl rest

generateTruthTable :: Formula -> TruthTable
generateTruthTable (Formula vars clauses) = TruthTable vars (generateTruthTableRows (varCombinations vars) clauses)
	where
		generateTruthTableRows :: [Clause] -> [Clause] -> [TruthTableRow]
		generateTruthTableRows (cl:[]) clauses = [TruthTableRow cl (truthValueOf cl clauses)]
		generateTruthTableRows (cl:rest) clauses = (TruthTableRow cl (truthValueOf cl clauses)):(generateTruthTableRows rest clauses)
		generateTruthTableRows [] _ = []


----------------------------------------------------------
--            Parsing of data from the input            --
----------------------------------------------------------

parseLiteral :: String -> [Variable] -> Maybe (Literal, [Variable])
parseLiteral ('-':v:[]) vars =
	if isLowcaseAlpha v
		then if v `elem` vars
			then return (Literal v False, vars)
			else return (Literal v False, vars ++ [v])
		else Nothing
parseLiteral (v:[]) vars =
	if isLowcaseAlpha v
		then if v `elem` vars
			then return (Literal v True, vars)
			else return (Literal v True, vars ++ [v])
		else Nothing
parseLiteral _ _ = Nothing

parseClause :: [String] -> [Variable] -> Maybe (Clause, [Variable])
parseClause line vars = parseClause' line vars []
	where
		parseClause' :: [String] -> [Variable] -> [Literal] -> Maybe (Clause, [Variable])
		parseClause' [] vars lits =
			if (length lits) == 0
				then Nothing
				else return (Clause lits, vars)
		parseClause' (v:rest) vars lits =
			case parseLiteral v vars of
				Nothing -> Nothing
				Just (lit, newVars) -> parseClause' rest newVars (lits ++ [lit])

parseFormula :: [String] -> Result Formula
parseFormula lines =
	case parseFormula' lines [] [] of
		Nothing -> Left "Wrong format of input file."
		Just formula -> return formula
	where
		parseFormula' :: [String] -> [Variable] -> [Clause] -> Maybe Formula
		parseFormula' [] vars clauses =
			if (length vars) == 0
				then Nothing
				else return $ Formula vars clauses
		parseFormula' (line:rest) vars clauses =
			case parseClause (splitOn "," line) vars of
				Nothing -> Nothing
				Just (clause, newVars) -> parseFormula' rest newVars (clauses ++ [clause])

----------------------------------------------------------
--            Processing of startup options             --
----------------------------------------------------------

processArgAct :: String -> Maybe ProgramAction
processArgAct "-i" = return PrintFormula
processArgAct "-t" = return PrintThruthTable
processArgAct "-b" = return PrintBdd
processArgAct "-r" = return PrintRbdd
processArgAct _ = Nothing

processArgs :: [String] -> Either String ProgramOptions
processArgs [act] =
	case processArgAct act of
		Nothing -> Left "Invalid startup options."
		Just act' -> return $ ProgramOptions Nothing act'
processArgs [act,inp] =
	case processArgAct act of
		Nothing -> Left "Invalid startup options."
		Just act' -> return $ ProgramOptions (Just inp) act'
processArgs _ = Left "Invalid startup options."

runWithOpts :: ProgramOptions -> IO ExitCode
runWithOpts opts = do
	inputHandle <- openFileOrStdin (input opts)
	lines <- readLines inputHandle []
	case (action opts) of
		PrintFormula -> do
			case parseFormula lines of
				Left err -> errorAndFail err
				Right formula -> do
					putStrLn (show formula)
					return ExitSuccess
		PrintThruthTable -> do
			case parseFormula lines of
				Left err -> errorAndFail err
				Right formula -> do
					let tt = generateTruthTable formula
					putStrLn (show tt)
					return ExitSuccess
		PrintBdd -> errorAndFail "NIY"
		PrintRbdd -> errorAndFail "NIY"

run :: [String] -> IO ExitCode
run args = do
	let opts = processArgs args
	case opts of
		Left err -> errorAndFail err
		Right opts' -> runWithOpts opts'

main :: IO ()
main = do
	args <- getArgs
	result <- run args
	case result of
		ExitSuccess -> exitSuccess
		ExitFailure ec -> exitWith (ExitFailure ec)
