-- Project: formula-2-bdd (FLP 2015/2016)
-- University: Faculty of Information Technology, Brno University of Technology
-- Author: Marek Milkovič (xmilko01)

import Data.List
import Data.List.Split
import System.Environment
import System.Exit
import System.IO

----------------------------------------------------------
--                  Type definitions                    --
----------------------------------------------------------

-- | Type capable of returning the expected value from function, or string in case of error.
type Result a = Either String a

-- | Represents program action specified through startup arguments.
data ProgramAction = PrintFormula | PrintThruthTable | PrintBdd | PrintRbdd deriving (Show,Eq,Ord,Enum)

-- | Represents all program options provided through startup arguments.
data ProgramOptions = ProgramOptions {
	input :: Maybe FilePath,
	action :: ProgramAction
} deriving Show

-- | Represents variable.
type Variable = Char

-- | Represents literal of variable with boolean value.
data Literal = Literal {
	var :: Variable,
	val :: Bool
} deriving Eq
instance Show Literal where
	show (Literal var val) =
		if val
			then [var]
			else '-':[var]

-- | Represents clause in DNF formula.
data Clause = Clause {
	literals :: [Literal]
} deriving Eq
instance Show Clause where
	show (Clause (lit:[])) = show lit
	show (Clause (lit:lits)) = (show lit) ++ (',':(show (Clause lits)))

-- | Represents DNF formula.
data Formula = Formula {
	vars :: [Variable],
	clauses :: [Clause]
}
instance Show Formula where
	show (Formula vars (cl:[])) = show cl
	show (Formula vars (cl:clauses)) = (show cl) ++ ('\n':(show (Formula vars clauses)))

-- | Represents single row in truth table.
data TruthTableRow = TruthTableRow {
	ttclause :: Clause,
	ttval :: Bool
}

-- | Represents truth table.
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

-- | Represents BDD.
data Bdd =
	Nonterminal {
		bvar :: Variable,
		blow :: Bdd,
		bhigh :: Bdd
	} |
	Terminal {
		bval :: Bool
	} deriving Eq
instance Show Bdd where
	show (Terminal val) =
		if val
			then ['1', '\n']
			else ['0', '\n']
	show (Nonterminal bvar low high) = showPath (Nonterminal bvar low high) []
		where
			showPath (Nonterminal bvar low high) path =
				showPath low (path ++ [Literal bvar False]) ++
				showPath high (path ++ [Literal bvar True])
			showPath (Terminal val) [] =
				if val
					then ['1', '\n']
					else ['0', '\n']
			showPath t (lit:lits) =
				if val lit
					then [var lit] ++ "=>" ++ (showPath t lits)
					else [var lit] ++ "->" ++ (showPath t lits)

----------------------------------------------------------
--                  Utility functions                   --
----------------------------------------------------------

-- | Checks whether the character is lowercase letter from 'a' to 'z'.
isLowcaseAlpha :: Char -> Bool
isLowcaseAlpha c = c `elem` ['a'..'z']

-- | Opens file at specified path and returns handle to it. Returns handle to standard input if path is 'Nothing'.
openFileOrStdin :: Maybe FilePath -> IO Handle
openFileOrStdin path = do
	case path of
		Nothing -> return stdin
		Just path' -> openFile path' ReadMode

-- | Reads the input handle and stored all read lines into list.
readLines :: Handle -> [String] -> IO [String]
readLines inputHandle lines = do
	eof <- hIsEOF inputHandle
	if eof
		then return lines
		else do
			line <- hGetLine inputHandle
			readLines inputHandle (lines ++ [line])

-- | Prints error message on standard error output and return 'ExitFailure'.
errorAndFail :: String -> IO ExitCode
errorAndFail msg = do
	hPutStrLn stderr msg
	return (ExitFailure 1)

-- | Checks whether all elements of first list are elements in the second list.
isSublistOf :: (Eq a) => [a] -> [a] -> Bool
isSublistOf [] y = True
isSublistOf (x:xs) y =
	if x `elem` y
		then xs `isSublistOf` y
		else False

----------------------------------------------------------
--                Binary decision diagram               --
----------------------------------------------------------

-- | Performs reduction of given BDD and return R(O)BDD.
reduceBdd :: Bdd -> Bdd
reduceBdd bdd = let newBdd = reduceBdd' bdd in
	if bdd /= newBdd
		then reduceBdd' newBdd
		else bdd
	where
		reduceBdd' :: Bdd -> Bdd
		reduceBdd' (Terminal val) = Terminal val
		reduceBdd' (Nonterminal var low high) =
			if low == high
				then reduceBdd' low
				else Nonterminal var (reduceBdd' low) (reduceBdd' high)

-- | Generates BDD from truth table.
generateBdd :: TruthTable -> Bdd
generateBdd (TruthTable vars rows) = generateBdd' vars rows []
	where
		generateBdd' :: [Variable] -> [TruthTableRow] -> [Literal] -> Bdd
		generateBdd' [] ttrows path =
			case (find (\x -> path `isSublistOf` (literals (ttclause x))) ttrows) of
				Nothing -> error "Fatal error during construction of BDD!"
				Just row -> Terminal (ttval row)
		generateBdd' (var:vars) ttrows path =
			Nonterminal var
			(generateBdd' vars ttrows $ path ++ [Literal var False])
			(generateBdd' vars ttrows $ path ++ [Literal var True])

----------------------------------------------------------
--                 Truth table functions                --
----------------------------------------------------------

-- | Returns list of all possible literals of given variable. Example: for input "a" returns [-a,a] (in this order).
literalsOfVariable :: Variable -> [Literal]
literalsOfVariable var = [(Literal var val) | val <- [False, True]]

-- | Returns list of all possible interleaved literals of specified variables. Example: for input ["a","b","c"] returns [[-a,-b,-c],[-a,-b,c],...] (in this order).
literalsOfVariables :: [Variable] -> [[Literal]]
literalsOfVariables [] = [[]]
literalsOfVariables (var:vars) = [(lit:lits) | lit <- literalsOfVariable var, lits <- literalsOfVariables vars]

-- | Transform list of all possible interleaved literals to a list of clauses.
clausesFromLiterals :: [[Literal]] -> [Clause]
clausesFromLiterals llits = [(Clause lits) | lits <- llits]

-- | Computes list of all possible clauses from given list of variables.
varCombinations :: [Variable] -> [Clause]
varCombinations vars = clausesFromLiterals $ literalsOfVariables vars

-- | Determines truth value of single clause based on clauses from DNF formula.
truthValueOf :: Clause -> [Clause] -> Bool
truthValueOf cl [] = False
truthValueOf cl (clause:rest) =
	if (literals clause) `isSublistOf` (literals cl)
		then True
		else truthValueOf cl rest

-- | Generates the truth table from formula.
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

-- | Parses the literal (of string type), populates the list of variables found and returns maybe tuple of parsed literal and list of new variables.
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

-- | Parses the clause as list of literals (of string type) and return maybe tuple of parsed clause and list of variables present in the clause.
parseClause :: [String] -> [Variable] -> Maybe (Clause, [Variable])
parseClause line vars = parseClause' line vars []
	where
		parseClause' :: [String] -> [Variable] -> [Literal] -> Maybe (Clause, [Variable])
		parseClause' [] vars lits =
			if (length lits) == 0 -- No literals parsed and we are already at the end of recursion, end with error.
				then Nothing
				else return (Clause lits, vars)
		parseClause' (v:rest) vars lits =
			case parseLiteral v vars of
				Nothing -> Nothing
				Just (lit, newVars) -> parseClause' rest newVars (lits ++ [lit])

-- | Parses the formula from the list of clauses (of string type) and returns either parsed formula or error.
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

-- | Parses the single startup argument and maybe returns program action.
processArgAct :: String -> Maybe ProgramAction
processArgAct "-i" = return PrintFormula
processArgAct "-t" = return PrintThruthTable
processArgAct "-b" = return PrintBdd
processArgAct "-r" = return PrintRbdd
processArgAct _ = Nothing

-- | Prases the startup arguments and returns either parsed program options or error.
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

-- | Runs the program with given program options (already parser startup arguments) and returns exit code 'ExitSuccess' or 'ExitFailure'.
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
		PrintBdd -> do
			case parseFormula lines of
				Left err -> errorAndFail err
				Right formula -> do
					let tt = generateTruthTable formula
					let bdd = generateBdd tt
					putStr (show bdd)
					return ExitSuccess
		PrintRbdd -> do
			case parseFormula lines of
				Left err -> errorAndFail err
				Right formula -> do
					let tt = generateTruthTable formula
					let bdd = generateBdd tt
					let rbdd = reduceBdd bdd
					putStr (show rbdd)
					return ExitSuccess

-- | Runs the program with given list of startup arguments and returns exit code 'ExitSuccess' or 'ExitFailure'.
run :: [String] -> IO ExitCode
run args = do
	let opts = processArgs args
	case opts of
		Left err -> errorAndFail err
		Right opts' -> runWithOpts opts'

-- | Entry point.
main :: IO ()
main = do
	args <- getArgs
	result <- run args
	case result of
		ExitSuccess -> exitSuccess
		ExitFailure ec -> exitWith (ExitFailure ec)
