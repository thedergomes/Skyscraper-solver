-- Elder Gomes ci: 25108409
import System.IO
import Data.Char
import Data.List
import Control.Monad

-- Estos son otros puzzles probados con este solucionador
-- ((norte),(sur),(este),(oeste))

-- s = "((3,3,2,1,2,2,3),(2,3,5,4,1,4,2),(3,2,5,2,4,1,3),(4,3,2,4,1,4,2))"
-- s = "((0,2,3,0,2,0,0),(6,0,0,0,2,4,0),(0,4,0,0,0,0,0),(5,0,4,5,0,4,0))"

-- s::[Int]
-- s = [0,0,1,2,0,0,3,0,0,0,1,0,0,2,0,0]
-- s = [0,2,3,0,2,0,0,6,0,0,0,2,4,0,0,4,0,0,0,0,0,5,0,4,5,0,4,0]

-- (0,0,1,2),(0,0,3,0),(0,0,1,0),(0,2,0,0)
-- data NState = NState { b::Board, n::Int, c::[Int] } deriving (Show)

type Cell = [Int]
type Board = [Cell]

-- proporciona los indices de las celdas a partir del indice de una fila dada
cellIndexFromRowIndex::Int->Int->[Int]
cellIndexFromRowIndex n rowi = map (rowi*n+) [0..n-1]

-- proporciona los indices de las celdas a partir del indice de una columna dada
cellIndexFromColIndex::Int->Int->[Int]
cellIndexFromColIndex n coli = [coli+n*i | i <- [0..n-1]]

-- determina a que polo pertenece el indice para poder obtener su columna o fila
cellIndexFromClueIndex::Int->Int->[Int]
cellIndexFromClueIndex ci n
  | ci<n = cellIndexFromColIndex n ci --norte
  | ci>=n && ci<2*n = reverse . cellIndexFromColIndex n $ ci-n --sur
  | ci>=2*n && ci<3*n = cellIndexFromRowIndex n $ -3*n+ci+n --este
  | ci>=3*n && ci<4*n = reverse . cellIndexFromRowIndex n $ -4*n+ci+n --oeste

-- muta la tabla en las posicines dadas reemplazando el valor actual por otra secuencia
applyCells::[Cell]->[Int]->Board->Board
applyCells _ [] board = board
applyCells [] _ board = board
applyCells (cell:cells) (ci:cellIndices) board = applyCells cells cellIndices $ replaceVal' board ci cell

test::[[Int]]->Int->[Int]->Board
test board _ [] = board
test board val (ci:cluesIndex) = test (replaceVal' board ci [val]) (val+1) cluesIndex

-- Esta funcion "muta" la tabla en la posicion dada con el valor dado
replaceVal'::Board->Int->Cell->Board
replaceVal' board pos val = take pos board ++ val : drop (pos+1) board

-- inicializa la tabla infiriendo algunos valores a partir de las pistas n, 1 y 1<pista<n
initialization::Board->[Int]->Int->Int->Board
initialization b [] _ _ = b
initialization b (c:clues) n ci
  | c == n = initialization (test b 1 cellIndices) clues n $ ci+1
  | c == 1 = initialization (replaceVal' b (head cellIndices) [n]) clues n $ ci+1
  | 1 < c && c < n = initialization (other cellIndices 0 n c b) clues n $ ci+1
  | otherwise = initialization b clues n $ ci+1
  where cellIndices = cellIndexFromClueIndex ci n

-- cluesIndex es el arreblo de posiciones relacionadas a la pista
-- i es la posicion del arreglo de posiciones iniciando desde 0
other::[Int]->Int->Int->Int->Board->Board
other [] _ _ _ board = board
other (ci:cluesIndex) i n clueval board = other cluesIndex (i+1) n clueval . replaceVal' board ci . take minimun $ board !! ci
  where minimun = n-clueval+1+i

-- modifica la tabla en las posiciones proporcionadas en cellIndex eliminando en valor dado
removeValInCI::Int->Board->[Int]->Board
removeValInCI cellVal = foldl (\ board i -> replaceVal' board i . delete cellVal $ board !! i)

-- si se encuentra un celda que posea un valor unico se aplica la eliminacion de ese valor en la fila y columna donde este ubicado
eliminate::Board->Int->Board
eliminate board n = foldl (aux n) board [0..n*n-1]
  where aux n nBoard i
          | isCellFixed (nBoard !! i) = removeValInCI (head (nBoard !! i)) nBoard $ getCrossIndicesFromCell  i n
          | otherwise = nBoard

isCellFixed::Cell->Bool
isCellFixed [_] = True
isCellFixed _ = False

-- A partir de un indice de celda se obtienen los indices de la fila y la columna sin incluir a la celda proporcionada
getCrossIndicesFromCell::Int->Int->[Int]
getCrossIndicesFromCell cellIndex n = filter (cellIndex/=) $ row ++ col
  where col = cellIndexFromColIndex n $ cellIndex `mod` n
        row = cellIndexFromRowIndex n $ cellIndex `div` n

-- total de presencias de un numero dado en un conjunto de indices de celdas
totalNsInRow::[Int]->Board->Int->Int
totalNsInRow rowI board nValue = sum [ 1 | idx <- rowI, nValue `elem`(board !! idx) ]

indexOfRowPoeResult::Board->Int->[Int]->Maybe Int
indexOfRowPoeResult board nValue = find (\idx-> let cell = board!!idx in nValue `elem` cell && not (isCellFixed cell))

passClueCheck::Int->[Int]->Bool
passClueCheck 0 _ = True
passClueCheck clue s = let (x', _) = foldl' (\ (y, max) x -> if x > max then (y+1, x) else (y, max)) (0,0) s in x' == clue

-- Funcion que genera secuencias unicas a partir de un conjunto de posibilidades contenidas en cada
-- celda de una fila/columna
makeAllUniqueSequences::[Cell]->[Cell]
makeAllUniqueSequences [] = [[]]
makeAllUniqueSequences (x:xs) = [ x':y' | x' <- x, y' <- y, x' `notElem` y']
  where y = makeAllUniqueSequences xs

generatePossibleSequences::Board->[Int]->Int->Int->Board
generatePossibleSequences board cellIndices clue opClue = filter (f) sequences
  where combination = makeAllUniqueSequences $ map (board!!) cellIndices
        sequences = filter (passClueCheck clue) combination
        f = passClueCheck opClue . reverse

-- combina el grupo de sequencias filtradas para generar nuevos posibles soluciones
-- ejemplo:[[1,2,4,3],[2,3,4,1]] => [[1,2],[2,3],[4],[3,1]]
combinerSeq::[[Int]]->[[Int]]
combinerSeq [] = repeat [] 
combinerSeq (x:xs) = zipWith (\ a b -> if a `notElem` b then a:b else b) x  $ combinerSeq xs

-- Esa funcion itera los indices de las celdas no resueltas(las que tienen celdas > 1)
-- prueba cada valor contenido en cada celda, aplica eliminacion con loop' y comprueba que todas las celdas no enten vacias 
-- asi determina que llego a una solucion valida
solver'::[Int]->Board->Int->[Int]->Board
solver' ucis board n clues = foldl (fn) board ucis
  where fn acc i
          | isCellFixed cell = acc
          | otherwise = do
            tv <- cell
            let 
              tryList = replaceVal' board i [tv]
              nboard = loop' tryList [[]] n clues
            guard $ any (not . null) nboard
            nboard
              where cell = board!!i

-- Esta funcion genera secuencias de posibles valores a partir de las posibilidades ya contenidas en el tablero, las filtra para 
-- obtener solo las que satisfagan las pistas y luego las aplica al tablero
prueba::Board->[Int]->Int->[Int]->Board
prueba board [] _ _ = board
prueba board (ci:clueIndices) n clues = prueba boardWithSequence clueIndices n clues
  where cellIndices = cellIndexFromClueIndex ci n
        boardWithSequence = applyCells (combinerSeq possibleSequences) cellIndices board
        possibleSequences = generatePossibleSequences board cellIndices (clues!!ci) $ clues!!(ci+n) 

-- Esta funcion debe ejecutarse luego de haber aplicado la primera etapa de la aplicacion de restricciones es decir la inializacion
-- el bucle se realizara hasta que ya no se realicen mas cambios en la tabla
-- topAndLeftClueIndex proporciona los indices de las pistas norte y este
loop'::Board->Board->Int->[Int]->Board
loop' actualB beforeB n clues
  | actualB == beforeB = actualB
  | otherwise = loop' (prueba (eliminate posiVal n) topAndLeftClueIndex n clues) actualB n clues
    where topAndLeftClueIndex = [0..(n-1)]++[(2*n)..(3*n-1)]
          posiVal = foldl (iterateRow n) actualB [1..n] 

iterateRow::Int->Board->Int->Board
iterateRow n board val = foldl (\ nb i -> 
  let cellIndices = cellIndexFromRowIndex n i
      indexOfRowPoeResult' = indexOfRowPoeResult nb val cellIndices
  in  crossOff (totalNsInRow cellIndices nb val) indexOfRowPoeResult' nb [val]) board [0..n-1]

-- elimina el valor dado de las celdas en la tabla 
crossOff::Int->Maybe Int->Board->[Int]->Board
crossOff 1 (Just i) board cellVal = replaceVal' board i cellVal
crossOff _ _ board _ = board

solve::[Int]->Int->[[Int]]
solve clues n =  solver' unresolvedCell x n clues
  where w = initialization board clues n 0
        x = loop' w [] n clues
        unresolvedCell = findIndices (not . isCellFixed) x
        board = replicate (n*n) [1..n]

-- Con Estas funciones se imprime la solucion en el formato solicitado
fu'::Int->[Int]->Board
fu' _ [] = []
fu' n l = let (h, t) = splitAt n l in h:fu' n t

fu''::Board->String
fu'' = map (aux) . show
  where aux '[' = '('
        aux ']' = ')'
        aux x = x

e::String->[Int]
e = map (read) . words . map (aux)
  where aux x 
          | isDigit x = x
          | otherwise = ' '

main = do
  s <- readFile "puzzle.txt"
  when (s /= "") $ do
  let 
    clues = e s
    n = (length clues) `div` 4
  putStrLn $ "R="++(fu'' . fu' n . concat) (solve clues n)