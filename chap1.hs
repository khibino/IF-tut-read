
main :: IO ()
main = print $ quadruple (20 :: Int)

quadruple :: Num a => a -> a
quadruple x = let twice_x = x+x
              in twice_x + twice_x

cons :: a -> [a] -> [a]
cons = (:)

infinite :: a -> [a]
infinite n = let ns = cons n ns
             in ns
