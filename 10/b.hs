import Data.List
import Data.Maybe

main = interact $ show . mid . sort . filter (/= 0) . map solve . lines

mid lst = lst !! (n `div` 2) where n = length lst

isopen = (flip elem) "[({<"

score '(' = 1
score '[' = 2
score '{' = 3
score '<' = 4

ispair '(' ')' = True
ispair '[' ']' = True
ispair '{' '}' = True
ispair '<' '>' = True
ispair _ _ = False

solve = g . fromMaybe [] . foldl' f (Just []) where
  g = foldl' (\acc x -> acc * 5 + x) 0 . map score 
  f Nothing _ = Nothing
  f (Just lst) c
    | isopen c = Just $ c : lst
    | otherwise = case lst of
        [] -> Nothing
        (hd:rst) -> if ispair hd c then Just rst else Nothing
