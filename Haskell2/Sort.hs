merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = if x < y then x : merge xs (y:ys) else y : merge (x:xs) ys

msort [] = []
msort [x] = [x]
msort xs = let l = length xs `div` 2 in merge (msort (take l xs)) (msort (drop l xs)) 
