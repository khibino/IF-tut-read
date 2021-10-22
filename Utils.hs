module Utils where

-- 使用アドレス数、未使用アドレス集合、アドレスと内容の組の集合
type Heap a = (Int, [Addr], [(Addr, a)])
type Addr = Int

hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), cts) n = ((size+1, free, (next, n) : cts), next)
hAlloc (_   , []         ,   _) _ = error "hAlloc: no free node. can't allocate."

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = (size, free, (a,n) : remove cts a)

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size-1, a:free, remove cts a)

hLookup :: Heap a -> Addr -> a
hLookup (_size, _free, cts) a =
  aLookup cts a (error $ "can't find node " ++ showaddr a ++ " in heap")

hAddresses :: Heap a -> [Addr]
hAddresses (_size, _free, cts) = [addr | (addr, _node) <- cts]

hSize :: Heap a -> Int
hSize (size, _free, _cts) = size

hNull :: Addr
hNull = 0

hIsnull :: Addr -> Bool
hIsnull = (== 0)

showaddr :: Addr -> String
showaddr = ("#" ++) . shownum

shownum :: Int -> String
shownum = show

remove :: [(Addr, a)] -> Addr -> [(Addr, a)]
remove [] a = error ("Attempt to update or free nonexistent address " ++ showaddr a)
remove ((a',n):cts) a | a == a'   = cts
                      | otherwise = (a',n) : remove cts a

type Assoc a b = [(a, b)]

aLookup :: Eq a => Assoc a b -> a -> b -> b
aLookup []         _k' def              = def
aLookup ((k,v):bs) k'  def | k == k'    = v
                           | otherwise  = aLookup bs k' def

aDomain :: Assoc a b -> [a]
aDomain alist = [key | (key, _val) <- alist]

aRange :: Assoc a b -> [b]
aRange alist = [val | (_key, val) <- alist]

aEmpty :: Assoc a b
aEmpty = []
