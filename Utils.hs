module Utils where

-- 使用アドレス数、未使用アドレス集合、アドレスと内容の組の集合
data Heap a =
  Heap
  { size :: Int
  , frees :: [Addr]
  , allocs :: [(Addr, a)]
  , count :: Int
  }
-- type Heap a = (Int, [Addr], [(Addr, a)])
type Addr = Int

instance Show a => Show (Heap a) where
  show Heap { size = s, allocs = as, count = c } = show (s, as, c)

hInitial :: Heap a
hInitial = Heap 0 [1..] [] 0

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc Heap { size = s, frees = next:free, allocs = cts, count = c } n = (Heap { size = s+1, frees = free, allocs = (next, n) : cts, count = c + 1}, next)
hAlloc Heap { frees = []} _ = error "hAlloc: no free node. can't allocate."

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate h@(Heap { allocs = cts }) a n = h { allocs = (a,n) : remove cts a }

hFree :: Heap a -> Addr -> Heap a
hFree h@(Heap { size = s, frees = free, allocs = cts }) a = h { size = s-1, frees = a:free, allocs = remove cts a }

hLookup :: Heap a -> Addr -> a
hLookup Heap { allocs = cts } a =
  aLookup cts a (error $ "can't find node " ++ showaddr a ++ " in heap")

hAddresses :: Heap a -> [Addr]
hAddresses Heap { allocs = cts } = [addr | (addr, _node) <- cts]

hSize :: Heap a -> Int
hSize Heap { size = s } = s

hNull :: Addr
hNull = 0

hIsnull :: Addr -> Bool
hIsnull = (== 0)

hAssoc :: Heap a -> Assoc Addr a
hAssoc = allocs

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
