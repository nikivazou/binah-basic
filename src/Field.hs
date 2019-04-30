{-# LANGUAGE GADTs #-}
{-@ LIQUID "--no-pattern-inline"                @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--ple" @-}
module Field where

--import qualified Database.Persist

{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }
  deriving Eq

-- {-@ measure prop :: a -> b           @-}
-- {-@ type Prop E = {v:_ | prop v = E} @-}
-- {-@
{-@ measure sharedItemProp :: Int->Int-> Bool@-}
{-@ measure todoItemProp :: String->Int->Bool@-}

{-@selectSharedItem :: forall <q :: RefinedSharedItem -> User -> Bool, r :: RefinedSharedItem -> Bool, p :: User -> Bool>.
  {row :: RefinedSharedItem<r> |- User<p> <: User<q row>}
  FilterList<q, r> RefinedSharedItem -> Tagged<p> [{v:RefinedSharedItem<r>| sharedItemProp (shareFrom v) (shareTo v)}]
@-}
selectSharedItem :: FilterList RefinedSharedItem -> Tagged [RefinedSharedItem]
selectSharedItem = undefined


{-@ filterSharedTo ::
       val: Int -> RefinedFilter<{\row -> shareTo row == val}, {\row v -> True}> RefinedSharedItem @-}
filterSharedTo :: Int -> RefinedFilter RefinedSharedItem
filterSharedTo val = RefinedFilter Filter

{-@ exampleSharedList1 :: FilterList<{\_ v ->True}, {\row -> shareTo row == 1}> RefinedSharedItem @-}
exampleSharedList1 :: FilterList RefinedSharedItem
exampleSharedList1 = filterSharedTo 1 ?: Empty

{-@ exampleselectSharedItem1 :: Tagged<{\v -> True}> [{v : RefinedSharedItem |sharedItemProp (shareFrom v) 1 }] @-}
exampleselectSharedItem1 :: Tagged [RefinedSharedItem]
exampleselectSharedItem1 = selectSharedItem exampleSharedList1

-- {-@projectSharedItemShareFromFn :: forall <q :: User->Bool>.
{-@ reflect projectSharedItemShareFrom @-}
-- {-@ projectSharedItemShareFrom :: xs:[RefinedSharedItem<r>] -> Tagged [{v:Int |  }] @-}
projectSharedItemShareFrom :: [RefinedSharedItem] -> Tagged [Int]
projectSharedItemShareFrom inputL= sequence' (map' projectSharedItemShareFromFn inputL)
  -- [RefinedSharedItem] -> Tagged<q>[Int]@-}

{-@measure Field.sequence' :: forall <p::User->Bool, r::a->Bool>. [Tagged<p> a<r>] -> Tagged <p> [a<r>]@-}
{-@assume sequence' ::forall <p::User->Bool, r::a->Bool>. [Tagged<p> a<r>] -> Tagged <p> [a<r>]@-}
sequence' :: [Tagged a] -> Tagged [a]
sequence' = undefined

{-@ reflect map'@-}
map' :: (a->b) -> [a] -> [b]
map' f [] = []
map' f (x:xs) = (f x):(map' f xs)

{-@measure Field.projectSharedItemShareFromFn::forall <r :: RefinedSharedItem -> Bool, p :: User -> Bool>.
                                { row :: RefinedSharedItem<r> |- User<p> <: User<{\v-> True}> }
               v:RefinedSharedItem<r> -> Tagged<p>{from:Int|sharedItemProp from (shareTo v)}@-}
projectSharedItemShareFromFn :: RefinedSharedItem -> Tagged Int
projectSharedItemShareFromFn = undefined

{-@selectTodoItem :: forall <q :: RefinedTodoItem -> User -> Bool, r :: RefinedTodoItem -> Bool, p :: User -> Bool>.
  {row :: RefinedTodoItem<r> |- User<p> <: User<q row>}
  FilterList<q, r> RefinedTodoItem -> Tagged<p> [{v:RefinedTodoItem<r>| todoItemProp (task v) (tuserId v)}]
@-}
selectTodoItem :: FilterList RefinedTodoItem -> Tagged [RefinedTodoItem]
selectTodoItem = undefined

{-@ filterTodoTask ::
       val: Int -> RefinedFilter<{\row -> tuserId row == val}, {\row v -> tuserId row == userId v || sharedItemProp (tuserId row) (userId v)}> RefinedTodoItem @-}
filterTodoTask :: Int -> RefinedFilter RefinedTodoItem
filterTodoTask val = RefinedFilter Filter

{-@ exampleTodoList1 :: FilterList<{\row v -> (tuserId row == userId v) || (sharedItemProp  (tuserId row) (userId v)) }, {\row -> tuserId row == 1}> RefinedTodoItem @-}
exampleTodoList1 :: FilterList RefinedTodoItem
exampleTodoList1 = filterTodoTask 1 ?: Empty

{-@ exampleTodoItemSelect1 :: Tagged<{\v -> userId v == 1}> [{v : RefinedTodoItem |todoItemProp (task v) 1 }] @-}
exampleTodoItemSelect1 :: Tagged [RefinedTodoItem]
exampleTodoItemSelect1 = selectTodoItem exampleTodoList1

{-@ filterTodoTask_IN ::
       val: [Int] -> RefinedFilter<{\row -> inlist (tuserId row) val}, {\row v -> tuserId row == userId v || sharedItemProp  (tuserId row) (userId v)}> RefinedTodoItem @-}
filterTodoTask_IN :: [Int] -> RefinedFilter RefinedTodoItem
filterTodoTask_IN val = RefinedFilter Filter


{-@ exampleTodoList2 :: FilterList<{\row v -> (tuserId row == userId v) || (sharedItemProp  (tuserId row) (userId v)) }, {\row -> inlist (tuserId row) lst1}> RefinedTodoItem @-}
exampleTodoList2 :: FilterList RefinedTodoItem
exampleTodoList2 = filterTodoTask_IN lst1 ?: Empty


-- {-@ exampleTodoItemSelect2 :: Tagged<{\v -> userId v == 1}> [{v : RefinedTodoItem |todoItemProp (task v) 1 }] @-}
-- exampleTodoItemSelect2 :: Tagged [RefinedTodoItem]
-- exampleTodoItemSelect2 = selectTodoItem exampleTodoList2


{-@exampleselectSharedItem2 :: Tagged <{\v -> True}> [{val:Int|sharedItemProp val 1 }]@-}
exampleselectSharedItem2 :: Tagged [Int]
exampleselectSharedItem2 =  do
  -- {-@ rows :: [{v:RefinedSharedItem | sharedItemProp (shareFrom v) 1}] @-}
  rows <- exampleselectSharedItem1
  projectSharedItemShareFrom' rows


-- {-@ reflect projectSharedItemShareFrom' @-}
{-@ projectSharedItemShareFrom' :: [{v:RefinedSharedItem|sharedItemProp (shareFrom v) 1}] -> Tagged<{\v -> userId v == 1}> [{v:Int | sharedItemProp v 1}] @-}
projectSharedItemShareFrom' :: [RefinedSharedItem] -> Tagged [Int]
projectSharedItemShareFrom' inputL = sequence'' testIntermediate
  where
    {-@testIntermediate ::  [Tagged<{\v -> userId v == 1}>{from:Int|sharedItemProp from 1}]@-}
    testIntermediate = (map'' projectSharedItemShareFromFn' inputL)
  -- [RefinedSharedItem] -> Tagged<q>[Int]@-}
{-@measure Field.sequence'' :: forall <r::a->Bool>. [Tagged<{\v -> userId v == 1}> a<r>] -> Tagged <{\v -> userId v == 1}> [a<r>]@-}
{-@assume sequence'' ::forall <r::a->Bool>. [Tagged<{\v -> userId v == 1}> a<r>] -> Tagged <{\v -> userId v == 1}> [a<r>]@-}
sequence'' :: [Tagged a] -> Tagged [a]
sequence'' = undefined

-- {-@ reflect map''@-}
{-@ assume map'' :: ({v:RefinedSharedItem| sharedItemProp (shareFrom v) 1} -> Tagged<{\v -> userId v == 1}>{from:Int|sharedItemProp from 1})
              -> [{v:RefinedSharedItem| sharedItemProp (shareFrom v) 1}] -> [Tagged<{\v -> userId v == 1}>{from:Int|sharedItemProp from 1}]  @-}
map'' :: (RefinedSharedItem->Tagged Int) -> [RefinedSharedItem] -> [Tagged Int]
-- map'' f [] = []
-- map'' f (x:xs) = (f x):(map' f xs)
map'' = undefined

{-@measure Field.projectSharedItemShareFromFn'::
                {v:RefinedSharedItem| sharedItemProp (shareFrom v) 1} -> Tagged<{\v -> userId v == 1}>{from:Int|sharedItemProp from 1}@-}
projectSharedItemShareFromFn' :: RefinedSharedItem -> Tagged Int
projectSharedItemShareFromFn' = undefined
-- {-@ exampleTodoItemSelect2 :: Tagged<{\v -> userId v == 1}> [RefinedTodoItem] @-}
-- exampleTodoItemSelect2 :: Tagged [RefinedTodoItem]
-- exampleTodoItemSelect2 = do
--     rows <- exampleselectSharedItem1
--     fromList <- projectSharedItemShareFrom rows
--     selectTodoItem (filterTodoTask_IN fromList ?: Empty)



{-@ reflect inlist@-}
inlist :: Int -> [Int] -> Bool
inlist _ [] = False
inlist a (x:xs) = if x == a then True else inlist a xs


{-@reflect lst1@-}
lst1::[Int]
lst1 = [1,2]




{-@ data variance Tagged covariant contravariant @-}

-- Placeholder for Data.Persistent's Filter type
data Filter a = Filter 

{-@ data RefinedFilter record <r :: record -> Bool, q :: record -> User -> Bool> = RefinedFilter (Filter record) @-}
data RefinedFilter record = RefinedFilter (Filter record)

{-@ data variance RefinedFilter covariant covariant contravariant @-}

{-@
data User = User
     { userId   :: Int,
       userName :: String
     , userFriend :: Int
     , userSSN    :: Int
     }
@-}
data User = User { userId::Int, userName :: String, userFriend :: Int, userSSN :: Int }
    deriving (Eq, Show)

-- data RefinedUser =RefinedUser {tuserName::String ,refUserUserId:: Int}
{-@ data RefinedTodoItem =RefinedTodoItem {task::String, refTodoItemTodoItemId::Int, done::Bool,tuserId::Int} @-}
data RefinedTodoItem =RefinedTodoItem {task::String, refTodoItemTodoItemId::Int, done::Bool,tuserId::Int}
{-@ data RefinedSharedItem =RefinedSharedItem {shareFrom::Int, shareTo::Int, refSharedItemSharedItemId :: Int} @-}
data RefinedSharedItem =RefinedSharedItem {shareFrom::Int, shareTo::Int, refSharedItemSharedItemId :: Int}

-- {-@ 
-- assume selectListSharedItem :: MonadIO m => forall <q :: RefinedSharedItem -> RefinedUser -> Bool, r :: RefinedSharedItem -> Bool, p :: RefinedUser -> Bool>.
-- {row :: RefinedSharedItem<r> |- RefinedUser<p> <: RefinedUser<q row>}
-- FilterList<q, r> RefinedSharedItem ->  ReaderT SqlBackend m (Tagged<p> [RefinedSharedItem<r>])
-- @-}
-- selectListSharedItem :: MonadIO m => FilterList RefinedSharedItem -> ReaderT SqlBackend m (Tagged [RefinedSharedItem])
-- selectListSharedItem filterList =fmap Tagged (fmap (fmap map_entity_toRefSharedItem) reader_data)




{-@
data EntityField record typ <q :: record -> User -> Bool> where 
   Field.UserName :: EntityField <{\row v -> userId v = userFriend row}> User {v:_ | True}
 | Field.UserFriend :: EntityField <{\row v -> userId v = userFriend row}> User {v:_ | True}
 | Field.UserSSN :: EntityField <{\row v -> userId v = userId row}> User {v:_ | True}
@-}
{-@ data variance EntityField covariant covariant contravariant @-}
data EntityField a b where
  UserName :: EntityField User String
  UserFriend :: EntityField User Int
  UserSSN :: EntityField User Int

{-@ filterUserName ::
       val: String -> RefinedFilter<{\row -> userName row == val}, {\row v -> userId v = userFriend row}> User @-}
filterUserName :: String -> RefinedFilter User
filterUserName val = RefinedFilter Filter


{-@ filterUserSSN ::
       val: Int -> RefinedFilter<{\row -> userSSN row == val}, {\row v -> userId v = userId row}> User @-}
filterUserSSN :: Int -> RefinedFilter User
filterUserSSN val = RefinedFilter Filter


{-@ filterUserFriend ::
       val: Int -> RefinedFilter<{\row ->userFriend row == val}, {\row v -> userId v = userFriend row}> User @-}
filterUserFriend :: Int -> RefinedFilter User
filterUserFriend val = RefinedFilter Filter

{-@
data FilterList a <q :: a -> User -> Bool, r :: a -> Bool> where
    Empty :: FilterList<{\_ _ -> True}, {\_ -> True}> a
  | Cons :: RefinedFilter<{\_ -> True}, {\_ _ -> False}> a ->
            FilterList<{\_ _ -> False}, {\_ -> True}> a ->
            FilterList<q, r> a
@-}
{-@ data variance FilterList covariant contravariant covariant @-}
data FilterList a = Empty | Cons (RefinedFilter a) (FilterList a)

-- Don't use `Cons` to construct FilterLists: only ever use `?:`. This should be
-- enforced by not exporting `Cons`.

infixr 5 ?:
{-@
(?:) :: forall <r :: a -> Bool, r1 :: a -> Bool, r2 :: a -> Bool,
                q :: a -> User -> Bool, q1 :: a -> User -> Bool, q2 :: a -> User -> Bool>.
  {a_r1 :: a<r1>, a_r2 :: a<r2> |- {v:a | v == a_r1 && v == a_r2} <: a<r>}
  {row :: a<r> |- User<q row> <: User<q1 row>}
  {row :: a<r> |- User<q row> <: User<q2 row>}
  RefinedFilter<r1, q1> a ->
  FilterList<q2, r2> a ->
  FilterList<q, r> a
@-}
(?:) :: RefinedFilter a -> FilterList a -> FilterList a
f ?: fs = f `Cons` fs

{-@
selectList :: forall <q :: a -> User -> Bool, r :: a -> Bool, p :: User -> Bool>.
  {row :: a<r> |- User<p> <: User<q row>}
  FilterList<q, r> a -> Tagged<p> [{v:a<r>| True}]
@-}
selectList :: FilterList a -> Tagged [a]
selectList = undefined

{-@ assume projectUser :: forall <r :: User -> Bool, q :: User -> User -> Bool, p :: User -> Bool>.
                         { row :: User<r> |- User<p> <: User<q row> }
                         [User<r>] -> f: EntityField<q> User typ
                         -> Tagged<p> [typ]
@-}
projectUser ::
      [User]
      -> EntityField User typ
      -> Tagged [typ]
projectUser = undefined

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure  = Tagged
  -- f (a -> b) -> f a -> f b
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x
  (Tagged _) >>  t = t
  fail          = error

{-@ instance Monad Tagged where
     >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>.
            x:Tagged <p> a
         -> (u:a -> Tagged <p> (b <f u>))
         -> Tagged <p> (b<f (content x)>);
     >>  :: forall <p :: User -> Bool>.
            x:Tagged<{\v -> false}> a
         -> Tagged<p> b
         -> Tagged<p> b;
     return :: a -> Tagged <{\v -> true}> a
  @-}

{- Client code -}

{-@ exampleList1 :: FilterList<{\_ -> True}, {\_ -> True}> User @-}
exampleList1 :: FilterList User
exampleList1 = Empty

{-@ exampleList2 :: FilterList<{\_ v -> userId v == 1}, {\user -> userFriend user == 1}> User @-}
exampleList2 :: FilterList User
exampleList2 = filterUserFriend 1 ?: Empty

{-@ exampleList3 :: FilterList<{\_ v -> userId v == 1}, {\user -> userFriend user == 1 && userName user == "alice"}> User @-}
exampleList3 :: FilterList User
exampleList3 = filterUserName "alice" ?: filterUserFriend 1 ?: Empty

{-@ exampleList4 :: FilterList<{\_ v -> userId v == 1}, {\user -> userFriend user == 1 && userName user == "alice"}> User @-}
exampleList4 :: FilterList User
exampleList4 = filterUserFriend 1 ?: filterUserName "alice" ?: Empty

{-@ exampleList5 :: FilterList<{\row v -> userId v == userFriend row}, {\user -> userName user == "alice"}> User @-}
exampleList5 :: FilterList User
exampleList5 = filterUserName "alice" ?: Empty

{-@ exampleSelectList1 :: Tagged<{\v -> userId v == 1}> [{v : User | userFriend v == 1}] @-}
exampleSelectList1 :: Tagged [User]
exampleSelectList1 = selectList (filterUserFriend 1 ?: Empty)

{-@ exampleSelectList2 :: Tagged<{\v -> userId v == 1}> [{v : User | userFriend v == 1 && userName v == "alice"}] @-}
exampleSelectList2 :: Tagged [User]
exampleSelectList2 = selectList (filterUserName "alice" ?: filterUserFriend 1 ?: Empty)

{-@ exampleSelectList3 :: Tagged<{\v -> False}> [{v : User | userName v == "alice"}] @-}
exampleSelectList3 :: Tagged [User]
exampleSelectList3 = selectList (filterUserName "alice" ?: Empty)

-- | This is fine: user 1 can see both the filtered rows and the name field in
--   each of these rows
{-@ names :: Tagged<{\v -> userId v == 1}> [String]
@-}
names :: Tagged [String]
names = do
  rows <- selectList (filterUserFriend 1 ?: Empty)
  projectUser rows UserName

-- | This is bad: the result of the query is not public
-- {-@ bad1 :: Tagged<{\v -> true}> [{v: User | userFriend v == 1}]
-- @-}
-- bad1 :: Tagged [User]
-- bad1 = selectList (filterUserFriend 1 ?: Empty)

-- | This is bad: who knows who else has name "alice" and is not friends with user 1?
-- {-@ bad2 :: Tagged<{\v -> userId v == 1}> [{v: User | userName v == "alice"}]
-- @-}
-- bad2 :: Tagged [User]
-- bad2 = selectList (filterUserName "alice" ?: Empty)

-- | This is bad: user 1 can see the filtered rows but not their SSNs
-- {-@ badSSNs :: Tagged<{\v -> userId v == 1}> [Int]
-- @-}
-- badSSNs :: Tagged [Int]
-- badSSNs = do
--   rows <- selectList (filterUserFriend 1 ?: Empty)
--   projectUser rows UserSSN
