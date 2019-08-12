import qualified Data.Map as Map; import Data.Map (Map)
import qualified Data.Set as Set; import Data.Set (Set)
type Var = String
type Type = String
(\/) = Set.union
int = Set.singleton "int"
bool = Set.singleton "bool"
char = Set.singleton "char"
string = Set.singleton "string"
when c s = if c then s else Set.empty
has k v m = Map.lookup k m == Just v

a, b, c :: Map Var Type -> Set Type
a _ = int \/ bool
b m =
  when (has "a" "int" m) char
  \/ when (has "a" "bool" m) string
c m =
  when (has "a" "int" m && has "b" "char" m) bool
  \/ when (has "a" "bool" m && has "b" "string" m) char
