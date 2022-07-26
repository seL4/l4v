(* c.f. Concurrent/cache.ML *)
(* FIXME: maybe add a threshold on the number of elements and do LRU? *)

signature MEMOCACHE =
sig
  val create: 'table -> ('table -> 'key -> 'value lazy option) ->
    ('key * 'value lazy -> 'table -> 'table) -> (('key -> 'value) -> 'key -> 'value) -> 'key -> 'value
end;

structure MemoCache: MEMOCACHE =
struct

fun create empty lookup update f =
  let
    val cache = Synchronized.var "memo-cache" empty;
    fun apply x =
      Synchronized.change_result cache
        (fn tab =>
          (case lookup tab x of
            SOME y => (y, tab)
          | NONE =>
              let val y = Lazy.lazy (fn () => f apply x)
              in (y, update (x, y) tab) end))
      |> Lazy.force;
  in apply end;

end;
