(*
 * Extracted from Isabelle sources (src/Pure/library.ML)
 *
 * @TAG(OTHER_BSD)
 *)


signature LIBRARY =
sig

  val sort : ('a * 'a -> order) -> 'a list -> 'a list

end

structure Library : LIBRARY =
struct

(*stable mergesort -- preserves order of equal elements*)
fun mergesort unique ord =
  let
    fun merge (xs as x :: xs') (ys as y :: ys') =
          (case ord (x, y) of
            LESS => x :: merge xs' ys
          | EQUAL =>
              if unique then merge xs ys'
              else x :: merge xs' ys
          | GREATER => y :: merge xs ys')
      | merge [] ys = ys
      | merge xs [] = xs;

    fun merge_all [xs] = xs
      | merge_all xss = merge_all (merge_pairs xss)
    and merge_pairs (xs :: ys :: xss) = merge xs ys :: merge_pairs xss
      | merge_pairs xss = xss;

    fun runs (x :: y :: xs) =
          (case ord (x, y) of
             LESS => ascending y [x] xs
           | EQUAL =>
               if unique then runs (x :: xs)
               else ascending y [x] xs
           | GREATER => descending y [x] xs)
      | runs xs = [xs]

    and ascending x xs (zs as y :: ys) =
          (case ord (x, y) of
             LESS => ascending y (x :: xs) ys
           | EQUAL =>
               if unique then ascending x xs ys
               else ascending y (x :: xs) ys
           | GREATER => rev (x :: xs) :: runs zs)
      | ascending x xs [] = [rev (x :: xs)]

    and descending x xs (zs as y :: ys) =
          (case ord (x, y) of
             GREATER => descending y (x :: xs) ys
           | EQUAL =>
               if unique then descending x xs ys
               else (x :: xs) :: runs zs
           | LESS => (x :: xs) :: runs zs)
      | descending x xs [] = [x :: xs];

  in merge_all o runs end;

fun sort ord = mergesort false ord;

end
