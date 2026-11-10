structure Type_dtype =
struct

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness (an interactive session may
    create more than one such pair, and they need to be distinguished).
 ---------------------------------------------------------------------------*)

type id = KernelSig.kernelid

(*---------------------------------------------------------------------------*
 * HOL types are somewhat akin to terms in first order logic.                *
 *---------------------------------------------------------------------------*)

type tyconst = id * int

datatype hol_type = Tyv of string
                  | Tyapp of tyconst * hol_type list;

(*---------------------------------------------------------------------------*
 * The "holty" wrapper on tmconst tells whether the constant is polymorphic  *
 * or not.  Currently, this is only an approximation: if it is GRND, then    *
 * the constant has no type variables.  If POLY, the constant may or may     *
 * not have type variables.                                                  *
 *---------------------------------------------------------------------------*)

datatype holty = GRND of hol_type
               | POLY of hol_type

fun to_hol_type (GRND ty) = ty
  | to_hol_type (POLY ty) = ty;

(*---------------------------------------------------------------------------*
 * Memo tables for one traversal of a value that may share subvalues (a     *
 * term or type DAG).  ML has no pointer hash, so a table is searched by a  *
 * bounded structural sample of the key; a hit needs [same] (pointer        *
 * equality in the kernel), so the hash only picks the bucket searched and  *
 * cannot change a result.                                                  *
 *                                                                          *
 * The first [threshold] calls of [memo] run [compute] directly and keep no *
 * result, and a node met again among those calls is recomputed, its result *
 * unshared.  Each bucket keeps only the [bucket_limit] most recent         *
 * entries, so keys that all hash alike (a long list or numeral spine) cost *
 * a bounded search; a key whose entry was dropped is recomputed.           *
 *                                                                          *
 * A memoised walk costs more per node than a plain one, so a kernel walk   *
 * first runs plain, calling [tick] on a [budget] at each interior node,    *
 * and runs memoised only when [tick] raises [OverBudget]: on a small value *
 * that walk is the stock one, and on a DAG it stops after [budget_size]    *
 * nodes, however many paths the DAG has.                                   *
 *---------------------------------------------------------------------------*)

structure Memo =
struct
  val threshold = 256
  val bucket_limit = 8
  val initial_size = 64

  val window = 256
  val budget_size = 65536

  exception OverBudget
  fun budget () = ref budget_size
  fun tick r = if !r = 0 then raise OverBudget else r := !r - 1

  (* [start] is the call count after which the table is in use; [hits]
     counts hits since then. *)
  type ('a, 'b) table =
       {hash : 'a -> word, same : 'a * 'a -> bool, calls : int ref,
        start : int ref, hits : int ref,
        count : int ref, buckets : ('a * word * 'b) list array ref}

  fun new hash same : ('a, 'b) table =
      {hash = hash, same = same, calls = ref 0, start = ref threshold,
       hits = ref 0, count = ref 0, buckets = ref (Array.fromList [])}

  (* A table that has stored [window] entries with fewer than one hit in
     eight is walking a tree, where it only costs: drop it, and try again
     once the call has made as many calls again. *)
  fun give_up ({calls, start, hits, count, buckets, ...} : ('a, 'b) table) =
      (buckets := Array.fromList []; count := 0; hits := 0;
       start := 2 * !calls)

  fun index (h, buckets) =
      Word.toInt (Word.andb (h, Word.fromInt (Array.length buckets - 1)))

  fun grow (buckets : ('a * word * 'b) list array ref) =
      let
        val old = !buckets
        val new = Array.array (Int.max (initial_size, 2 * Array.length old),
                               [])
        fun add (e as (_, h, _)) =
            let val i = index (h, new)
            in Array.update (new, i, e :: Array.sub (new, i)) end
      in
        Array.app (List.app add o List.rev) old;
        buckets := new
      end

  fun insert ({buckets, count, ...} : ('a, 'b) table) (e as (_, h, _)) =
      let
        val _ = if !count >= 2 * Array.length (!buckets) then grow buckets
                else ()
        val b = !buckets
        val i = index (h, b)
        val bucket = e :: Array.sub (b, i)
      in
        if length bucket > bucket_limit then
          Array.update (b, i, List.take (bucket, bucket_limit))
        else (Array.update (b, i, bucket); count := !count + 1)
      end

  fun memo (t as {hash, same, calls, start, hits, count, buckets}
             : ('a, 'b) table) key compute =
      (calls := !calls + 1;
       if !calls <= !start then compute ()
       else
        let
          val h = hash key
          fun find [] = NONE
            | find ((k, _, v) :: rest) =
                if same (key, k) then SOME v else find rest
          val b = !buckets
        in
          case (if Array.length b = 0 then NONE
                else find (Array.sub (b, index (h, b)))) of
            SOME v => (hits := !hits + 1; v)
          | NONE =>
              let val v = compute ()
              in
                insert t (key, h, v);
                if !count = window andalso 8 * !hits < window
                then give_up t else ();
                v
              end
        end)

  fun mix (h1, h2) = Word.+ (Word.* (h1, 0w31), h2)
  fun string_hash s =
      CharVector.foldl (fn (c, h) => mix (h, Word.fromInt (Char.ord c)))
                       0w5381 s
  fun id_hash id = string_hash (KernelSig.name_of id)
end


(* A sample of a type's top three levels, for Memo buckets. *)
fun type_hash ty =
    let
      fun sample _ (Tyv s) = Memo.string_hash s
        | sample 0 (Tyapp ((id, _), _)) = Memo.id_hash id
        | sample d (Tyapp ((id, _), args)) =
            List.foldl (fn (a, h) => Memo.mix (h, sample (d - 1) a))
                       (Memo.id_hash id) args
    in
      sample 3 ty
    end

fun same_type (ty1 : hol_type, ty2) = Portable.pointer_eq (ty1, ty2)

(*---------------------------------------------------------------------------*
 * [mk_ty_sub theta] is a substitution function for theta whose memo lasts   *
 * as long as the function, so a caller substituting into several types    *
 * (the typed leaves of a term) shares it across them.  Unchanged subtypes  *
 * are returned as they are (SAME).                                         *
 *---------------------------------------------------------------------------*)

fun mk_ty_sub [] = (fn _ => Lib.SAME)
  | mk_ty_sub theta =
    let
      val table = Memo.new type_hash same_type
      fun sub (ty as Tyapp (tyc, args)) =
            Memo.memo table ty (fn () =>
              case Lib.delta_map sub args of
                Lib.SAME => Lib.SAME
              | Lib.DIFF args' => Lib.DIFF (Tyapp (tyc, args')))
        | sub v =
            case Lib.subst_assoc (fn x => x = v) theta of
              NONE => Lib.SAME
            | SOME ty => Lib.DIFF ty
    in
      sub
    end

(* [mk_polymorphic ()] tests for type variables, with a memo that lasts as
   long as the function. *)
fun mk_polymorphic () =
    let
      val table = Memo.new type_hash same_type
      fun poly (Tyv _) = true
        | poly (ty as Tyapp (_, args)) =
            Memo.memo table ty (fn () => List.exists poly args)
    in
      poly
    end

(* Each kernel's ty_sub and polymorphic: a plain walk while the type is
   small, and past Memo's budget the memoised walk of mk_ty_sub or
   mk_polymorphic. *)
fun ty_sub [] _ = Lib.SAME
  | ty_sub theta ty =
    let
      val left = Memo.budget ()
      fun sub (Tyapp (tyc, args)) =
            (Memo.tick left;
             case Lib.delta_map sub args of
               Lib.SAME => Lib.SAME
             | Lib.DIFF args' => Lib.DIFF (Tyapp (tyc, args')))
        | sub v =
            case Lib.subst_assoc (fn x => x = v) theta of
              NONE => Lib.SAME
            | SOME ty => Lib.DIFF ty
    in
      sub ty handle Memo.OverBudget => mk_ty_sub theta ty
    end

fun polymorphic ty =
    let
      val left = Memo.budget ()
      fun poly (Tyv _) = true
        | poly (Tyapp (_, args)) = (Memo.tick left; List.exists poly args)
    in
      poly ty handle Memo.OverBudget => mk_polymorphic () ty
    end

end
