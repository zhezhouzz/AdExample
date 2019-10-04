fun paren s = "(" ^ s ^ ")"
fun pLn s = print (s ^ "\n")
fun list2string (f, l) =
    let
        val r = List.foldl (fn (e, r) =>
                               case r of
                                   NONE => SOME (f e)
                                 | SOME s => SOME (s ^ ", " ^ (f e))
                           ) NONE l
    in
        case r of
            NONE => "[]"
          | SOME r => "[" ^ r ^ "]"
    end
val counter = ref 0
fun newSym () =
    let
        val ret = "k" ^ (Int.toString (!counter))
        val _ = counter := ((!counter) + 1)
    in
        ret
    end

structure AdAst =
struct

datatype t = Id
           | Exl
           | Exr
           | Delta of t * t
           | Prim of string
           | Circ of t * t

fun layoutAdAst (Id, _) = "id"
  | layoutAdAst (Prim opr, _) = opr
  | layoutAdAst (Exl, _) = "exl"
  | layoutAdAst (Exr, _) = "exr"
  | layoutAdAst (Delta (e1, e2), ifp) =
    let
        val s = (layoutAdAst (e1, true)) ^ " Δ " ^ (layoutAdAst (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutAdAst (Circ (e1, e2), ifp) =
    let
        val s = (layoutAdAst (e1, true)) ^ " o " ^ (layoutAdAst (e2, true))
    in
        if ifp then paren s else s
    end

fun layout func = layoutAdAst (func, false)
end;

structure Dynamic =
struct
structure A = AdAst;
datatype t = Scalar of int
           | Pair of t * t
fun eval (A.Id, input) : t = input
  | eval (A.Exl, Pair (v1, _)) = v1
  | eval (A.Exr, Pair (_, v2)) = v2
  | eval (A.Delta (f1, f2), input) = Pair (eval (f1, input), eval (f2, input))
  | eval (A.Prim "mulC", Pair (Scalar i1, Scalar i2)) = Scalar (i1 * i2)
  | eval (A.Prim "addC", Pair (Scalar i1, Scalar i2)) = Scalar (i1 + i2)
  | eval (A.Circ (f1, f2), input) = eval (f1, eval (f2, input))
  | eval (_, _) = raise Fail "dynamic error"

fun layout (Scalar i) = Int.toString i
  | layout (Pair (v1, v2)) = paren ((layout v1) ^ ", " ^ (layout v2))
end

structure LinearFunc =
struct
structure Dy = Dynamic;
datatype t = Scale of Dy.t
           | Id
           | Exl
           | Exr
           | Product of t * t
           | Delta of t * t
           | Prim of string
           | Circ of t * t
fun layoutAux (Id, _) = "id"
  | layoutAux (Prim opr, _) = opr
  | layoutAux (Exl, _) = "exl"
  | layoutAux (Exr, _) = "exr"
  | layoutAux (Delta (e1, e2), ifp) =
    let
        val s = (layoutAux (e1, true)) ^ " Δ " ^ (layoutAux (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Product (e1, e2), ifp) =
    let
        val s = (layoutAux (e1, true)) ^ " × " ^ (layoutAux (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Circ (e1, e2), ifp) =
    let
        val s = (layoutAux (e1, true)) ^ " o " ^ (layoutAux (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Scale n, ifp) =
    let
        val s = "scale " ^ (Dy.layout n)
    in
        if ifp then paren s else s
    end
fun layout func = layoutAux (func, false)
end

structure Diff =
struct
structure A = AdAst;
structure L = LinearFunc;
structure Dy = Dynamic;
(* newtype Dk a b = D (a → b × (a 'k' b)) *)
type t = Dy.t -> (Dy.t * L.t)
(* Fig 6 *)
(* linearD f f' = D (λa → (f a, f')) *)
fun linearD (f: A.t) (l: L.t) = (fn x => (Dy.eval (f, x), l))
fun diff A.Id = linearD A.Id L.Id
  (* exl = linearD exl exl *)
  (* exr = linearD exr exr *)
  | diff A.Exl = linearD A.Exl L.Exl
  | diff A.Exr = linearD A.Exr L.Exr
  | diff (A.Delta (g, f)) =
    (fn a =>
        let
            val res = Dy.eval (A.Delta (g, f), a)
            val (_, f') = (diff f) a
            val (_, g') = (diff g) a
        in
            (res, L.Delta (f', g'))
        end
    )
  (* addC = linearD addC addC *)
  | diff (A.Prim "addC") = linearD (A.Prim "addC") (L.Prim "addC")
  (* D (λ(a, b) → (a · b, scale b ▽ scale a)) *)
  (* f ▽ g = jam o (f × g) *)
  (* jam is the same as addC here *)
  | diff (A.Prim "mulC") =
    (fn a =>
        let
            val res = Dy.eval (A.Prim "mulC", a)
        in
            case a of
                Dy.Pair (a, b) => (res, L.Circ (L.Prim "addC", L.Product (L.Scale b, L.Scale a)))
              | _ => raise Fail "diff error"
        end
    )
  (* D g ◦ D f = D (λa → let { (b, f') = f a; (c, g') = g b } in (c, g' ◦ f')) *)
  | diff (A.Circ (g, f)) =
    (fn a =>
        let
            val (b, f') = (diff f) a
            val (c, g') = (diff g) b
        in
            (c, L.Circ (g', f'))
        end
    )
  | diff _ = raise Fail "diff error"
end

infix  3 <\     fun x <\ f = fn y => f (x, y);
infix  3 \>     fun f \> y = f y ;
structure A = AdAst;
structure Dy = Dynamic;
structure L = LinearFunc;
let
    val sqr = (A.Prim "mulC") <\A.Circ\> (A.Id <\A.Delta\> A.Id)
    val magSqr = (A.Prim "addC") <\A.Circ\>
                                  (((A.Prim "mulC") <\A.Circ\> (A.Exl <\A.Delta\> A.Exl)) <\A.Delta\> ((A.Prim "mulC") <\A.Circ\> (A.Exr <\A.Delta\> A.Exr)))
    val _ = pLn (A.layout sqr)
    val _ = pLn (A.layout magSqr)
    val _ = pLn (Dy.layout (Dy.eval (sqr, Dy.Scalar 3)))
    val _ = pLn (Dy.layout (Dy.eval (magSqr, Dy.Pair (Dy.Scalar 3, Dy.Scalar 4))))
    fun printD (v, f') = pLn ("res: " ^ (Dy.layout v) ^ "; d: " ^ (L.layout f'))
    val sqr' = (Diff.diff sqr)
    val _ = printD (sqr' (Dy.Scalar 3))
    val magSqr' = (Diff.diff magSqr)
    val _ = printD (magSqr' (Dy.Pair (Dy.Scalar 3, Dy.Scalar 4)))
in
    ()
end;
