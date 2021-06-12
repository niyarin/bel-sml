datatype belobj =
NIL
|SYMBOL of string
|CHAR of char
|PAIR of ((belobj ref) * (belobj ref)) ref;

fun bel_car (PAIR(bel_pair)) = !(#1(!bel_pair))
  | bel_car _ = NIL;

fun bel_cdr (PAIR(bel_pair)) = !(#2(!bel_pair))
  | bel_cdr _ = NIL;
fun bel_cadr bel_pair = bel_car(bel_cdr(bel_pair));

fun bel_xar (PAIR(bel_pair), bel_obj) =
    (#1(!bel_pair) := bel_obj;
     bel_obj)
  | bel_xar (_, _) = NIL;

fun bel_xdr (PAIR(bel_pair), bel_obj) =
    (#2(!bel_pair) := bel_obj;
     bel_obj)
  | bel_xdr (_, _) = NIL;

fun bel_join(a, b) = PAIR(ref (ref a, ref b));

fun bel_type (PAIR(_)) = SYMBOL("pair")
  | bel_type (CHAR(_)) = SYMBOL("char")
  | bel_type (SYMBOL(_)) = SYMBOL("symbol")
  | bel_type NIL = SYMBOL("pair");

fun bel_id (PAIR(x), PAIR(y)) =
  if (x = y) then SYMBOL("t") else NIL
  | bel_id (SYMBOL(x), SYMBOL(y)) =
  if (x = y) then SYMBOL("t") else NIL
  | bel_id (CHAR(x), CHAR(y)) =
  if (x = y) then SYMBOL("t") else NIL
  | bel_id (NIL, NIL) = SYMBOL("t")
  | bel_id (_, _) = NIL;

val coin_seed = Random.rand(1,1);
val coin_gen = Random.randRange(0,1);
fun bel_coin _ =
let val v = coin_gen coin_seed in
  if (v = 0)
  then SYMBOL("t")
  else NIL
end;

fun make_symbol(str) =
  case str of
    "nil" => NIL
     |_ => SYMBOL(str);

fun drop_while (pred, ls) =
    let fun loop (ls) =
        if (pred(hd(ls)))
        then loop(tl(ls))
        else ls
    in loop(ls)
    end;

fun read_list cls =
  let fun loop (cls) =
    let val cls_ = drop_while(space_p,cls) in
      case hd(cls_) of
         #")" => (NIL,tl(cls_))
         | _ => let val (v, rest) = read_str_aux(cls_)
                    val (v2,rest2) = loop(rest)
                in (PAIR(ref (ref v,ref v2)), rest2)
                end
    end
   in loop(cls)
  end
and char_list_to_bel_string (cls) =
    let fun loop (cls) =
      if (cls = nil)
      then NIL
      else PAIR(ref (ref(CHAR(hd(cls))), ref(loop(tl(cls)))))
      in loop(cls)
      end
and read_string cls =
  let fun loop (res, cls) = 
    if (hd(cls) = #"\"")
    then (res, tl(cls))
    else loop(res@[hd(cls)], tl(cls))
  in loop([], cls)
  end
and
space_p c =
    c = #" " orelse
    c = #"\t" orelse
    c = #"\n"
and
read_symbol cls =
    let
     fun loop(cls, res) =
       if (space_p (hd(cls)) orelse hd(cls) = #")")
       then (make_symbol(implode(res)), cls)
       else loop(tl(cls), res@[hd(cls)])
    in loop(cls,[])
    end
and
read_str_aux cls =
  if (space_p(hd(cls)))
  then read_str_aux(tl(cls))
  else
    case hd(cls) of
      #"(" => read_list(tl(cls))
       | #")" => (NIL,cls)
       | _ => read_symbol(cls)


fun read_str input_str =
    read_str_aux(explode(input_str));


fun make_prim (name_string) =
  bel_join(SYMBOL("lit"), bel_join(SYMBOL("prim"), bel_join(SYMBOL(name_string),NIL)));

fun bel_eval (PAIR(expression), global_env, lexical_env) =
  bel_eval_expression(bel_car(PAIR(expression)), PAIR(expression), global_env, lexical_env)
  | bel_eval (SYMBOL("t"), global_env, lexical_env) = SYMBOL("t")
  | bel_eval (SYMBOL("nil"), global_env, lexical_env) = NIL
  | bel_eval (SYMBOL(sym), global_env, lexical_env) = NIL
  | bel_eval (bel_obj, global_env, lexical_env) = bel_obj
and bel_eval_expression (SYMBOL("quote"), expression, global_env, lexical_env) =
    bel_cadr(expression)
  |bel_eval_expression (ope, expression, global_env, lexical_env) =
    let val evaled_ope = bel_eval(ope,global_env,lexical_env) in
      evaled_ope
    end;
