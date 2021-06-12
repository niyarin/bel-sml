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
fun bel_caar bel_pair = bel_car(bel_car(bel_pair));
fun bel_caddr bel_pair = bel_cadr(bel_cdr(bel_pair));

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

fun make_prims (name_string_list) =
  let fun loop (name_list) = 
  if (name_list = nil)
  then NIL
  else bel_join(bel_join(SYMBOL(hd(name_list)), make_prim(hd(name_list))), loop(tl(name_list)))
  in loop(name_string_list)
end;

fun make_default_global (_) =
  make_prims(["id", "join", "car", "cdr", "type", "xar", "xdr", "coin"]);

fun bel_assq (PAIR(p), bel_obj) =
    if (bel_caar(PAIR(p)) = bel_obj)
    then bel_car(PAIR(p))
    else bel_assq(bel_cdr(PAIR(p)), bel_obj)
  |bel_assq (_, _) = NIL;

fun bel_eval (PAIR(expression), global_env, lexical_env) =
  bel_eval_expression(bel_car(PAIR(expression)), PAIR(expression), global_env, lexical_env)
  | bel_eval (SYMBOL("t"), global_env, lexical_env) = SYMBOL("t")
  | bel_eval (SYMBOL("nil"), global_env, lexical_env) = NIL
  | bel_eval (SYMBOL(sym), global_env, lexical_env) =
      bel_cdr(bel_assq(global_env, SYMBOL(sym)))(*WIP*)
  | bel_eval (bel_obj, global_env, lexical_env) = bel_obj
and bel_eval_expression (SYMBOL("quote"), expression, global_env, lexical_env) =
    bel_cadr(expression)
  |bel_eval_expression (SYMBOL("lit"), expression, global_env, lexical_env) = expression
  |bel_eval_expression (operator, expression, global_env, lexical_env) =
    let val evaled_operator = bel_eval(operator,global_env,lexical_env) in
      if (bel_car(evaled_operator) = SYMBOL("lit"))
      then
        case bel_cadr(evaled_operator) of
           SYMBOL("prim") =>
           bel_eval_prim(bel_caddr(evaled_operator),expression, global_env, lexical_env)
           |_ => NIL
      else NIL
    end
and bel_map_eval(PAIR(bel_pair), global_env, lexical_env) =
      bel_join(bel_eval(bel_car(PAIR(bel_pair)), global_env, lexical_env),
               bel_map_eval(bel_cdr(PAIR(bel_pair)), global_env, lexical_env))
  | bel_map_eval(_,_,_) = NIL
and bel_eval_prim(ope, expression, global_env, lexical_env) =
    let val evaled_operands =
        bel_map_eval(bel_cdr(expression),global_env, lexical_env)
    in
      case ope of
           SYMBOL("id") => bel_id(bel_car(evaled_operands),bel_cadr(evaled_operands))
           |SYMBOL("join") => bel_join(bel_car(evaled_operands),bel_cadr(evaled_operands))
           |SYMBOL("car") => bel_car(bel_car(evaled_operands))
           |SYMBOL("cdr") => bel_cdr(bel_car(evaled_operands))
           |SYMBOL("type") => bel_type(bel_car(evaled_operands))
           |SYMBOL("xar") => bel_xar(bel_car(evaled_operands),bel_cadr(evaled_operands))
           |SYMBOL("xdr") => bel_xdr(bel_car(evaled_operands),bel_cadr(evaled_operands))
           |SYMBOL("coin") => bel_coin(nil)
           |_ => ope
    end;
