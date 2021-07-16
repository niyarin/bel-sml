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
fun bel_cddr bel_pair = bel_cdr(bel_cdr(bel_pair));
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

fun bel_syn (bel_char_list) =
  let fun loop (ls, carray) =
    if (ls = NIL)
    then SYMBOL(implode(carray))
    else let val CHAR(c) = bel_car(ls)
         in
            loop(bel_cdr(ls), carray@[c])
         end
  in
    loop (bel_char_list, [])
  end

fun bel_list2(a, b) = bel_join(a, bel_join(b, NIL));
fun bel_list3(a, b, c) = bel_join(a, bel_list2(b, c));
fun bel_list4(a, b, c, d) = bel_join(a,bel_list3(b, c, d));
fun bel_list5(a, b, c, d, e) = bel_join(a,bel_list4(b, c, d, e));

fun bel_reverse_with_tail(ls,tail) =
  let fun loop (ls, res) =
    if (ls = NIL)
    then res
    else loop (bel_cdr(ls), bel_join(bel_car(ls), res))
  in loop(ls, tail)
  end

fun bel_reverse(ls) = bel_reverse_with_tail(ls, NIL);

fun bel_concatenate(ls) =
let val head_pair = bel_join(NIL,NIL)
    val tconc = bel_join(head_pair, head_pair)
    fun add_val_to_tconc(NIL, tconc) = NIL
      | add_val_to_tconc(ls, tconc) =
      (bel_xdr(bel_cdr(tconc), bel_join(bel_car(ls),NIL));
       bel_xdr(tconc, bel_cddr(tconc));
       add_val_to_tconc(bel_cdr(ls), tconc))
    fun concatenate_aux(ls, tconc) =
      if (bel_cdr(ls) = NIL)
      then (bel_xdr(bel_cdr(tconc), bel_car(ls)); bel_cdr(bel_car(tconc)))
      else (add_val_to_tconc(bel_car(ls), tconc); concatenate_aux(bel_cdr(ls),tconc))
in concatenate_aux(ls, tconc)
end

fun make_prim (name_string) =
  bel_join(SYMBOL("lit"), bel_join(SYMBOL("prim"), bel_join(SYMBOL(name_string),NIL)));

fun bel_obj_to_sml_str (bel_obj) =
    bel_obj_to_sml_str_aux(bel_obj, [])
and search_memo (obj, memo) =
  let fun loop ([], idx) = ~1
        | loop (tgt::rest, idx) =
            if (tgt = obj)
            then idx
            else loop(rest, idx+1)
  in loop(memo, 0)
  end
and bel_obj_to_sml_str_aux (NIL, _) =
    "nil"
  | bel_obj_to_sml_str_aux(SYMBOL(sym), memo_array) =
    sym
  | bel_obj_to_sml_str_aux(CHAR(c), memo_array) = "\\" ^ implode([c])
  | bel_obj_to_sml_str_aux(pair, memo_array) =
     let val memo_idx = search_memo(pair, memo_array) in
       if (memo_idx = ~1)
       then "("
            ^ bel_obj_to_sml_str_aux(bel_car(pair), memo_array@[pair])
            ^ " . "
            ^ bel_obj_to_sml_str_aux(bel_cdr(pair), memo_array@[pair])
            ^ ")"
       else "#" ^ Int.toString(memo_idx)
     end

fun bel_print (obj) = print(bel_obj_to_sml_str(obj));

(*一部のSYMBOL("concatenate")みたいなのをlitにかえる*)
fun quasi_quote_traverse obj =
let val list_lit = make_prim("list")
    val join_lit = make_prim("join")
    val concatenate_lit = make_prim("concatenate")
  fun quasi_quote_traverse_internal(pair as PAIR(_)) =
          bel_list2(concatenate_lit ,bel_join(list_lit, quasi_quote_traverse_aux(pair)))
    | quasi_quote_traverse_internal(other) =
          bel_list2(SYMBOL("quote"), other)
  and quasi_quote_traverse_aux(ls as PAIR(_)) =
    (case bel_car(ls) of
        pair as PAIR(_) =>
            (case bel_car(pair) of
                  SYMBOL("unquote") =>
                  bel_join(bel_list3(join_lit,bel_cadr(pair),NIL),
                           quasi_quote_traverse_aux(bel_cdr(ls)))
                  |SYMBOL("unquote-splicing") =>
                  bel_join(bel_cadr(pair),quasi_quote_traverse_aux(bel_cdr(ls)))
                  |_ =>
                  bel_join(bel_list3(join_lit,quasi_quote_traverse_internal(pair),NIL),quasi_quote_traverse_aux(bel_cdr(ls))))
        |_ => bel_join(bel_list2(SYMBOL("quote"),bel_join(bel_car(ls), NIL)),
                       quasi_quote_traverse_aux(bel_cdr(ls))))
  | quasi_quote_traverse_aux(_) = NIL
in quasi_quote_traverse_internal(obj)
end;

fun map_add_quote (NIL) = NIL
  |map_add_quote  (ls) = bel_join(bel_list2(SYMBOL("quote"), bel_car(ls)),
                                      map_add_quote(bel_cdr(ls)));
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
         #"." => let val (v, rest) = read_str_aux(tl(cls_))
                     val cls__ = tl(rest) (*remove right paren*)
                 in (v, cls__)
                 end
         | #")" => (NIL,tl(cls_))
         | _ => let val (v, rest) = read_str_aux(cls_)
                    val (v2,rest2) = loop(rest)
                in (bel_join(v, v2), rest2)
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
    then (char_list_to_bel_string(res), tl(cls))
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
      | #"'" =>
          let val (quote_body,next_cls) = read_str_aux(tl(cls)) in
           (bel_join(SYMBOL("quote"), bel_join(quote_body, NIL)), next_cls)
          end
      | #"`" =>
          let val (body,next_cls) = read_str_aux(tl(cls)) in
           (bel_join(SYMBOL("quasiquote"), bel_join(body, NIL)), next_cls)
          end
      | #"," =>
          let val second = hd(tl(cls))
          in if (second = #"@")
             then
               let val (body,next_cls) = read_str_aux(tl(tl(cls))) in
                 (bel_join(SYMBOL("unquote-splicing"),
                           bel_join(body, NIL)), next_cls)
                end
             else
                let val (body,next_cls) = read_str_aux(tl(cls)) in
                 (bel_join(SYMBOL("unquote"), bel_join(body, NIL)), next_cls)
                end
          end
      | #"\\" => (CHAR(hd(tl(cls))), tl(tl(cls)))
      | #")" => (NIL,cls)
      | #"\"" => read_string(tl(cls))
      | _ => read_symbol(cls)


fun read_str input_str =
    read_str_aux(explode(input_str));


fun make_prims (name_string_list) =
  let fun loop (name_list) = 
  if (name_list = nil)
  then NIL
  else bel_join(bel_join(SYMBOL(hd(name_list)), make_prim(hd(name_list))), loop(tl(name_list)))
  in loop(name_string_list)
end;

fun make_default_global (_) =
  make_prims(["id", "join", "car", "cdr", "type",
              "xar", "xdr", "coin", "sym"]);

fun bel_assq (PAIR(p), bel_obj) =
    if (bel_caar(PAIR(p)) = bel_obj)
    then bel_car(PAIR(p))
    else bel_assq(bel_cdr(PAIR(p)), bel_obj)
  |bel_assq (_, _) = NIL;

fun bel_last_pair (PAIR(ls)) =
    if (bel_cdr(PAIR(ls)) = NIL)
    then PAIR(ls)
    else bel_last_pair(bel_cdr(PAIR(ls)))
  | bel_last_pair(_) = NIL;

fun bel_update_alist (als, key, v) =(*alsがNILであってはならない*)
    let val apair = bel_assq(als, key) in
      if (apair = NIL)
      then bel_xdr(bel_last_pair(als),bel_join(bel_join(key, v), NIL))
      else bel_xdr(apair, v)
    end

fun bel_make_local_env (formals, args, tail) =
    let fun loop (formals, args, res) = 
        if (formals = NIL)
        then res
        else
          case formals of
            SYMBOL(_) => bel_join(bel_join(formals, args), res)
             | _ => loop(bel_cdr(formals), bel_cdr(args),
                         bel_join(bel_join(bel_car(formals), bel_car(args)), res))
    in
      loop (formals, args, tail)
    end

exception BelUnknownPrimitive;
exception BelUnknownLit;

fun bel_eval_stack(PAIR(expression), stack, next,global_env, lexical_env) =
      bel_eval_expression(bel_car(PAIR(expression)), PAIR(expression),
                          stack, next, global_env, lexical_env)
  | bel_eval_stack (SYMBOL("t"), stack, next, global_env, lexical_env) =
      bel_val_push(SYMBOL("t"), stack, global_env, lexical_env)
  | bel_eval_stack (SYMBOL("nil"), stack, next, global_env, lexical_env) =
      bel_val_push(NIL, stack, global_env, lexical_env)
  | bel_eval_stack (SYMBOL(sym), stack, next, global_env, lexical_env) =
    let val hit_local = bel_assq(lexical_env, SYMBOL(sym))
    in
      if (hit_local = NIL)
      then bel_val_push(bel_cdr(bel_assq(global_env, SYMBOL(sym))),
                        stack, global_env, lexical_env)
      else bel_val_push(bel_cdr(hit_local),
                        stack, global_env, lexical_env)
    end
  | bel_eval_stack (bel_obj, stack, next, global_env, lexical_env) =
      bel_val_push(bel_obj, stack, global_env, lexical_env)
and bel_val_push(value, NIL,  global_env, lexical_env) = value
  | bel_val_push(value, stack_pair, global_env, lexical_env) =
      let val stack_cell = bel_car(stack_pair)
          val expression = bel_car(stack_cell)
          val evaled = bel_cadr(stack_cell)
          val next = bel_caddr(stack_cell)
      in bel_eval_stack(expression, bel_cdr(stack_pair), (bel_join(value, evaled), next), global_env, lexical_env)
      end
and bel_contain_macro_in_evaled_p (evaled) =
    bel_cdr(evaled) = NIL andalso
    bel_caar(evaled) = SYMBOL("lit") andalso
    bel_cadr(bel_car(evaled)) = SYMBOL("mac")
and bel_eval_expression (CHAR(_), expression, stack, next, global_env, lexical_env) =
      bel_val_push(expression , stack, global_env, lexical_env)
  |bel_eval_expression (SYMBOL("quote"), expression, stack, next, global_env, lexical_env) =
      bel_val_push(bel_cadr(expression), stack, global_env, lexical_env)
  | bel_eval_expression (SYMBOL("lit"), expression, stack, next, global_env, lexical_env) =
      bel_val_push(expression, stack, global_env, lexical_env)
  | bel_eval_expression (SYMBOL("set"), expression, stack, (NIL, NIL), global_env, lexical_env) =
      bel_eval_expression (SYMBOL("set"), expression, stack, (NIL, bel_cdr(expression)), global_env, lexical_env)
  | bel_eval_expression (SYMBOL("set"), expression, stack, (evaled, NIL), global_env, lexical_env) =
        (if (evaled = NIL) then NIL else bel_update_alist(global_env, bel_cadr(evaled), bel_car(evaled));
         bel_val_push(NIL, stack, global_env, lexical_env))
  | bel_eval_expression (SYMBOL("set"), expression, stack, (evaled, next), global_env, lexical_env) =
      (if (evaled = NIL) then NIL else bel_update_alist(global_env, bel_cadr(evaled), bel_car(evaled));
       bel_eval_stack(bel_cadr(next), bel_join(bel_list3(expression, bel_join(bel_car(next), NIL), bel_cddr(next)), stack),
                     (NIL, NIL), global_env, lexical_env))
  | bel_eval_expression (SYMBOL("if"), expression, stack, (NIL, NIL), global_env, lexical_env) =
         bel_eval_stack(bel_cadr(expression), bel_join(bel_list3(expression, NIL, NIL), stack),
                        (NIL, NIL), global_env, lexical_env)
  | bel_eval_expression (SYMBOL("if"), expression, stack, (evaled, NIL), global_env, lexical_env) =
        if (bel_car(evaled) = NIL)
        then bel_eval_stack(bel_cadr(bel_cddr(expression)), stack, (NIL, NIL), global_env,lexical_env)
        else bel_eval_stack(bel_cadr(bel_cdr(expression)), stack, (NIL, NIL), global_env,lexical_env)
  | bel_eval_expression(SYMBOL("def"), expression, stack, (NIL,NIL), global_env, lexical_env) =
        bel_eval_stack(bel_list3(SYMBOL("set"), bel_cadr(expression),
                                 bel_list5(SYMBOL("lit"), SYMBOL("clo"), NIL,
                                 bel_cadr(bel_cdr(expression)),bel_cadr(bel_cddr(expression)))),
                       stack, (NIL, NIL), global_env, lexical_env)
  | bel_eval_expression(SYMBOL("mac"), expression, stack, (NIL,NIL), global_env, lexical_env) =
        bel_eval_stack(bel_list3(SYMBOL("set"), bel_cadr(expression),
                                 bel_list3(SYMBOL("lit"), SYMBOL("mac"),
                                 bel_list5(SYMBOL("lit"), SYMBOL("clo"), NIL,
                                 bel_cadr(bel_cdr(expression)),bel_cadr(bel_cddr(expression))))),
                       stack, (NIL, NIL), global_env, lexical_env)
  | bel_eval_expression (SYMBOL("apply"), expression, stack, (NIL, NIL), global_env, lexical_env) =
        bel_eval_stack(bel_caddr(expression), bel_join(bel_list3(expression, NIL, bel_cddr(bel_cdr(expression))), stack),
                      (NIL,  NIL), global_env,lexical_env)
  | bel_eval_expression( SYMBOL("quasiquote"), expression, stack, (NIL, NIL), global_env, lexical_env) =
        bel_eval_stack(quasi_quote_traverse(bel_cadr(expression)), stack, (NIL, NIL), global_env, lexical_env)
  | bel_eval_expression (SYMBOL("apply"), expression, stack, (evaled, NIL), global_env, lexical_env) =
       bel_eval_stack( bel_join(bel_cadr(expression), map_add_quote(bel_reverse_with_tail(bel_cdr(evaled), bel_car(evaled)))),
                       stack,(NIL, NIL), global_env, lexical_env)
  | bel_eval_expression (SYMBOL("apply"), expression, stack, (evaled, next), global_env, lexical_env) =
        bel_eval_stack(bel_car(next), bel_join(bel_list3(expression, evaled, bel_cdr(next)), stack),
                       (NIL,  NIL), global_env,lexical_env)
  | bel_eval_expression (SYMBOL("ccc"), expression, stack,
                         next, global_env, lexical_env) =
     let val cont = bel_list4(SYMBOL("lit"),
                              SYMBOL("cont"),
                              stack,
                              lexical_env)
     in bel_join(bel_cadr(expression),
                 bel_join(bel_list2(SYMBOL("quote"), cont),NIL))
     end
  |bel_eval_expression (operator, expression, stack, (NIL, NIL) , global_env, lexical_env) =
    bel_eval_expression (operator, expression, stack, (NIL, expression) , global_env, lexical_env)
  |bel_eval_expression (operator, expression, stack, (evaled, NIL) , global_env, lexical_env) =
    (* To check lit*)
    let val evaled = bel_reverse( evaled) in
      case bel_cadr(bel_car(evaled)) of
         SYMBOL("prim") => bel_eval_prim(bel_caddr(bel_car(evaled)), bel_cdr(evaled), stack, global_env, lexical_env)
         |SYMBOL("clo") =>
             let val clo = bel_car(evaled)
                 val clo_env = bel_caddr(clo)
                 val formals = bel_caddr(bel_cdr(clo))
                 val body = bel_caddr(bel_cddr(clo))
             in
               bel_eval_stack(body, stack, (NIL, NIL),global_env,
                              bel_make_local_env(formals, bel_cdr(evaled), clo_env))
             end
         |_ =>
             let val SYMBOL(sym) = bel_cadr(bel_car(evaled))
             in (print(sym);print("\n"); raise BelUnknownLit)
             end
    end
  |bel_eval_expression (operator, expression, stack, (evaled, next) , global_env, lexical_env) =
   if (bel_contain_macro_in_evaled_p(evaled))
   then
        let val macro = bel_car(evaled)
            val quoted_eval1 = bel_join(bel_caddr(macro), map_add_quote(next))
            val quoted_eval2 = bel_eval_stack(quoted_eval1, NIL, (NIL, NIL), global_env, NIL)
            in bel_eval_stack(quoted_eval2, stack, (NIL, NIL), global_env, lexical_env)
        end
   else
    bel_eval_stack(bel_car(next), bel_join(bel_list3(expression, evaled, bel_cdr(next)), stack),
                  (NIL, NIL), global_env, lexical_env)
and bel_eval_prim(ope, evaled_operands, stack, global_env, lexical_env) =
      case ope of
           SYMBOL("id") =>
             bel_val_push(bel_id(bel_car(evaled_operands),bel_cadr(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("join") =>
             bel_val_push(bel_join(bel_car(evaled_operands),bel_cadr(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("car") =>
             bel_val_push(bel_car(bel_car(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("cdr") =>
             bel_val_push(bel_cdr(bel_car(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("type") =>
             bel_val_push(bel_type(bel_car(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("xar") =>
             bel_val_push(bel_xar(bel_car(evaled_operands),bel_cadr(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("xdr") =>
             bel_val_push(bel_xdr(bel_car(evaled_operands),bel_cadr(evaled_operands)),
                          stack, global_env, lexical_env)
           |SYMBOL("coin") =>
             bel_val_push(bel_coin(nil),
                          stack, global_env, lexical_env)
           |SYMBOL("sym") =>
            bel_val_push(bel_syn(bel_car(evaled_operands)),
                         stack, global_env, lexical_env)
           |SYMBOL("concatenate") =>
            bel_val_push(bel_concatenate(bel_car(evaled_operands)),
                         stack, global_env, lexical_env)
            |SYMBOL("list") => bel_val_push(evaled_operands,stack, global_env, lexical_env)
           |_ => raise  BelUnknownPrimitive;

fun bel_eval_simple(expression) =
  let val global = make_default_global(nil)
      in bel_eval_stack(expression, NIL, (NIL, NIL) , global, NIL)
  end;


fun simple_repl_loop env =(*ECHO REPL*)
    (print(">");
     case TextIO.inputLine TextIO.stdIn of
     SOME line =>
     let val expression = #1(read_str(line))
         val evaled = bel_eval_stack(expression, NIL, (NIL, NIL) , env, NIL)
     in (print(bel_obj_to_sml_str(evaled));print("\n");simple_repl_loop(env))
     end
     |NONE => ())
and bel_simple_repl _ = simple_repl_loop(make_default_global(nil));
