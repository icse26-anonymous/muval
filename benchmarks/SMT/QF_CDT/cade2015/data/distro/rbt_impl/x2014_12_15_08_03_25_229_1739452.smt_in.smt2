;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_list_fun$ 0 )
(declare-sort A_a_option_fun$ 0 )
(declare-sort A_list_nat_fun$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_rbt_bool_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort A_b_prod_bool_fun$ 0 )
(declare-sort A_list_a_list_fun$ 0 )
(declare-sort A_a_b_prod_list_fun$ 0 )
(declare-sort A_b_prod_a_list_fun$ 0 )
(declare-sort A_b_rbt_a_b_rbt_fun$ 0 )
(declare-sort A_a_b_prod_option_fun$ 0 )
(declare-sort A_b_prod_a_option_fun$ 0 )
(declare-sort A_b_prod_list_nat_fun$ 0 )
(declare-sort A_b_prod_list_bool_fun$ 0 )
(declare-sort A_b_prod_list_a_list_fun$ 0 )
(declare-sort A_list_a_b_prod_list_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_list_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_option_fun$ 0 )
(declare-sort A_b_rbt_a_b_rbt_bool_fun_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_bool_fun_fun$ 0 )
(declare-sort A_b_prod_list_a_b_prod_list_fun$ 0 )
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))(Color$ (r$ )(b$ ))(A_b_rbt$ (empty$ )(branch$ (select$ Color$ )(selecta$ A_b_rbt$ )(selectb$ A$ )(selectc$ B$ )(selectd$ A_b_rbt$ )))(A_b_prod$ (pair$ (fst$ A$ )(snd$ B$ )))(A_b_prod_list$ (nil$a )(cons$a (hd$a A_b_prod$ )(tl$a A_b_prod_list$ )))(A_b_prod_option$ (none$ )(some$ (the$ A_b_prod$ )))(A_option$ (none$a )(some$a (the$a A$ )))(B_list$ (nil$b )(cons$b (hd$b B$ )(tl$b B_list$ )))))
(declare-fun t$ ()A_b_rbt$ )
(declare-fun uu$ ()A_a_bool_fun_fun$ )
(declare-fun uua$ ()B_b_bool_fun_fun$ )
(declare-fun uub$ ()A_b_rbt_a_b_rbt_bool_fun_fun$ )
(declare-fun zip$ (A_list$ B_list$ )A_b_prod_list$ )
(declare-fun bind$ (A_list$ A_a_b_prod_list_fun$ )A_b_prod_list$ )
(declare-fun keys$ (A_b_rbt$ )A_list$ )
(declare-fun maps$ (A_a_b_prod_list_fun$ )A_list_a_b_prod_list_fun$ )
(declare-fun null$ (A_b_prod_list$ )Bool )
(declare-fun bind$a (A_b_prod_list$ A_b_prod_a_list_fun$ )A_list$ )
(declare-fun bind$b (A_b_prod_list$ A_b_prod_a_b_prod_list_fun$ )A_b_prod_list$ )
(declare-fun bind$c (A_list$ A_a_list_fun$ )A_list$ )
(declare-fun maps$a (A_b_prod_a_list_fun$ )A_b_prod_list_a_list_fun$ )
(declare-fun maps$b (A_b_prod_a_b_prod_list_fun$ )A_b_prod_list_a_b_prod_list_fun$ )
(declare-fun maps$c (A_a_list_fun$ )A_list_a_list_fun$ )
(declare-fun null$a (A_list$ )Bool )
(declare-fun member$ (A_b_prod_list$ )A_b_prod_bool_fun$ )
(declare-fun splice$ (A_b_prod_list$ )A_b_prod_list_a_b_prod_list_fun$ )
(declare-fun entries$ (A_b_rbt$ )A_b_prod_list$ )
(declare-fun fun_app$ (A_b_rbt_bool_fun$ A_b_rbt$ )Bool )
(declare-fun list_ex$ (A_b_prod_bool_fun$ )A_b_prod_list_bool_fun$ )
(declare-fun map_rbt$ (A_a_fun$ B_b_fun$ )A_b_rbt_a_b_rbt_fun$ )
(declare-fun member$a (A_list$ )A_bool_fun$ )
(declare-fun product$ (A_list$ B_list$ )A_b_prod_list$ )
(declare-fun rel_rbt$ (A_a_bool_fun_fun$ B_b_bool_fun_fun$ )A_b_rbt_a_b_rbt_bool_fun_fun$ )
(declare-fun rotate1$ (A_b_prod_list$ )A_b_prod_list$ )
(declare-fun splice$a (A_list$ )A_list_a_list_fun$ )
(declare-fun fun_app$a (A_b_rbt_a_b_rbt_bool_fun_fun$ A_b_rbt$ )A_b_rbt_bool_fun$ )
(declare-fun fun_app$b (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$c (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$d (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$e (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$f (A_b_rbt_a_b_rbt_fun$ A_b_rbt$ )A_b_rbt$ )
(declare-fun fun_app$g (A_b_prod_list_bool_fun$ A_b_prod_list$ )Bool )
(declare-fun fun_app$h (A_list_bool_fun$ A_list$ )Bool )
(declare-fun fun_app$i (A_b_prod_bool_fun$ A_b_prod$ )Bool )
(declare-fun fun_app$j (A_b_prod_list_nat_fun$ A_b_prod_list$ )Nat$ )
(declare-fun fun_app$k (A_list_nat_fun$ A_list$ )Nat$ )
(declare-fun fun_app$l (A_a_fun$ A$ )A$ )
(declare-fun fun_app$m (B_b_fun$ B$ )B$ )
(declare-fun fun_app$n (A_b_prod_list_a_b_prod_list_fun$ A_b_prod_list$ )A_b_prod_list$ )
(declare-fun fun_app$o (A_list_a_list_fun$ A_list$ )A_list$ )
(declare-fun fun_app$p (A_list_a_b_prod_list_fun$ A_list$ )A_b_prod_list$ )
(declare-fun fun_app$q (A_b_prod_list_a_list_fun$ A_b_prod_list$ )A_list$ )
(declare-fun list_ex$a (A_bool_fun$ )A_list_bool_fun$ )
(declare-fun list_ex1$ (A_b_prod_bool_fun$ )A_b_prod_list_bool_fun$ )
(declare-fun pred_rbt$ (A_bool_fun$ B_bool_fun$ A_b_rbt$ )Bool )
(declare-fun rotate1$a (A_list$ )A_list$ )
(declare-fun list_ex1$a (A_bool_fun$ )A_list_bool_fun$ )
(declare-fun gen_length$ (Nat$ )A_b_prod_list_nat_fun$ )
(declare-fun lexordp_eq$ (A_b_prod_a_b_prod_bool_fun_fun$ A_b_prod_list$ )A_b_prod_list_bool_fun$ )
(declare-fun map_filter$ (A_a_b_prod_option_fun$ )A_list_a_b_prod_list_fun$ )
(declare-fun gen_length$a (Nat$ )A_list_nat_fun$ )
(declare-fun lexordp_eq$a (A_a_bool_fun_fun$ A_list$ )A_list_bool_fun$ )
(declare-fun map_filter$a (A_b_prod_a_option_fun$ )A_b_prod_list_a_list_fun$ )
(declare-fun map_filter$b (A_b_prod_a_b_prod_option_fun$ )A_b_prod_list_a_b_prod_list_fun$ )
(declare-fun map_filter$c (A_a_option_fun$ )A_list_a_list_fun$ )
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A_b_rbt$ ))(! (= (fun_app$ (fun_app$a uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uub$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$b (fun_app$c uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uua$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$d (fun_app$e uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uu$ ?v0 )?v1 )))):named a2 ))
(assert (! (not (not (= (keys$ t$ )nil$ ))):named a3 ))
(assert (! (not (= t$ empty$ )):named a4 ))
(assert (! (= (keys$ empty$ )nil$ ):named a5 ))
(assert (! (forall ((?v0 A_b_prod_list$ ))(=> (and (=> (= ?v0 nil$a )false )(=> (not (= ?v0 nil$a ))false ))false )):named a6 ))
(assert (! (forall ((?v0 A_list$ ))(=> (and (=> (= ?v0 nil$ )false )(=> (not (= ?v0 nil$ ))false ))false )):named a7 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ ))(pred_rbt$ ?v0 ?v1 empty$ )):named a8 ))
(assert (! (forall ((?v0 A_a_b_prod_list_fun$ ))(! (= (bind$ nil$ ?v0 )nil$a ):pattern ((bind$ nil$ ?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_b_prod_a_list_fun$ ))(! (= (bind$a nil$a ?v0 )nil$ ):pattern ((bind$a nil$a ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_list_fun$ ))(! (= (bind$b nil$a ?v0 )nil$a ):pattern ((bind$b nil$a ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (bind$c nil$ ?v0 )nil$ ):pattern ((bind$c nil$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ ))(! (= (fun_app$f (map_rbt$ ?v0 ?v1 )empty$ )empty$ ):pattern ((map_rbt$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_b_rbt$ ))(=> (and (=> (= ?v0 empty$ )false )(forall ((?v1 Color$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(=> (= ?v0 (branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))false )))false )):named a14 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(not (= empty$ (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a15 ))
(assert (! (forall ((?v0 A_b_prod_bool_fun$ ))(! (= (fun_app$g (list_ex1$ ?v0 )nil$a )false ):pattern ((list_ex1$ ?v0 )))):named a16 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$h (list_ex1$a ?v0 )nil$ )false ):pattern ((list_ex1$a ?v0 )))):named a17 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ ))(fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )empty$ )empty$ )):named a18 ))
(assert (! (forall ((?v0 A_b_prod$ ))(! (= (fun_app$i (member$ nil$a )?v0 )false ):pattern ((fun_app$i (member$ nil$a )?v0 )))):named a19 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$d (member$a nil$ )?v0 )false ):pattern ((fun_app$d (member$a nil$ )?v0 )))):named a20 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$j (gen_length$ ?v0 )nil$a )?v0 ):pattern ((gen_length$ ?v0 )))):named a21 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$k (gen_length$a ?v0 )nil$ )?v0 ):pattern ((gen_length$a ?v0 )))):named a22 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ )(?v5 Color$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(= (= (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )(branch$ ?v5 ?v6 ?v7 ?v8 ?v9 ))(and (= ?v0 ?v5 )(and (= ?v1 ?v6 )(and (= ?v2 ?v7 )(and (= ?v3 ?v8 )(= ?v4 ?v9 ))))))):named a23 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ ))(! (= (pred_rbt$ ?v0 ?v1 (branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))(and (pred_rbt$ ?v0 ?v1 ?v3 )(and (fun_app$d ?v0 ?v4 )(and (fun_app$b ?v1 ?v5 )(pred_rbt$ ?v0 ?v1 ?v6 ))))):pattern ((pred_rbt$ ?v0 ?v1 (branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))))):named a24 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ ))(! (= (fun_app$f (map_rbt$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))(branch$ ?v2 (fun_app$f (map_rbt$ ?v0 ?v1 )?v3 )(fun_app$l ?v0 ?v4 )(fun_app$m ?v1 ?v5 )(fun_app$f (map_rbt$ ?v0 ?v1 )?v6 ))):pattern ((fun_app$f (map_rbt$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))))):named a25 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 Color$ )(?v8 A_b_rbt$ )(?v9 A$ )(?v10 B$ )(?v11 A_b_rbt$ ))(! (= (fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))(branch$ ?v7 ?v8 ?v9 ?v10 ?v11 ))(and (= ?v2 ?v7 )(and (fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )?v3 )?v8 )(and (fun_app$d (fun_app$e ?v0 ?v4 )?v9 )(and (fun_app$b (fun_app$c ?v1 ?v5 )?v10 )(fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )?v6 )?v11 )))))):pattern ((fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))(branch$ ?v7 ?v8 ?v9 ?v10 ?v11 ))))):named a26 ))
(assert (! (= (rel_rbt$ uu$ uua$ )uub$ ):named a27 ))
(assert (! (forall ((?v0 Color$ )(?v1 Color$ )(?v2 A_a_bool_fun_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 A_b_rbt$ )(?v5 A_b_rbt$ )(?v6 A$ )(?v7 A$ )(?v8 B$ )(?v9 B$ )(?v10 A_b_rbt$ )(?v11 A_b_rbt$ ))(=> (and (= ?v0 ?v1 )(and (fun_app$ (fun_app$a (rel_rbt$ ?v2 ?v3 )?v4 )?v5 )(and (fun_app$d (fun_app$e ?v2 ?v6 )?v7 )(and (fun_app$b (fun_app$c ?v3 ?v8 )?v9 )(fun_app$ (fun_app$a (rel_rbt$ ?v2 ?v3 )?v10 )?v11 )))))(fun_app$ (fun_app$a (rel_rbt$ ?v2 ?v3 )(branch$ ?v0 ?v4 ?v6 ?v8 ?v10 ))(branch$ ?v1 ?v5 ?v7 ?v9 ?v11 )))):named a28 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ ))(not (fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )empty$ )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 )))):named a29 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ ))(not (fun_app$ (fun_app$a (rel_rbt$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))empty$ ))):named a30 ))
(assert (! (= (entries$ empty$ )nil$a ):named a31 ))
(assert (! (forall ((?v0 A_b_prod_list$ ))(! (= (fun_app$n (splice$ ?v0 )nil$a )?v0 ):pattern ((splice$ ?v0 )))):named a32 ))
(assert (! (forall ((?v0 A_list$ ))(! (= (fun_app$o (splice$a ?v0 )nil$ )?v0 ):pattern ((splice$a ?v0 )))):named a33 ))
(assert (! (forall ((?v0 A_a_b_prod_list_fun$ ))(! (= (fun_app$p (maps$ ?v0 )nil$ )nil$a ):pattern ((maps$ ?v0 )))):named a34 ))
(assert (! (forall ((?v0 A_b_prod_a_list_fun$ ))(! (= (fun_app$q (maps$a ?v0 )nil$a )nil$ ):pattern ((maps$a ?v0 )))):named a35 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_list_fun$ ))(! (= (fun_app$n (maps$b ?v0 )nil$a )nil$a ):pattern ((maps$b ?v0 )))):named a36 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (fun_app$o (maps$c ?v0 )nil$ )nil$ ):pattern ((maps$c ?v0 )))):named a37 ))
(assert (! (forall ((?v0 A_b_rbt$ ))(=> (and (=> (= ?v0 empty$ )false )(and (forall ((?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(=> (= ?v0 (branch$ r$ ?v1 ?v2 ?v3 ?v4 ))false ))(forall ((?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(=> (= ?v0 (branch$ b$ ?v1 ?v2 ?v3 ?v4 ))false ))))false )):named a38 ))
(assert (! (= (null$ nil$a )true ):named a39 ))
(assert (! (= (null$a nil$ )true ):named a40 ))
(assert (! (forall ((?v0 A_b_prod_list$ ))(= (= ?v0 nil$a )(null$ ?v0 ))):named a41 ))
(assert (! (forall ((?v0 A_list$ ))(= (= ?v0 nil$ )(null$a ?v0 ))):named a42 ))
(assert (! (forall ((?v0 A_b_prod_list$ ))(= (= (rotate1$ ?v0 )nil$a )(= ?v0 nil$a ))):named a43 ))
(assert (! (forall ((?v0 A_list$ ))(= (= (rotate1$a ?v0 )nil$ )(= ?v0 nil$ ))):named a44 ))
(assert (! (forall ((?v0 A_a_b_prod_option_fun$ ))(! (= (fun_app$p (map_filter$ ?v0 )nil$ )nil$a ):pattern ((map_filter$ ?v0 )))):named a45 ))
(assert (! (forall ((?v0 A_b_prod_a_option_fun$ ))(! (= (fun_app$q (map_filter$a ?v0 )nil$a )nil$ ):pattern ((map_filter$a ?v0 )))):named a46 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_option_fun$ ))(! (= (fun_app$n (map_filter$b ?v0 )nil$a )nil$a ):pattern ((map_filter$b ?v0 )))):named a47 ))
(assert (! (forall ((?v0 A_a_option_fun$ ))(! (= (fun_app$o (map_filter$c ?v0 )nil$ )nil$ ):pattern ((map_filter$c ?v0 )))):named a48 ))
(assert (! (forall ((?v0 A_b_prod_bool_fun$ ))(! (= (fun_app$g (list_ex$ ?v0 )nil$a )false ):pattern ((list_ex$ ?v0 )))):named a49 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$h (list_ex$a ?v0 )nil$ )false ):pattern ((list_ex$a ?v0 )))):named a50 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_bool_fun_fun$ )(?v1 A_b_prod_list$ ))(! (= (fun_app$g (lexordp_eq$ ?v0 nil$a )?v1 )true ):pattern ((fun_app$g (lexordp_eq$ ?v0 nil$a )?v1 )))):named a51 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_list$ ))(! (= (fun_app$h (lexordp_eq$a ?v0 nil$ )?v1 )true ):pattern ((fun_app$h (lexordp_eq$a ?v0 nil$ )?v1 )))):named a52 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_bool_fun_fun$ )(?v1 A_b_prod_list$ ))(! (= (fun_app$g (lexordp_eq$ ?v0 ?v1 )nil$a )(= ?v1 nil$a )):pattern ((lexordp_eq$ ?v0 ?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_list$ ))(! (= (fun_app$h (lexordp_eq$a ?v0 ?v1 )nil$ )(= ?v1 nil$ )):pattern ((lexordp_eq$a ?v0 ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_bool_fun_fun$ )(?v1 A_b_prod_list$ ))(fun_app$g (lexordp_eq$ ?v0 ?v1 )?v1 )):named a55 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_list$ ))(fun_app$h (lexordp_eq$a ?v0 ?v1 )?v1 )):named a56 ))
(assert (! (not (= r$ b$ )):named a57 ))
(assert (! (forall ((?v0 Color$ ))(=> (and (=> (= ?v0 r$ )false )(=> (= ?v0 b$ )false ))false )):named a58 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_bool_fun_fun$ )(?v1 A_b_prod_list$ ))(fun_app$g (lexordp_eq$ ?v0 nil$a )?v1 )):named a59 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_list$ ))(fun_app$h (lexordp_eq$a ?v0 nil$ )?v1 )):named a60 ))
(assert (! (= (rotate1$ nil$a )nil$a ):named a61 ))
(assert (! (= (rotate1$a nil$ )nil$ ):named a62 ))
(assert (! (forall ((?v0 A_b_prod_list$ ))(! (= (fun_app$n (splice$ nil$a )?v0 )?v0 ):pattern ((fun_app$n (splice$ nil$a )?v0 )))):named a63 ))
(assert (! (forall ((?v0 A_list$ ))(! (= (fun_app$o (splice$a nil$ )?v0 )?v0 ):pattern ((fun_app$o (splice$a nil$ )?v0 )))):named a64 ))
(assert (! (forall ((?v0 B_list$ ))(! (= (product$ nil$ ?v0 )nil$a ):pattern ((product$ nil$ ?v0 )))):named a65 ))
(assert (! (forall ((?v0 B_list$ ))(! (= (zip$ nil$ ?v0 )nil$a ):pattern ((zip$ nil$ ?v0 )))):named a66 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_bool_fun_fun$ )(?v1 A_b_prod$ )(?v2 A_b_prod_list$ ))(! (= (fun_app$g (lexordp_eq$ ?v0 (cons$a ?v1 ?v2 ))nil$a )false ):pattern ((lexordp_eq$ ?v0 (cons$a ?v1 ?v2 ))))):named a67 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_list$ ))(! (= (fun_app$h (lexordp_eq$a ?v0 (cons$ ?v1 ?v2 ))nil$ )false ):pattern ((lexordp_eq$a ?v0 (cons$ ?v1 ?v2 ))))):named a68 ))
(assert (! (forall ((?v0 A_b_prod_list$ )(?v1 A_b_prod_list$ )(?v2 A_b_prod_list$ ))(=> (and (= (fun_app$n (splice$ ?v0 )?v1 )?v2 )(and (forall ((?v3 A_b_prod_list$ ))(=> (and (= ?v0 nil$a )(and (= ?v1 ?v3 )(= ?v2 ?v3 )))false ))(and (forall ((?v3 A_b_prod$ )(?v4 A_b_prod_list$ ))(=> (and (= ?v0 (cons$a ?v3 ?v4 ))(and (= ?v1 nil$a )(= ?v2 (cons$a ?v3 ?v4 ))))false ))(forall ((?v3 A_b_prod$ )(?v4 A_b_prod_list$ )(?v5 A_b_prod$ )(?v6 A_b_prod_list$ ))(=> (and (= ?v0 (cons$a ?v3 ?v4 ))(and (= ?v1 (cons$a ?v5 ?v6 ))(= ?v2 (cons$a ?v3 (cons$a ?v5 (fun_app$n (splice$ ?v4 )?v6 ))))))false )))))false )):named a69 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(=> (and (= (fun_app$o (splice$a ?v0 )?v1 )?v2 )(and (forall ((?v3 A_list$ ))(=> (and (= ?v0 nil$ )(and (= ?v1 ?v3 )(= ?v2 ?v3 )))false ))(and (forall ((?v3 A$ )(?v4 A_list$ ))(=> (and (= ?v0 (cons$ ?v3 ?v4 ))(and (= ?v1 nil$ )(= ?v2 (cons$ ?v3 ?v4 ))))false ))(forall ((?v3 A$ )(?v4 A_list$ )(?v5 A$ )(?v6 A_list$ ))(=> (and (= ?v0 (cons$ ?v3 ?v4 ))(and (= ?v1 (cons$ ?v5 ?v6 ))(= ?v2 (cons$ ?v3 (cons$ ?v5 (fun_app$o (splice$a ?v4 )?v6 ))))))false )))))false )):named a70 ))
(check-sat )
;(get-unsat-core )
