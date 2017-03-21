import java.util.HashMap;

public class Options {

	public static final String version = "0.2";

	public static final String usage = 
			"********************************************************************************\n" +
					"*              FuzzSMT " + version + "                                                     *\n"  +
					"*              Fuzzing Tool for SMT-LIB 1.2 Benchmarks                         *\n" +
					"*              written by Robert Daniel Brummayer, 2009                        *\n" + 
					"********************************************************************************\n" +
					"\n" +
					"usage: fuzzsmt <logic> [option...]\n\n" +
					"  <logic> is one of the following:\n" + 
					"  QF_A, QF_AUFBV, QF_AUFLIA, QF_AX, QF_BV, QF_IDL, QF_LIA, QF_LRA,\n" + 
					"  QF_NIA, QF_NRA, QF_RDL, QF_UF, QF_UFBV, QF_UFIDL, QF_UFLIA, QF_UFLRA,\n" +
					"  QF_UFNIA, QF_UFNRA, QF_UFRDL, AUFLIA, AUFLIRA and AUFNIRA.\n" + 
					"\n" +
					"  for details about SMT see: www.smtlib.org\n" +
					"\n" +
					"  general options:\n\n" + 
					"  -h                   print usage information and exit\n" +
					"  -V                   print version and exit\n" +
					"  -seed <seed>         initialize random number generator with <seed>\n" +
					"\n" +
					"  -bool-random         generate a random boolean layer (default)\n" +
					"  -bool-and            use an n-ary AND for the boolean layer\n" +
					"  -bool-or             use an n-ary OR for the boolean layer\n" +
					"  -bool-cnf <f>        generate a boolean CNF layer\n" +
					"                       with <f> * <literals> clauses\n" +
					"\n" +
					"QF_A and QF_AX options:\n" +
					"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
					"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
					"  -mi <indices>        use min <indices> index variables      (default  1)\n" +
					"  -Mi <indices>        use max <indices> index variables      (default  5)\n" +
					"  -me <elements>       use min <elements> element variables   (default  1)\n" +
					"  -Me <elements>       use max <elements> element variables   (default  5)\n" +
					"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
					"  -Mr <reads>          use max <reads> reads                  (default 10)\n" +
					"  -mw <writes>         use min <writes> writes                (default  0)\n" +
					"  -Mw <writes>         use max <writes> writes                (default 10)\n" +
					"  -ref <refs>          set min number of references for terms\n" +
					"                       in input and main layer to <refs>      (default  1)\n" +
					"\n" +
					"QF_AUFBV options:\n" +
					"  -mv <vars>           use min <vars> bit-vector variables    (default  1)\n" +
					"  -Mv <vars>           use max <vars> bit-vector variables    (default  5)\n" +
					"  -mc <consts>         use min <const> bit-vector constants   (default  1)\n" +
					"  -Mc <consts>         use max <const> bit-vector constants   (default  2)\n" +
					"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
					"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
					"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
					"  -Mr <reads>          use max <reads> reads                  (default  5)\n" +
					"  -mw <writes>         use min <writes> writes                (default  0)\n" +
					"  -Mw <writes>         use max <writes> writes                (default  5)\n" +
					"  -mxn <n>             compare min <n> arrays for equality    (default  0)\n" +
					"  -Mxn <n>             compare max <n> arrays for equality    (default  0)\n" +
					"  -mbw <bw>            set min bit-width to <bw>              (default  1)\n" +
					"  -Mbw <bw>            set max bit-width to <bw>              (default 16)\n" +
					"  -mf <funcs>          use min <funcs> uninterpreted BV funcs (default  0)\n" +
					"  -Mf <funcs>          use max <funcs> uninterpreted BV funcs (default  0)\n" +
					"  -mp <preds>          use min <preds> uninterpreted BV preds (default  0)\n" +
					"  -Mp <preds>          use max <preds> uninterpreted BV preds (default  0)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"  -g                   do not guard BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n"+
					"  -n                   do not use BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n" +
					"  -ref <refs>          set min number of references for terms\n" + 
					"                       in input and main layer to <refs>      (default  1)\n" +
					"\n" +
					"QF_AUFLIA and AUFLIA options:\n" +
					"  -mv <vars>           use min <vars> integer variables       (default  1)\n" +
					"  -Mv <vars>           use max <vars> integer variables       (default  3)\n" +
					"  -mc <consts>         use min <const> integer constants      (default  1)\n" +
					"  -Mc <consts>         use max <const> integer constants      (default  3)\n" +
					"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
					"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
					"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
					"  -Mr <reads>          use max <reads> reads                  (default  5)\n" +
					"  -mw <writes>         use min <writes> writes                (default  0)\n" +
					"  -Mw <writes>         use max <writes> writes                (default  5)\n" +
					"  -x                   compare arrays for equality            (default no)\n" +
					"  -mfi <f>             use min <f> uninterpreted int funcs    (default  1)\n" +
					"  -Mfi <f>             use max <f> uninterpreted int funcs    (default  1)\n" +
					"  -mfar <f>            use min <f> uninterpreted array funcs  (default  1)\n" +
					"  -Mfar <f>            use max <f> uninterpreted array funcs  (default  1)\n" +
					"  -mpi <p>             use min <p> uninterpreted int preds    (default  1)\n" +
					"  -Mpi <p>             use max <p> uninterpreted int preds    (default  1)\n" +
					"  -mpar <p>            use min <p> uninterpreted array preds  (default  1)\n" +
					"  -Mpar <p>            use max <p> uninterpreted array preds  (default  1)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
					"                       bit-width is used to\n" +
					"                       restrict the constants\n" +
					"  -ref <refs>          set min number of references for terms\n" + 
					"                       in input and main layer to <refs>      (default  1)\n" +
					" AUFLIA only:\n" +
					"  -mqfi <qf>           use min <qf> quantified formulas over\n" +
					"                       integer function and predicates        (default  1)\n" +
					"  -Mqfi <qf>           use max <qf> quantified formulas over\n" +
					"                       integer function and predicates        (default  1)\n" +
					"  -mqfar <qf>          use min <qf> quantified formulas over\n" +
					"                       array function and predicates          (default  0)\n" +
					"  -Mqfar <qf>          use max <qf> quantified formulas over\n" +
					"                       array function and predicates          (default  0)\n" +
					"  -mqv <qv>            set min number of quantified\n" +
					"                       variables per quantifier to <qn>       (default  1)\n" +
					"  -Mqv <qv>            set max number of quantified\n" +
					"                       variables per quantifier to <qn>       (default  3)\n" +
					"  -mqn <qn>            set min quantifier nesting\n" +
					"                       level to <qn>                          (default  0)\n" +
					"  -Mqn <qn>            set max quantifier nesting\n" +
					"                       level to <qn>                          (default  1)\n" +
					"\n" +
					"AUFLIRA and AUFNIRA options:\n" +
					"  -mvi <vars>          use min <vars> integer variables       (default  1)\n" +
					"  -Mvi <vars>          use max <vars> integer variables       (default  2)\n" +
					"  -mvr <vars>          use min <vars> real variables          (default  1)\n" +
					"  -Mvr <vars>          use max <vars> real variables          (default  2)\n" +
					"  -mci <consts>        use min <const> integer constants      (default  1)\n" +
					"  -Mci <consts>        use max <const> integer constants      (default  3)\n" +
					"  -mcr <consts>        use min <const> real constants         (default  1)\n" +
					"  -Mcr <consts>        use max <const> real constants         (default  3)\n" +
					"  -mar1 <arrays>       use min <arrays> array1 variables      (default  1)\n" +
					"  -Mar1 <arrays>       use max <arrays> array1 variables      (default  2)\n" +
					"  -mar2 <arrays>       use min <arrays> array2 variables      (default  1)\n" +
					"  -Mar2 <arrays>       use max <arrays> array2 variables      (default  2)\n" +
					"  -mr1 <reads>         use min <reads> reads on array1 terms  (default  1)\n" +
					"  -Mr1 <reads>         use max <reads> reads on array1 terms  (default  4)\n" +
					"  -mr2 <reads>         use min <reads> reads on array2 terms  (default  1)\n" +
					"  -Mr2 <reads>         use max <reads> reads on array2 terms  (default  4)\n" +
					"  -mw1 <writes>        use min <writes> writes on array1 terms(default  0)\n" +
					"  -Mw1 <writes>        use max <writes> writes on array1 terms(default  3)\n" +
					"  -mw2 <writes>        use min <writes> writes on array2 terms(default  0)\n" +
					"  -Mw2 <writes>        use max <writes> writes on array2 terms(default  3)\n" +
					"  -x1                  compare array1 terms for equality      (default no)\n" +
					"  -x2                  compare array2 terms for equality      (default no)\n" +
					"  -mfi <f>             use min <f> uninterpreted int funcs    (default  1)\n" +
					"  -Mfi <f>             use max <f> uninterpreted int funcs    (default  1)\n" +
					"  -mfr <f>             use min <f> uninterpreted real funcs   (default  1)\n" +
					"  -Mfr <f>             use max <f> uninterpreted real funcs   (default  1)\n" +
					"  -mfar1 <f>           use min <f> uninterpreted array1 funcs (default  1)\n" +
					"  -Mfar1 <f>           use max <f> uninterpreted array1 funcs (default  1)\n" +
					"  -mfar2 <f>           use min <f> uninterpreted array2 funcs (default  1)\n" +
					"  -Mfar2 <f>           use max <f> uninterpreted array2 funcs (default  1)\n" +
					"  -mpi <p>             use min <p> uninterpreted int preds    (default  1)\n" +
					"  -Mpi <p>             use max <p> uninterpreted int preds    (default  1)\n" +
					"  -mpr <p>             use min <p> uninterpreted real preds   (default  1)\n" +
					"  -Mpr <p>             use max <p> uninterpreted real preds   (default  1)\n" +
					"  -mpar1 <p>           use min <p> uninterpreted array1 preds (default  1)\n" +
					"  -Mpar1 <p>           use max <p> uninterpreted array1 preds (default  1)\n" +
					"  -mpar2 <p>           use min <p> uninterpreted array2 preds (default  1)\n" +
					"  -Mpar2 <p>           use max <p> uninterpreted array2 preds (default  1)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
					"                       bit-width is used to\n" +
					"                       restrict the constants\n" +
					"  -mqfi <qf>           use min <qf> quantified formulas over\n" +
					"                       integer function and predicates        (default  1)\n" +
					"  -Mqfi <qf>           use max <qf> quantified formulas over\n" +
					"                       integer function and predicates        (default  1)\n" +
					"  -mqfr <qf>           use min <qf> quantified formulas over\n" +
					"                       real function and predicates           (default  1)\n" +
					"  -Mqfr <qf>           use max <qf> quantified formulas over\n" +
					"                       real function and predicates           (default  1)\n" +
					"  -mqfar1 <qf>         use min <qf> quantified formulas over\n" +
					"                       array1 function and predicates         (default  0)\n" +
					"  -Mqfar1 <qf>         use max <qf> quantified formulas over\n" +
					"                       array1 function and predicates         (default  0)\n" +
					"  -mqfar2 <qf>         use min <qf> quantified formulas over\n" +
					"                       array2 function and predicates         (default  0)\n" +
					"  -Mqfar2 <qf>         use max <qf> quantified formulas over\n" +
					"                       array2 function and predicates         (default  0)\n" +
					"  -mqv <qv>            set minimum number of quantified\n" +
					"                       variables per quantifier to <qn>       (default  1)\n" +
					"  -Mqv <qv>            set maximum number of quantified\n" +
					"                       variables per quantifier to <qn>       (default  3)\n" +
					"  -mqn <qn>            set minimum quantifier nesting\n" +
					"                       level to <qn>                          (default  0)\n" +
					"  -Mqn <qn>            set maximum quantifier nesting\n" +
					"                       level to <qn>                          (default  1)\n" +
					"  -ref <refs>          set min number of references for terms\n" + 
					"                       in input and main layer to <refs>      (default  1)\n" +
					"\n" +
					"QF_BV and QF_UFBV options:\n" +
					"  -mv <vars>           use min <vars> bit-vector variables    (default  1)\n" +
					"  -Mv <vars>           use max <vars> bit-vector variables    (default  5)\n" +
					"  -mc <consts>         use min <const> bit-vector constants   (default  1)\n" +
					"  -Mc <consts>         use max <const> bit-vector constants   (default  2)\n" +
					"  -mbw <bw>            set min bit-width to <bw>              (default  1)\n" +
					"  -Mbw <bw>            set max bit-width to <bw>              (default 16)\n" +
					"  -g                   do not guard BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n"+
					"  -n                   do not use BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n" +
					"  -ref <refs>          set min number of references for terms\n" +
					"                       in input and main layer to <refs>      (default  1)\n" +
					"\n" +
					" QF_UFBV only:\n" +
					"  -mf <funcs>          use min <funcs> uninterpreted funcs    (default  1)\n" +
					"  -Mf <funcs>          use max <funcs> uninterpreted funcs    (default  2)\n" +
					"  -mp <preds>          use min <preds> uninterpreted preds    (default  1)\n" +
					"  -Mp <preds>          use max <preds> uninterpreted preds    (default  2)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"\n" +
					"QF_IDL, QF_UFIDL, QF_RDL and QF_UFRDL options:\n" +
					"  -mv <vars>           use min <vars> variables               (default  1)\n" +
					"  -Mv <vars>           use max <vars> variables               (default  8)\n" +
					"  -mc <consts>         use min <const> integer constants      (default  1)\n" +
					"  -Mc <consts>         use max <const> integer constants      (default  6)\n" +
					"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
					"                       bit-width is used to\n" +
					"                       restrict the constants\n" +
					"  -ref <refs>          set minimum number of references\n" +  
					"                       for vars and consts to <refs>          (default  5)\n" +
					" QF_UFIDL and QF_UFRDL only:\n" +
					"  -mf <funcs>          use min <funcs> uninterpreted funcs    (default  1)\n" +
					"  -Mf <funcs>          use max <funcs> uninterpreted funcs    (default  2)\n" +
					"  -mp <preds>          use min <preds> uninterpreted preds    (default  1)\n" +
					"  -Mp <preds>          use max <preds> uninterpreted preds    (default  2)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"\n" +
					"QF_LIA, QF_UFLIA, QF_NIA, QF_UFNIA, QF_LRA,\n" +  
					"QF_UFLRA, QF_NRA and QF_UFNRA options:\n" +
					"  -mv <vars>           use min <vars> variables               (default  1)\n" +
					"  -Mv <vars>           use max <vars> variables               (default  3)\n" +
					"  -mc <consts>         use min <const> integer constants      (default  1)\n" +
					"  -Mc <consts>         use max <const> integer constants      (default  3)\n" +
					"                       in the real context, integer constants\n" +
					"                       are used, amongst others, to generate\n" +
					"                       real constants of the form (c1 / c2)\n" +
					"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
					"                       bit-width is used to\n" +
					"                       restrict the constants\n" +
					"  -ref <refs>          set minimum number of references\n" +  
					"                       for vars and consts to <refs>          (default  1)\n" +
					" QF_UFLIA, QF_UFNIA, QF_UFLRA and QF_UFNRA only:\n" +
					"  -mf <funcs>          use min <funcs> uninterpreted funcs    (default  1)\n" +
					"  -Mf <funcs>          use max <funcs> uninterpreted funcs    (default  2)\n" +
					"  -mp <preds>          use min <preds> uninterpreted preds    (default  1)\n" +
					"  -Mp <preds>          use max <preds> uninterpreted preds    (default  2)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"\n" +
					"QF_UF options:\n" +
					"  -ms <sorts>          use min <sorts> sorts                  (default  1)\n" +
					"  -Ms <sorts>          use max <sorts> sorts                  (default  3)\n" +
					"  -mv <vars>           use min <vars> variables for each sort (default  1)\n" +
					"  -Mv <vars>           use max <vars> variables for each sort (default  3)\n" +
					"  -mf <funcs>          use at least <funcs> functions         (default  5)\n" +
					"  -mp <preds>          use at least <preds> predicates        (default  5)\n" +
					"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
					"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
					"  -ref <refs>          set min number of references for terms\n" + 
					"                       in input and main layer to <refs>      (default  1)\n" +
					"\n";
	
	public static HashMap<String, Object> getDefaults(){
		HashMap<String, Object> opts = new HashMap<String, Object>();
		
		return opts;
	}
	
	public static HashMap<String, Object> getDefaultsForLogic(HashMap<String, Object> opts, SMTLogic logic){
		switch(logic){
			default:
				return getDefaults();
		}
	}
}
