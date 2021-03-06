(* Delphin Load Script for poly/ML
 * Note that this has been compiled with Poly/ML 5.0 Release
 *)

val print = TextIO.print;

PolyML.Compiler.debug := false;
use "twelf/src/compat/array.sig";
use "twelf/src/compat/vector.sig";
use "twelf/src/compat/path.sig";
use "twelf/src/compat/substring.sig";
use "twelf/src/compat/text-io.sig";
use "twelf/src/compat/timer.sig";
use "twelf/src/compat/compat.sig";
use "twelf/src/compat/compat.fun";
use "twelf/src/compat/compat.sml";
use "twelf/src/timing/timing.sml";
use "twelf/src/timing/timers.sig";
use "twelf/src/timing/timers.fun";
use "twelf/src/timing/timers.sml";
use "twelf/src/global/global.sig";
use "twelf/src/global/global.sml";
use "twelf/src/lambda/fgnopn.sig";
use "twelf/src/lambda/fgnopntable.fun";
PolyML.Compiler.debug := true;
use "twelf/src/lambda/intsyn.sig";
use "twelf/src/lambda/intsyn.fun";
use "twelf/src/lambda/whnf.sig";
use "twelf/src/lambda/whnf.fun";
use "twelf/src/lambda/conv.sig";
use "twelf/src/lambda/conv.fun";
PolyML.Compiler.debug := false;
use "twelf/src/table/table.sig";
use "twelf/src/table/hash-table.sml";
use "twelf/src/table/string-hash.sig";
use "twelf/src/table/string-hash.sml";
use "twelf/src/table/red-black-tree.fun";
use "twelf/src/table/sparse-array.sig";
use "twelf/src/table/sparse-array.fun";
use "twelf/src/table/sparse-array2.sig";
use "twelf/src/table/sparse-array2.fun";
use "twelf/src/table/table.sml";
use "twelf/src/order/order.sig";
use "twelf/src/order/order.fun";
use "twelf/src/order/order.sml";
use "twelf/src/lambda/tomega.sig";
use "twelf/src/lambda/tomega.fun";
use "twelf/src/lambda/tomega.sml";
use "twelf/src/paths/paths.sig";
use "twelf/src/paths/paths.fun";
use "twelf/src/paths/origins.sig";
use "twelf/src/paths/origins.fun";
use "twelf/src/paths/paths.sml";
use "twelf/src/table/queue.sig";
use "twelf/src/table/queue.sml";
use "twelf/src/index/index.sig";
use "twelf/src/index/index.fun";
use "twelf/src/index/index-skolem.fun";
use "twelf/src/index/index.sml";
PolyML.Compiler.debug := true;
use "twelf/src/trail/trail.sig";
use "twelf/src/trail/notrail.sml";
use "twelf/src/trail/trail.sml";
use "twelf/src/lambda/constraints.sig";
use "twelf/src/lambda/constraints.fun";
use "twelf/src/names/names.sig";
use "twelf/src/names/names.fun";
use "twelf/src/subordinate/intset.sml";
use "twelf/src/subordinate/subordinate.sig";
use "twelf/src/subordinate/subordinate.fun";
use "twelf/src/lambda/unify.sig";
use "twelf/src/lambda/unify.fun";
use "twelf/src/lambda/abstract.sig";
use "twelf/src/lambda/abstract.fun";
use "twelf/src/lambda/approx.sig";
use "twelf/src/lambda/approx.fun";
use "twelf/src/lambda/lambda.sml";
PolyML.Compiler.debug := false;
use "twelf/src/style/style.sig";
use "twelf/src/style/style.fun";
use "twelf/src/style/style.sml";
use "twelf/src/stream/stream.sml";
use "twelf/src/frontend/lexer.sig";
use "twelf/src/frontend/lexer.fun";
use "twelf/src/frontend/twelf.sig";
use "twelf/src/formatter/formatter.sig";
use "twelf/src/formatter/formatter.fun";
use "twelf/src/formatter/formatter.sml";
use "twelf/src/print/print-xml.sig";
use "twelf/src/print/print-xml.fun";
use "twelf/src/print/print-omdoc.fun";
use "twelf/src/print/print-twega.sig";
use "twelf/src/print/print-twega.fun";
use "twelf/src/print/symbol.sig";
use "twelf/src/print/symbol.fun";
use "twelf/src/print/print.sig";
use "twelf/src/print/print.fun";
use "twelf/src/print/clause-print.sig";
use "twelf/src/print/clause-print.fun";
use "twelf/src/print/print.sml";
use "twelf/src/typecheck/strict.sig";
use "twelf/src/typecheck/strict.fun";
use "twelf/src/typecheck/typecheck.sig";
use "twelf/src/typecheck/typecheck.fun";
use "twelf/src/typecheck/typecheck.sml";
use "twelf/src/modes/modesyn.sml";
use "twelf/src/modes/modetable.sig";
use "twelf/src/modes/modetable.fun";
use "twelf/src/modes/modedec.sig";
use "twelf/src/modes/modedec.fun";
use "twelf/src/modes/modecheck.sig";
use "twelf/src/modes/modecheck.fun";
use "twelf/src/modes/modeprint.sig";
use "twelf/src/modes/modeprint.fun";
use "twelf/src/modes/modes.sml";
use "twelf/src/tabling/tabledsyn.sig";
use "twelf/src/tabling/tabledsyn.fun";
use "twelf/src/tabling/tabled.sml";
use "twelf/src/solvers/cs-manager.sig";
use "twelf/src/solvers/cs-manager.fun";
use "twelf/src/domains/integers.sig";
use "twelf/src/domains/integers.fun";
use "twelf/src/domains/field.sig";
use "twelf/src/domains/ordered-field.sig";
use "twelf/src/domains/rationals.sig";
use "twelf/src/domains/rationals.fun";
use "twelf/src/domains/integers-mod.fun";
use "twelf/src/domains/domains.sml";
use "twelf/src/solvers/cs.sig";
use "twelf/src/solvers/cs-eq-field.sig";
use "twelf/src/solvers/cs-eq-field.fun";
use "twelf/src/solvers/cs-ineq-field.fun";
use "twelf/src/solvers/cs-eq-strings.fun";
use "twelf/src/solvers/cs-eq-bools.fun";
use "twelf/src/solvers/cs-eq-integers.sig";
use "twelf/src/solvers/cs-eq-integers.fun";
use "twelf/src/solvers/cs-ineq-integers.fun";
use "twelf/src/solvers/cs-integers-word.fun";
use "twelf/src/solvers/solvers.sml";
use "twelf/src/terminate/checking.sig";
use "twelf/src/terminate/checking.fun";
use "twelf/src/terminate/reduces.sig";
use "twelf/src/terminate/reduces.fun";
use "twelf/src/terminate/terminate.sml";
use "twelf/src/thm/thmsyn.sig";
use "twelf/src/thm/thmsyn.fun";
use "twelf/src/thm/thmprint.sig";
use "twelf/src/thm/thmprint.fun";
use "twelf/src/thm/thm.sig";
use "twelf/src/thm/thm.fun";
use "twelf/src/thm/thm.sml";
use "twelf/src/compile/compsyn.sig";
use "twelf/src/compile/compsyn.fun";
use "twelf/src/compile/cprint.sig";
use "twelf/src/compile/cprint.fun";
use "twelf/src/compile/compile.sig";
use "twelf/src/compile/compile.fun";
use "twelf/src/compile/assign.sig";
use "twelf/src/compile/assign.fun";
use "twelf/src/compile/compile.sml";
use "twelf/src/opsem/absmachine.sig";
use "twelf/src/opsem/absmachine.fun";
use "twelf/src/opsem/abstract.sig";
use "twelf/src/opsem/abstract.fun";
use "twelf/src/opsem/index.sig";
use "twelf/src/opsem/index.fun";
use "twelf/src/opsem/tabled.sig";
use "twelf/src/opsem/tabled.fun";
use "twelf/src/opsem/ptrecon.sig";
use "twelf/src/opsem/ptrecon.fun";
use "twelf/src/opsem/trace.sig";
use "twelf/src/opsem/trace.fun";
use "twelf/src/opsem/tmachine.fun";
use "twelf/src/opsem/swmachine.fun";
use "twelf/src/opsem/opsem.sml";
use "twelf/src/m2/meta-global.sig";
use "twelf/src/m2/meta-global.sml";
use "twelf/src/table/ring.sig";
use "twelf/src/table/ring.sml";
use "twelf/src/m2/metasyn.sig";
use "twelf/src/m2/metasyn.fun";
use "twelf/src/m2/meta-abstract.sig";
use "twelf/src/m2/meta-abstract.fun";
use "twelf/src/m2/meta-print.sig";
use "twelf/src/m2/meta-print.fun";
use "twelf/src/m2/init.sig";
use "twelf/src/m2/init.fun";
use "twelf/src/m2/search.sig";
use "twelf/src/m2/search.fun";
use "twelf/src/m2/lemma.sig";
use "twelf/src/m2/lemma.fun";
use "twelf/src/m2/splitting.sig";
use "twelf/src/m2/splitting.fun";
use "twelf/src/m2/filling.sig";
use "twelf/src/m2/filling.fun";
use "twelf/src/m2/recursion.sig";
use "twelf/src/m2/recursion.fun";
use "twelf/src/m2/qed.sig";
use "twelf/src/m2/qed.fun";
use "twelf/src/m2/strategy.sig";
use "twelf/src/m2/strategy.fun";
use "twelf/src/m2/prover.sig";
use "twelf/src/m2/prover.fun";
use "twelf/src/m2/mpi.sig";
use "twelf/src/m2/mpi.fun";
use "twelf/src/m2/skolem.sig";
use "twelf/src/m2/skolem.fun";
use "twelf/src/m2/m2.sml";
use "twelf/src/modules/modsyn.sig";
use "twelf/src/modules/modsyn.fun";
use "twelf/src/modules/modules.sml";
use "twelf/src/heuristic/heuristic.sig";
use "twelf/src/heuristic/heuristic.sum.fun";
use "twelf/src/meta/global.sig";
use "twelf/src/meta/funsyn.sig";
use "twelf/src/meta/funsyn.fun";
use "twelf/src/meta/statesyn.sig";
use "twelf/src/meta/init.sig";
use "twelf/src/meta/strategy.sig";
use "twelf/src/meta/relfun.sig";
use "twelf/src/meta/prover.fun";
use "twelf/src/meta/funprint.sig";
use "twelf/src/meta/print.sig";
use "twelf/src/meta/print.fun";
use "twelf/src/meta/filling.sig";
use "twelf/src/meta/data.sig";
use "twelf/src/meta/splitting.sig";
use "twelf/src/meta/recursion.sig";
use "twelf/src/meta/inference.sig";
use "twelf/src/meta/strategy.fun";
use "twelf/src/meta/statesyn.fun";
use "twelf/src/meta/funtypecheck.sig";
use "twelf/src/meta/uniquesearch.sig";
use "twelf/src/meta/inference.fun";
use "twelf/src/meta/abstract.sig";
use "twelf/src/meta/splitting.fun";
use "twelf/src/meta/uniquesearch.fun";
use "twelf/src/meta/search.sig";
use "twelf/src/meta/search.fun";
use "twelf/src/meta/recursion.fun";
use "twelf/src/meta/mpi.sig";
use "twelf/src/meta/mpi.fun";
use "twelf/src/meta/data.fun";
use "twelf/src/meta/global.fun";
use "twelf/src/meta/filling.fun";
use "twelf/src/meta/init.fun";
use "twelf/src/meta/abstract.fun";
use "twelf/src/meta/funnames.sig";
use "twelf/src/meta/funnames.fun";
use "twelf/src/meta/funprint.fun";
use "twelf/src/meta/weaken.sig";
use "twelf/src/meta/weaken.fun";
use "twelf/src/meta/funweaken.sig";
use "twelf/src/meta/funweaken.fun";
use "twelf/src/meta/funtypecheck.fun";
use "twelf/src/meta/relfun.fun";
use "twelf/src/meta/meta.sml";
use "twelf/src/worldcheck/worldsyn.sig";
use "twelf/src/worldcheck/worldsyn.fun";
use "twelf/src/worldcheck/worldify.sig";
use "twelf/src/worldcheck/worldify.fun";
use "twelf/src/worldcheck/worldprint.sig";
use "twelf/src/worldcheck/worldprint.fun";
use "twelf/src/worldcheck/worldcheck.sml";
use "twelf/src/unique/unique.sig";
use "twelf/src/unique/unique.fun";
use "twelf/src/unique/unique.sml";
use "twelf/src/cover/cover.sig";
use "twelf/src/cover/cover.fun";
use "twelf/src/cover/total.sig";
use "twelf/src/cover/total.fun";
use "twelf/src/cover/cover.sml";
use "twelf/src/tomega/abstract.sig";
use "twelf/src/tomega/abstract.fun";
use "twelf/src/tomega/tomegaprint.sig";
use "twelf/src/tomega/tomegaprint.fun";
use "twelf/src/tomega/typecheck.sig";
use "twelf/src/tomega/typecheck.fun";
use "twelf/src/tomega/opsem.sig";
use "twelf/src/tomega/opsem.fun";
use "twelf/src/tomega/redundant.sig";
use "twelf/src/tomega/redundant.fun";
use "twelf/src/tomega/converter.sig";
use "twelf/src/tomega/converter.fun";
use "twelf/src/tomega/coverage.sig";
use "twelf/src/tomega/coverage.fun";
use "twelf/src/tomega/tomega.sml";
use "twelf/src/frontend/recon-term.sig";
use "twelf/src/frontend/recon-term.fun";
use "twelf/src/frontend/recon-condec.sig";
use "twelf/src/frontend/recon-condec.fun";
use "twelf/src/frontend/recon-query.sig";
use "twelf/src/frontend/recon-query.fun";
use "twelf/src/frontend/recon-mode.sig";
use "twelf/src/frontend/recon-mode.fun";
use "twelf/src/frontend/recon-thm.sig";
use "twelf/src/frontend/recon-thm.fun";
use "twelf/src/frontend/recon-module.sig";
use "twelf/src/frontend/recon-module.fun";
use "twelf/src/frontend/parsing.sig";
use "twelf/src/frontend/parsing.fun";
use "twelf/src/frontend/parse-term.sig";
use "twelf/src/frontend/parse-term.fun";
use "twelf/src/frontend/parse-condec.sig";
use "twelf/src/frontend/parse-condec.fun";
use "twelf/src/frontend/parse-query.sig";
use "twelf/src/frontend/parse-query.fun";
use "twelf/src/frontend/parse-fixity.sig";
use "twelf/src/frontend/parse-fixity.fun";
use "twelf/src/frontend/parse-mode.sig";
use "twelf/src/frontend/parse-mode.fun";
use "twelf/src/frontend/parse-thm.sig";
use "twelf/src/frontend/parse-thm.fun";
use "twelf/src/frontend/parse-module.sig";
use "twelf/src/frontend/parse-module.fun";
use "twelf/src/frontend/parser.sig";
use "twelf/src/frontend/parser.fun";
use "twelf/src/frontend/solve.sig";
use "twelf/src/frontend/solve.fun";
use "twelf/src/frontend/fquery.sig";
use "twelf/src/frontend/fquery.fun";
use "twelf/src/frontend/unknownexn.sig";
use "twelf/src/frontend/twelf.fun";
use "twelf/src/frontend/unknownexn.fun";
use "twelf/src/frontend/unknownexn-stub.sml";
use "twelf/src/frontend/frontend.sml";
use "twelf/src/server/sigint.sig";
use "twelf/src/server/sigint-polyml.sml";
use "twelf/src/server/server.sml";


(* Delphin *)

PolyML.print_depth 15;
PolyML.error_depth 15;

fun stackTrace f = PolyML.exception_trace(fn () => f);

open PolyML.Debug;
(* Manual at: http://www.polyml.org/docs/Debugging.html *)

PolyML.Compiler.debug := true;
use "elaboration/extSyntax.sml";
use "elaboration/intSyntax.sml";
use "elaboration/abstract2.fun";
use "elaboration/world.fun";
use "elaboration/approx.sml";
use "elaboration/tempSyntax.sml";
use "elaboration/abstract.sig";
use "elaboration/abstract.fun";
use "elaboration/abstract.sml";
use "elaboration/unifyDelphin.fun";
use "elaboration/unifyDelphin.sml";
use "typecheck/typecheck.sig";
use "typecheck/typecheck.fun";
use "elaboration/worldChecker.fun";
use "elaboration/normalizeDelphin.sml";
use "elaboration/printDelphinExt.sml";
use "elaboration/printDelphinInt.sml";
use "elaboration/strict.sml";
use "elaboration/coverage.fun";

use "elaboration/convert.sig";
use "elaboration/convert.fun";

use "opsem/opsem.sig";
use "opsem/opsem.fun";

use "elaboration/terminate.sml";


(* delphin Frontend *)
(* If you change the lexer or grammar
 * you MUST run ml-lex and ml-yacc MANUALLY
 *)
use "frontend/ml-yacc-lib-mod/base.sig";
use "frontend/ml-yacc-lib-mod/join.sml";
use "frontend/ml-yacc-lib-mod/lrtable.sml";
use "frontend/ml-yacc-lib-mod/stream.sml";
use "frontend/ml-yacc-lib-mod/parser2.sml";

use "frontend/LFparsing.sml";
use "frontend/interface.sig";
use "frontend/interface.fun";
PolyML.Compiler.debug := false;
use "frontend/delphin.grm.sig";
use "frontend/polyUnsafe.sml"; (* Dummy "Unsafe" structure for lexer *)
use "frontend/delphin.lex.sml"; 
use "frontend/delphin.grm.sml";
use "frontend/parse-prg.sig";
use "frontend/parse-prg.fun";
PolyML.Compiler.debug := true;
use "frontend/delphin.sig";
use "frontend/delphin.fun";
use "frontend/delphin.sml";
